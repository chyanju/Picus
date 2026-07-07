//! CDCL(T) main loop.
//!
//! Drives [`sat::Solver`] step by step, notifying the theory plug-in
//! of each newly-committed literal and consulting it at full
//! assignment. Theory conflicts become learnt clauses via
//! [`sat::Solver::add_theory_lemma_with_trail`].

use std::collections::HashMap;

use num_bigint::BigUint;

use crate::frontend::formula::Formula;
use crate::metric;
use crate::solve::{SolveOutcome, UnknownCause};
use crate::sat::{ConflictOutcome, LBool, Lit, Solver, Var};
use crate::timeout::CancelToken;

use super::atoms::AtomTable;
use super::cnf::{tseitin, TseitinResult};
use super::ee_filtered::EeFilteredTheory;
use super::equality_engine::{EqualityEngine, RegisterOutcome};
use super::ff_theory::FfTheory;
use super::ff_theory_incremental::IncrementalFfTheoryState;
use super::multi_prime::FfTheoryRouter;
use super::theory::{CheckOutcome, Theory};

/// The UF section of a query: applications plus their symbol table,
/// both in the producing builder's frame. An empty section makes
/// [`solve_formula_with_ufs`] construct exactly the objects
/// [`solve_formula`] always has (bit-identity for UF-free queries).
pub struct UfSection<'a> {
    pub apps: &'a [crate::frontend::encoder::UfApp],
    pub symbols: &'a [String],
}

impl UfSection<'static> {
    pub fn empty() -> Self {
        UfSection { apps: &[], symbols: &[] }
    }
}

/// Solve a `Formula` over GF(`prime`) via CDCL(T) with the FF theory.
/// `var_names` is the producing builder's variable frame (used by
/// the SAT-side atom table to reverse-resolve `PolyTerm` indices to
/// names for `AtomKey` canonicalisation). `Sat(model)` carries the
/// FF variable assignments; `Unknown` is returned on cancellation,
/// theory `Unknown`, or iteration cap.
pub fn solve_formula(
    prime: BigUint,
    var_names: &[String],
    formula: &Formula,
    cancel: &CancelToken,
) -> SolveOutcome {
    solve_formula_with_ufs(prime, var_names, formula, UfSection::empty(), cancel)
}

/// UF-aware CDCL(T) entry: solve `formula ∧ congruence(ufs)`.
///
/// With an empty UF section this is exactly [`solve_formula`]. With
/// applications present the `uf_mode` knob picks the decision
/// procedure: `lazy` (default) runs the congruence-closure equality
/// hub combined with the FF theory; `ackermann` eagerly expands the
/// congruence axiom before the loop and certifies every Sat by
/// 0-filling app-referenced variables absent from the atom-var-only
/// post-check model, then checking congruence — including the Tseitin
/// `Constant(true)` shortcut, whose bare empty model would otherwise
/// bypass certification.
pub fn solve_formula_with_ufs(
    prime: BigUint,
    var_names: &[String],
    formula: &Formula,
    ufs: UfSection<'_>,
    cancel: &CancelToken,
) -> SolveOutcome {
    if ufs.apps.is_empty() {
        return solve_formula_ff(prime, var_names, formula, cancel);
    }
    if !picus_core::config::with(|c| c.uf_enabled) {
        log::debug!("cdclt: uf_enabled = false; refusing a UF-bearing query");
        return SolveOutcome::Unknown(UnknownCause::UfUnsupported);
    }
    metric::incr!(crate::profile::NATIVE_FF.uf_cdclt_entries);
    match picus_core::config::with(|c| c.uf_mode) {
        picus_core::config::UfMode::Ackermann => {
            solve_formula_uf_ackermann(prime, var_names, formula, ufs, cancel)
        }
        picus_core::config::UfMode::Lazy => {
            solve_formula_uf_lazy(prime, var_names, formula, ufs, cancel)
        }
    }
}

/// Eager leg (`uf_mode = ackermann`): expand the congruence axiom into
/// Boolean clauses, run the FF pipeline, congruence-certify any Sat.
fn solve_formula_uf_ackermann(
    prime: BigUint,
    var_names: &[String],
    formula: &Formula,
    ufs: UfSection<'_>,
    cancel: &CancelToken,
) -> SolveOutcome {
    let pair_cap = picus_core::config::with(|c| c.uf_pair_cap);
    let (expanded, care_complete) =
        match crate::frontend::uf::ackermannize(formula, ufs.apps, pair_cap) {
            Ok(x) => x,
            Err(kind) => {
                log::debug!("cdclt: uf expansion refused: {}", kind);
                return SolveOutcome::Unknown(match kind {
                    crate::frontend::uf::UfRefusalKind::Disabled => UnknownCause::UfUnsupported,
                    crate::frontend::uf::UfRefusalKind::PairCap { .. } => UnknownCause::UfCap,
                });
            }
        };
    match solve_formula_ff(prime, var_names, &expanded, cancel) {
        SolveOutcome::Sat(model) => crate::frontend::uf::certify_uf_sat(
            model,
            ufs.apps,
            ufs.symbols,
            var_names,
            care_complete,
            true,
        ),
        other => other,
    }
}

/// Lazy leg (`uf_mode = lazy`, the default): the congruence-closure
/// equality hub ([`super::uf_theory::UfCombinedTheory`]) combined with
/// the FF theory over the UNEXPANDED formula.
///
/// Setup, all pre-loop at root level:
/// 1. Tseitin as today (a `Constant(true)` formula proceeds — the
///    apps still need a certified model, never a bare `Sat({})`).
/// 2. Build the e-graph: one Var node per referenced frame index, one
///    App node per application, definitionally merged with its result
///    variable. Symbols arrive pre-interned per solve — this alone is
///    the cross-copy congruence mechanism.
/// 3. Care-atom interning (the arrangement vocabulary): per symbol,
///    per application pair, the differing argument-position atoms plus
///    the result atom, each registered as a trigger + hub view;
///    bounded by `uf_pair_cap` (deterministic prefix + degraded
///    continue). Plus ingestion of every pre-existing equality-shaped
///    atom (var = var / var = const) as a trigger — the FF→hub channel
///    for known-wire equalities.
/// 4. Level-0 closure over the syntactic facts; every entailed trigger
///    atom is asserted as a pre-loop unit clause (`enqueue_theory`
///    rejects the empty reasons a first-round propagation would
///    carry). A conflicting unit surfaces root Unsat via BCP — zero
///    decisions, zero GB calls.
/// 5. The usual theory pipeline, wrapped UF-outermost; `cdclt_loop`
///    itself is unchanged (`all_assigned` forces every care atom
///    decided — that IS the equality-arrangement enumeration).
fn solve_formula_uf_lazy(
    prime: BigUint,
    var_names: &[String],
    formula: &Formula,
    ufs: UfSection<'_>,
    cancel: &CancelToken,
) -> SolveOutcome {
    use std::collections::HashMap as Map;
    use std::rc::Rc;

    use super::egraph::{EGraph, TermId};
    use super::uf_theory::{UfOutcomeFlags, UfSetup};
    use crate::frontend::encoder::{PolyTerm, UfApp};

    let pair_cap = picus_core::config::with(|c| c.uf_pair_cap);
    if pair_cap == 0 {
        // The immediate-refusal test convention, shared with the
        // eager leg's precheck.
        return SolveOutcome::Unknown(UnknownCause::UfCap);
    }

    let mut sat = Solver::new();
    let mut atoms = AtomTable::new(prime.clone());
    let top = match tseitin(formula, var_names, &mut atoms, &mut sat) {
        TseitinResult::Constant(true) => None,
        TseitinResult::Constant(false) => return SolveOutcome::Unsat(None),
        TseitinResult::Lit(l) => Some(l),
    };
    if let Some(top) = top {
        if !sat.add_clause(vec![top]) {
            return SolveOutcome::Unsat(None);
        }
        if sat.is_unsat() {
            return SolveOutcome::Unsat(None);
        }
    }

    // ---- e-graph over the applications ----
    let mut eg = EGraph::new();
    let mut var_nodes: Map<u32, TermId> = Map::new();
    fn node_of(eg: &mut EGraph, map: &mut std::collections::HashMap<u32, TermId>, idx: u32) -> TermId {
        *map.entry(idx).or_insert_with(|| eg.add_var(idx))
    }
    // Dedup exact duplicates (same symbol, args, result) so the pair
    // budget matches the eager leg's accounting.
    let mut seen: std::collections::HashSet<&UfApp> = std::collections::HashSet::new();
    let mut deduped: Vec<&UfApp> = Vec::with_capacity(ufs.apps.len());
    for app in ufs.apps {
        if seen.insert(app) {
            deduped.push(app);
        }
    }
    for app in &deduped {
        let arg_nodes: Vec<TermId> = app
            .args
            .iter()
            .map(|&a| node_of(&mut eg, &mut var_nodes, a))
            .collect();
        let app_node = eg.add_app(app.symbol, &arg_nodes);
        let r_node = node_of(&mut eg, &mut var_nodes, app.result);
        eg.merge_definitional(app_node, r_node);
    }

    // ---- care-atom interning ----
    let vterm = |v: u32| -> Vec<PolyTerm> {
        vec![PolyTerm { coeff: BigUint::from(1u32), vars: vec![(v, 1)] }]
    };
    let mut atom_view: Map<Var, (TermId, TermId)> = Map::new();
    let mut groups: std::collections::BTreeMap<u32, Vec<&UfApp>> =
        std::collections::BTreeMap::new();
    for app in &deduped {
        groups.entry(app.symbol).or_default().push(app);
    }
    let mut emitted: u64 = 0;
    let mut truncated = false;
    'care: for group in groups.values() {
        let m = group.len();
        if m < 2 {
            continue;
        }
        if group[0].args.is_empty() {
            // Nullary symbols: the setup closure merges the app nodes,
            // but the FF theory only learns the entailed result
            // equalities through registered trigger atoms — chain them
            // (m−1 atoms, mirroring ackermannize's nullary budget) so
            // the level-0 unit assertion below can carry them across.
            for app in group.iter().skip(1) {
                if emitted >= pair_cap {
                    truncated = true;
                    break 'care;
                }
                emitted += 1;
                if !app.args.is_empty() || group[0].result == app.result {
                    continue;
                }
                let (x, y) = (group[0].result, app.result);
                match atoms.intern_eq(&vterm(x), &vterm(y), var_names, &mut sat) {
                    crate::cdclt::atoms::InternResult::Var(v) => {
                        let tx = node_of(&mut eg, &mut var_nodes, x);
                        let ty = node_of(&mut eg, &mut var_nodes, y);
                        eg.register_trigger_atom(tx, ty, v);
                        atom_view.insert(v, (tx, ty));
                    }
                    crate::cdclt::atoms::InternResult::Trivial(_) => {}
                }
            }
            continue;
        }
        for i in 0..m {
            for j in (i + 1)..m {
                if emitted >= pair_cap {
                    truncated = true;
                    break 'care;
                }
                emitted += 1;
                let (ai, aj) = (group[i], group[j]);
                if ai.args.len() != aj.args.len() {
                    continue;
                }
                let mut pair_atoms: Vec<(u32, u32)> = Vec::new();
                for (&x, &y) in ai.args.iter().zip(aj.args.iter()) {
                    if x != y {
                        pair_atoms.push((x, y));
                    }
                }
                if ai.result != aj.result {
                    pair_atoms.push((ai.result, aj.result));
                }
                for (x, y) in pair_atoms {
                    match atoms.intern_eq(&vterm(x), &vterm(y), var_names, &mut sat) {
                        crate::cdclt::atoms::InternResult::Var(v) => {
                            let tx = node_of(&mut eg, &mut var_nodes, x);
                            let ty = node_of(&mut eg, &mut var_nodes, y);
                            eg.register_trigger_atom(tx, ty, v);
                            atom_view.insert(v, (tx, ty));
                        }
                        crate::cdclt::atoms::InternResult::Trivial(_) => {}
                    }
                }
            }
        }
    }
    let care_complete = !truncated;
    if truncated {
        log::debug!(
            target: "picus::gb_stats",
            "cdclt: care-atom interning truncated at uf_pair_cap = {}; continuing degraded",
            pair_cap
        );
    }

    // ---- ingest pre-existing equality-shaped atoms as triggers ----
    let name_to_idx: Map<&str, u32> = var_names
        .iter()
        .enumerate()
        .map(|(i, n)| (n.as_str(), i as u32))
        .collect();
    for i in 0..atoms.n_atom_slots() {
        let v = Var(i as u32);
        if atoms.is_auxiliary(v) || atom_view.contains_key(&v) {
            continue;
        }
        let Some(key) = atoms.atom(v) else { continue };
        if let Some((na, nb)) = key.as_var_pair_eq(&prime) {
            if let (Some(&ia), Some(&ib)) =
                (name_to_idx.get(na.as_str()), name_to_idx.get(nb.as_str()))
            {
                let ta = node_of(&mut eg, &mut var_nodes, ia);
                let tb = node_of(&mut eg, &mut var_nodes, ib);
                eg.register_trigger_atom(ta, tb, v);
                atom_view.insert(v, (ta, tb));
            }
        } else if let Some((name, value)) = key.as_single_var_eq(&prime) {
            if let Some(&iv) = name_to_idx.get(name.as_str()) {
                let tv = node_of(&mut eg, &mut var_nodes, iv);
                let tc = eg.add_const(&value);
                eg.register_trigger_atom(tv, tc, v);
                atom_view.insert(v, (tv, tc));
            }
        }
    }

    // ---- level-0 closure + unit assertion (setup entailments) ----
    for (v, pol) in eg.closure_entailed_triggers() {
        let lit = if pol { Lit::pos(v) } else { Lit::neg(v) };
        if !sat.add_clause(vec![lit]) {
            return SolveOutcome::Unsat(None);
        }
    }
    if sat.is_unsat() {
        return SolveOutcome::Unsat(None);
    }

    // ---- wrap the theory pipeline UF-outermost and run ----
    let flags = Rc::new(UfOutcomeFlags::default());
    let setup = UfSetup {
        eg,
        atom_view,
        apps: ufs.apps.to_vec(),
        symbols: ufs.symbols.to_vec(),
        var_names: var_names.to_vec(),
        prime: prime.clone(),
        care_complete,
        flags: Rc::clone(&flags),
    };

    let choice = resolve_theory_choice();
    let use_ee = picus_core::config::with(|c| c.cdclt_equality_engine);
    let ee = if use_ee {
        let mut e = EqualityEngine::new();
        let mut contradiction = false;
        for i in 0..atoms.n_atom_slots() {
            let v = Var(i as u32);
            if atoms.is_auxiliary(v) {
                continue;
            }
            if let Some(key) = atoms.atom(v) {
                if let RegisterOutcome::Contradiction = e.register_atom(v, key) {
                    contradiction = true;
                    break;
                }
            }
        }
        if contradiction {
            return SolveOutcome::Unsat(None);
        }
        Some(e)
    } else {
        None
    };

    fn run_uf<T: Theory>(
        sat: &mut Solver,
        inner: T,
        ee: Option<EqualityEngine>,
        setup: super::uf_theory::UfSetup,
        cancel: &CancelToken,
    ) -> SolveOutcome {
        match ee {
            Some(e) => {
                let mut th = super::uf_theory::UfCombinedTheory::new(
                    EeFilteredTheory::new(e, inner),
                    setup,
                );
                cdclt_loop(sat, &mut th, cancel)
            }
            None => {
                let mut th = super::uf_theory::UfCombinedTheory::new(inner, setup);
                cdclt_loop(sat, &mut th, cancel)
            }
        }
    }
    let outcome = match choice {
        TheoryChoice::Router => {
            let mut router = FfTheoryRouter::new(vec![atoms], cancel);
            let n_slots = router.slot_atoms_mut(0).n_atom_slots();
            for i in 0..n_slots {
                let v = Var(i as u32);
                if router.slot_atoms_mut(0).atom(v).is_some() {
                    router.assign_var(v, 0);
                }
            }
            run_uf(&mut sat, router, ee, setup, cancel)
        }
        TheoryChoice::Incremental => {
            let max_vars = var_names.len() + atoms.n_atom_slots() + 64;
            let theory = IncrementalFfTheoryState::new(&atoms, cancel, max_vars);
            run_uf(&mut sat, theory, ee, setup, cancel)
        }
        TheoryChoice::Plain => {
            let theory = FfTheory::new(&atoms, cancel);
            run_uf(&mut sat, theory, ee, setup, cancel)
        }
    };

    // Refine the surfaced cause from the hub's post-solve flags.
    match outcome {
        SolveOutcome::Unknown(UnknownCause::DegradedTheory) if flags.degraded_by_cap.get() => {
            SolveOutcome::Unknown(UnknownCause::UfCap)
        }
        SolveOutcome::Unknown(UnknownCause::DegradedTheory) if flags.infeasible.get() => {
            SolveOutcome::Unknown(UnknownCause::UfIncomplete)
        }
        other => other,
    }
}

/// The FF-only CDCL(T) pipeline (the pre-UF `solve_formula` body).
fn solve_formula_ff(
    prime: BigUint,
    var_names: &[String],
    formula: &Formula,
    cancel: &CancelToken,
) -> SolveOutcome {
    let mut sat = Solver::new();
    let mut atoms = AtomTable::new(prime);
    let top = match tseitin(formula, var_names, &mut atoms, &mut sat) {
        TseitinResult::Constant(true) => return SolveOutcome::Sat(HashMap::new()),
        TseitinResult::Constant(false) => return SolveOutcome::Unsat(None),
        TseitinResult::Lit(l) => l,
    };
    if !sat.add_clause(vec![top]) {
        return SolveOutcome::Unsat(None);
    }
    if sat.is_unsat() {
        return SolveOutcome::Unsat(None);
    }

    let choice = resolve_theory_choice();
    let use_ee = picus_core::config::with(|c| c.cdclt_equality_engine);

    // Build the EE once if requested; it is generic over the inner
    // theory choice (FfTheory or FfTheoryRouter).
    let ee = if use_ee {
        let mut e = EqualityEngine::new();
        for i in 0..atoms.n_atom_slots() {
            let v = Var(i as u32);
            if atoms.is_auxiliary(v) {
                continue;
            }
            if let Some(key) = atoms.atom(v) {
                if let RegisterOutcome::Contradiction = e.register_atom(v, key) {
                    // Two atoms whose canonical polynomials match and
                    // whose polarities already disagree at registration
                    // — impossible today (no notifies have fired yet),
                    // but the path is sound: return root-level UNSAT.
                    return SolveOutcome::Unsat(None);
                }
            }
        }
        Some(e)
    } else {
        None
    };

    match choice {
        TheoryChoice::Router => {
            let mut router = FfTheoryRouter::new(vec![atoms], cancel);
            let n_slots = router.slot_atoms_mut(0).n_atom_slots();
            for i in 0..n_slots {
                let v = Var(i as u32);
                if router.slot_atoms_mut(0).atom(v).is_some() {
                    router.assign_var(v, 0);
                }
            }
            run_with_optional_ee(&mut sat, router, ee, cancel)
        }
        TheoryChoice::Incremental => {
            // Conservative max-vars budget: every named variable plus every
            // atom slot can claim a ring slot (atoms are interned eagerly via
            // user names; aux-only slots never reach `build_atom_polys`).
            // Disequality witnesses claim additional slots; bound them by
            // the same conservative cap so a `degraded` flip from
            // slot-budget exhaustion is reachable only on pathological
            // inputs.
            let max_vars = var_names.len() + atoms.n_atom_slots() + 64;
            let theory = IncrementalFfTheoryState::new(&atoms, cancel, max_vars);
            run_with_optional_ee(&mut sat, theory, ee, cancel)
        }
        TheoryChoice::Plain => {
            let theory = FfTheory::new(&atoms, cancel);
            run_with_optional_ee(&mut sat, theory, ee, cancel)
        }
    }
}

/// Resolved theory pipeline for one solve.
enum TheoryChoice {
    Router,
    Incremental,
    Plain,
}

/// Compute the theory choice once from the knob pair, with explicit
/// precedence (Router > Incremental > Plain). A knob shadowed by a
/// higher-precedence knob is warned about: a benchmark run that flips
/// the shadowed knob would otherwise silently measure nothing.
fn resolve_theory_choice() -> TheoryChoice {
    let use_router = picus_core::config::with(|c| c.cdclt_multi_prime_router);
    let use_incremental = picus_core::config::with(|c| c.cdclt_incremental_theory);
    if use_router {
        if use_incremental {
            log::warn!(
                "cdclt_incremental_theory is shadowed by cdclt_multi_prime_router; \
                 the incremental theory will not run"
            );
        }
        TheoryChoice::Router
    } else if use_incremental {
        TheoryChoice::Incremental
    } else {
        TheoryChoice::Plain
    }
}

/// Drive the CDCL(T) loop over `theory`, wrapped in the equality engine
/// when one was built — the single owner of the EE-wrap-or-not branch.
fn run_with_optional_ee<T: Theory>(
    sat: &mut Solver,
    theory: T,
    ee: Option<EqualityEngine>,
    cancel: &CancelToken,
) -> SolveOutcome {
    match ee {
        Some(e) => {
            let mut wrapped = EeFilteredTheory::new(e, theory);
            cdclt_loop(sat, &mut wrapped, cancel)
        }
        None => {
            let mut theory = theory;
            cdclt_loop(sat, &mut theory, cancel)
        }
    }
}

/// Multi-prime entry: solve a list of per-prime `(prime, var_names,
/// formula)` triples against a single SAT solver and a
/// [`FfTheoryRouter`]. Tseitin runs once per prime so each tseitin
/// call's atoms intern into the matching prime's [`AtomTable`]; the
/// resulting top-level literals are conjoined as unit clauses.
///
/// A length-1 input degrades to the single-prime path
/// ([`solve_formula`]) verbatim so callers can route both shapes
/// through the same multi-prime API.
///
/// Precondition: per-prime `var_names` sets are disjoint (cross-prime
/// equalities are ill-typed SMT-LIB, and `parse_boolean_multi` rejects
/// them). The router's model join guards this: a colliding name with a
/// conflicting value degrades the check to Unknown rather than
/// returning a last-writer-wins witness.
///
/// UF applications are NOT supported on this entry (a symbol spanning
/// primes is ill-typed): the signature carries bare formulas, so a
/// caller holding a UF-bearing builder must refuse with
/// `Unknown(UfUnsupported)` before extracting the formula — silently
/// dropping the applications would weaken the query (spurious SAT).
///
/// PARKED: no production caller — see `smt2::parse_boolean_multi`.
#[doc(hidden)]
#[allow(dead_code)] // parked: no production caller yet
pub(crate) fn solve_formula_multi(
    primes_subs: Vec<(BigUint, Vec<String>, crate::frontend::formula::Formula)>,
    cancel: &CancelToken,
) -> SolveOutcome {
    if primes_subs.len() == 1 {
        let (prime, var_names, formula) = primes_subs.into_iter().next().unwrap();
        return solve_formula(prime, &var_names, &formula, cancel);
    }

    // This entry always routes through FfTheoryRouter; the incremental
    // and equality-engine knobs do not apply here.
    if picus_core::config::with(|c| c.cdclt_incremental_theory || c.cdclt_equality_engine) {
        log::warn!(
            "cdclt_incremental_theory / cdclt_equality_engine are ignored \
             on the multi-prime path"
        );
    }
    let mut sat = Solver::new();
    let mut atoms_by_prime: Vec<AtomTable> = Vec::with_capacity(primes_subs.len());
    // Slot index in the router matches the order of `primes_subs`.
    // `var_to_slot` maps every non-aux SAT Var produced by tseitin to
    // its owning slot so the router routes facts to the correct
    // sub-theory at notify time.
    let mut var_to_slot: HashMap<Var, usize> = HashMap::new();

    for (slot_idx, (prime, var_names, formula)) in primes_subs.into_iter().enumerate() {
        let mut atoms = AtomTable::new(prime);
        let top = match tseitin(&formula, &var_names, &mut atoms, &mut sat) {
            TseitinResult::Constant(true) => {
                atoms_by_prime.push(atoms);
                continue;
            }
            TseitinResult::Constant(false) => return SolveOutcome::Unsat(None),
            TseitinResult::Lit(l) => l,
        };
        if !sat.add_clause(vec![top]) {
            atoms_by_prime.push(atoms);
            return SolveOutcome::Unsat(None);
        }
        if sat.is_unsat() {
            atoms_by_prime.push(atoms);
            return SolveOutcome::Unsat(None);
        }
        // Snapshot every non-aux Var atoms touched into the slot map.
        for i in 0..atoms.n_atom_slots() {
            let v = Var(i as u32);
            if atoms.atom(v).is_some() {
                var_to_slot.insert(v, slot_idx);
            }
        }
        atoms_by_prime.push(atoms);
    }

    let mut router = FfTheoryRouter::new(atoms_by_prime, cancel);
    for (v, slot) in var_to_slot {
        router.assign_var(v, slot);
    }
    cdclt_loop(&mut sat, &mut router, cancel)
}

/// Max CDCL(T) main-loop iterations before [`cdclt_loop`] returns
/// `Unknown`. Configured via [`crate::config::RuntimeConfig::cdclt_iter_cap`].
pub(crate) fn iter_cap() -> u64 {
    crate::config::with(|c| c.cdclt_iter_cap)
}

fn cdclt_loop<T: Theory>(
    sat: &mut Solver,
    theory: &mut T,
    cancel: &CancelToken,
) -> SolveOutcome {
    let mut notified: usize = 0;
    let mut theory_levels: usize = 0;
    let cap = iter_cap();
    let mut iters: u64 = 0;

    loop {
        if cancel.is_cancelled() {
            return SolveOutcome::Unknown(UnknownCause::Cancelled);
        }
        iters += 1;
        if iters > cap {
            log::debug!(
                target: "picus::gb_stats",
                "cdclt: iteration cap reached (cdclt_iter_cap = {})",
                cap
            );
            metric::incr!(crate::profile::UNKNOWNS.iter_cap_hits);
            return SolveOutcome::Unknown(UnknownCause::IterCap);
        }

        if let Some(conflict) = sat.propagate() {
            match sat.handle_conflict(conflict) {
                ConflictOutcome::RootUnsat => return SolveOutcome::Unsat(None),
                ConflictOutcome::GiveUp => {
                    return SolveOutcome::Unknown(UnknownCause::DegradedTheory)
                }
                ConflictOutcome::Learned { trail_pre } => {
                    resync_after_lemma(sat, theory, &mut theory_levels, &mut notified, trail_pre);
                    continue;
                }
            }
        }

        sync_theory_after_propagate(sat, theory, &mut theory_levels);
        let trail = sat.trail();
        while notified < trail.len() {
            let lit = trail[notified];
            theory.notify_fact(lit.var(), lit.is_positive());
            notified += 1;
        }

        // Early partial-assignment check (defaults to None on every
        // shipped theory). An early Unsat feeds the same conflict path
        // as a post_check Unsat instead of deciding out the remaining
        // variables of a proven-inconsistent subtree; per the trait
        // contract an early Sat must already hold for every extension.
        if let Some(outcome) = theory.early_check() {
            match outcome {
                CheckOutcome::Unsat { core } => {
                    let trail_pre_lemma = apply_theory_conflict(sat, &core);
                    let trail_pre_lemma = match trail_pre_lemma {
                        Some(n) => n,
                        None if sat.gave_up() => {
                            return SolveOutcome::Unknown(UnknownCause::DegradedTheory)
                        }
                        None => return SolveOutcome::Unsat(None),
                    };
                    resync_after_lemma(sat, theory, &mut theory_levels, &mut notified, trail_pre_lemma);
                    continue;
                }
                CheckOutcome::Sat(model) => return SolveOutcome::Sat(model),
                // A partial-trail Unknown carries no information.
                CheckOutcome::Unknown => {}
            }
        }

        match run_theory_propagation(sat, theory) {
            TheoryStep::Progressed => continue,
            TheoryStep::Conflict(trail_pre_lemma) => {
                resync_after_lemma(sat, theory, &mut theory_levels, &mut notified, trail_pre_lemma);
                continue;
            }
            TheoryStep::RootUnsat => return SolveOutcome::Unsat(None),
            TheoryStep::GiveUp => return SolveOutcome::Unknown(UnknownCause::DegradedTheory),
            TheoryStep::Idle => {}
        }

        if sat.all_assigned() {
            match theory.post_check() {
                CheckOutcome::Sat(model) => {
                    // The model carried by the theory's final
                    // `post_check` already covers every named
                    // variable: Bool vars are encoded as FF elements
                    // in {0, 1} in the polynomial namespace, so they
                    // come through the GB SAT point alongside the FF
                    // vars. SAT-only aux vars (Tseitin literals) are
                    // intentionally not surfaced.
                    return SolveOutcome::Sat(model);
                }
                CheckOutcome::Unsat { core } => {
                    let trail_pre_lemma = apply_theory_conflict(sat, &core);
                    let trail_pre_lemma = match trail_pre_lemma {
                        Some(n) => n,
                        None if sat.gave_up() => {
                            return SolveOutcome::Unknown(UnknownCause::DegradedTheory)
                        }
                        None => return SolveOutcome::Unsat(None),
                    };
                    resync_after_lemma(sat, theory, &mut theory_levels, &mut notified, trail_pre_lemma);
                    continue;
                }
                CheckOutcome::Unknown => {
                    return SolveOutcome::Unknown(if cancel.is_cancelled() {
                        UnknownCause::Cancelled
                    } else {
                        UnknownCause::DegradedTheory
                    })
                }
            }
        }

        let next = sat.pick_decision().expect("not all assigned ⇒ Undef var exists");
        let ok = sat.decide(next);
        debug_assert!(ok);
    }
}

enum TheoryStep {
    /// No new derivation fired this round.
    Idle,
    /// At least one new literal was enqueued.
    Progressed,
    /// Lemma learnt and SAT backtracked; caller must sync theory.
    /// The wrapped value is the trail length right before the lemma's
    /// asserting literal was enqueued (see `add_theory_lemma_with_trail`).
    Conflict(usize),
    /// Lemma forced root-level UNSAT.
    RootUnsat,
    /// Theory-conflict resolution bailed; solve is Unknown (not UNSAT).
    GiveUp,
}

/// One round of theory propagation. Each derived `(atom, polarity)`
/// becomes a no-op (SAT agrees), an `enqueue_theory` (SAT Undef), or a
/// theory lemma (SAT disagrees).
fn run_theory_propagation<T: Theory>(sat: &mut Solver, theory: &mut T) -> TheoryStep {
    let props = theory.propagate();
    if props.is_empty() {
        return TheoryStep::Idle;
    }
    let mut progressed = false;
    for (atom_var, polarity) in props {
        let prop_lit = if polarity {
            Lit::pos(atom_var)
        } else {
            Lit::neg(atom_var)
        };
        match sat.value(atom_var) {
            LBool::Undef => {
                let reason_facts = theory.explain(atom_var, polarity);
                let reason_lits: Vec<Lit> = reason_facts
                    .iter()
                    .map(|&(v, p)| if p { Lit::pos(v) } else { Lit::neg(v) })
                    .collect();
                if sat.enqueue_theory(prop_lit, reason_lits) {
                    progressed = true;
                }
            }
            LBool::True if polarity => {}
            LBool::False if !polarity => {}
            _ => {
                let reason_facts = theory.explain(atom_var, polarity);
                let mut lemma: Vec<Lit> = Vec::with_capacity(reason_facts.len() + 1);
                lemma.push(prop_lit);
                for (fav, fpol) in reason_facts {
                    let fl = if fpol { Lit::pos(fav) } else { Lit::neg(fav) };
                    lemma.push(-fl);
                }
                match sat.add_theory_lemma_with_trail(lemma) {
                    Some(trail_pre) => return TheoryStep::Conflict(trail_pre),
                    None if sat.gave_up() => return TheoryStep::GiveUp,
                    None => return TheoryStep::RootUnsat,
                }
            }
        }
    }
    if progressed {
        TheoryStep::Progressed
    } else {
        TheoryStep::Idle
    }
}

/// Turn an atom-core into a SAT lemma and apply it. On success returns
/// `Some(trail_len_before_asserting)` (the position the lemma's
/// asserting literal sits at after the internal backtrack). Returns
/// `None` if the lemma forces root-level UNSAT. An Undef core var
/// indicates the theory's push/pop state diverged from SAT's.
fn apply_theory_conflict(sat: &mut Solver, core: &[Var]) -> Option<usize> {
    let mut lits: Vec<Lit> = Vec::with_capacity(core.len());
    for &v in core {
        match sat.value(v) {
            LBool::True => lits.push(Lit::neg(v)),
            LBool::False => lits.push(Lit::pos(v)),
            LBool::Undef => {
                // A theory core literal that is unassigned in SAT means the
                // theory's fact trail diverged from SAT's assignment (a
                // push/pop accounting violation). Building a conflict clause
                // from a partial core, or reporting UNSAT, would be unsound;
                // bail to Unknown instead of panicking on a valid input.
                log::warn!(
                    "theory core var {:?} is Undef (theory/SAT trail divergence); giving up to Unknown",
                    v
                );
                sat.mark_give_up();
                return None;
            }
        }
    }
    sat.add_theory_lemma_with_trail(lits)
}

fn sync_theory_after_propagate<T: Theory>(
    sat: &Solver,
    theory: &mut T,
    theory_levels: &mut usize,
) {
    let dl = sat.decision_level() as usize;
    // The main loop makes at most one decision per iteration and syncs every
    // iteration, so `dl` rises by at most 1 per call: the loop pushes a single
    // level whose `facts.len()` snapshot (see `Theory::push`) belongs to
    // exactly that decision level. If decisions were ever batched, multiple
    // pushes here would snapshot the same `facts.len()` and a later single
    // `pop()` would discard several levels' facts at once, desyncing the theory
    // trail from SAT. Enforce the invariant so such a change fails loudly.
    debug_assert!(
        dl <= *theory_levels + 1,
        "theory push assumes <=1 new decision level per sync (dl={dl}, theory_levels={})",
        *theory_levels
    );
    while *theory_levels < dl {
        theory.push();
        *theory_levels += 1;
    }
}

fn sync_theory_after_backtrack<T: Theory>(
    sat: &Solver,
    theory: &mut T,
    theory_levels: &mut usize,
) {
    let dl = sat.decision_level() as usize;
    while *theory_levels > dl {
        theory.pop();
        *theory_levels -= 1;
    }
}

/// Resync after a lemma forced a backjump: rewind the theory trail to the
/// new decision level and rewind `notified` so the next pass re-notifies
/// from the position the asserting literal now occupies. The three lemma
/// sites (propagation conflict, theory-propagation disagreement, post-check
/// UNSAT) must use the identical rewind formula, so it lives here once.
fn resync_after_lemma<T: Theory>(
    sat: &Solver,
    theory: &mut T,
    theory_levels: &mut usize,
    notified: &mut usize,
    trail_pre_lemma: usize,
) {
    sync_theory_after_backtrack(sat, theory, theory_levels);
    *notified = (*notified).min(trail_pre_lemma).min(sat.trail_len());
}

#[cfg(test)]
#[path = "orchestrator_tests.rs"]
mod tests;
