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
