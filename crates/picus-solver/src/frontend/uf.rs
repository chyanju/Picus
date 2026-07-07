//! Uninterpreted-function (UF) support: the eager Ackermann lowering
//! and the model-side congruence certification shared by every Sat
//! gate.
//!
//! The constraint language carries applications `r = f(a_1, ..., a_k)`
//! ([`crate::frontend::encoder::UfApp`]) whose only axiom is
//! congruence: equal argument tuples imply equal results.
//! `ackermannize` compiles the axiom into Boolean clauses over the
//! existing FF literals (atom-level Ackermann reduction — sound and
//! complete over GF(p) for the quantifier-free, variable-argument
//! language; Kroening & Strichman ch. 3), bounded by the
//! `uf_pair_cap` knob. [`verify_uf_congruence`] re-checks a candidate
//! model against the apps and produces the model-completing function
//! table; no Sat verdict for a UF-bearing query leaves the crate
//! without passing it.

use std::collections::{BTreeMap, HashMap};

use num_bigint::BigUint;

use crate::frontend::encoder::{PolyTerm, UfApp, UfSymbolId, VarIdx};
use crate::frontend::formula::{Formula, Literal};
use crate::solve::{SolveOutcome, UnknownCause};

/// Why a UF-bearing query was refused before solving.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UfRefusalKind {
    /// The `uf_enabled` kill switch is off.
    Disabled,
    /// The projected congruence-pair count exceeds `uf_pair_cap`
    /// with `cap = 0` (the immediate-refusal test convention).
    PairCap { pairs: usize, cap: u64 },
}

impl std::fmt::Display for UfRefusalKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UfRefusalKind::Disabled => f.write_str("uf_enabled = false"),
            UfRefusalKind::PairCap { pairs, cap } => {
                write!(f, "{} congruence pairs exceed uf_pair_cap = {}", pairs, cap)
            }
        }
    }
}

/// A (partial) function table: `(symbol, argument values) -> result
/// value`. Keys are VALUES, not variable identities, so cross-copy
/// consistency is checked automatically. Unlisted argument tuples are
/// unconstrained; the table extended by any default value elsewhere is
/// a total congruence-consistent function.
pub type UfTable = HashMap<(UfSymbolId, Vec<BigUint>), BigUint>;

/// Why a model failed UF certification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UfViolation {
    /// An argument or result variable of a multi-application symbol is
    /// absent from the model (single-application symbols are skipped:
    /// congruence is vacuous for one application).
    MissingVar { symbol: String, var: String },
    /// Two applications with equal evaluated argument tuples map to
    /// different results — the model violates congruence.
    Collision {
        symbol: String,
        args: Vec<BigUint>,
        r1: BigUint,
        r2: BigUint,
    },
}

impl std::fmt::Display for UfViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UfViolation::MissingVar { symbol, var } => {
                write!(f, "model is missing '{}' referenced by symbol '{}'", var, symbol)
            }
            UfViolation::Collision { symbol, args, r1, r2 } => {
                write!(
                    f,
                    "congruence violation on '{}'({:?}): {} vs {}",
                    symbol, args, r1, r2
                )
            }
        }
    }
}

fn symbol_name(symbols: &[String], id: UfSymbolId) -> String {
    symbols
        .get(id as usize)
        .cloned()
        .unwrap_or_else(|| format!("<uf#{}>", id))
}

/// Build the function table induced by `model` over `apps`, failing on
/// a congruence collision. Fail-closed for multi-application symbols:
/// a missing argument/result variable is an `Err`. Single-application
/// symbols with missing variables are SKIPPED (congruence is vacuous
/// for one application), so legitimate Sats never degrade over a
/// variable no constraint mentions.
pub fn build_uf_table(
    apps: &[UfApp],
    symbols: &[String],
    var_names: &[String],
    model: &HashMap<String, BigUint>,
) -> Result<UfTable, UfViolation> {
    let mut per_symbol_count: HashMap<UfSymbolId, usize> = HashMap::new();
    for app in apps {
        *per_symbol_count.entry(app.symbol).or_insert(0) += 1;
    }
    let lookup = |idx: VarIdx| -> Option<&BigUint> {
        var_names.get(idx as usize).and_then(|n| model.get(n))
    };
    let mut table: UfTable = HashMap::new();
    for app in apps {
        let single = per_symbol_count[&app.symbol] == 1;
        let mut vals: Vec<BigUint> = Vec::with_capacity(app.args.len());
        let mut missing: Option<VarIdx> = None;
        for &a in &app.args {
            match lookup(a) {
                Some(v) => vals.push(v.clone()),
                None => {
                    missing = Some(a);
                    break;
                }
            }
        }
        let result = if missing.is_none() { lookup(app.result) } else { None };
        let missing = missing.or(if result.is_none() { Some(app.result) } else { None });
        if let Some(m) = missing {
            if single {
                continue;
            }
            return Err(UfViolation::MissingVar {
                symbol: symbol_name(symbols, app.symbol),
                var: var_names
                    .get(m as usize)
                    .cloned()
                    .unwrap_or_else(|| format!("<var#{}>", m)),
            });
        }
        let result = result.expect("checked above").clone();
        match table.entry((app.symbol, vals)) {
            std::collections::hash_map::Entry::Vacant(e) => {
                e.insert(result);
            }
            std::collections::hash_map::Entry::Occupied(e) => {
                if *e.get() != result {
                    let (sym, args) = e.key().clone();
                    return Err(UfViolation::Collision {
                        symbol: symbol_name(symbols, sym),
                        args,
                        r1: e.get().clone(),
                        r2: result,
                    });
                }
            }
        }
    }
    Ok(table)
}

/// Certify that `model` respects congruence over `apps`: `Ok(table)`
/// iff equal evaluated argument tuples map to equal results, per
/// symbol. Intent-named alias of [`build_uf_table`] for the Sat gates.
pub fn verify_uf_congruence(
    apps: &[UfApp],
    symbols: &[String],
    var_names: &[String],
    model: &HashMap<String, BigUint>,
) -> Result<UfTable, UfViolation> {
    build_uf_table(apps, symbols, var_names, model)
}

fn var_term(v: VarIdx) -> Vec<PolyTerm> {
    vec![PolyTerm { coeff: BigUint::from(1u32), vars: vec![(v, 1)] }]
}

fn eq_lit(a: VarIdx, b: VarIdx) -> Formula {
    Formula::Lit(Literal::Eq(var_term(a), var_term(b)))
}

fn neq_lit(a: VarIdx, b: VarIdx) -> Formula {
    Formula::Lit(Literal::Neq(var_term(a), var_term(b)))
}

/// Eager Ackermann reduction: conjoin, onto `formula`, one congruence
/// clause per same-symbol application pair —
/// `¬(a_i^1 = a_j^1) ∨ ... ∨ ¬(a_i^k = a_j^k) ∨ (r_i = r_j)` — with:
/// exact-duplicate applications deduplicated; argument positions where
/// both applications name the same variable dropped (identical tuples
/// degenerate to the unit clause `r_i = r_j`); nullary symbols chained
/// as `r_1 = r_i` (m−1 unit clauses — valid because unconditional
/// equality is transitive; conditional k >= 1 pairs stay all-pairs).
///
/// Adds atoms/clauses only — zero ring variables. Returns the expanded
/// formula plus `care_complete`: `false` when `pair_cap` truncated the
/// emission to a deterministic prefix (Unsat stays sound — every
/// emitted clause is entailed — and Sat is then only accepted after
/// table certification). `pair_cap = 0` refuses immediately (the
/// `cdclt_iter_cap = 0` test convention).
///
/// The budget counts emitted clauses: C(m,2) per k>=1 symbol, m−1 per
/// nullary symbol.
pub(crate) fn ackermannize(
    formula: &Formula,
    apps: &[UfApp],
    pair_cap: u64,
) -> Result<(Formula, bool), UfRefusalKind> {
    if apps.is_empty() {
        return Ok((formula.clone(), true));
    }

    // Dedup exact duplicates, preserving first-occurrence order.
    let mut seen: std::collections::HashSet<&UfApp> = std::collections::HashSet::new();
    let mut deduped: Vec<&UfApp> = Vec::with_capacity(apps.len());
    for app in apps {
        if seen.insert(app) {
            deduped.push(app);
        }
    }

    // Group by symbol, ascending symbol id (deterministic emission
    // order), occurrence order within a group.
    let mut groups: BTreeMap<UfSymbolId, Vec<&UfApp>> = BTreeMap::new();
    for app in deduped {
        groups.entry(app.symbol).or_default().push(app);
    }

    // Projected budget, before any clause allocation.
    let mut projected: usize = 0;
    for group in groups.values() {
        let m = group.len();
        if m < 2 {
            continue;
        }
        let is_nullary = group[0].args.is_empty();
        projected = projected.saturating_add(if is_nullary { m - 1 } else { m * (m - 1) / 2 });
    }
    if pair_cap == 0 {
        return Err(UfRefusalKind::PairCap { pairs: projected, cap: 0 });
    }

    let mut clauses: Vec<Formula> = Vec::new();
    let mut emitted: u64 = 0;
    let mut truncated = false;
    'emit: for group in groups.values() {
        let m = group.len();
        if m < 2 {
            continue;
        }
        if group[0].args.is_empty() {
            // Nullary chain: r_1 = r_i. Guard against mixed-arity
            // groups (a poisoned input that slipped past an entry
            // refusal): an unconditional equality against a k>=1
            // application would over-constrain — congruence across
            // arities is vacuous, so skip such apps.
            for app in group.iter().skip(1) {
                if emitted >= pair_cap {
                    truncated = true;
                    break 'emit;
                }
                emitted += 1;
                if !app.args.is_empty() {
                    continue;
                }
                if group[0].result != app.result {
                    clauses.push(eq_lit(group[0].result, app.result));
                }
            }
            continue;
        }
        for i in 0..m {
            for j in (i + 1)..m {
                if emitted >= pair_cap {
                    truncated = true;
                    break 'emit;
                }
                emitted += 1;
                let (ai, aj) = (group[i], group[j]);
                if ai.args.len() != aj.args.len() {
                    // Different arities never produce equal argument
                    // tuples; congruence is vacuous for this pair.
                    // (Well-formed inputs never get here — the builder
                    // poisons arity mismatches — but a zipped
                    // comparison would silently compare a prefix and
                    // over-constrain, so guard explicitly.)
                    continue;
                }
                if ai.result == aj.result {
                    // The consequent is trivially true; so is the clause.
                    continue;
                }
                let mut lits: Vec<Formula> = Vec::new();
                for (x, y) in ai.args.iter().zip(aj.args.iter()) {
                    if x != y {
                        lits.push(neq_lit(*x, *y));
                    }
                }
                if lits.is_empty() {
                    // Identical argument tuples: unit r_i = r_j.
                    clauses.push(eq_lit(ai.result, aj.result));
                } else {
                    lits.push(eq_lit(ai.result, aj.result));
                    clauses.push(Formula::Or(lits));
                }
            }
        }
    }

    if truncated {
        log::debug!(
            target: "picus::gb_stats",
            "ackermannize: emitted {} of {} congruence clauses (uf_pair_cap = {}); \
             continuing degraded (Sat requires table certification)",
            emitted,
            projected,
            pair_cap
        );
    }
    let expanded = if clauses.is_empty() {
        formula.clone()
    } else {
        let mut parts = Vec::with_capacity(clauses.len() + 1);
        parts.push(formula.clone());
        parts.extend(clauses);
        Formula::And(parts)
    };
    Ok((expanded, !truncated))
}

/// Certify a candidate model against the apps before it may surface as
/// a verdict. Every Sat exit for a UF-bearing query passes through here
/// (or the equivalent hub check on the lazy path).
///
/// `fill_missing` distinguishes the two callers: the GB routes receive
/// full ring points and fill nothing; the CDCL(T) Ackermann route
/// receives atom-var-only models, so every app-referenced variable
/// missing from the model is 0-filled first —
/// under complete pair expansion the only missing multi-app variables
/// are shared-position variables, whose fill cannot change tuple
/// agreement, and under a degraded prefix a fill-induced collision
/// correctly fails certification.
///
/// Failure classification threads `care_complete`: a collision under a
/// COMPLETE expansion is defect-class (the expansion should have made
/// it unsatisfiable — log + typed Unknown, never Sat); under a
/// degraded prefix it is the expected budget outcome, `Unknown(UfCap)`
/// with no defect logging.
pub(crate) fn certify_uf_sat(
    mut model: HashMap<String, BigUint>,
    apps: &[UfApp],
    symbols: &[String],
    var_names: &[String],
    care_complete: bool,
    fill_missing: bool,
) -> SolveOutcome {
    if apps.is_empty() {
        return SolveOutcome::Sat(model);
    }
    if fill_missing {
        for app in apps {
            for &v in app.args.iter().chain(std::iter::once(&app.result)) {
                match var_names.get(v as usize) {
                    Some(name) => {
                        model.entry(name.clone()).or_insert_with(|| BigUint::from(0u32));
                    }
                    None => {
                        log::error!(
                            "uf gate: app references var index {} outside the frame ({} names)",
                            v,
                            var_names.len()
                        );
                        return SolveOutcome::Unknown(UnknownCause::UfIncomplete);
                    }
                }
            }
        }
    }
    match verify_uf_congruence(apps, symbols, var_names, &model) {
        Ok(table) => {
            log::debug!(
                target: "picus::gb_stats",
                "uf gate: model certified; function table has {} entries",
                table.len()
            );
            SolveOutcome::Sat(model)
        }
        Err(UfViolation::Collision { .. }) if !care_complete => {
            // Expected outcome of the degraded-continue policy: the
            // uncovered pair suffix was violated by this candidate.
            SolveOutcome::Unknown(UnknownCause::UfCap)
        }
        Err(v) => {
            log::error!(
                "uf gate: model failed congruence certification under a complete \
                 expansion (defect class, fail-closed): {}",
                v
            );
            SolveOutcome::Unknown(UnknownCause::UfIncomplete)
        }
    }
}

#[cfg(test)]
#[path = "uf_tests.rs"]
mod tests;
