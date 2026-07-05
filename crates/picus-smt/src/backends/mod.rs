//! Solver backend trait and common types.
//!
//! The cvc5 and z3 backends are opt-in Cargo features (default off): the
//! default `native` build skips their expensive vendored compiles. Enable
//! them with `--features cvc5` / `--features z3`.

#[cfg(feature = "cvc5")]
pub mod cvc5_ff;
#[cfg(feature = "cvc5")]
pub mod cvc5_nia;
pub mod native_ff;
/// Native-engine lowering methods on `PolySystem` (kept off the
/// solver-agnostic IR so `poly_system` depends only on picus-core).
mod native_lower;
#[cfg(feature = "z3")]
pub mod z3_nia;

use num_bigint::BigUint;
use std::collections::HashMap;
use thiserror::Error;

use crate::poly_system::PolySystem;
use picus_core::timeout::CancelToken;

/// Why a solver could not commit to `Sat` or `Unsat`. Discriminating
/// these lets callers retry with a longer budget (`Timeout`),
/// downgrade the verdict (`IncompleteTheory`), or surface a hard
/// failure to the user (`BackendError`).
#[derive(Debug, Clone)]
pub enum UnknownReason {
    /// The budget (wall-clock timeout or cancel token) fired before
    /// the solver finished.
    Timeout,
    /// The solver's theory can't decide this query (e.g. cvc5 QF_FF
    /// returning `unknown` on an `or` clause it doesn't currently
    /// handle, or a GB engine missing field polys for a small prime).
    IncompleteTheory,
    /// Internal solver failure: panic recovery, process crash,
    /// malformed model, etc. The string carries the original message
    /// for logs / debugging.
    BackendError(String),
}

/// Result from a solver invocation.
#[derive(Debug, Clone)]
pub enum SolverResult {
    Unsat,
    Sat(HashMap<String, BigUint>),
    Unknown(UnknownReason),
}

#[derive(Debug, Error)]
pub enum SolverError {
    #[error("solver error: {0}")]
    Internal(String),
}

/// Trait for solver backends.
///
/// Backends consume a [`PolySystem`] constraint system and decide it: they assert
/// every `equalities` polynomial `= 0`, each `disjunctions` clause as an
/// `or`, each `disequalities` pair as `x_a ≠ x_b`, each `assignments` pair as
/// `x_i = val`, expand `bitsums`, optionally add `x^p - x` field polynomials
/// (`add_field_polys`), and run SMT `(check-sat)`. The IR carries no
/// uniqueness/wire semantics — a uniqueness query reaches a backend as an
/// ordinary constraint system whose `disequalities` hold the single target
/// pair (see `picus_analysis::uniqueness`). SAT models are returned as
/// `HashMap<String, BigUint>` keyed by the ring's canonical variable names
/// (`x0`, `y3`, ...).
pub trait SolverBackend {
    /// Run the SMT query encoded by `ir`. The backend honours **both**
    /// `timeout_ms` (its own per-call budget) and `cancel` (an external
    /// cancellation channel, e.g. Ctrl-C reaching the analyser). Either
    /// firing should land in `SolverResult::Unknown(UnknownReason::Timeout)`.
    /// Backends that only support one of the two should document that
    /// limitation rather than silently ignoring the other.
    fn solve(
        &mut self,
        ir: &PolySystem,
        timeout_ms: u64,
        cancel: &CancelToken,
    ) -> Result<SolverResult, SolverError>;

    fn dump_smt(&self, ir: &PolySystem) -> String;
}

/// Factory closure constructing a fresh backend instance.
pub type BackendFactory = fn() -> Box<dyn SolverBackend>;

/// Inventory entry for an SMT backend.
///
/// Backends register themselves with `inventory::submit!` from their
/// own module; [`create_backend_by_name`] walks the registry at
/// *dispatch* time, and [`crate::SolverKind::from_str`] consults it to
/// list the known backends in its error message. *Selection by name*,
/// however, goes through the built-in [`crate::SolverKind`] enum (used
/// by `--solver` and config files), so a new backend that should be
/// reachable via `--solver` also needs a matching `SolverKind` variant
/// and `from_str` arm. A backend registered only via `inventory::submit!`
/// is dispatchable through `create_backend_by_name` directly but is not
/// selectable by name. The built-in `SolverKind` `name` values are the
/// lowercase strings here.
pub struct SolverBackendDescriptor {
    /// Stable name used by `--solver`, `SolverKind::from_str`, and
    /// `dump_smt` log lines.
    pub name: &'static str,
    /// Theory this backend serves. `create_backend` filters by
    /// `(name, theory)`.
    pub theory: crate::Theory,
    /// Factory closure constructing a fresh backend instance.
    pub factory: BackendFactory,
}

inventory::collect!(SolverBackendDescriptor);

/// Iterate every backend descriptor registered via `inventory`.
/// Stable order by `(name, theory)` for reproducible dispatch.
pub fn all_backend_descriptors() -> Vec<&'static SolverBackendDescriptor> {
    let mut v: Vec<&SolverBackendDescriptor> =
        inventory::iter::<SolverBackendDescriptor>.into_iter().collect();
    v.sort_by_key(|d| (d.name, d.theory));
    v
}

/// Look up a backend by `(name, theory)`. Returns the factory's
/// freshly-built instance, or `None` if no descriptor matches.
pub fn create_backend_by_name(
    name: &str,
    theory: crate::Theory,
) -> Option<Box<dyn SolverBackend>> {
    all_backend_descriptors()
        .into_iter()
        .find(|d| d.name == name && d.theory == theory)
        .map(|d| (d.factory)())
}

// ─── Shared SMT-LIB-text helpers (NIA backends) ────────────────────

/// Emit a single `Poly` as an SMT-LIB nonlinear-integer-arithmetic
/// expression. Each `(coeff, monomial_vars)` term becomes
/// `(* coeff v1 v2 ...)`; the sum is wrapped in `(+ ...)` when it has
/// more than one term, and an empty polynomial reduces to literal `0`.
#[cfg(any(feature = "cvc5", feature = "z3"))]
pub(crate) fn poly_to_smtlib_nia(ir: &PolySystem, poly: &picus_core::poly::Poly) -> String {
    let parts: Vec<String> = ir
        .poly_terms(poly)
        .map(|(coeff, vars)| {
            let mut atoms = vec![coeff.to_string()];
            atoms.extend(vars);
            if atoms.len() == 1 {
                atoms.pop().unwrap()
            } else {
                format!("(* {})", atoms.join(" "))
            }
        })
        .collect();
    match parts.len() {
        0 => "0".to_string(),
        1 => parts.into_iter().next().unwrap(),
        _ => format!("(+ {})", parts.join(" ")),
    }
}

/// Emit a single `Poly` as an SMT-LIB QF_FF expression, using
/// `ff.add` / `ff.mul` and `#fNmP` literals over the field defined
/// by the ring's prime.
#[cfg(feature = "cvc5")]
pub(crate) fn poly_to_smtlib_ff(ir: &PolySystem, poly: &picus_core::poly::Poly) -> String {
    let p = ir.ring.field().prime();
    let parts: Vec<String> = ir
        .poly_terms(poly)
        .map(|(coeff, vars)| {
            let mut atoms = vec![format!("#f{}m{}", coeff, p)];
            atoms.extend(vars);
            if atoms.len() == 1 {
                atoms.pop().unwrap()
            } else {
                format!("(ff.mul {})", atoms.join(" "))
            }
        })
        .collect();
    match parts.len() {
        0 => format!("#f0m{}", p),
        1 => parts.into_iter().next().unwrap(),
        _ => format!("(ff.add {})", parts.join(" ")),
    }
}

// ─── Shared backend logic (cvc5 / z3) ──────────────────────────────

/// Emit the complete SMT-LIB `QF_NIA` script shared by the cvc5 and z3
/// NIA backends. Their `dump_smt` bodies are byte-identical except for the
/// modulo operator: cvc5 emits `mod`, z3 emits `rem` (both reduce the
/// polynomial modulo the prime on the `[0, p)`-ranged variables this
/// declares). Callers pass `mod_op` (`"mod"` / `"rem"`) accordingly.
#[cfg(any(feature = "cvc5", feature = "z3"))]
pub(crate) fn dump_smt_nia(ir: &PolySystem, mod_op: &str) -> String {
    let p = ir.ring.field().prime();
    let mut lines = Vec::new();
    lines.push("(set-logic QF_NIA)".to_string());
    for name in ir.ring.var_names() {
        lines.push(format!("(declare-const {} Int)", name));
        lines.push(format!("(assert (and (>= {0} 0) (< {0} {1})))", name, p));
    }
    for poly in &ir.equalities {
        lines.push(format!(
            "(assert (= ({} {} {}) 0))",
            mod_op,
            poly_to_smtlib_nia(ir, poly),
            p
        ));
    }
    {
        let names = ir.ring.var_names();
        for &(a, b) in &ir.disequalities {
            lines.push(format!("(assert (not (= {} {})))", names[a], names[b]));
        }
    }
    lines.push("(check-sat)".to_string());
    lines.push("(get-model)".to_string());
    lines.join("\n")
}

/// Entry guard run at the top of every external backend's `solve()`.
/// Returns `Some(result)` when the query must short-circuit before any
/// solver work, or `None` to proceed.
///
/// * **Cancellation is honoured at entry only.** These backends can't
///   interrupt an in-flight solve (cvc5 runs in-process via the `cvc5-ff`
///   bindings, which expose no mid-call cancel hook; z3's own `timeout`
///   param covers the wall-clock budget), so a pre-cancelled token returns
///   `Unknown(Timeout)` immediately and the per-call budget covers the rest.
/// * **Unsupported IR features are refused, not silently dropped.** Each
///   backend lowers equalities and the target disequality (plus, when
///   `allow_disjunctions`, `or` clauses). Any `assignments` / `bitsums`
///   (and `disjunctions` on the NIA backends, which set `allow_disjunctions`
///   to `false`) it can't lower would weaken the query — dropped constraints
///   → spurious SAT → a false counter-example — so refuse with
///   `Unknown(IncompleteTheory)` rather than solve a different problem. The
///   R1CS uniqueness query never populates these, so the guard is inert on
///   the supported path.
#[cfg(any(feature = "cvc5", feature = "z3"))]
pub(crate) fn preflight(
    ir: &PolySystem,
    cancel: &CancelToken,
    allow_disjunctions: bool,
) -> Option<SolverResult> {
    if cancel.is_cancelled() {
        return Some(SolverResult::Unknown(UnknownReason::Timeout));
    }
    let unsupported_disjunctions = !allow_disjunctions && !ir.disjunctions.is_empty();
    if unsupported_disjunctions || !ir.assignments.is_empty() || !ir.bitsums.is_empty() {
        return Some(SolverResult::Unknown(UnknownReason::IncompleteTheory));
    }
    None
}

/// Resolve each `(a, b)` index pair in `ir.disequalities` to the pair of
/// declared variable names `(names[a], names[b])`. Returns
/// `Err(SolverError::Internal(..))` naming the offending pair if either
/// index has no declared variable: silently dropping the constraint would
/// leave the query trivially SAT (a spurious counter-example / false
/// UNSAFE), so backends surface it as an error (→ `Unknown`) instead. A
/// uniqueness query carries the single target pair; other producers may add
/// more.
///
/// Each backend then emits its own API-specific `(not (= a b))` assertion
/// over the returned names.
#[cfg(any(feature = "cvc5", feature = "z3"))]
pub(crate) fn resolve_disequalities(ir: &PolySystem) -> Result<Vec<(String, String)>, SolverError> {
    let names = ir.ring.var_names();
    let mut out = Vec::with_capacity(ir.disequalities.len());
    for &(a, b) in &ir.disequalities {
        match (names.get(a), names.get(b)) {
            (Some(na), Some(nb)) => out.push((na.clone(), nb.clone())),
            _ => {
                return Err(SolverError::Internal(format!(
                    "disequality ({}, {}) missing a declared variable",
                    a, b
                )));
            }
        }
    }
    Ok(out)
}

/// Build a cvc5 `Term` for a single `Poly`, shared by the cvc5 FF and NIA
/// backends. The two lowerings differ only in the theory-specific pieces,
/// which the caller supplies:
///
/// * `mul_kind` / `add_kind` — the product / sum `Kind`
///   (`FiniteFieldMult` + `FiniteFieldAdd` for FF; `Mult` + `Add` for NIA),
/// * `mk_coeff` — construct a coefficient literal from its `BigUint` value,
/// * `mk_zero` — construct the additive-identity literal (empty polynomial),
/// * `mk_var` — construct the fallback constant for a monomial variable not
///   present in `vars` (a defensive path; `vars` holds every ring variable).
///
/// Each `(coeff, monomial_vars)` term becomes `mk_term(mul_kind, [coeff,
/// v1, ...])` (or the bare coefficient when the monomial is constant); the
/// sum is wrapped in `mk_term(add_kind, ..)` when it has more than one term.
#[cfg(feature = "cvc5")]
#[allow(clippy::too_many_arguments)]
pub(crate) fn build_poly_cvc5<'a>(
    tm: &'a ::cvc5_ff::TermManager,
    vars: &HashMap<String, ::cvc5_ff::Term<'a>>,
    ir: &PolySystem,
    poly: &picus_core::poly::Poly,
    mul_kind: ::cvc5_ff::Kind,
    add_kind: ::cvc5_ff::Kind,
    mk_coeff: impl Fn(&BigUint) -> ::cvc5_ff::Term<'a>,
    mk_zero: impl Fn() -> ::cvc5_ff::Term<'a>,
    mk_var: impl Fn(&str) -> ::cvc5_ff::Term<'a>,
) -> ::cvc5_ff::Term<'a> {
    let mut sum_parts: Vec<::cvc5_ff::Term<'a>> = Vec::new();
    for (coeff, var_names) in ir.poly_terms(poly) {
        let c = mk_coeff(&coeff);
        if var_names.is_empty() {
            sum_parts.push(c);
            continue;
        }
        let mut factors: Vec<::cvc5_ff::Term<'a>> = Vec::with_capacity(var_names.len() + 1);
        factors.push(c);
        for n in var_names {
            factors.push(vars.get(&n).cloned().unwrap_or_else(|| mk_var(&n)));
        }
        sum_parts.push(tm.mk_term(mul_kind, &factors));
    }
    match sum_parts.len() {
        0 => mk_zero(),
        1 => sum_parts.into_iter().next().unwrap(),
        _ => tm.mk_term(add_kind, &sum_parts),
    }
}

#[cfg(test)]
mod tests;
