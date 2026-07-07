//! UNSAT core type and high-level solving API.
//!
//! An UNSAT core is a list of input fact indices that are jointly
//! unsatisfiable. The split-GB solver returns the traced dependency core
//! when the whole-ring element can be attributed to a subset of inputs,
//! and the all-input core as a sound fallback otherwise.

use std::collections::HashMap;

use num_bigint::BigUint;

use crate::split_gb::bitprop::BitProp;
use crate::frontend::encoder::EncodedSystem;
use crate::gb::ideal::Ideal;
use crate::gb::model;
use crate::poly::{FfPolyRing, Poly};
use crate::split_gb::split_find_zero_cancel;
use crate::timeout::CancelToken;
use std::time::Duration;

/// An UNSAT core: indices into the `original_polys` slice passed to the
/// solve entry point (`bitsum_polys` and Rabinowitsch witnesses never
/// appear in a core). Carried as `Option` on [`SolveOutcome::Unsat`]:
/// `None` means UNSAT was proved without computing an attributable core
/// — consumers must not substitute a fabricated one.
pub type UnsatCore = Vec<usize>;

/// Why a solve returned [`SolveOutcome::Unknown`]. Carried on the
/// variant so the backend seam can map each cause to the right
/// user-facing reason (retryable timeout vs incompleteness vs engine
/// defect) instead of labelling every Unknown a timeout. Verdict
/// classification is unaffected — every cause is still just Unknown.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnknownCause {
    /// The cancel token fired (external cancel or per-call timeout).
    Cancelled,
    /// CDCL(T) outer-iteration cap (`cdclt_iter_cap`) exhausted.
    IterCap,
    /// DNF expansion cap (`dnf_cap`) exceeded.
    DnfCap,
    /// A bounded (non-exhaustive) model search ran dry without a
    /// verdict.
    BoundedSearch,
    /// A theory degraded (sticky degradation flag, SAT give-up, slot
    /// budget) and no verdict over the full trail is safe.
    DegradedTheory,
    /// Engine failure: caught panic or internal error, fail-closed.
    EngineFailure,
    /// The encoder rejected the input.
    EncodingFailure,
    /// A produced model failed re-verification (an engine defect; the
    /// fail-closed gate held).
    ModelValidation,
    /// A UF budget was exhausted: the `uf_pair_cap` precheck refused
    /// (cap 0), or a degraded-prefix expansion's Sat candidate failed
    /// table certification. Retrying with the same budget is pointless.
    UfCap,
    /// The UF completeness envelope was exceeded on a path that cannot
    /// split: a congruence-gate rejection under a COMPLETE expansion
    /// (defect class — the fail-closed gate held).
    UfIncomplete,
    /// Policy refusal for a UF-bearing query: `uf_enabled = false`, or
    /// an entry that does not support UF refused instead of silently
    /// dropping the applications.
    UfUnsupported,
}

impl std::fmt::Display for UnknownCause {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            UnknownCause::Cancelled => "cancelled/timeout",
            UnknownCause::IterCap => "cdclt iteration cap",
            UnknownCause::DnfCap => "dnf expansion cap",
            UnknownCause::BoundedSearch => "bounded search exhausted",
            UnknownCause::DegradedTheory => "theory degraded",
            UnknownCause::EngineFailure => "engine failure",
            UnknownCause::EncodingFailure => "encoding failure",
            UnknownCause::ModelValidation => "model validation failure",
            UnknownCause::UfCap => "uf pair cap",
            UnknownCause::UfIncomplete => "uf congruence certification failure",
            UnknownCause::UfUnsupported => "uf unsupported on this path",
        };
        f.write_str(s)
    }
}

/// Outcome of the core solver.
///
/// `Unsat` and `Unknown` are distinct: `Unsat` is a proof of
/// infeasibility, `Unknown` indicates the search was cancelled or
/// bounded out. Callers may retry on `Unknown` with relaxed bounds.
#[derive(Debug, Clone)]
pub enum SolveOutcome {
    /// SAT — a model assigning every variable a field element (as BigUint).
    Sat(HashMap<String, BigUint>),
    /// UNSAT. `Some(core)` names input facts that suffice for the
    /// contradiction; `None` means no attributable core was computed
    /// (the verdict is still a proof).
    Unsat(Option<UnsatCore>),
    /// Unknown — no verdict; the [`UnknownCause`] says why. Distinct
    /// from `Unsat`.
    Unknown(UnknownCause),
}

/// Solve a system of polynomial constraints using the Split GB algorithm.
///
/// `original_polys` is the full list of input polynomial generators (in
/// the same order as `encoded.polys`); the returned `UnsatCore` is a list
/// of indices into this slice.
#[cfg(test)]
pub(crate) fn solve_split_gb<'r>(
    poly_ring: &'r FfPolyRing,
    original_polys: &[Poly],
    bitsum_polys: &[Poly],
) -> SolveOutcome {
    solve_split_gb_cancel(poly_ring, original_polys, bitsum_polys, &CancelToken::none())
}

/// Sub-budget for the monolithic radical-membership GB (config
/// `radical_membership`), capping the futile cost on a GB-bound query so the
/// split path still gets most of the solve timeout.
const RADICAL_MEMBERSHIP_BUDGET: Duration = Duration::from_millis(3000);

/// Monolithic-GB radical Safe fast-path (config `radical_membership`).
///
/// `gens` is the full query system: constraint generators, bitsum
/// definitions, and the query's Rabinowitsch witness `(x_a−x_b)·w − 1`.
/// Computes their *monolithic* Gröbner basis and returns `Some(Unsat)` iff it
/// is the whole ring — i.e. `1 ∈ ⟨I, (x_a−x_b)·w − 1⟩`, so `x_a−x_b ∈ √I`, so
/// the system has no solution over the algebraic closure (hence none over
/// GF(p)) and the disequality query is UNSAT (the output is forced unique =
/// Safe). No attributable core is computed on this path.
///
/// Bounded by `cancel ⊕ budget`: a GB-bound query exhausts the sub-budget and
/// returns `None`, falling through to the split path. Sound one-directional —
/// only a fully-computed whole-ring GB yields a verdict; a non-whole-ring or
/// cancelled GB is inconclusive.
pub(crate) fn radical_membership_unsat(
    poly_ring: &FfPolyRing,
    gens: Vec<Poly>,
    cancel: &CancelToken,
) -> Option<SolveOutcome> {
    let budget = CancelToken::with_timeout(RADICAL_MEMBERSHIP_BUDGET);
    let tok = CancelToken::either(cancel, &budget);
    match Ideal::new_with_cancel(poly_ring, gens, &tok) {
        Ok(ideal) if ideal.is_whole_ring() => Some(SolveOutcome::Unsat(None)),
        _ => None,
    }
}

/// Solve an `EncodedSystem` directly.  Convenience wrapper.
pub fn solve_encoded(encoded: &EncodedSystem) -> SolveOutcome {
    solve_encoded_with_cancel(encoded, &CancelToken::none())
}

/// Solve an `EncodedSystem` with cooperative timeout.
///
/// Returns `SolveOutcome::Unknown` if the cancel token fires.
///
/// When the system carries UF applications, a Sat outcome is
/// additionally certified against them (congruence over the model's
/// values) before it may surface — GB paths return full ring points,
/// so no model completion is needed here. Unsat needs no check: the
/// polynomial fragment alone refuting the query refutes the stronger
/// UF-bearing system too.
pub fn solve_encoded_with_cancel(
    encoded: &EncodedSystem,
    cancel: &CancelToken,
) -> SolveOutcome {
    let outcome =
        solve_split_gb_cancel(&encoded.poly_ring, &encoded.polynomials, &encoded.bitsum_polys, cancel);
    if encoded.uf_apps.is_empty() {
        return outcome;
    }
    match outcome {
        SolveOutcome::Sat(model) => crate::frontend::uf::certify_uf_sat(
            model,
            &encoded.uf_apps,
            &encoded.uf_symbols,
            encoded.poly_ring.var_names(),
            encoded.uf_care_complete,
            false,
        ),
        other => other,
    }
}

/// Solve with cooperative cancellation.
pub fn solve_split_gb_cancel<'r>(
    poly_ring: &'r FfPolyRing,
    original_polys: &[Poly],
    bitsum_polys: &[Poly],
    cancel: &CancelToken,
) -> SolveOutcome {
    // Linear (Gaussian) pre-elimination is applied once at the top level
    // (`PolySystem::pre_eliminate_linear` in the backend), so the generators
    // reaching this conjunctive core — on both the direct and the CDCL(T)
    // per-check paths — are already reduced. This function does not
    // re-eliminate.

    // Pre-GB short-circuit: a generator that is itself a nonzero constant
    // makes the ideal the whole ring (a nonzero field constant is a unit),
    // so the system is UNSAT. This mirrors cvc5's `postRewriteFfEq` folding
    // a `const = const` assertion to `false` before the solver runs, and
    // lets a trivially-contradictory input (an assertion `2 = 1`, or an
    // equality that rewrote to a nonzero constant) skip partition building
    // and the split-GB fixpoint. The `is_whole_ring` check after the
    // fixpoint reaches the same verdict; this short-circuit only moves the
    // detection before partition building, and yields the exact one-element
    // core for this case.
    if let Some(i) = original_polys
        .iter()
        .position(|p| !p.is_zero() && p.is_constant())
    {
        return SolveOutcome::Unsat(Some(vec![i]));
    }

    // Opt-in monolithic radical-membership Safe fast-path: decide the query
    // UNSAT by one whole-ring check on the monolithic GB of the combined
    // system, skipping partition building and the model search (which
    // enumerates exponentially on forced-equal outputs the per-partition
    // whole-ring check below cannot see).
    if crate::config::with(|c| c.radical_membership) {
        let combined: Vec<Poly> = original_polys
            .iter()
            .chain(bitsum_polys.iter())
            .map(|p| poly_ring.ring.clone_el(p))
            .collect();
        if let Some(outcome) =
            radical_membership_unsat(poly_ring, combined, cancel)
        {
            return outcome;
        }
    }

    let (gens, provenance) =
        crate::split_gb::build_partitions(poly_ring, original_polys, bitsum_polys);
    // Lower each generator's provenance to its UNSAT-core dependency set: an
    // original input `i` depends on itself; a bitsum definition has none.
    let deps: Vec<Vec<std::collections::BTreeSet<usize>>> = provenance
        .iter()
        .map(|part| {
            part.iter()
                .map(|prov| {
                    let mut s = std::collections::BTreeSet::new();
                    if let Some(i) = prov {
                        s.insert(*i);
                    }
                    s
                })
                .collect()
        })
        .collect();

    let mut bit_prop = BitProp::new(poly_ring);
    bit_prop.scan_polys(original_polys);
    bit_prop.scan_polys(bitsum_polys);
    let traced = match crate::split_gb::split_gb_cancel_traced(
        poly_ring,
        gens,
        deps,
        &mut bit_prop,
        cancel,
    ) {
        Ok(t) => t,
        Err(_) => {
            return SolveOutcome::Unknown(if cancel.is_cancelled() {
                UnknownCause::Cancelled
            } else {
                UnknownCause::EngineFailure
            });
        }
    };
    let split_basis = traced.split_basis;

    if split_basis.iter().any(|b| b.is_whole_ring()) {
        return SolveOutcome::Unsat(traced.unsat_core);
    }

    match split_find_zero_cancel(poly_ring, split_basis, &mut bit_prop, cancel) {
        Ok(crate::split_gb::SplitFindZeroOutcome::Sat(point)) => {
            let mut model_map = HashMap::new();
            let field = &poly_ring.field();
            for (idx, val) in point.iter().enumerate() {
                if idx < poly_ring.var_names().len() {
                    model_map.insert(poly_ring.var_names()[idx].clone(), field.to_biguint(val));
                }
            }
            if model::verify_model(poly_ring, original_polys, &model_map)
                && model::verify_model(poly_ring, bitsum_polys, &model_map)
            {
                SolveOutcome::Sat(model_map)
            } else {
                log::warn!("model validation failed; reporting Unknown");
                SolveOutcome::Unknown(UnknownCause::ModelValidation)
            }
        }
        Ok(crate::split_gb::SplitFindZeroOutcome::Unsat) => {
            SolveOutcome::Unsat(None)
        }
        Ok(crate::split_gb::SplitFindZeroOutcome::Unknown) => {
            SolveOutcome::Unknown(if cancel.is_cancelled() {
                UnknownCause::Cancelled
            } else {
                UnknownCause::BoundedSearch
            })
        }
        Err(_) => SolveOutcome::Unknown(if cancel.is_cancelled() {
            UnknownCause::Cancelled
        } else {
            UnknownCause::EngineFailure
        }),
    }
}

#[cfg(test)]
#[path = "solve_tests.rs"]
mod tests;
