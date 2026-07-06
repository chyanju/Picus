//! Branching heuristics for the split-GB DFS search.
//!
//! Two entry points:
//!
//! * [`apply_rule`] runs the three-tier branching strategy on a single
//!   ideal: (1) enumerate roots of a univariate polynomial in the basis,
//!   (2) compute and enumerate roots of a minimal polynomial if the
//!   ideal is zero-dimensional, (3) fall back to round-robin enumeration
//!   over unassigned variables.
//! * [`apply_rule_multi`] runs (1) and (2) against every basis in a
//!   [`SplitGb`] before falling back to round-robin. Used by the
//!   search-frame branching point in [`super::search`].
//!
//! Each tier lives in one helper shared by both entry points: the
//! soundness rule around incomplete root extraction (a partial root set
//! must never be treated as exhaustive — pruning a satisfying
//! assignment would be an unsound UNSAT) has a single owner, and the
//! multi-basis fallback runs the round-robin tier directly.

use crate::gb::brancher::{univariate_coeffs, Brancher};
use crate::gb::ideal::Ideal;
use crate::metric;
use crate::poly::FfPolyRing;
use crate::timeout::CancelToken;

use super::PartialPoint;

/// Tier 1: a univariate polynomial of `gb` in an unassigned variable
/// whose roots were extracted *completely*. Incomplete extraction falls
/// through (`None`) rather than risk an unsound infeasible conclusion.
fn try_univariate<'r>(
    poly_ring: &'r FfPolyRing,
    gb: &Ideal<'r>,
    r: &PartialPoint,
    cancel: &CancelToken,
) -> Option<Brancher> {
    let ring = &poly_ring.ring;
    let field = &poly_ring.field();
    for p in &gb.basis {
        let appearing = ring.appearing_indeterminates(p);
        if appearing.len() == 1 {
            let (var_idx, _) = appearing[0];
            if r[var_idx].is_none() {
                if let Some(coeffs) = univariate_coeffs(poly_ring, p, var_idx) {
                    let (roots, complete) =
                        crate::gb::roots::find_roots_checked_cancel(field, &coeffs, Some(cancel));
                    if complete {
                        return Some(Brancher::Roots(
                            roots.into_iter().map(|v| (var_idx, v)).collect(),
                        ));
                    }
                }
            }
        }
    }
    None
}

/// Tier 2: `gb` is zero-dimensional and some unassigned variable's
/// minimal polynomial splits completely. A *complete* empty root set
/// proves the ideal inconsistent under any assignment to that variable
/// (empty `Roots` ⇒ backtrack); an *incomplete* set falls through.
fn try_min_poly<'r>(
    poly_ring: &'r FfPolyRing,
    gb: &Ideal<'r>,
    r: &PartialPoint,
    cancel: &CancelToken,
) -> Option<Brancher> {
    if !gb.is_zero_dim() {
        return None;
    }
    let field = &poly_ring.field();
    for v in 0..poly_ring.n_vars() {
        if r[v].is_none() {
            if let Some(coeffs) = gb.min_poly_cancel(v, cancel) {
                let (roots, complete) =
                    crate::gb::roots::find_roots_checked_cancel(field, &coeffs, Some(cancel));
                if complete {
                    return Some(Brancher::Roots(
                        roots.into_iter().map(|val| (v, val)).collect(),
                    ));
                }
            }
        }
    }
    None
}

/// Tier 3: lazy round-robin enumeration over the unassigned variables.
fn round_robin_fallback(poly_ring: &FfPolyRing, r: &PartialPoint) -> Brancher {
    let unassigned: Vec<usize> = (0..poly_ring.n_vars()).filter(|i| r[*i].is_none()).collect();
    if unassigned.is_empty() {
        return Brancher::Roots(Vec::new());
    }
    Brancher::round_robin(unassigned, poly_ring.field().prime())
}

/// Apply the three-tier branching rule on a single basis.
#[cfg(test)]
pub(crate) fn apply_rule<'r>(
    poly_ring: &'r FfPolyRing,
    gb: &Ideal<'r>,
    r: &PartialPoint,
    cancel: &CancelToken,
) -> Brancher {
    try_univariate(poly_ring, gb, r, cancel)
        .or_else(|| try_min_poly(poly_ring, gb, r, cancel))
        .unwrap_or_else(|| round_robin_fallback(poly_ring, r))
}

/// Like [`apply_rule`] but checks every basis for univariate / zero-dim
/// structure before one round-robin fallback. The detected branching
/// structure is mathematically valid in any of the bases.
#[metric]
pub(super) fn apply_rule_multi<'r>(
    poly_ring: &'r FfPolyRing,
    bases: &[Ideal<'r>],
    r: &PartialPoint,
    cancel: &CancelToken,
) -> Brancher {
    for gb in bases {
        if let Some(b) = try_univariate(poly_ring, gb, r, cancel) {
            return b;
        }
    }
    for gb in bases {
        if let Some(b) = try_min_poly(poly_ring, gb, r, cancel) {
            return b;
        }
    }
    if bases.is_empty() {
        // No basis to branch on: an empty candidate set (immediate
        // backtrack), matching the caller's no-partition contract.
        return Brancher::Roots(Vec::new());
    }
    round_robin_fallback(poly_ring, r)
}

// `univariate_coeffs` and the round-robin constructor are shared with
// `gb::model` via `gb::brancher`, so the load-bearing `exhaustive`
// predicate has a single source.

#[cfg(test)]
#[path = "branching_tests.rs"]
mod tests;
