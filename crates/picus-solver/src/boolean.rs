//! Strategy router for the Boolean layer, plus the historical
//! `boolean::` paths as re-exports.
//!
//! The Boolean IR lives in [`crate::frontend::formula`]; the DNF
//! strategy in `crate::dnf`; the CDCL(T) strategy in
//! [`crate::cdclt`]. This module owns only the choice between them, so
//! neither strategy depends on the other.

use crate::solve::SolveOutcome;
use crate::timeout::CancelToken;

pub use crate::dnf::{dnf_size_cap, solve_boolean_query_dnf};
pub use crate::frontend::formula::{
    rewrite_disjunctive_bit, BooleanQuery, Formula, Literal,
};

/// Solve a [`BooleanQuery`].
///
/// Default path: CDCL(T) over the original formula via
/// [`crate::cdclt::solve_formula_with_ufs`] (UF applications riding on
/// the query's builder are handed through; an empty section is exactly
/// the pre-UF pipeline). The DNF-enumeration path is retained as a
/// baseline and is selected by the `dnf_enabled` config flag (CLI
/// `--dnf`; used for cross-validation tests); DNF cannot host a
/// theory, so a UF-bearing query on that path is eagerly
/// Ackermannized first and each disjunct's Sat is congruence-certified.
pub fn solve_boolean_query(query: &BooleanQuery, cancel: &CancelToken) -> SolveOutcome {
    let has_uf = query.builder.has_uf();
    if has_uf {
        // The CDCL(T)/DNF routes never run `encode` on the full input
        // system, so the encoder's poison refusal must be mirrored
        // here: an ill-formed UF section (arity mismatch) is refused,
        // never solved as a different problem.
        if let Some(msg) = query.builder.uf_poisoned() {
            log::warn!("boolean: refusing ill-formed uf section: {}", msg);
            return SolveOutcome::Unknown(crate::solve::UnknownCause::EncodingFailure);
        }
    }
    if crate::config::with(|c| c.dnf_enabled) {
        if has_uf {
            return solve_boolean_query_dnf_with_ufs(query, cancel);
        }
        solve_boolean_query_dnf(query, cancel)
    } else {
        crate::cdclt::solve_formula_with_ufs(
            query.prime.clone(),
            query.var_names(),
            &query.formula,
            crate::cdclt::UfSection {
                apps: query.builder.uf_apps(),
                symbols: query.builder.uf_symbols(),
            },
            cancel,
        )
    }
}

/// DNF leg for UF-bearing queries: eager Ackermann expansion of the
/// formula (bounded by `uf_pair_cap`), then the DNF baseline unchanged
/// on a query whose builder carries the apps — each disjunct's encoded
/// system keeps them, so `solve_encoded_with_cancel` congruence-
/// certifies every per-disjunct Sat. A truncated expansion marks the
/// fanned-out systems `uf_care_complete = false`, so a certification
/// failure is classified as the expected `Unknown(UfCap)`.
fn solve_boolean_query_dnf_with_ufs(
    query: &BooleanQuery,
    cancel: &CancelToken,
) -> SolveOutcome {
    use crate::solve::UnknownCause;
    if !crate::config::with(|c| c.uf_enabled) {
        log::debug!("dnf: uf_enabled = false; refusing a UF-bearing query");
        return SolveOutcome::Unknown(UnknownCause::UfUnsupported);
    }
    let pair_cap = crate::config::with(|c| c.uf_pair_cap);
    let (expanded, care_complete) = match crate::frontend::uf::ackermannize(
        &query.formula,
        query.builder.uf_apps(),
        pair_cap,
    ) {
        Ok(x) => x,
        Err(kind) => {
            log::debug!("dnf: uf expansion refused: {}", kind);
            return SolveOutcome::Unknown(match kind {
                crate::frontend::uf::UfRefusalKind::Disabled => UnknownCause::UfUnsupported,
                crate::frontend::uf::UfRefusalKind::PairCap { .. } => UnknownCause::UfCap,
            });
        }
    };
    let mut builder = query.builder.clone();
    builder.set_uf_care_complete(care_complete);
    let expanded_query = BooleanQuery::from_builder_and_formula(builder, expanded);
    solve_boolean_query_dnf(&expanded_query, cancel)
}
