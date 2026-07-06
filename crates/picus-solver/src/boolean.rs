//! Strategy router for the Boolean layer, plus the historical
//! `boolean::` paths as re-exports.
//!
//! The Boolean IR lives in [`crate::frontend::formula`]; the DNF
//! strategy in [`crate::dnf`]; the CDCL(T) strategy in
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
/// [`crate::cdclt::solve_formula`]. The DNF-enumeration path is
/// retained as a baseline and is selected by the `dnf_enabled` config
/// flag (CLI `--dnf`; used for cross-validation tests).
pub fn solve_boolean_query(query: &BooleanQuery, cancel: &CancelToken) -> SolveOutcome {
    if crate::config::with(|c| c.dnf_enabled) {
        solve_boolean_query_dnf(query, cancel)
    } else {
        crate::cdclt::solve_formula(
            query.prime.clone(),
            query.var_names(),
            &query.formula,
            cancel,
        )
    }
}
