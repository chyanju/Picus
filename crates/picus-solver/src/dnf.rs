//! DNF-enumeration strategy for Boolean queries: expand to disjunctive
//! normal form and decide each disjunct as a conjunctive system. The
//! baseline / cross-validation counterpart to the CDCL(T) orchestrator;
//! selected by the `dnf_enabled` config flag via the
//! `boolean::solve_boolean_query` router.

use crate::frontend::encoder::encode;
use crate::frontend::formula::BooleanQuery;
use crate::solve::{solve_encoded_with_cancel, SolveOutcome};
use crate::timeout::CancelToken;

/// Maximum DNF disjunct count before [`solve_boolean_query_dnf`]
/// gives up and returns `Unknown`. Configured via
/// [`crate::config::RuntimeConfig::dnf_cap`].
pub fn dnf_size_cap() -> u64 {
    crate::config::with(|c| c.dnf_cap)
}

/// DNF-enumeration path: try each DNF disjunct in order through the
/// GB solver. Returns `Sat` on the first SAT disjunct, `Unsat` only
/// if every disjunct is UNSAT (with an empty core — per-disjunct
/// cores index into different polynomial sets), or `Unknown` if any
/// disjunct came back `Unknown` and none came back SAT.
///
/// Returns `Unknown` without materializing the DNF when the formula's
/// estimated DNF size exceeds [`dnf_size_cap`].
pub fn solve_boolean_query_dnf(query: &BooleanQuery, cancel: &CancelToken) -> SolveOutcome {
    let cap = dnf_size_cap();
    if query.formula.dnf_size_estimate(cap) >= cap {
        return SolveOutcome::Unknown;
    }
    let systems = query.to_disjunct_systems();
    if systems.is_empty() {
        return SolveOutcome::Unsat(None);
    }
    let mut saw_unknown = false;
    for sys in &systems {
        if cancel.is_cancelled() {
            return SolveOutcome::Unknown;
        }
        let encoded = match encode(sys) {
            Ok(e) => e,
            Err(_) => {
                saw_unknown = true;
                continue;
            }
        };
        match solve_encoded_with_cancel(&encoded, cancel) {
            SolveOutcome::Sat(m) => return SolveOutcome::Sat(m),
            SolveOutcome::Unknown => saw_unknown = true,
            SolveOutcome::Unsat(_) => continue,
        }
    }
    if saw_unknown {
        SolveOutcome::Unknown
    } else {
        SolveOutcome::Unsat(None)
    }
}
