//! Pure Rust finite field solver for zero-knowledge circuit verification.
//!
//! This crate implements a Groebner-basis-based satisfiability solver for
//! polynomial systems over prime finite fields GF(p), designed as a drop-in
//! replacement for cvc5's QF_FF theory solver within the Picus ecosystem.
//!
//! The algorithm follows `OKTB23` "Satisfiability Modulo Finite Fields" (CAV 2023).
//!
//! Test-file convention: the unit tests for `x.rs` live in the sibling
//! `x_tests.rs` (attached with `#[cfg(test)] #[path = ...]`); additional
//! suites for the same module are `x_tests_<topic>.rs` with an
//! unabbreviated topic. Files compiled only under `cfg(test)` carry the
//! `_tests` suffix so an audit of the runtime surface can skip them by
//! name.

#![warn(unreachable_pub)]

// Public modules. The only external crate consuming this one is
// picus-smt's native backend; the remaining public surface serves the
// crate's own bins (`run_smt2`, `cvc5_compare`), benches, and
// integration tests. Everything else is pub(crate).
pub(crate) mod bits;
pub mod boolean;
pub mod cdclt;
pub(crate) mod dnf;
pub(crate) mod engine;
pub mod frontend;
pub mod gb;
pub mod incremental_context;
pub mod push_pop;
pub mod smt2;
pub mod solve;
#[cfg(feature = "testkit")]
pub mod testkit;
pub(crate) mod split_gb;

// Curated facade: the items picus-smt's native backend actually
// consumes, re-exported at the root so the seam is one flat, greppable
// list — and the spelling picus-smt imports through, so narrowing a
// deep module breaks here first (the deep module paths remain valid).
pub use boolean::{solve_boolean_query, BooleanQuery, Formula, Literal};
pub use frontend::encoder::{
    encode, ConstraintSystem, ConstraintSystemBuilder, EncodedSystem, PolyTerm, UfApp,
    UfSymbolId,
};
pub use frontend::uf::{
    build_uf_table, verify_uf_congruence, UfRefusalKind, UfTable, UfViolation,
};
pub use gb::linsolve::eliminate_linear;
pub use incremental_context::{digest_constraint_side, IncrementalSolverContext};
pub use solve::{solve_encoded_with_cancel, SolveOutcome, UnknownCause};

pub(crate) mod sat;

#[cfg(test)]
mod strategy_dispatch_tests;

// Shared substrate (runtime config, GF(p) algebra, polynomial ring,
// profiler, cancellation) lives in picus-core; in-crate code refers to
// it as `crate::{config, ff, poly, profile, timeout}`. In particular
// the algebra spelling is `crate::ff::field` etc. — `use crate::engine`
// is reserved for the GB/root-finding kernels, so a layering grep on it
// shows exactly the engine's real consumers.
pub(crate) use picus_core::{config, ff, poly, profile, timeout};
// The `metric::` namespace (incr!/add!/max!/timer!): in-crate call sites
// read `metric::incr!(..)` etc., syntactically distinct from logic.
// `metric` (module, type namespace) and the `#[metric]` attribute (macro
// namespace) coexist under one name; `use crate::metric` brings both.
pub(crate) use picus_core::metric;
pub(crate) use picus_metric_macros::metric;

use thiserror::Error;

/// Internal error type for the Gröbner-basis engine: the `Err` arm of
/// `Result<_, EngineError>` throughout `engine::buchberger` and `gb::ideal`,
/// surfacing cooperative cancellation (`EngineError::Timeout`) and internal
/// failures. Distinct from the backend-facing `picus_smt::backends::SolverError`
/// returned to `SolverBackend::solve` callers (this one never crosses the
/// crate boundary).
#[derive(Debug, Error)]
pub enum EngineError {
    #[error("solver error: {0}")]
    Internal(String),
    #[error("encoding error: {0}")]
    Encoding(String),
    /// A panic caught at the Gröbner-engine boundary — an engine bug,
    /// not a property of the input. The unwind is converted to a
    /// fail-closed degrade (empty basis → Unknown) in
    /// `gb::ideal::engine`; `site`/`message` keep the defect
    /// diagnosable. This conversion assumes `panic = "unwind"`: a
    /// `panic = "abort"` profile turns the degrade into a process
    /// abort.
    #[error("engine panic at {site}: {message}")]
    EnginePanic {
        site: &'static str,
        message: String,
    },
    #[error("timeout")]
    Timeout,
}
