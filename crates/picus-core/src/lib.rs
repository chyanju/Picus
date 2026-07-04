//! Shared algebra and runtime substrate for the Picus solver stack.
//!
//! - [`ff`]: finite-field arithmetic over GF(p), dense and sparse
//!   multivariate polynomials, divisibility masks, and geobucket reduction.
//! - [`poly`]: the polynomial ring facade ([`poly::FfPolyRing`], [`poly::Poly`]).
//! - [`config`]: thread-local runtime configuration ([`config::RuntimeConfig`],
//!   [`config::ReprKind`], [`config::GbStrategy`]).
//! - [`timeout`]: cooperative cancellation ([`timeout::CancelToken`]).
//! - [`profile`]: zero-dependency phase profiler.
//!
//! Consumed by `picus-solver` (GB / CDCL(T) engine), `picus-smt` (backend
//! adapters) and `picus-analysis` (propagation lemmas).

pub mod config;
pub mod ff;
pub mod poly;
pub mod profile;
pub mod timeout;

/// Namespaced instrumentation vocabulary. Every profiling call site goes
/// through this `metric::` namespace, so `grep -E 'metric::|#\[metric\]'`
/// finds exactly the profiling and nothing in main logic.
///
/// The vocabulary spans two independently-gated subsystems (see [`config`]):
/// - **gb-stats** (`gb_stats_enabled`): `incr!`, `add!`, `max!`, `timer!`,
///   `timer_local!`, `gate!`, `stopwatch!`, `def!`, `next!`, `bump!`, `scope!`
///   — counters/timers backed by [`profile`]'s `AtomicU64` registries,
///   [`profile::MetricTimer`]/[`profile::LocalTimer`], and `observe_max`.
/// - **gb-trace** (`gb_trace_enabled`): `trace!`, `clock!` — verbose tracing.
///
/// The separate `#[metric]` attribute (from `picus-metric-macros`) is a
/// *third* subsystem: it wraps a fn body in a [`profile::ScopedTimer`] and is
/// gated by `profile_enabled` (the `--profile wall` phase table), NOT gb-stats.
pub mod metric {
    pub use crate::{
        __metric_add as add, __metric_bump as bump, __metric_clock as clock,
        __metric_def as def, __metric_gate as gate,
        __metric_incr as incr, __metric_max as max, __metric_next as next,
        __metric_scope as scope, __metric_stopwatch as stopwatch,
        __metric_timer as timer, __metric_timer_local as timer_local,
        __metric_trace as trace,
    };
}
