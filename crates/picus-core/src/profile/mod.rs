//! Zero-external-deps profiling substrate.
//!
//! Fuses three independently-gated subsystems behind one `profile::` namespace:
//!
//! - [`counters`] — the `gb_stats`-gated `AtomicU64` counter registries
//!   ([`SPLIT_DFS`], [`SPLIT_GB`], [`IDEAL`], [`NATIVE_FF`]) and their stderr
//!   dump ([`dump_split_stats_to_stderr`]).
//! - [`metric`] — the `metric::` instrumentation DSL (`__metric_*` macros plus
//!   [`MetricTimer`] / [`LocalTimer`] / [`Gate`]), gated by `gb_stats` /
//!   `gb_trace`.
//! - [`phase`] — the wall-clock [`ScopedTimer`] phase profiler
//!   ([`take`] / [`dump_to_stderr`] / [`is_enabled`]), gated by
//!   `profile_enabled` (CLI `--profile wall`); the target of the `#[metric]`
//!   attribute from `picus-metric-macros`.
//!
//! All public items are re-exported here, so the `profile::` paths used across
//! the workspace resolve unchanged regardless of which submodule they live in.

mod counters;
mod metric;
mod phase;

pub use counters::{
    dump_split_stats_to_stderr, gb_stats_enabled, gb_trace_enabled, observe_max, IdealCounters,
    NativeFfBackendCounters, SplitDfsCounters, SplitGbCounters, IDEAL, NATIVE_FF, SPLIT_DFS,
    SPLIT_GB,
};
pub use metric::{Gate, LocalTimer, MetricTimer};
pub use phase::{dump_to_stderr, is_enabled, take, ScopedTimer};

#[cfg(test)]
#[path = "profile_tests.rs"]
mod tests;
