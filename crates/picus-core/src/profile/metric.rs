//! The `metric::` instrumentation DSL: the `#[macro_export]` `__metric_*`
//! macros and the RAII timer / gate types that back them.
//!
//! gb-stats instrumentation is invoked through the `metric::` namespace
//! (`metric::incr!`, `metric::add!`, `metric::max!`, `metric::timer!`, ...).
//! Every profiling site uses this syntax and does not borrow main-logic syntax
//! (`let`, `+=`, `if`), so `grep -E 'metric::|#\[metric\]'` finds exactly the
//! profiling. NOTE: the `metric::` macros here are gated by `gb_stats_enabled`
//! (except `trace!`/`clock!`, gated by `gb_trace_enabled`); the `#[metric]`
//! attribute is a *separate* subsystem — it wraps a fn in a `ScopedTimer` gated
//! by `profile_enabled` (the `--profile wall` phase table), NOT gb-stats.
//!
//! Each macro takes the *typed counter path* (e.g.
//! `SPLIT_GB.fixpoint_iters_total`) and lowers to a direct,
//! `gb_stats_enabled`-gated atomic update (compiler-checked, no name dispatch).
//! The `__metric_*` macros are the `#[macro_export]` implementations,
//! re-exported under clean names by the `metric` module in `lib.rs`; call sites
//! use `metric::incr!(PATH)` etc., not these directly.
//!
//! Vocabulary: incr! / add! / max! (counters), timer! (RAII into a global
//! counter) / timer_local! (RAII into a local u64 tally) / stopwatch! (gb-stats
//! `Option<Instant>` read at several points), gate! (read the flag once into a
//! cached Gate for a hot loop/step, then pass it to a gated timer!/timer_local!),
//! def! / bump! (local accumulators: declare / `+=`, drained once via a
//! gb-stats-gated scope! + add!), next! (increment-and-return for a
//! counter-as-id), scope! { } (a gb-stats-gated pure-profiling block),
//! trace! { } / clock! (the gb-*trace* sink: verbose per-step output, distinct
//! flag from gb-stats).
//!
//! Hot-loop gating: the per-monomial reducer timing in `ff::polynomial::
//! dense_reduce` and the per-step sub-region timing in `ff::geobucket::
//! sub_scaled_tail` must not do a thread-local config read on every iteration.
//! They use `metric::gate!(g)` to read `gb_stats_enabled()` once, then gate the
//! inner timers on the cached bool via `metric::timer_local!(g, ..)` /
//! `metric::timer!(g, ..)`.

use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Instant;

use super::counters::gb_stats_enabled;

/// Backs `metric::incr!(counter)`: `counter += 1` when gb-stats is on.
#[macro_export]
#[doc(hidden)]
macro_rules! __metric_incr {
    ($c:expr) => {
        if $crate::profile::gb_stats_enabled() {
            $c.fetch_add(1, ::std::sync::atomic::Ordering::Relaxed);
        }
    };
}

/// Backs `metric::add!(counter, n)`: `counter += n` when gb-stats is on.
#[macro_export]
#[doc(hidden)]
macro_rules! __metric_add {
    ($c:expr, $n:expr) => {
        if $crate::profile::gb_stats_enabled() {
            $c.fetch_add($n, ::std::sync::atomic::Ordering::Relaxed);
        }
    };
}

/// Backs `metric::max!(counter, v)`: `counter = max(counter, v)` when on.
#[macro_export]
#[doc(hidden)]
macro_rules! __metric_max {
    ($c:expr, $v:expr) => {
        if $crate::profile::gb_stats_enabled() {
            $crate::profile::observe_max(&$c, $v);
        }
    };
}

/// RAII timer that adds its elapsed wall-clock (ns) to `slot` on drop. Takes a
/// timestamp only when [`gb_stats_enabled`] (checked once at construction), so
/// it is a no-op in production. Construct via `metric::timer!`.
pub struct MetricTimer<'a> {
    slot: Option<(&'a AtomicU64, Instant)>,
}

impl<'a> MetricTimer<'a> {
    #[inline]
    pub fn new(slot: &'a AtomicU64) -> Self {
        Self::new_gated(gb_stats_enabled(), slot)
    }

    /// Like [`Self::new`] but takes a pre-read gb-stats flag (a cached
    /// [`Gate`]), so a caller timing two sub-regions of one hot step reads
    /// the thread-local config once rather than per `metric::timer!`. See
    /// `metric::timer!(gate, counter)`.
    #[inline]
    pub fn new_gated(on: bool, slot: &'a AtomicU64) -> Self {
        if on {
            MetricTimer { slot: Some((slot, Instant::now())) }
        } else {
            MetricTimer { slot: None }
        }
    }
}

impl Drop for MetricTimer<'_> {
    #[inline]
    fn drop(&mut self) {
        if let Some((slot, start)) = self.slot {
            slot.fetch_add(start.elapsed().as_nanos() as u64, Ordering::Relaxed);
        }
    }
}

/// Backs `metric::timer!(counter);` (re-reads the gb-stats flag) and
/// `metric::timer!(gate, counter);` (uses a pre-read [`Gate`], for a hot step
/// that times two sub-regions without re-reading the thread-local config).
/// Statement-form RAII timer: expands to a hidden, block-scoped guard (no bare
/// `let` at the call site); on drop it adds the elapsed ns to `counter`. Times
/// "this line → end of enclosing block".
#[macro_export]
#[doc(hidden)]
macro_rules! __metric_timer {
    ($c:expr) => {
        let _metric_guard = $crate::profile::MetricTimer::new(&$c);
    };
    ($gate:expr, $c:expr) => {
        let _metric_guard = $crate::profile::MetricTimer::new_gated($gate.on, &$c);
    };
}

/// RAII timer that accumulates its elapsed ns into a **local** `u64` (not a
/// global counter) on drop, gated by gb-stats. For per-phase time tallies that
/// are summed into a local across a loop and printed in a `metric::scope!`
/// dump. Construct via `metric::timer_local!`.
pub struct LocalTimer<'a> {
    slot: Option<(&'a mut u64, Instant)>,
}

impl<'a> LocalTimer<'a> {
    #[inline]
    pub fn new(slot: &'a mut u64) -> Self {
        Self::new_gated(gb_stats_enabled(), slot)
    }

    /// Like [`Self::new`] but takes a pre-read gb-stats flag (a cached
    /// [`Gate`]), so a hot loop does not re-read the thread-local config on
    /// every iteration. See `metric::timer_local!(gate, local)`.
    #[inline]
    pub fn new_gated(on: bool, slot: &'a mut u64) -> Self {
        if on {
            LocalTimer { slot: Some((slot, Instant::now())) }
        } else {
            LocalTimer { slot: None }
        }
    }
}

/// A cached gb-stats gate. Read `gb_stats_enabled()` once (e.g. at the top of a
/// hot reducer loop) via `metric::gate!(g)`, then pass `g` to the per-iteration
/// `metric::timer_local!(g, ..)` so the hottest loop reads a cached bool field
/// rather than re-doing a thread-local config lookup every iteration.
#[derive(Clone, Copy)]
pub struct Gate {
    pub on: bool,
}

impl Gate {
    #[inline]
    pub fn new() -> Self {
        Gate { on: gb_stats_enabled() }
    }
}

impl Default for Gate {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for LocalTimer<'_> {
    #[inline]
    fn drop(&mut self) {
        if let Some((slot, start)) = &mut self.slot {
            **slot += start.elapsed().as_nanos() as u64;
        }
    }
}

/// Backs `metric::timer_local!(local);` (re-reads the gb-stats flag) and
/// `metric::timer_local!(gate, local);` (uses a pre-read [`Gate`], for hot
/// loops). Block-scoped RAII timer adding elapsed ns to the local `u64`
/// accumulator on drop. See [`LocalTimer`].
#[macro_export]
#[doc(hidden)]
macro_rules! __metric_timer_local {
    ($local:expr) => {
        let _metric_guard = $crate::profile::LocalTimer::new(&mut $local);
    };
    ($gate:expr, $local:expr) => {
        let _metric_guard = $crate::profile::LocalTimer::new_gated($gate.on, &mut $local);
    };
}

/// Backs `metric::gate!(g);`: read the gb-stats flag once into a cached
/// [`Gate`] for a hot loop, then gate per-iteration `metric::timer_local!(g, ..)`
/// on the cached bool instead of re-reading the thread-local config.
#[macro_export]
#[doc(hidden)]
macro_rules! __metric_gate {
    ($name:ident) => {
        let $name = $crate::profile::Gate::new();
    };
}

/// Backs `metric::stopwatch!(name);`: declare an `Option<Instant>` profiling
/// local that is `Some(now)` only when gb-stats is on, readable at several
/// later `metric::scope!` dump points via `name.map(|t| t.elapsed())`. The
/// gb-stats analogue of [`metric::clock!`] (which is gb-trace).
#[macro_export]
#[doc(hidden)]
macro_rules! __metric_stopwatch {
    ($name:ident) => {
        let $name = if $crate::profile::gb_stats_enabled() {
            ::core::option::Option::Some(::std::time::Instant::now())
        } else {
            ::core::option::Option::None
        };
    };
}

// Local-accumulator vocabulary for hot loops: keep per-iteration work to a
// plain local `+=` (no atomic), then drain once via a gb-stats-gated
// `metric::scope!` + `metric::add!`. `def`/`bump` are always-on (a local
// `u64`, negligible when stats are off); only the drain block is gated.

/// Backs `metric::def!(acc);` (accumulator `= 0`) and
/// `metric::def!(name = expr);` (a profiling-local seeded from `expr`, e.g. an
/// entry snapshot of a counter, or `metric::next!`).
#[macro_export]
#[doc(hidden)]
macro_rules! __metric_def {
    ($name:ident) => {
        let mut $name: u64 = 0;
    };
    ($name:ident = $init:expr) => {
        let $name = $init;
    };
}

/// Backs `metric::next!(counter)`: increment `counter` and return the new
/// value (a per-call sequence id) when gb-stats is on, else `0`. For
/// profiling ids that need the post-increment value, which `metric::incr!`
/// discards.
#[macro_export]
#[doc(hidden)]
macro_rules! __metric_next {
    ($c:expr) => {
        if $crate::profile::gb_stats_enabled() {
            $c.fetch_add(1, ::std::sync::atomic::Ordering::Relaxed) + 1
        } else {
            0
        }
    };
}

/// Backs `metric::trace! { ... }`: run a pure gb-*trace* block (gated by
/// `gb_trace_enabled`, the verbose per-step diagnostic sink, distinct from the
/// gb-stats `metric::scope!`).
#[macro_export]
#[doc(hidden)]
macro_rules! __metric_trace {
    ($($body:tt)*) => {
        if $crate::profile::gb_trace_enabled() {
            $($body)*
        }
    };
}

/// Backs `metric::clock!(name);`: declare an `Option<Instant>` profiling
/// local that is `Some(now)` only when gb-trace is on, for a
/// `metric::trace!`-printed elapsed. No `Instant::now()` cost when trace is off.
#[macro_export]
#[doc(hidden)]
macro_rules! __metric_clock {
    ($name:ident) => {
        let $name = if $crate::profile::gb_trace_enabled() {
            ::core::option::Option::Some(::std::time::Instant::now())
        } else {
            ::core::option::Option::None
        };
    };
}

/// Backs `metric::bump!(acc)` / `metric::bump!(acc, n)`: local `acc += 1|n`.
#[macro_export]
#[doc(hidden)]
macro_rules! __metric_bump {
    ($name:ident) => {
        $name += 1;
    };
    ($name:ident, $n:expr) => {
        $name += $n;
    };
}

/// Backs `metric::scope! { ... }`: run a pure-profiling block only when
/// gb-stats is on. For telemetry that is more than one counter (stats-only
/// computation feeding several counters, a per-run dump). The block must
/// contain only profiling — no main-logic side effects, since it is skipped
/// when gb-stats is off.
#[macro_export]
#[doc(hidden)]
macro_rules! __metric_scope {
    ($($body:tt)*) => {
        if $crate::profile::gb_stats_enabled() {
            $($body)*
        }
    };
}
