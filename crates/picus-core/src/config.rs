//! Runtime configuration for the solver.
//!
//! Single thread-local [`RuntimeConfig`] aggregates every runtime
//! knob: GB strategy, F4 toggle, DNF cap, CDCL(T) iteration cap,
//! GB-stats / GB-trace / phase-profile flags. Most production code
//! reads values via [`with`] at the point of use; engine-scoped knobs
//! are instead snapshotted once at engine construction (see
//! `BuchbergerConfig` in picus-solver), so a `BuchbergerState` runs
//! under exactly the config that built it. Callers override fields via
//! [`set`] (one-shot) or [`ConfigGuard`] (RAII scope); per-thread
//! storage keeps concurrent solves on different threads independent.
//!
//! The thread-local seed is the compiled [`RuntimeConfig::default`];
//! file and CLI layers are merged on top by the `picus` facade
//! (`resolve_config`) via [`RuntimeConfig::apply_overlay`].

use serde::{Deserialize, Serialize};
use std::cell::RefCell;

/// Strategy for computing a Groebner basis. Set via
/// [`RuntimeConfig::gb_strategy`].
#[derive(Copy, Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum GbStrategy {
    /// Plain DegRevLex Buchberger on `P`. Default.
    Direct,
    /// Homogenize → GB on `P[h]` → dehomogenize → interreduce.
    ByHomog,
    /// Pick `Direct` if every input is already homogeneous w.r.t. the
    /// total-degree grading; otherwise pick `ByHomog`.
    Auto,
}

impl std::str::FromStr for GbStrategy {
    type Err = String;
    /// Parse the kebab-case name (matching the serde representation).
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "direct" => Ok(GbStrategy::Direct),
            "by-homog" => Ok(GbStrategy::ByHomog),
            "auto" => Ok(GbStrategy::Auto),
            other => Err(format!(
                "unknown gb-strategy '{other}'. Valid: direct, by-homog, auto"
            )),
        }
    }
}

/// Polynomial storage representation, selected at ring construction and
/// carried by `ff::PolyRing.repr`. Applies to the IR (`PolySystem` equalities/
/// disjunctions, lemma `learned` buffers) and the native Gröbner solve.
///
/// `Dense` stores each monomial as a full-length exponent vector
/// (O(n_vars) per term); `Sparse` stores only the nonzero `(var, exp)`
/// pairs (O(nnz) per term). On wide rings (tens of thousands of variables)
/// dense resident memory is O(n_vars · terms), so `Sparse` is the scalable
/// choice. Both are kept permanently: `Dense` is the differential-test
/// oracle and is faster on small/narrow rings.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ReprKind {
    Dense,
    Sparse,
}

impl std::str::FromStr for ReprKind {
    type Err = String;
    /// Parse the kebab-case name (matching the serde representation).
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "dense" => Ok(ReprKind::Dense),
            "sparse" => Ok(ReprKind::Sparse),
            other => Err(format!("unknown poly-repr '{other}'. Valid: dense, sparse")),
        }
    }
}

/// Declarative source of truth for the solver's runtime knobs. From one
/// annotated `name: Type = default` field list this generates the
/// [`RuntimeConfig`] struct (with per-field docs), its [`Default`] impl,
/// the parallel [`RuntimeOverlay`] (each field wrapped in `Option`), and
/// [`RuntimeConfig::apply_overlay`] — so every knob is named exactly once.
macro_rules! runtime_config {
    (
        $(
            $(#[$fmeta:meta])*
            $field:ident : $ty:ty = $default:expr
        ),* $(,)?
    ) => {
        #[derive(Clone, Debug, PartialEq, Eq)]
        pub struct RuntimeConfig {
            $(
                $(#[$fmeta])*
                pub $field: $ty,
            )*
        }

        impl Default for RuntimeConfig {
            fn default() -> Self {
                Self {
                    $($field: $default,)*
                }
            }
        }

        /// Partial overlay for [`RuntimeConfig`]: every field is optional, so a
        /// single config layer (file, environment, CLI) carries only the knobs
        /// it actually sets. Merged onto a base via [`RuntimeConfig::apply_overlay`];
        /// later layers win.
        ///
        /// TOML keys mirror the [`RuntimeConfig`] field names exactly, so adding
        /// a knob is one field here plus one line in `apply_overlay` — no rename
        /// bookkeeping. `deny_unknown_fields` turns a mistyped key into an error
        /// rather than a silent no-op.
        #[derive(Default, Debug, Clone, Serialize, Deserialize)]
        #[serde(default, deny_unknown_fields)]
        pub struct RuntimeOverlay {
            $(
                pub $field: Option<$ty>,
            )*
        }

        impl RuntimeConfig {
            /// Merge the `Some` fields of `o` onto `self`; `None` fields are
            /// left untouched. This is the overlay/merge step that layers a
            /// config file, environment, or CLI flags onto a base config.
            pub fn apply_overlay(&mut self, o: &RuntimeOverlay) {
                $(
                    if let Some(v) = o.$field { self.$field = v; }
                )*
            }
        }
    };
}

runtime_config! {
    /// GB algorithm strategy.
    gb_strategy: GbStrategy = GbStrategy::Direct,
    /// Use F4 matrix reduction for batched same-sugar S-pairs.
    use_f4: bool = false,
    /// DNF expansion cap (max disjunct count) before
    /// `solve_boolean_query_dnf` (in picus-solver) returns `Unknown`.
    dnf_cap: u64 = 100_000,
    /// Pick DNF instead of CNF for the boolean layer.
    dnf_enabled: bool = false,
    /// CDCL(T) outer-iteration cap. Set `0` to force an immediate
    /// `Unknown` (used by tests); `u64::MAX` for effectively unbounded.
    cdclt_iter_cap: u64 = 1_000_000,
    /// Emit per-run GB statistics (basis size, S-pair counts, F4 batch
    /// distribution) to stderr.
    gb_stats_enabled: bool = false,
    /// Emit GB trace events for the in-flight basis to stderr.
    gb_trace_enabled: bool = false,
    /// Enable the phase profiler (`ScopedTimer`).
    profile_enabled: bool = false,
    /// Reuse the incremental Buchberger cache between successive
    /// `solve()` calls in the same `NativeFfBackend` instance. The cache
    /// amortises split-GB across calls whose constraint set didn't
    /// change. Disabling it forces every call to rebuild the basis from
    /// scratch — useful for benchmarking or for diagnosing cache bugs.
    cache_enabled: bool = true,
    /// Representation of the IR poly type ([`ReprKind`]). Defaults to
    /// `Sparse` so lowering + the cvc5 path scale on wide rings (the dense
    /// form OOMs there); set `poly_repr = "dense"` in config (CLI
    /// `--poly-repr dense`) to force the dense representation (the
    /// differential-test oracle, faster on small rings).
    poly_repr: ReprKind = ReprKind::Sparse,
    /// Opt-in linear (Gaussian) pre-elimination (cvc5 `gauss.cpp`
    /// analogue): before solving, reduce the nonlinear constraints modulo
    /// a Gröbner basis of the linear subsystem, substituting out pivot
    /// variables. Off by default — split-GB already handles linear
    /// constraints in basis 0, and the substitution can densify the
    /// nonlinear part and add per-`solve` overhead. Exposed as a knob for
    /// linear-heavy conjunctive circuits where it may pay off.
    linear_elim: bool = false,
    /// Track inter-reduction reducer dependencies in the single-GB UNSAT-core
    /// tracer (`GbTracer`), so a trivial core reflects the basis elements that
    /// actually reduced the contradiction — matching cvc5/CoCoA's precise
    /// cores. On by default, and only meaningful on the non-default SingleGb
    /// path: that path tail-reduces the basis and emits `on_inter_reduce`
    /// events (gated by this flag). The default split-GB path never
    /// tail-reduces during its incremental extends, so no inter-reduce events
    /// fire there regardless of this flag; its UNSAT core is instead
    /// attributed by a conservative union (see `split_gb::fixpoint`). Set
    /// false to drop the small per-reduce counting cost on the SingleGb path.
    track_inter_reduce_deps: bool = true,
    /// Triangular model construction (cvc5 `multi_roots` analogue) on the
    /// default split-GB path: decide a zero-dimensional combined system by
    /// univariate-root + back-substitution enumeration instead of the
    /// brancher DFS. Sound — SAT returns a verified witness, UNSAT comes only
    /// from a complete zero-dimensional enumeration, and any other case
    /// (positive-dimensional, inconclusive, cancelled) falls back to the DFS,
    /// so it can change timing and `Unknown` resolution but never a definite
    /// verdict. Off by default: it builds the combined GB the split path
    /// otherwise avoids, so it is opt-in for zero-dimensional workloads the
    /// bounded brancher leaves `Unknown`.
    split_triangular: bool = false,
    /// Ideal-membership Safe fast-path for uniqueness queries on the
    /// cached split-GB path. Before extending the constraint-side basis
    /// with a query disequality's Rabinowitsch polynomial, reduce the
    /// difference `x_a − x_b` against that basis: a zero remainder proves
    /// `x_a − x_b ∈ I`, so the two copies are forced equal on every
    /// solution and the disequality query is UNSAT — returned directly,
    /// skipping the Rabinowitsch extend. Sound: reduction to zero against
    /// the constraint generators proves membership, so the verdict matches
    /// the full solve; a nonzero remainder is inconclusive and falls
    /// through. For primes ≤ 1000 the basis already carries the field
    /// polynomials, so the test is exact radical membership; for large
    /// primes it is a one-sided Safe filter (misses fall through). On by
    /// default.
    membership_fastpath: bool = true,
    /// Monolithic-GB radical Safe fast-path. Upgrade of `membership_fastpath`:
    /// rather than reducing `x_a − x_b` against the union of the per-partition
    /// bases (not a Gröbner basis of the combined ideal, so a nonzero remainder
    /// is inconclusive), compute the *monolithic* GB of the combined query
    /// system `constraints ∪ bitsum ∪ {(x_a−x_b)·w − 1}` (the Rabinowitsch
    /// witness) and test `is_whole_ring`. Whole-ring ⇔ `x_a − x_b ∈ √I`, so the
    /// system has no solution over the algebraic closure (hence none over
    /// GF(p)) and the query is UNSAT (the output is forced unique = Safe) — the
    /// Rabinovich radical-membership test, catching `√I \ I` cases plain ideal
    /// membership misses. Bounded by a sub-budget so a GB-bound query falls
    /// through to the split path. Off by default; sound one-directional
    /// (whole-ring ⇒ UNSAT only). One-sided over GF(p): a uniqueness holding in
    /// GF(p) but not over the closure — e.g. curve addition laws relying on a
    /// field-specific fact such as `d` being a non-residue — is not in `√I` and
    /// falls through. CLI: --radical-membership on|off.
    radical_membership: bool = false,
    /// Compute the native split-GB under an elimination term order on the
    /// alt-copy (`y`) variables instead of DegRevLex, driving those
    /// variables out of the leading terms first (see
    /// [`crate::ff::matrix_order::MatrixOrder::elim`]). The split-GB engine
    /// reads its order from the ring, so this only changes which (equally
    /// valid) reduced GB of the same ideal is computed; SAT/UNSAT verdicts
    /// are preserved (`verify_model` / whole-ring detection are
    /// order-independent). Off by default: the elimination order's
    /// leading-term structure can make the model search (`find_zero`)
    /// exhaust the per-query budget on some circuits, degrading them to
    /// `unknown` (never a wrong verdict — soundness is order-independent).
    /// Kept as a research knob; re-evaluate if the model search gains an
    /// elimination-aware branching strategy.
    matrix_elim_order: bool = false,
    /// Size-adaptive term-order selection for the native split-GB. When
    /// set, the encoder builds the solve ring under the alt-copy
    /// elimination order only for rings of at least
    /// `frontend::encoder::DYNAMIC_ORDER_MIN_VARS` variables, and DegRevLex
    /// below that — the elimination order helps only large systems (EdDSA
    /// family) and regresses tiny ones. The split-GB is
    /// order-agnostic, so this only changes which equally valid GB is
    /// computed; verdicts are guarded independently of the order. On by
    /// default: the size guard routes small rings, where the elimination
    /// order regresses, to DegRevLex.
    dynamic_order: bool = true,
    /// Signature-based Gröbner basis (GVW with signature-safe reduction) in
    /// place of the per-pair Buchberger run, for rings of at least
    /// `ff::buchberger::GVW_MIN_VARS` variables. GVW carries a Schreyer
    /// module signature on every labeled polynomial and J-pair, reduces
    /// signature-safely, and skips a J-pair a recorded syzygy / rewrite /
    /// singular criterion proves redundant — so the zero-reductions the
    /// product / Gebauer-Möller / Buchberger criteria fail to predict are
    /// never paid for, rather than reduced-then-discarded. Off by default:
    /// the GVW basis equals the per-pair reduced GB (verdict-identical), but
    /// timeout circuits are bounded by the intrinsic Gröbner-basis size, not
    /// by the zero-reductions GVW removes, so it does not resolve them. The
    /// size guard routes small rings — where a from-scratch GVW recompute on
    /// each split-GB extend regresses — to the per-pair engine. Kept as a
    /// research knob and the foundation for further signature work.
    signature_criterion: bool = false,
    /// Use Zech (discrete-log) tables for prime fields with
    /// `prime <= ff::field::ZECH_LOG_MAX_PRIME`, turning multiply / inverse /
    /// power into table lookups. Result-identical (the stored element is the
    /// plain residue either way). Off by default, for two reasons: (i) picus's
    /// deployed workload is BN254 on the GMP backend, where the small-prime
    /// path is never taken; (ii) the speedup is not uniform — `inv` wins
    /// everywhere (a table lookup vs extended Euclid), but `mul` regresses on
    /// mid-size primes because the ~1 MB `exp` table overflows L2 and Gröbner
    /// reduction is mul-heavy, and only marginally wins on tiny primes. So the
    /// net is workload-dependent; kept as an opt-in knob for inverse-heavy
    /// small-prime arithmetic, with an `O(prime)` table build per field.
    zech_log_small_fp: bool = false,
    /// Cache the geobucket reducer's divisor index (DivMask buckets + degree
    /// order) across S-pair reductions whose active basis is unchanged,
    /// instead of rebuilding it per call. Result-preserving (same normal
    /// form). Off by default: a growing basis changes the active set often,
    /// so the rebuild on a cache miss offsets the saving; opt-in for long
    /// runs of reductions against a stable basis.
    reducer_index_cache: bool = false,
    /// Memoize the Frobenius polynomial `x^p mod f` across calls to
    /// `distinct_linear_part` keyed by `(prime, f.coeffs)`. The result is a
    /// pure function of its key, so cached values are always correct. Helps
    /// model-construction phases that call root-finding on the same `(ring,
    /// f)` across multiple DFS branches.
    frobenius_cache: bool = true,
    /// In multivariate model construction (`find_zero_cancel`), use the
    /// incremental Buchberger driver (`compute_gb_incremental_with_order`)
    /// to extend the basis with the new `(var − val)` constraint at every
    /// DFS branch, instead of running a fresh full Buchberger over the
    /// merged generator list. Result-preserving (same reduced GB modulo
    /// canonicalisation) — only the work to reach it is amortized across
    /// branches.
    branching_incremental_gb: bool = true,
    /// Route the FF theory through `cdclt::multi_prime::FfTheoryRouter`
    /// instead of the single-prime `FfTheory`. Capability flag for
    /// future multi-prime SMT-LIB inputs; the parser today still
    /// rejects multi-prime sessions, so the router runs in single-slot
    /// mode (path-equivalent to `FfTheory` on the same input). Off by
    /// default until the parser is widened to emit per-prime atom tables.
    cdclt_multi_prime_router: bool = false,
    /// Interpose `cdclt::equality_engine::EqualityEngine` before the
    /// FF theory at fact-notification time. `Fresh` facts forward,
    /// `Redundant` facts drop, `Contradiction` facts surface a
    /// precise 2-literal lemma `{atom, witness}` via
    /// `EqualityEngine::prior_witness` instead of deferring to the
    /// inner GB collapse. Off by default.
    cdclt_equality_engine: bool = false,
    /// Reorder F4 S-pair batches by predicted Hilbert-function drop
    /// (Bigatti–Caboara–Robbiano selection oracle with
    /// `HilbertNum::add_generators_incremental` per candidate;
    /// `HILBERT_SELECT_BASIS_CAP=250` ceiling). Default ON when the
    /// F4 path is in use (`use_f4=true`); inert when the per-pair
    /// path runs. On homogeneous systems the oracle has nothing to rank.
    f4_hilbert_select: bool = true,
    /// Cross-batch sparse reducer-row cache inside `F4Workspace`:
    /// stores only the basis index per cache entry and rematerialises
    /// the reducer poly via `basis[bi].poly.mul_term(m / LT(basis[bi]),
    /// 1)` at hit time. Default ON when `use_f4=true`; inert
    /// otherwise. Per-entry memory drops from O(n_terms × n_vars) to
    /// O(1) word, freeing allocator pressure on wider-ring F4 workloads.
    f4_sparse_reducer_cache: bool = true,
    /// Route the FF theory through `cdclt::ff_theory_incremental::
    /// IncrementalFfTheoryState`, which carries an `IncrementalGB`
    /// across SAT decisions instead of rebuilding the basis per
    /// `post_check`. Off by default; the wire-up ports the tier1+tier2
    /// propagation from `FfTheory` and falls back to Unknown on
    /// large-prime non-trivial bases (BN254/BabyJubJub) pending model
    /// extraction.
    cdclt_incremental_theory: bool = false,
}

thread_local! {
    static THREAD_CONFIG: RefCell<RuntimeConfig> = RefCell::new(RuntimeConfig::default());
}

/// Read a snapshot of the current thread's config.
pub fn with<R>(f: impl FnOnce(&RuntimeConfig) -> R) -> R {
    THREAD_CONFIG.with(|c| f(&c.borrow()))
}

/// Replace the thread's config. The previous value is discarded; prefer
/// [`ConfigGuard`] for scoped overrides.
pub fn set(new: RuntimeConfig) {
    THREAD_CONFIG.with(|c| *c.borrow_mut() = new);
}

/// RAII override: installs `new` for the lifetime of the guard, then
/// restores the previous config on drop. Tests use this to flip a
/// single knob without leaking the change to sibling tests.
pub struct ConfigGuard {
    prev: RuntimeConfig,
}

impl ConfigGuard {
    pub fn install(new: RuntimeConfig) -> Self {
        let prev = THREAD_CONFIG.with(|c| c.borrow().clone());
        set(new);
        Self { prev }
    }

    /// Replace just one field, keeping the rest of the current config.
    pub fn with_override(f: impl FnOnce(&mut RuntimeConfig)) -> Self {
        let prev = THREAD_CONFIG.with(|c| c.borrow().clone());
        let mut next = prev.clone();
        f(&mut next);
        set(next);
        Self { prev }
    }
}

impl Drop for ConfigGuard {
    fn drop(&mut self) {
        THREAD_CONFIG.with(|c| *c.borrow_mut() = self.prev.clone());
    }
}

#[cfg(test)]
#[path = "config_tests.rs"]
mod tests;
