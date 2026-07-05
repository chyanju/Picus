use clap::{Parser, Subcommand, ValueEnum};
use std::path::PathBuf;

#[derive(Parser)]
#[command(
    name = "picus",
    about = "Picus — automated detection of under-constrained signals in ZK circuits",
    version
)]
pub(crate) struct Cli {
    #[command(subcommand)]
    pub(crate) command: Commands,
}

#[derive(ValueEnum, Clone, Copy)]
pub(crate) enum OutputFormat {
    Human,
    Json,
}

#[derive(Subcommand)]
pub(crate) enum Commands {
    /// Check uniqueness of signals in an R1CS circuit
    Check {
        /// Path to the .r1cs file
        #[arg(long)]
        r1cs: PathBuf,

        /// Config file (TOML). Layered under the flags below, over the
        /// built-in defaults. If omitted, `./picus.toml` is used when
        /// present. See `picus.default.toml` for the full schema and
        /// defaults.
        #[arg(long)]
        config: Option<PathBuf>,

        /// Solver backend. Built-in names: native, cvc5, z3, none.
        /// Resolved through `SolverKind::from_str`; the inventory of
        /// registered backends supplies the "known backends" list shown
        /// on an unknown name. [default: native]
        #[arg(long)]
        solver: Option<String>,

        /// SMT theory: ff (finite field) or nia (nonlinear integer
        /// arithmetic). [default: ff]
        #[arg(long)]
        theory: Option<String>,

        /// Per-query solver timeout in milliseconds. [default: 5000]
        #[arg(long)]
        timeout: Option<u64>,

        /// Wire selection strategy, validated against the live registry
        /// (an unknown name lists the valid ones). [default: counter]
        #[arg(long)]
        selector: Option<String>,

        /// Propagation lemmas to enable.
        /// Formats: all, none, all-X,Y (exclude), none+X,Y (include).
        /// Names are validated against the live registry (an unknown name
        /// lists the valid ones); see docs/lemmas.md. [default: all]
        #[arg(long)]
        lemmas: Option<String>,

        /// Dump SMT queries to a directory for debugging
        #[arg(long, name = "dump-smt")]
        dump_smt: Option<PathBuf>,

        /// Output format
        #[arg(long, default_value = "human", value_enum)]
        format: OutputFormat,

        /// Profile output: none, wall (per-site wall-clock). Stats are
        /// written to stderr. [default: none]
        #[arg(long, value_parser = ["none", "wall"])]
        profile: Option<String>,

        /// GB strategy (native only), matching the `gb_strategy` config key:
        ///   direct   — DegRevLex Buchberger on P (default, baseline);
        ///   by-homog — homogenize → GB on P[h] → dehom → interreduce;
        ///   auto     — pick by-homog iff some input is non-homogeneous.
        /// Targets the bit-decomp family where sugar mis-prediction swells
        /// intermediate expressions. [default: direct]
        #[arg(long, value_parser = ["direct", "by-homog", "auto"])]
        gb_strategy: Option<String>,

        /// Deprecated alias for `--gb-strategy` (off→direct, on→by-homog).
        /// Kept for backward compatibility; prefer `--gb-strategy`.
        #[arg(long, value_parser = ["off", "on", "auto"], hide = true)]
        gb_by_homog: Option<String>,

        /// Polynomial representation for the native FF backend:
        /// sparse (scales on wide rings) or dense (faster on narrow
        /// rings). [default: sparse]
        #[arg(long, value_parser = ["sparse", "dense"])]
        poly_repr: Option<String>,

        /// Use F4 matrix reduction for batched same-sugar S-pairs
        /// (native FF backend only). Research flag.
        #[arg(long)]
        use_f4: bool,

        /// Pick DNF instead of CNF for the boolean layer (native FF
        /// backend only). Research flag.
        #[arg(long)]
        dnf: bool,

        /// DNF expansion cap; native FF returns Unknown beyond this
        /// disjunct count. [default: 100000]
        #[arg(long)]
        dnf_cap: Option<u64>,

        /// CDCL(T) outer-iteration cap. `0` = immediate Unknown
        /// (test helper); large values = effectively unbounded.
        /// [default: 1000000]
        #[arg(long)]
        cdclt_iter_cap: Option<u64>,

        /// Emit per-run GB statistics (basis size, S-pair counts) to
        /// stderr (native FF backend only).
        #[arg(long)]
        gb_stats: bool,

        /// Emit GB trace events for the in-flight basis to stderr
        /// (native FF backend only).
        #[arg(long)]
        gb_trace: bool,

        /// Disable the native FF backend's incremental Buchberger
        /// cache between successive solve() calls. Useful for
        /// benchmarking or for diagnosing cache bugs.
        #[arg(long)]
        no_cache: bool,

        /// Disable the aboz lemma's entailed zero-product disjunctions
        /// (native FF backend only). Default: enabled.
        #[arg(long)]
        no_aboz_disj: bool,

        /// Enable linear (Gaussian) pre-elimination before solving (native
        /// FF backend only). Off by default; may help linear-heavy
        /// conjunctive circuits, but densifies the nonlinear part on the
        /// general workload.
        #[arg(long)]
        linear_elim: bool,

        /// Triangular model construction (cvc5 multi_roots analogue) on the
        /// default split-GB path: on | off. Decides a zero-dimensional
        /// combined system by univariate-root enumeration instead of the
        /// brancher DFS. Omit to use the built-in default.
        #[arg(long, value_parser = ["on", "off"])]
        split_triangular: Option<String>,

        /// Ideal-membership Safe fast-path for uniqueness queries on the
        /// cached split-GB path (native FF backend only): on | off. Reduce
        /// `x_a − x_b` against the constraint-side basis and return UNSAT
        /// directly on a zero remainder, skipping the Rabinowitsch extend.
        /// Omit to use the built-in default.
        #[arg(long, value_parser = ["on", "off"])]
        membership_fastpath: Option<String>,
        /// Monolithic-GB radical Safe fast-path for uniqueness queries (native
        /// FF backend only): on | off. Upgrade of --membership-fastpath:
        /// whole-ring test on the monolithic GB of `I ∪ {(x_a−x_b)·w − 1}`,
        /// deciding `x_a − x_b ∈ √I` and catching forced-equal outputs the
        /// partition reduction misses. Omit to use the built-in default (off).
        #[arg(long, value_parser = ["on", "off"])]
        radical_membership: Option<String>,

        /// Compute the native split-GB under an elimination term order on
        /// the alt-copy (y) variables instead of DegRevLex (native FF
        /// backend only): on | off. Omit to use the built-in default.
        #[arg(long, value_parser = ["on", "off"])]
        matrix_elim_order: Option<String>,

        /// Size-adaptive term-order selection for the native split-GB:
        /// on | off. Uses the alt-copy elimination order on large rings and
        /// DegRevLex on small ones. Omit to use the built-in default.
        #[arg(long, value_parser = ["on", "off"])]
        dynamic_order: Option<String>,


        /// Zech (discrete-log) multiplication tables for small prime fields
        /// (`prime <= 2^20`): on | off. Result-identical; only the small-prime
        /// path is affected (BN254 stays on GMP). Omit for the built-in default.
        #[arg(long, value_parser = ["on", "off"])]
        zech_log_small_fp: Option<String>,

        /// Cache the reducer's divisor index across reductions with an
        /// unchanged active basis (native FF backend only): on | off. Omit
        /// to use the built-in default.
        #[arg(long, value_parser = ["on", "off"])]
        reducer_index_cache: Option<String>,

        /// Memoize `x^p mod f` (Frobenius polynomial) across univariate root
        /// finding calls on the same `(ring, f)`: on | off. Omit to use the
        /// built-in default.
        #[arg(long, value_parser = ["on", "off"])]
        frobenius_cache: Option<String>,

        /// In multivariate model construction, extend the GB incrementally
        /// when a DFS branch adds `(var − val)` instead of recomputing it
        /// from scratch: on | off. Omit to use the built-in default.
        #[arg(long, value_parser = ["on", "off"])]
        branching_incremental_gb: Option<String>,

        /// Route CDCL(T) facts through `cdclt::multi_prime::FfTheoryRouter`
        /// (single slot for the input prime; capability for future
        /// multi-prime SMT-LIB inputs): on | off. Omit to use the
        /// built-in default.
        #[arg(long, value_parser = ["on", "off"])]
        cdclt_multi_prime_router: Option<String>,

        /// Interpose `cdclt::equality_engine::EqualityEngine` before the
        /// FF theory at fact-notification time, dropping
        /// canonical-polynomial duplicates: on | off. Omit to use the
        /// built-in default.
        #[arg(long, value_parser = ["on", "off"])]
        cdclt_equality_engine: Option<String>,

        /// F4 Hilbert-driven S-pair batch selection (stub; flag plumbs
        /// through but no F4 dispatch path consumes it yet): on | off.
        #[arg(long, value_parser = ["on", "off"])]
        f4_hilbert_select: Option<String>,

        /// F4 cross-batch sparse reducer-row cache (stub; flag plumbs
        /// through but the upgrade is deferred): on | off.
        #[arg(long, value_parser = ["on", "off"])]
        f4_sparse_reducer_cache: Option<String>,

        /// Route the FF theory through
        /// `cdclt::ff_theory_incremental::IncrementalFfTheoryState`
        /// (cross-decision IncrementalGB; large-prime non-trivial
        /// bases return Unknown until model extraction lands): on | off.
        #[arg(long, value_parser = ["on", "off"])]
        cdclt_incremental_theory: Option<String>,
    },

    /// Print R1CS circuit information
    Info {
        /// Path to the .r1cs file
        #[arg(long)]
        r1cs: PathBuf,

        /// Print all constraints in human-readable form
        #[arg(long)]
        constraints: bool,

        /// Output format
        #[arg(long, default_value = "human", value_enum)]
        format: OutputFormat,
    },
}
