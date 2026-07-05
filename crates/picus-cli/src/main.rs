mod args;
mod commands;
mod output;

use clap::Parser;
use picus::{
    dump_gb_stats, dump_profile, resolve_config, AnalysisOverlay, EngineOverlay, GbStrategy,
    PicusConfigOverlay, ReprKind,
};

use args::{Cli, Commands};
use commands::{cmd_check, cmd_info, exit_error, install_profile_signal_handler, on_off};

fn main() {
    env_logger::init();
    install_profile_signal_handler();
    let cli = Cli::parse();

    match cli.command {
        Commands::Check {
            r1cs,
            config,
            solver,
            theory,
            timeout,
            selector,
            lemmas,
            dump_smt,
            format,
            profile,
            gb_strategy,
            gb_by_homog,
            poly_repr,
            use_f4,
            dnf,
            dnf_cap,
            cdclt_iter_cap,
            gb_stats,
            gb_trace,
            no_cache,
            no_aboz_disj,
            linear_elim,
            split_triangular,
            membership_fastpath,
            radical_membership,
            matrix_elim_order,
            dynamic_order,
            signature_criterion,
            zech_log_small_fp,
            reducer_index_cache,
            frobenius_cache,
            branching_incremental_gb,
            cdclt_multi_prime_router,
            cdclt_equality_engine,
            f4_hilbert_select,
            f4_sparse_reducer_cache,
            cdclt_incremental_theory,
        } => {
            // CLI overlay — the highest-precedence config layer. Only the
            // flags actually passed on the command line become `Some`; everything
            // else stays `None` and falls through to the config file,
            // then built-in defaults (see `resolve_config`). On/off bool
            // flags can only turn a knob *on* (or, for the `no_*` flags,
            // off).
            let overlay = PicusConfigOverlay {
                analysis: AnalysisOverlay {
                    solver,
                    theory,
                    selector,
                    timeout_ms: timeout,
                    lemmas,
                    dump_smt,
                },
                engine: EngineOverlay {
                    // Prefer the canonical --gb-strategy (parsed by the enum's
                    // FromStr, rejecting unknown values); fall back to the
                    // deprecated --gb-by-homog alias (off/on/auto).
                    gb_strategy: gb_strategy
                        .as_deref()
                        .map(|s| s.parse::<GbStrategy>().unwrap_or_else(|e| exit_error(&e)))
                        .or_else(|| {
                            gb_by_homog.as_deref().map(|s| match s {
                                "on" => GbStrategy::ByHomog,
                                "auto" => GbStrategy::Auto,
                                _ => GbStrategy::Direct,
                            })
                        }),
                    poly_repr: poly_repr
                        .as_deref()
                        .map(|s| s.parse::<ReprKind>().unwrap_or_else(|e| exit_error(&e))),
                    use_f4: use_f4.then_some(true),
                    dnf_enabled: dnf.then_some(true),
                    dnf_cap,
                    cdclt_iter_cap,
                    gb_stats_enabled: gb_stats.then_some(true),
                    gb_trace_enabled: gb_trace.then_some(true),
                    cache_enabled: no_cache.then_some(false),
                    aboz_emit_disjunctions: no_aboz_disj.then_some(false),
                    profile_enabled: profile.as_deref().map(|s| s == "wall"),
                    linear_elim: linear_elim.then_some(true),
                    // Config-file only (no CLI flag): precise inter-reduce
                    // core tracking is a niche knob; set it via picus.toml.
                    track_inter_reduce_deps: None,
                    split_triangular: on_off(&split_triangular),
                    membership_fastpath: on_off(&membership_fastpath),
                    radical_membership: on_off(&radical_membership),
                    matrix_elim_order: on_off(&matrix_elim_order),
                    dynamic_order: on_off(&dynamic_order),
                    signature_criterion: on_off(&signature_criterion),
                    zech_log_small_fp: on_off(&zech_log_small_fp),
                    reducer_index_cache: on_off(&reducer_index_cache),
                    frobenius_cache: on_off(&frobenius_cache),
                    branching_incremental_gb: on_off(&branching_incremental_gb),
                    cdclt_multi_prime_router: on_off(&cdclt_multi_prime_router),
                    cdclt_equality_engine: on_off(&cdclt_equality_engine),
                    f4_hilbert_select: on_off(&f4_hilbert_select),
                    f4_sparse_reducer_cache: on_off(&f4_sparse_reducer_cache),
                    cdclt_incremental_theory: on_off(&cdclt_incremental_theory),
                },
            };
            let resolved = resolve_config(config.as_deref(), &overlay)
                .unwrap_or_else(|e| exit_error(&e.to_string()));
            cmd_check(r1cs, resolved, format);
        }
        Commands::Info {
            r1cs,
            constraints,
            format,
        } => cmd_info(r1cs, constraints, format),
    }
    dump_profile("cli");
    dump_gb_stats();
}
