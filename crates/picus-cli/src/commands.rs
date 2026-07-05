use anstream::println as aprintln;
use owo_colors::OwoColorize;
use picus::{
    check_r1cs, dump_gb_stats, dump_profile, read_r1cs_file, CheckResult, PicusConfig, SolverKind,
};
use std::path::PathBuf;

use crate::args::OutputFormat;
use crate::output::{
    print_counter_example_human, print_field, print_field_pair, print_section, CheckOutput,
    CircuitInfo, ConfigInfo, CounterExampleJson, InfoOutput,
};

pub(crate) fn exit_error(msg: &str) -> ! {
    aprintln!("{} {}", "error:".red().bold(), msg);
    std::process::exit(1);
}

/// Map a tri-state `--flag on|off` argument (parsed by clap into
/// `Option<String>`) to `Option<bool>`: `None` when the flag was not passed,
/// else `Some(s == "on")`. The `value_parser` restricts `s` to `on`/`off`.
pub(crate) fn on_off(v: &Option<String>) -> Option<bool> {
    v.as_deref().map(|s| s == "on")
}

/// On SIGTERM/SIGINT, dump profile counters to stderr before exiting.
/// Enables profiling of runs that don't terminate cleanly. The dumps are
/// no-ops when no profile/stats data has been recorded.
pub(crate) fn install_profile_signal_handler() {
    use signal_hook::consts::{SIGINT, SIGTERM};
    use signal_hook::iterator::Signals;
    let mut signals = match Signals::new([SIGTERM, SIGINT]) {
        Ok(s) => s,
        Err(_) => return,
    };
    std::thread::spawn(move || {
        for sig in signals.forever() {
            dump_profile(&format!("signal={}", sig));
            dump_gb_stats();
            // Re-raise default behavior: exit with conventional code.
            std::process::exit(128 + sig);
        }
    });
}

// ============================================================
// check command
// ============================================================

pub(crate) fn cmd_check(r1cs_path: PathBuf, config: PicusConfig, format: OutputFormat) {
    // Pull the display-facing fields out before `config` moves into the
    // solve; the engine knobs travel inside `config`.
    let solver = config.analysis.solver;
    let theory = config.analysis.theory;
    let timeout = config.analysis.timeout_ms;
    let lemmas_display = config.analysis.lemmas.to_string();
    let theory_str = theory.as_str();

    // Validate up front for a clean message (check_r1cs validates too).
    if let Err(e) = picus::advanced::validate_combination(solver, theory) {
        exit_error(&e);
    }

    let r1cs = read_r1cs_file(&r1cs_path).unwrap_or_else(|e| {
        exit_error(&format!("failed to read R1CS file: {}", e));
    });

    let result = check_r1cs(&r1cs, config).unwrap_or_else(|e| exit_error(&e.to_string()));

    // Derived from the enums so any future solver+theory pair reads correctly
    // (no hand-maintained match, no `"unknown"` fall-through).
    let solver_display = if solver == SolverKind::None {
        "none".to_string()
    } else {
        format!("{} ({})", solver.as_str(), theory.smtlib_name())
    };

    match format {
        OutputFormat::Human => {
            print_section("Circuit");
            print_field("File", &r1cs_path.display().to_string());
            print_field_pair(
                "Wires",
                &r1cs.header.n_wires.to_string(),
                "Constraints",
                &r1cs.header.m_constraints.to_string(),
            );
            print_field_pair(
                "Pub Out",
                &r1cs.header.n_pub_out.to_string(),
                "Pub In",
                &r1cs.header.n_pub_in.to_string(),
            );
            print_field("Prv In", &r1cs.header.n_prv_in.to_string());
            aprintln!();
            print_section("Analysis");
            print_field("Solver", &solver_display);
            print_field("Lemmas", &lemmas_display);
            print_field("Timeout", &format!("{}ms", timeout));
            aprintln!();
            print_section("Result");

            match &result {
                CheckResult::Safe => {
                    aprintln!("  {} {}", "✓".green().bold(), "uniqueness: safe".green().bold());
                }
                CheckResult::Unsafe { witness_1, witness_2 } => {
                    aprintln!("  {} {}", "✗".red().bold(), "uniqueness: unsafe".red().bold());
                    print_counter_example_human(witness_1, witness_2);
                }
                CheckResult::Unknown(reason) => {
                    let label = format!("uniqueness: unknown ({})", reason.as_str());
                    aprintln!("  {} {}", "?".yellow().bold(), label.yellow().bold());
                }
            }
        }
        OutputFormat::Json => {
            let (result_str, cex) = match &result {
                CheckResult::Safe => ("safe".to_string(), None),
                CheckResult::Unsafe { witness_1, witness_2 } => {
                    ("unsafe".to_string(), Some(CounterExampleJson {
                        witness_1: witness_1.iter().map(|(k, v)| (k.clone(), v.to_string())).collect(),
                        witness_2: witness_2.iter().map(|(k, v)| (k.clone(), v.to_string())).collect(),
                    }))
                }
                CheckResult::Unknown(_) => ("unknown".to_string(), None),
            };

            let output = CheckOutput {
                circuit: CircuitInfo {
                    file: r1cs_path.display().to_string(),
                    wires: r1cs.header.n_wires,
                    constraints: r1cs.header.m_constraints,
                    pub_out: r1cs.header.n_pub_out,
                    pub_in: r1cs.header.n_pub_in,
                    prv_in: r1cs.header.n_prv_in,
                },
                config: ConfigInfo {
                    solver: solver.as_str().to_string(),
                    theory: theory_str.to_string(),
                    lemmas: lemmas_display,
                    timeout_ms: timeout,
                },
                result: result_str,
                counter_example: cex,
            };

            println!("{}", serde_json::to_string_pretty(&output).expect("JSON serialization failed"));
        }
    }
}

// ============================================================
// info command
// ============================================================

pub(crate) fn cmd_info(r1cs_path: PathBuf, show_constraints: bool, format: OutputFormat) {
    let r1cs = read_r1cs_file(&r1cs_path).unwrap_or_else(|e| {
        exit_error(&format!("failed to read R1CS file: {}", e));
    });

    match format {
        OutputFormat::Human => {
            print_section("R1CS Info");
            print_field("File", &r1cs_path.display().to_string());
            print_field("Version", &r1cs.version.to_string());
            print_field("Field Size", &format!("{} bytes", r1cs.header.field_size));
            print_field("Prime", &r1cs.header.prime_number.to_string());
            print_field("Wires", &r1cs.header.n_wires.to_string());
            print_field("Constraints", &r1cs.header.m_constraints.to_string());
            print_field("Pub Outputs", &r1cs.header.n_pub_out.to_string());
            print_field("Pub Inputs", &r1cs.header.n_pub_in.to_string());
            print_field("Prv Inputs", &r1cs.header.n_prv_in.to_string());
            print_field("Labels", &r1cs.header.n_labels.to_string());
            print_field("Inputs", &format!("{:?}", r1cs.inputs));
            print_field("Outputs", &format!("{:?}", r1cs.outputs));

            if show_constraints {
                aprintln!();
                print_section("Constraints");
                for i in 0..r1cs.header.m_constraints as usize {
                    aprintln!(
                        "  {} {}",
                        format!("[{}]", i).dimmed(),
                        r1cs.constraint_to_string(i)
                    );
                }
            }
        }
        OutputFormat::Json => {
            let output = InfoOutput {
                file: r1cs_path.display().to_string(),
                version: r1cs.version,
                field_size: r1cs.header.field_size,
                prime: r1cs.header.prime_number.to_string(),
                wires: r1cs.header.n_wires,
                constraints: r1cs.header.m_constraints,
                pub_out: r1cs.header.n_pub_out,
                pub_in: r1cs.header.n_pub_in,
                prv_in: r1cs.header.n_prv_in,
                labels: r1cs.header.n_labels,
                inputs: r1cs.inputs.clone(),
                outputs: r1cs.outputs.clone(),
            };

            println!("{}", serde_json::to_string_pretty(&output).expect("JSON serialization failed"));
        }
    }
}
