use anstream::println as aprintln;
use owo_colors::OwoColorize;
use picus::BigUint;
use serde::Serialize;
use std::collections::HashMap;

// ============================================================
// JSON schema types
// ============================================================

#[derive(Serialize)]
pub(crate) struct CheckOutput {
    pub(crate) circuit: CircuitInfo,
    pub(crate) config: ConfigInfo,
    pub(crate) result: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) counter_example: Option<CounterExampleJson>,
}

#[derive(Serialize)]
pub(crate) struct CircuitInfo {
    pub(crate) file: String,
    pub(crate) wires: u32,
    pub(crate) constraints: u32,
    pub(crate) pub_out: u32,
    pub(crate) pub_in: u32,
    pub(crate) prv_in: u32,
}

#[derive(Serialize)]
pub(crate) struct ConfigInfo {
    pub(crate) solver: String,
    pub(crate) theory: String,
    pub(crate) lemmas: String,
    pub(crate) timeout_ms: u64,
}

#[derive(Serialize)]
pub(crate) struct CounterExampleJson {
    pub(crate) witness_1: HashMap<String, String>,
    pub(crate) witness_2: HashMap<String, String>,
}

#[derive(Serialize)]
pub(crate) struct InfoOutput {
    pub(crate) file: String,
    pub(crate) version: u32,
    pub(crate) field_size: u32,
    pub(crate) prime: String,
    pub(crate) wires: u32,
    pub(crate) constraints: u32,
    pub(crate) pub_out: u32,
    pub(crate) pub_in: u32,
    pub(crate) prv_in: u32,
    pub(crate) labels: u64,
    pub(crate) inputs: Vec<usize>,
    pub(crate) outputs: Vec<usize>,
}

// ============================================================
// Human output helpers
// ============================================================

const SECTION_WIDTH: usize = 50;

pub(crate) fn print_section(title: &str) {
    let dashes = SECTION_WIDTH.saturating_sub(title.len() + 3);
    aprintln!(
        "{} {} {}",
        "──".dimmed(),
        title.bold(),
        "─".repeat(dashes).dimmed()
    );
}

pub(crate) fn print_field(label: &str, value: &str) {
    aprintln!("  {:<16}{}", format!("{}:", label).dimmed(), value);
}

pub(crate) fn print_field_pair(l1: &str, v1: &str, l2: &str, v2: &str) {
    aprintln!(
        "  {:<16}{:<8}{:<16}{}",
        format!("{}:", l1).dimmed(),
        v1,
        format!("{}:", l2).dimmed(),
        v2
    );
}

pub(crate) fn print_counter_example_human(
    witness_1: &HashMap<String, BigUint>,
    witness_2: &HashMap<String, BigUint>,
) {
    let mut x_vals: Vec<_> = witness_1.iter().collect();
    let mut y_vals: Vec<_> = witness_2.iter().collect();

    x_vals.sort_by_key(|(k, _)| picus::advanced::parse_var_index(k).unwrap_or(usize::MAX));
    y_vals.sort_by_key(|(k, _)| picus::advanced::parse_var_index(k).unwrap_or(usize::MAX));

    aprintln!();
    aprintln!("  {}:", "Counter-example".dimmed());
    aprintln!("    {}:", "Witness 1 (original)".dimmed());
    for (var, val) in &x_vals {
        aprintln!("      {} {} {}", var.bold(), "=".dimmed(), val);
    }
    aprintln!("    {}:", "Witness 2 (alternative)".dimmed());
    for (var, val) in &y_vals {
        aprintln!("      {} {} {}", var.bold(), "=".dimmed(), val);
    }
}
