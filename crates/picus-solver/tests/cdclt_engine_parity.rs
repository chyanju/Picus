//! Engine-matrix parity: the user-flippable CDCL(T) engine knobs
//! (`cdclt_multi_prime_router`, `cdclt_incremental_theory`,
//! `cdclt_equality_engine`, `use_f4`) must agree with the default
//! engine on a shared corpus. Router / equality-engine / F4 claim
//! path-equivalence, so they are held to strict verdict equality; the
//! incremental theory documentedly degrades (sticky flag, large-prime
//! gap, bounded model search), so it is held to soundness-modulo-
//! Unknown: its verdict equals the default's or is Unknown, never the
//! opposite verdict.

use picus_core::config::{ConfigGuard, RuntimeConfig};
use picus_core::timeout::CancelToken;
use picus_solver::cdclt::solve_formula;
use picus_solver::solve::SolveOutcome;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Verdict {
    Sat,
    Unsat,
    Unknown,
}

fn verdict(o: &SolveOutcome) -> Verdict {
    match o {
        SolveOutcome::Sat(_) => Verdict::Sat,
        SolveOutcome::Unsat(_) => Verdict::Unsat,
        SolveOutcome::Unknown => Verdict::Unknown,
    }
}

fn solve_default(src: &str) -> Verdict {
    let q = picus_solver::smt2::parse_boolean(src).expect("parse");
    verdict(&solve_formula(
        q.prime.clone(),
        q.var_names(),
        &q.formula,
        &CancelToken::none(),
    ))
}

fn solve_with(src: &str, set: impl Fn(&mut RuntimeConfig)) -> Verdict {
    let _g = ConfigGuard::with_override(|c| set(c));
    let q = picus_solver::smt2::parse_boolean(src).expect("parse");
    verdict(&solve_formula(
        q.prime.clone(),
        q.var_names(),
        &q.formula,
        &CancelToken::none(),
    ))
}

fn xorshift(state: &mut u64) -> u64 {
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    *state
}

/// Deterministic random 3-CNF over Boolean-shaped FF atoms in GF(7).
fn rand_3cnf(seed: u64, n_vars: usize, n_clauses: usize) -> String {
    let mut s = "(set-logic QF_FF)\n(define-sort F () (_ FiniteField 7))\n".to_string();
    for i in 0..n_vars {
        s.push_str(&format!("(declare-fun x{} () F)\n", i));
    }
    let mut state = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(1);
    for _ in 0..n_clauses {
        s.push_str("(assert (or");
        for _ in 0..3 {
            let v = (xorshift(&mut state) as usize) % n_vars;
            let c = (xorshift(&mut state) as usize) % 3;
            if xorshift(&mut state) & 1 == 1 {
                s.push_str(&format!(" (not (= x{} (as ff{} F)))", v, c));
            } else {
                s.push_str(&format!(" (= x{} (as ff{} F))", v, c));
            }
        }
        s.push_str("))\n");
    }
    s.push_str("(check-sat)\n");
    s
}

/// Corpus: fixed SAT/UNSAT shapes plus a deterministic random sweep.
fn corpus() -> Vec<(String, String)> {
    let mut out: Vec<(String, String)> = Vec::new();
    out.push((
        "or-sat".into(),
        "(set-logic QF_FF)\n(define-sort F () (_ FiniteField 7))\n\
         (declare-fun x () F)\n(declare-fun y () F)\n\
         (assert (or (= x (as ff1 F)) (= y (as ff2 F))))\n\
         (assert (= x (as ff3 F)))\n(check-sat)\n"
            .into(),
    ));
    out.push((
        "mutex-unsat".into(),
        "(set-logic QF_FF)\n(define-sort F () (_ FiniteField 7))\n\
         (declare-fun x () F)\n\
         (assert (= x (as ff1 F)))\n\
         (assert (or (= x (as ff2 F)) (= x (as ff3 F))))\n(check-sat)\n"
            .into(),
    ));
    out.push((
        "nested-implies".into(),
        "(set-logic QF_FF)\n(define-sort F () (_ FiniteField 7))\n\
         (declare-fun a () F)\n(declare-fun b () F)\n\
         (assert (=> (= a (as ff1 F)) (= b (as ff2 F))))\n\
         (assert (= a (as ff1 F)))\n\
         (assert (not (= b (as ff2 F))))\n(check-sat)\n"
            .into(),
    ));
    for seed in 0..20u64 {
        out.push((format!("rand3cnf-{}", seed), rand_3cnf(seed, 4, 6)));
    }
    out
}

/// Strict parity for engines whose docs claim path-equivalence.
///
/// Anti-vacuity floor: Unknown-baseline cases are skipped, so a
/// regression that degrades the default engine to Unknown across the
/// corpus would otherwise turn the whole matrix into a no-op. The
/// floor requires a minimum number of decided baselines with both
/// verdicts represented.
fn assert_strict(engine: &str, set: impl Fn(&mut RuntimeConfig) + Copy) {
    let mut decided = 0usize;
    let mut sat_seen = false;
    let mut unsat_seen = false;
    for (name, src) in corpus() {
        let base = solve_default(&src);
        match base {
            Verdict::Unknown => continue,
            Verdict::Sat => sat_seen = true,
            Verdict::Unsat => unsat_seen = true,
        }
        decided += 1;
        let got = solve_with(&src, set);
        assert_eq!(
            got, base,
            "[{}] engine {} diverged: default={:?} engine={:?}",
            name, engine, base, got
        );
    }
    assert!(
        decided >= 15,
        "engine {}: only {} of 23 baselines decided — parity matrix lost its teeth",
        engine,
        decided
    );
    assert!(
        sat_seen && unsat_seen,
        "engine {}: corpus no longer exercises both verdicts (sat={}, unsat={})",
        engine,
        sat_seen,
        unsat_seen
    );
}

#[test]
fn router_engine_matches_default() {
    assert_strict("multi-prime-router", |c| c.cdclt_multi_prime_router = true);
}

#[test]
fn equality_engine_matches_default() {
    assert_strict("equality-engine", |c| c.cdclt_equality_engine = true);
}

#[test]
fn f4_engine_matches_default() {
    assert_strict("use-f4", |c| c.use_f4 = true);
}

#[test]
fn incremental_engine_is_sound_modulo_unknown() {
    let mut decided = 0usize;
    for (name, src) in corpus() {
        let base = solve_default(&src);
        if base == Verdict::Unknown {
            continue;
        }
        decided += 1;
        let got = solve_with(&src, |c| c.cdclt_incremental_theory = true);
        assert!(
            got == base || got == Verdict::Unknown,
            "[{}] incremental theory produced the OPPOSITE verdict: default={:?} engine={:?}",
            name, base, got
        );
    }
    assert!(
        decided >= 15,
        "only {} of 23 baselines decided — soundness matrix lost its teeth",
        decided
    );
}
