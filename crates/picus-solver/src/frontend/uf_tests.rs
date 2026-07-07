use std::collections::HashMap;

use num_bigint::BigUint;

use super::*;
use crate::frontend::encoder::UfApp;

fn app(symbol: UfSymbolId, args: &[VarIdx], result: VarIdx) -> UfApp {
    UfApp { symbol, args: args.to_vec(), result }
}

fn names(n: usize) -> Vec<String> {
    (0..n).map(|i| format!("v{}", i)).collect()
}

fn model(pairs: &[(&str, u64)]) -> HashMap<String, BigUint> {
    pairs
        .iter()
        .map(|&(k, v)| (k.to_string(), BigUint::from(v)))
        .collect()
}

/// Count clauses added by ackermannize on top of the input formula.
fn added_clauses(f: &Formula, apps: &[UfApp], cap: u64) -> (usize, bool) {
    let (expanded, complete) = ackermannize(f, apps, cap).expect("no refusal");
    let n = match expanded {
        Formula::And(parts) => parts.len() - 1,
        _ => 0,
    };
    (n, complete)
}

#[test]
fn duplicate_apps_dedup_to_nothing() {
    let apps = vec![app(0, &[1, 2], 3), app(0, &[1, 2], 3)];
    let (n, complete) = added_clauses(&Formula::True, &apps, 4096);
    assert_eq!(n, 0, "exact duplicates must collapse before pairing");
    assert!(complete);
}

#[test]
fn identical_args_different_results_emit_unit_eq() {
    let apps = vec![app(0, &[1, 2], 3), app(0, &[1, 2], 4)];
    let (expanded, complete) = ackermannize(&Formula::True, &apps, 4096).unwrap();
    assert!(complete);
    let parts = match expanded {
        Formula::And(p) => p,
        other => panic!("expected And, got {:?}", other),
    };
    assert_eq!(parts.len(), 2);
    match &parts[1] {
        Formula::Lit(Literal::Eq(a, b)) => {
            assert_eq!(a[0].vars, vec![(3, 1)]);
            assert_eq!(b[0].vars, vec![(4, 1)]);
        }
        other => panic!("expected unit Eq(r_i, r_j), got {:?}", other),
    }
}

#[test]
fn nullary_symbols_chain_m_minus_1_units() {
    let apps = vec![app(0, &[], 1), app(0, &[], 2), app(0, &[], 3), app(0, &[], 4)];
    let (n, complete) = added_clauses(&Formula::True, &apps, 4096);
    assert_eq!(n, 3, "m applications of a nullary symbol chain to m-1 units");
    assert!(complete);
}

#[test]
fn general_pair_drops_shared_positions() {
    // f(x, y) = r1, f(x, z) = r2: position 0 shared, position 1 differs.
    let apps = vec![app(0, &[1, 2], 4), app(0, &[1, 3], 5)];
    let (expanded, _) = ackermannize(&Formula::True, &apps, 4096).unwrap();
    let parts = match expanded {
        Formula::And(p) => p,
        other => panic!("expected And, got {:?}", other),
    };
    match &parts[1] {
        Formula::Or(lits) => {
            assert_eq!(lits.len(), 2, "one Neq for the differing position + the Eq");
            assert!(matches!(&lits[0], Formula::Lit(Literal::Neq(_, _))));
            assert!(matches!(&lits[1], Formula::Lit(Literal::Eq(_, _))));
        }
        other => panic!("expected Or clause, got {:?}", other),
    }
}

#[test]
fn same_result_pair_is_trivially_true_and_skipped() {
    let apps = vec![app(0, &[1, 2], 4), app(0, &[1, 3], 4)];
    let (n, complete) = added_clauses(&Formula::True, &apps, 4096);
    assert_eq!(n, 0, "shared result variable makes the clause trivially true");
    assert!(complete);
}

#[test]
fn pair_cap_zero_refuses_immediately() {
    let apps = vec![app(0, &[1], 2)];
    let err = ackermannize(&Formula::True, &apps, 0).unwrap_err();
    assert!(matches!(err, UfRefusalKind::PairCap { cap: 0, .. }));
}

#[test]
fn pair_cap_overflow_truncates_to_deterministic_prefix() {
    // Three apps of one binary symbol: C(3,2) = 3 pairs; cap 2.
    let apps = vec![app(0, &[1, 2], 5), app(0, &[1, 3], 6), app(0, &[1, 4], 7)];
    let (n, complete) = added_clauses(&Formula::True, &apps, 2);
    assert_eq!(n, 2);
    assert!(!complete, "truncated expansion must report care_complete = false");
}

#[test]
fn table_builder_detects_collision() {
    // f(1) = 2 and f(1) = 3 under the model {a=1, r1=2, b=1, r2=3}.
    let apps = vec![app(0, &[0], 1), app(0, &[2], 3)];
    let vn = vec!["a".to_string(), "r1".to_string(), "b".to_string(), "r2".to_string()];
    let m = model(&[("a", 1), ("r1", 2), ("b", 1), ("r2", 3)]);
    let err = build_uf_table(&apps, &["f".to_string()], &vn, &m).unwrap_err();
    assert!(matches!(err, UfViolation::Collision { .. }));
}

#[test]
fn table_builder_accepts_congruent_model_across_frames() {
    let apps = vec![app(0, &[0], 1), app(0, &[2], 3)];
    let vn = vec!["a".to_string(), "r1".to_string(), "b".to_string(), "r2".to_string()];
    let m = model(&[("a", 1), ("r1", 2), ("b", 1), ("r2", 2)]);
    let table = build_uf_table(&apps, &["f".to_string()], &vn, &m).unwrap();
    assert_eq!(table.len(), 1, "equal tuples collapse to one table entry");
}

#[test]
fn single_app_symbol_with_missing_vars_is_skipped() {
    let apps = vec![app(0, &[0], 1)];
    let vn = vec!["a".to_string(), "r".to_string()];
    let m = model(&[]);
    let table = build_uf_table(&apps, &["f".to_string()], &vn, &m).unwrap();
    assert!(table.is_empty(), "vacuous single application is skipped, not failed");
}

#[test]
fn multi_app_symbol_with_missing_vars_fails_closed() {
    let apps = vec![app(0, &[0], 1), app(0, &[2], 3)];
    let vn = names(4);
    let m = model(&[("v0", 1), ("v1", 2)]);
    let err = build_uf_table(&apps, &["f".to_string()], &vn, &m).unwrap_err();
    assert!(matches!(err, UfViolation::MissingVar { .. }));
}

#[test]
fn certify_fills_missing_vars_with_zero_on_the_g4_route() {
    // Shared-arg shape: x_r = f(x_in), y_r = f(x_in) with x_in in no
    // polynomial — the model lacks it entirely. 0-fill must keep the
    // tuples equal, and the results agree, so certification passes.
    let apps = vec![app(0, &[0], 1), app(0, &[0], 2)];
    let vn = vec!["x_in".to_string(), "x_r".to_string(), "y_r".to_string()];
    let m = model(&[("x_r", 5), ("y_r", 5)]);
    let out = certify_uf_sat(m, &apps, &["f".to_string()], &vn, true, true);
    match out {
        SolveOutcome::Sat(model) => {
            assert_eq!(model["x_in"], BigUint::from(0u32), "0-filled");
        }
        other => panic!("expected certified Sat, got {:?}", other),
    }
}

#[test]
fn certify_collision_under_complete_expansion_is_defect_class() {
    let apps = vec![app(0, &[0], 1), app(0, &[2], 3)];
    let vn = names(4);
    let m = model(&[("v0", 1), ("v1", 2), ("v2", 1), ("v3", 3)]);
    let out = certify_uf_sat(m, &apps, &["f".to_string()], &vn, true, false);
    assert!(matches!(out, SolveOutcome::Unknown(UnknownCause::UfIncomplete)));
}

#[test]
fn certify_collision_under_degraded_prefix_is_ufcap() {
    let apps = vec![app(0, &[0], 1), app(0, &[2], 3)];
    let vn = names(4);
    let m = model(&[("v0", 1), ("v1", 2), ("v2", 1), ("v3", 3)]);
    let out = certify_uf_sat(m, &apps, &["f".to_string()], &vn, false, false);
    assert!(matches!(out, SolveOutcome::Unknown(UnknownCause::UfCap)));
}
