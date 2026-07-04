//! End-to-end tests for the advanced `picus::solve` API: build a `PolySystem`
//! constraint system directly and decide it, with no R1CS / uniqueness layer.

use std::sync::Arc;

use picus::{solve, BigUint, FfPolyRing, PicusConfig, PolySystem, PrimeField, SolverKind, SolverResult};

/// GF(`prime`) ring over the given variable names.
fn ring(prime: u32, names: &[&str]) -> Arc<FfPolyRing> {
    let field = PrimeField::new(BigUint::from(prime));
    Arc::new(FfPolyRing::new(
        field,
        names.iter().map(|s| s.to_string()).collect(),
    ))
}

#[test]
fn solve_sat_returns_model() {
    let r = ring(7, &["x"]);
    let mut ir = PolySystem::new(Arc::clone(&r));
    let x = ir.linear_term(&BigUint::from(1u32), 0);
    let three = ir.constant(&BigUint::from(3u32));
    ir.push_equality(r.sub(x, three)); // x - 3 = 0

    match solve(&ir, PicusConfig::default()).unwrap() {
        SolverResult::Sat(model) => assert_eq!(model.get("x"), Some(&BigUint::from(3u32))),
        other => panic!("expected Sat, got {:?}", other),
    }
}

#[test]
fn solve_unsat_on_contradiction() {
    let r = ring(7, &["x"]);
    let mut ir = PolySystem::new(Arc::clone(&r));
    let x1 = ir.linear_term(&BigUint::from(1u32), 0);
    let three = ir.constant(&BigUint::from(3u32));
    let x2 = ir.linear_term(&BigUint::from(1u32), 0);
    let five = ir.constant(&BigUint::from(5u32));
    ir.push_equality(r.sub(x1, three)); // x = 3
    ir.push_equality(r.sub(x2, five)); // x = 5

    assert!(matches!(
        solve(&ir, PicusConfig::default()).unwrap(),
        SolverResult::Unsat
    ));
}

#[test]
fn solve_field_polys_restrict_to_gfp() {
    // x^2 = 3 over GF(7): 3 is a non-residue (squares mod 7 are {1,2,4}), so
    // there is no solution *in GF(7)* — but x^2 - 3 is a nonzero polynomial
    // with roots in an extension. `set_add_field_polys(true)` injects x^7 - x,
    // restricting the variety to GF(7), which makes the system UNSAT.
    let r = ring(7, &["x"]);
    let mut ir = PolySystem::new(Arc::clone(&r));
    let xx = r.mul(r.var(0), r.var(0));
    let three = ir.constant(&BigUint::from(3u32));
    ir.push_equality(r.sub(xx, three));
    ir.set_add_field_polys(true);

    assert!(matches!(
        solve(&ir, PicusConfig::default()).unwrap(),
        SolverResult::Unsat
    ));
}

#[test]
fn solve_with_disequality() {
    // x*(x-1) = 0 pins x ∈ {0,1}; the disequality x ≠ x_one (a var pinned to 1)
    // forces x = 0. SAT with x = 0.
    let r = ring(7, &["x", "one"]);
    let mut ir = PolySystem::new(Arc::clone(&r));
    // x^2 - x = 0
    let xx = r.mul(r.var(0), r.var(0));
    let x = ir.linear_term(&BigUint::from(1u32), 0);
    ir.push_equality(r.sub(xx, x));
    // one = 1
    ir.add_assignment(1, BigUint::from(1u32));
    // x ≠ one
    ir.add_disequality(0, 1);
    ir.set_add_field_polys(true);

    match solve(&ir, PicusConfig::default()).unwrap() {
        SolverResult::Sat(model) => assert_eq!(model.get("x"), Some(&BigUint::from(0u32))),
        other => panic!("expected Sat with x=0, got {:?}", other),
    }
}

#[test]
fn solve_rejects_solver_none() {
    let r = ring(7, &["x"]);
    let ir = PolySystem::new(Arc::clone(&r));
    let cfg = PicusConfig {
        analysis: picus::AnalysisConfig {
            solver: SolverKind::None,
            ..Default::default()
        },
        ..Default::default()
    };
    assert!(solve(&ir, cfg).is_err());
}
