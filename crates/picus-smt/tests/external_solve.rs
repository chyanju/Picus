//! End-to-end solve tests for the external (cvc5 / z3) backends, exercising
//! real linking and solving — not just SMT-LIB text emission. Gated on the
//! `cvc5` / `z3` Cargo features, so the default build ignores this file.
//!
//! Each backend decides four tiny GF(7) systems built via the public `PolyIR`
//! builder, including two that exercise the `disequalities` path (the closing
//! `x_a != x_b` assertion every backend emits from `PolyIR::disequalities`).

#![cfg(any(feature = "cvc5", feature = "z3"))]

use std::sync::Arc;

use num_bigint::BigUint;

use picus_core::ff::field::PrimeField;
use picus_core::poly::FfPolyRing;
use picus_core::timeout::CancelToken;
use picus_smt::backends::SolverResult;
use picus_smt::poly_ir::PolyIR;
use picus_smt::{create_backend, SolverKind, Theory};

fn ring(prime: u32, names: &[&str]) -> Arc<FfPolyRing> {
    let field = PrimeField::new(BigUint::from(prime));
    Arc::new(FfPolyRing::new(
        field,
        names.iter().map(|s| s.to_string()).collect(),
    ))
}

fn solve(kind: SolverKind, theory: Theory, ir: &PolyIR) -> SolverResult {
    let mut backend = create_backend(kind, theory)
        .expect("valid combination")
        .expect("backend built (feature enabled)");
    backend
        .solve(ir, 10_000, &CancelToken::none())
        .expect("solve ok")
}

/// Run the shared verdict suite against one `(kind, theory)` backend.
fn run_suite(kind: SolverKind, theory: Theory) {
    // 1. x - 3 = 0  =>  SAT, x = 3.
    {
        let r = ring(7, &["x"]);
        let mut ir = PolyIR::new(Arc::clone(&r));
        let x = ir.linear_term(&BigUint::from(1u32), 0);
        let three = ir.constant(&BigUint::from(3u32));
        ir.push_equality(r.sub(x, three));
        ir.set_add_field_polys(true);
        match solve(kind, theory, &ir) {
            SolverResult::Sat(m) => assert_eq!(m.get("x"), Some(&BigUint::from(3u32)), "{kind:?}"),
            other => panic!("{kind:?}: expected Sat x=3, got {other:?}"),
        }
    }

    // 2. x - 3 = 0 AND x - 5 = 0  =>  UNSAT.
    {
        let r = ring(7, &["x"]);
        let mut ir = PolyIR::new(Arc::clone(&r));
        let x1 = ir.linear_term(&BigUint::from(1u32), 0);
        let three = ir.constant(&BigUint::from(3u32));
        let x2 = ir.linear_term(&BigUint::from(1u32), 0);
        let five = ir.constant(&BigUint::from(5u32));
        ir.push_equality(r.sub(x1, three));
        ir.push_equality(r.sub(x2, five));
        ir.set_add_field_polys(true);
        assert!(
            matches!(solve(kind, theory, &ir), SolverResult::Unsat),
            "{kind:?}: expected Unsat"
        );
    }

    // 3. x = 3, y = 5, x != y  =>  SAT (disequality path, satisfiable).
    {
        let r = ring(7, &["x", "y"]);
        let mut ir = PolyIR::new(Arc::clone(&r));
        let x = ir.linear_term(&BigUint::from(1u32), 0);
        let three = ir.constant(&BigUint::from(3u32));
        let y = ir.linear_term(&BigUint::from(1u32), 1);
        let five = ir.constant(&BigUint::from(5u32));
        ir.push_equality(r.sub(x, three));
        ir.push_equality(r.sub(y, five));
        ir.add_disequality(0, 1);
        ir.set_add_field_polys(true);
        match solve(kind, theory, &ir) {
            SolverResult::Sat(m) => {
                assert_eq!(m.get("x"), Some(&BigUint::from(3u32)), "{kind:?}");
                assert_eq!(m.get("y"), Some(&BigUint::from(5u32)), "{kind:?}");
            }
            other => panic!("{kind:?}: expected Sat, got {other:?}"),
        }
    }

    // 4. x = 3, y = 3, x != y  =>  UNSAT (disequality path, contradiction).
    //    This is the case the cvc5/z3 disequality refactor must get right.
    {
        let r = ring(7, &["x", "y"]);
        let mut ir = PolyIR::new(Arc::clone(&r));
        let x = ir.linear_term(&BigUint::from(1u32), 0);
        let three_x = ir.constant(&BigUint::from(3u32));
        let y = ir.linear_term(&BigUint::from(1u32), 1);
        let three_y = ir.constant(&BigUint::from(3u32));
        ir.push_equality(r.sub(x, three_x));
        ir.push_equality(r.sub(y, three_y));
        ir.add_disequality(0, 1);
        ir.set_add_field_polys(true);
        assert!(
            matches!(solve(kind, theory, &ir), SolverResult::Unsat),
            "{kind:?}: expected Unsat (x=y=3 but x!=y required)"
        );
    }
}

#[cfg(feature = "cvc5")]
#[test]
fn cvc5_ff_solves_gf7_suite() {
    run_suite(SolverKind::Cvc5, Theory::Ff);
}

#[cfg(feature = "z3")]
#[test]
fn z3_nia_solves_gf7_suite() {
    run_suite(SolverKind::Z3, Theory::Nia);
}
