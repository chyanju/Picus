//! Tests for the ideal-level GB entry points (`gb::ideal`): triviality
//! detection, cancellation, and traced UNSAT-core extraction through a
//! real Buchberger run.

use num_bigint::BigUint;

use crate::ff::field::PrimeField;
use crate::ff::monomial::MonomialOrder;
use crate::gb::ideal::{compute_gb_with_order, compute_gb_with_order_traced, GbOutcome};
use crate::gb::tracer::GbTracer;
use crate::poly::FfPolyRing;
use crate::timeout::CancelToken;

fn pr_x() -> FfPolyRing {
    FfPolyRing::new(PrimeField::new(BigUint::from(7u32)), vec!["x".into()])
}

fn has_trivial(pr: &FfPolyRing, gb: &[crate::poly::Poly]) -> bool {
    gb.iter().any(|p| !pr.is_zero(p) && p.is_constant())
}

#[test]
fn contradictory_input_yields_trivial_basis() {
    // x = 1 ∧ x = 2 over GF(7): the reduced GB is {1}.
    let pr = pr_x();
    let p1 = pr.sub(pr.var(0), pr.one());
    let p2 = pr.sub(pr.var(0), pr.constant(pr.field().from_int(2)));
    let gb = compute_gb_with_order(&pr, vec![p1, p2], &CancelToken::none(), MonomialOrder::DegRevLex)
        .expect_basis("gb");
    assert!(has_trivial(&pr, &gb), "expected a whole-ring (trivial) basis");
}

#[test]
fn consistent_input_yields_nontrivial_basis() {
    // x^2 = 1 over GF(7): consistent, non-trivial.
    let pr = pr_x();
    let x2 = pr.mul(pr.var(0), pr.var(0));
    let p = pr.sub(x2, pr.one());
    let gb = compute_gb_with_order(&pr, vec![p], &CancelToken::none(), MonomialOrder::DegRevLex)
        .expect_basis("gb");
    assert!(!gb.is_empty());
    assert!(!has_trivial(&pr, &gb));
}

#[test]
fn empty_input_yields_empty_basis() {
    let pr = pr_x();
    let gb = compute_gb_with_order(&pr, vec![], &CancelToken::none(), MonomialOrder::DegRevLex)
        .expect_basis("gb");
    assert!(gb.is_empty());
}

#[test]
fn pre_cancelled_token_yields_cancelled() {
    let pr = pr_x();
    let p1 = pr.sub(pr.var(0), pr.one());
    let p2 = pr.sub(pr.var(0), pr.constant(pr.field().from_int(2)));
    let out = compute_gb_with_order(&pr, vec![p1, p2], &CancelToken::cancelled(), MonomialOrder::DegRevLex);
    assert!(matches!(out, GbOutcome::Cancelled));
}

#[test]
fn lex_order_request_is_honoured() {
    // The Lex GB of a consistent system terminates and is non-trivial.
    let pr = FfPolyRing::new(
        PrimeField::new(BigUint::from(7u32)),
        vec!["x".into(), "y".into()],
    );
    let xy = pr.mul(pr.var(0), pr.var(1));
    let p = pr.sub(xy, pr.one());
    let gb = compute_gb_with_order(&pr, vec![p], &CancelToken::none(), MonomialOrder::Lex)
        .expect_basis("gb");
    assert!(!gb.is_empty());
    assert!(!has_trivial(&pr, &gb));
}

#[test]
fn traced_unsat_core_contains_the_contradiction() {
    // x = 2, x = 3, y = 1 in GF(7): the contradiction needs inputs 0 and 1
    // only. The tracer's core for the last pushed (trivial) element must
    // contain both, stay in range, and may conservatively include 2.
    let pr = FfPolyRing::new(
        PrimeField::new(BigUint::from(7u32)),
        vec!["x".into(), "y".into()],
    );
    let f = pr.field();
    let p0 = pr.sub(pr.var(0), pr.constant(f.from_int(2)));
    let p1 = pr.sub(pr.var(0), pr.constant(f.from_int(3)));
    let p2 = pr.sub(pr.var(1), pr.constant(f.from_int(1)));
    let mut tracer = GbTracer::new(3);
    let gb = compute_gb_with_order_traced(
        &pr,
        vec![p0, p1, p2],
        &CancelToken::none(),
        MonomialOrder::DegRevLex,
        &mut tracer,
    )
    .expect_basis("gb");
    assert!(has_trivial(&pr, &gb), "system is UNSAT: basis must be trivial");
    assert!(tracer.basis_count() > 0);
    let core = tracer.unsat_core_for(tracer.basis_count() - 1);
    assert!(core.contains(&0), "core must contain input 0 (x=2)");
    assert!(core.contains(&1), "core must contain input 1 (x=3)");
    assert!(core.iter().all(|&i| i < 3), "core must stay within the inputs");
}

#[test]
fn traced_sat_system_stays_nontrivial() {
    // x*y = 1 in GF(7): SAT; tracing must not disturb the basis.
    let pr = FfPolyRing::new(
        PrimeField::new(BigUint::from(7u32)),
        vec!["x".into(), "y".into()],
    );
    let xy = pr.mul(pr.var(0), pr.var(1));
    let p = pr.sub(xy, pr.one());
    let mut tracer = GbTracer::new(1);
    let gb = compute_gb_with_order_traced(
        &pr,
        vec![p],
        &CancelToken::none(),
        MonomialOrder::DegRevLex,
        &mut tracer,
    )
    .expect_basis("gb");
    assert!(!gb.is_empty());
    assert!(!has_trivial(&pr, &gb));
}
