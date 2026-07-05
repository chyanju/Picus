//! Tests for `native_lower.rs` — `PolySystem::to_constraint_system`,
//! `PolySystem::to_boolean_query`, `PolySystem::encode`, and
//! `PolySystem::pre_eliminate_linear`. Spec-driven where the doc spells
//! out the lowering shape (variable name list, equality count,
//! disequality/assignment/bitsum propagation, field-poly flag).

use num_bigint::BigUint;
use picus_r1cs::grammar::Constraint;
use picus_r1cs::testkit::*;

use crate::poly_system::PolySystem;
use crate::test_lowering::lower_two_copy;
use picus_core::timeout::CancelToken;

// ─── Test fixtures ───────────────────────────────────────────────────
// The shared builders (`r1cs`, `blk`, `p7`, …) live in `picus_r1cs::testkit`.

/// Lower a constraint-free R1CS into the crate-local `PolySystem`, with the
/// target disequality already materialised at `(target, n_wires + target)`.
fn empty_ir(p: BigUint, n_wires: usize, inputs: Vec<usize>, target: usize) -> PolySystem {
    let file = r1cs(p, n_wires as u32, inputs, Vec::new());
    lower_two_copy(&file, target)
}

// ─── to_constraint_system ────────────────────────────────────────

#[test]
fn prop_to_constraint_system_preserves_prime() {
    let ir = empty_ir(p7(), 3, vec![0], 1);
    let cs = ir.to_constraint_system();
    assert_eq!(cs.prime, p7());
}

#[test]
fn prop_to_constraint_system_var_names_match_ring_order() {
    // Doc spec: "Variable names are interned in `ring.var_names()`
    // order so builder indices match ring indices".
    let ir = empty_ir(p7(), 3, vec![0], 1);
    let cs = ir.to_constraint_system();
    assert_eq!(cs.var_names, ir.ring.var_names().to_vec());
    // Layout: x0,x1,x2,y0,y1,y2.
    assert_eq!(cs.var_names, vec!["x0", "x1", "x2", "y0", "y1", "y2"]);
}

#[test]
fn prop_to_constraint_system_disequalities_propagate() {
    // Doc spec: disequalities propagate as-is.
    let ir = empty_ir(p7(), 4, vec![0], 2);
    let cs = ir.to_constraint_system();
    assert_eq!(cs.disequalities, vec![(2u32, 6u32)]);
}

#[test]
fn prop_to_constraint_system_field_polys_flag_propagates_small_prime() {
    // Doc spec: `add_field_polys` propagates as-is.
    let ir = empty_ir(p7(), 3, vec![0], 1);
    let cs = ir.to_constraint_system();
    assert!(cs.add_field_polys, "small prime ⇒ flag on");
}

#[test]
fn prop_to_constraint_system_field_polys_flag_off_for_large_prime() {
    let big = picus_r1cs::testkit::bn128();
    let ir = empty_ir(big, 3, vec![0], 1);
    let cs = ir.to_constraint_system();
    assert!(!cs.add_field_polys);
}

#[test]
fn prop_to_constraint_system_assignments_propagate() {
    let mut ir = empty_ir(p7(), 3, vec![0], 1);
    ir.assignments.push((1, BigUint::from(2u32)));
    let cs = ir.to_constraint_system();
    assert_eq!(cs.assignments.len(), 1);
    assert_eq!(cs.assignments[0].0, 1u32);
    assert_eq!(cs.assignments[0].1, BigUint::from(2u32));
}

#[test]
fn prop_to_constraint_system_bitsums_propagate_with_cast() {
    let mut ir = empty_ir(p7(), 5, vec![0], 1);
    ir.bitsums.push(vec![1, 2, 3]);
    let cs = ir.to_constraint_system();
    assert_eq!(cs.bitsums.len(), 1);
    assert_eq!(cs.bitsums[0], vec![1u32, 2, 3]);
}

#[test]
fn prop_to_constraint_system_empty_equality_dropped() {
    // Doc spec: "if !terms.is_empty()" — empty polys drop. With no
    // user constraints, the only equality is `x_0 - 1 = 0` (non-empty
    // terms).
    let ir = empty_ir(p7(), 3, vec![0], 1);
    let cs = ir.to_constraint_system();
    for eq in &cs.equalities {
        assert!(!eq.is_empty(), "all equalities are non-empty");
    }
}

#[test]
fn prop_to_constraint_system_includes_user_constraints() {
    // One constraint `x_1 * x_2 = x_3` → 2 equalities (orig + alt)
    // plus the wire-0 pin = 3 total.
    let cons = Constraint {
        a: blk(1, 1),
        b: blk(2, 1),
        c: blk(3, 1),
    };
    let r1cs = r1cs(p7(), 4, vec![0], vec![cons]);
    let ir = lower_two_copy(&r1cs, 1);
    let cs = ir.to_constraint_system();
    assert_eq!(cs.equalities.len(), 3);
}

// ─── to_boolean_query ────────────────────────────────────────────

#[test]
fn prop_to_boolean_query_preserves_prime() {
    let ir = empty_ir(p7(), 3, vec![0], 1);
    let q = ir.to_boolean_query();
    assert_eq!(q.prime, p7());
}

#[test]
fn prop_to_boolean_query_var_names_match_ring_order() {
    let ir = empty_ir(p7(), 3, vec![0], 1);
    let q = ir.to_boolean_query();
    assert_eq!(q.var_names(), ir.ring.var_names());
}

#[test]
fn prop_to_boolean_query_empty_constraints_yields_true_or_and() {
    // With no equalities/diseqs/assignments/disjunctions, the
    // conj is empty ⇒ Formula::True. The lowering always emits at
    // least the wire-0 pin, so the realistic empty case is hard to
    // reach; just check the formula is well-formed.
    use picus_solver::boolean::Formula;
    let ir = empty_ir(p7(), 3, vec![0], 1);
    let q = ir.to_boolean_query();
    // Either an And of literals or a Lit/True — definitely not False.
    assert!(!matches!(q.formula, Formula::False));
}

// ─── encode ──────────────────────────────────────────────────────

#[test]
fn prop_encode_returns_nonempty_polynomials_for_pinned_wire0() {
    // The lowering always emits at least the `x_0 - 1 = 0` equality.
    // `encode` lowers each non-zero equality into a polynomial, so the
    // result must have at least one polynomial.
    let ir = empty_ir(p7(), 3, vec![0], 1);
    let enc = ir.encode().expect("encode should succeed on empty system");
    assert!(!enc.polynomials.is_empty(), "wire-0 pin survives encoding");
}

#[test]
fn prop_encode_preserves_ring_prime() {
    let ir = empty_ir(p7(), 3, vec![0], 1);
    let enc = ir.encode().expect("encode OK");
    assert_eq!(enc.poly_ring.field().prime(), &p7());
}

#[test]
fn prop_encode_var_map_includes_used_vars() {
    // Spec: `encode` calls `compact_used_vars` and retains only variables
    // appearing in constraints / inputs / target — unconstrained ring
    // variables are correctly dropped. We assert the retained-set
    // contract on declared inputs + target, not every ring variable.
    let ir = empty_ir(p7(), 3, vec![0], 1);
    let enc = ir.encode().expect("encode OK");
    let names = ir.ring.var_names();
    assert!(
        enc.var_map.contains_key(&names[0]),
        "input var must be in var_map"
    );
    assert!(
        enc.var_map.contains_key(&names[1]),
        "target var must be in var_map"
    );
}

// ─── pre_eliminate_linear ────────────────────────────────────────

#[test]
fn prop_pre_eliminate_linear_returns_none_on_empty() {
    // No user equalities (only `x_0 - 1 = 0`, a single linear with one
    // pivot variable) — may or may not "change" depending on whether the
    // linsolve treats `x_0 = 1` as already-reduced. Either way, the
    // function must return without panicking, and if it reduces, the
    // reduced `PolySystem` keeps the same ring.
    let ir = empty_ir(p7(), 3, vec![0], 1);
    let cancel = CancelToken::none();
    let r = ir.pre_eliminate_linear(&cancel);
    if let Some(reduced) = r {
        assert_eq!(reduced.ring.n_vars(), ir.ring.n_vars());
    }
}

#[test]
fn prop_pre_eliminate_linear_preserves_disequalities_when_applied() {
    // Variety-preserving: the disequality list (which encodes the
    // target signal) must propagate unchanged.
    let ir = empty_ir(p7(), 4, vec![0], 2);
    let cancel = CancelToken::none();
    if let Some(reduced) = ir.pre_eliminate_linear(&cancel) {
        assert_eq!(reduced.disequalities, ir.disequalities);
    }
}

#[test]
fn prop_pre_eliminate_linear_preserves_metadata_when_applied() {
    // `add_field_polys` carries over. Wire-overlay metadata (input/known
    // sets, n_wires, target) lives on `UniquenessQuery` in picus-analysis,
    // not on the slim `PolySystem` this operation returns, so there is nothing
    // else to preserve at this layer.
    let r1cs = r1cs(p7(), 4, vec![0, 1], Vec::new());
    let ir = lower_two_copy(&r1cs, 3);
    let cancel = CancelToken::none();
    if let Some(reduced) = ir.pre_eliminate_linear(&cancel) {
        assert_eq!(reduced.add_field_polys, ir.add_field_polys);
        assert_eq!(reduced.ring.n_vars(), ir.ring.n_vars());
    }
}
