//! Tests for the `UniquenessQuery` wire-bookkeeping overlay.

use std::collections::HashSet;
use std::sync::Arc;

use num_bigint::BigUint;
use picus_core::ff::field::PrimeField;
use picus_core::poly::FfPolyRing;
use picus_r1cs::grammar::Constraint;
use picus_r1cs::testkit::{blk, p7, r1cs, zero_blk};
use picus_smt::poly_system::PolySystem;

use crate::uniqueness::{
    polysystem_to_uniqueness_query, r1cs_to_uniqueness_query, LowerError, UniquenessQuery,
};

/// Build a `UniquenessQuery` over GF(7) with `2 * n_wires` variables
/// (`x0..`, `y0..`) and the given input wires.
fn query(n_wires: usize, inputs: &[usize]) -> UniquenessQuery {
    let field = PrimeField::new(BigUint::from(7u32));
    let mut names = Vec::with_capacity(2 * n_wires);
    for i in 0..n_wires {
        names.push(format!("x{}", i));
    }
    for i in 0..n_wires {
        names.push(format!("y{}", i));
    }
    let ring = Arc::new(FfPolyRing::new(field, names));
    let input_indices: HashSet<usize> = inputs.iter().copied().collect();
    let ir = PolySystem {
        ring,
        equalities: Vec::new(),
        disjunctions: Vec::new(),
        disequalities: Vec::new(),
        assignments: Vec::new(),
        bitsums: Vec::new(),
        add_field_polys: false,
    };
    UniquenessQuery {
        n_wires,
        input_indices: input_indices.clone(),
        known_signals: input_indices,
        target_signal: 0,
        base_disequalities: Vec::new(),
        ir,
    }
}

#[test]
fn wire_index_roundtrip() {
    let q = query(3, &[0]);
    assert_eq!(q.orig_var(2), 2);
    assert_eq!(q.alt_var(2), 5);
    assert_eq!(q.var_to_wire(2), 2);
    assert_eq!(q.var_to_wire(5), 2);
    assert_eq!(q.x_name(2), "x2");
    assert_eq!(q.y_name(2), "y2");
}

#[test]
fn set_target_writes_single_disequality() {
    let mut q = query(3, &[0]);
    q.set_target(2);
    assert_eq!(q.target_signal, 2);
    assert_eq!(q.ir.disequalities, vec![(2, 5)]);
}

#[test]
#[should_panic]
fn set_target_rejects_input_wire() {
    let mut q = query(3, &[0]);
    q.set_target(0);
}

#[test]
fn add_known_wire_appends_equality_for_noninput_and_is_idempotent() {
    let mut q = query(3, &[0]);
    let before = q.ir.equalities.len();
    q.add_known_wire(2);
    assert!(q.known_signals.contains(&2));
    assert_eq!(q.ir.equalities.len(), before + 1);
    // Second call must not append a duplicate `x_2 - y_2 = 0`.
    q.add_known_wire(2);
    assert_eq!(q.ir.equalities.len(), before + 1);
}

#[test]
fn add_known_wire_is_equality_noop_for_input_wire() {
    let mut q = query(3, &[0]);
    let before = q.ir.equalities.len();
    q.add_known_wire(0); // input: shares x_0 across copies, no fresh equality
    assert!(q.known_signals.contains(&0));
    assert_eq!(q.ir.equalities.len(), before);
}

// ─── R1CS → UniquenessQuery lowering ─────────────────────────────
//
// These exercise `r1cs_to_uniqueness_query` end-to-end: ring layout, wire-0
// pinning, copy symmetry, field-poly gating, error paths, and the wire
// overlay it records.

// Fixture builders (`r1cs`, `blk`, `zero_blk`, `p7`) live in
// `picus_r1cs::testkit`.

#[test]
fn r1cs_target_out_of_bounds_returns_err() {
    // Doc spec: target_signal ≥ n_wires must return WireOutOfBounds.
    let r1cs = r1cs(p7(), 3, vec![0], Vec::new());
    let r = r1cs_to_uniqueness_query(&r1cs, &HashSet::new(), 3);
    assert!(matches!(r, Err(LowerError::WireOutOfBounds { .. })));
}

#[test]
fn r1cs_target_equal_n_wires_is_err() {
    // Edge: equality is OOB (wires are 0-indexed up to n_wires-1).
    let r1cs = r1cs(p7(), 2, vec![0], Vec::new());
    assert!(r1cs_to_uniqueness_query(&r1cs, &HashSet::new(), 2).is_err());
}

#[test]
fn r1cs_ring_has_2n_vars() {
    // Doc spec: "the ring carries `2 * n_wires` variables".
    let r1cs = r1cs(p7(), 5, vec![0], Vec::new());
    let ir = r1cs_to_uniqueness_query(&r1cs, &HashSet::new(), 1).unwrap();
    assert_eq!(ir.ir.ring.n_vars(), 10);
}

#[test]
fn r1cs_var_names_layout() {
    // First `n_wires` are `xN`, then `n_wires` are `yN`.
    let r1cs = r1cs(p7(), 3, vec![0], Vec::new());
    let ir = r1cs_to_uniqueness_query(&r1cs, &HashSet::new(), 1).unwrap();
    let names = ir.ir.ring.var_names();
    assert_eq!(names, &["x0", "x1", "x2", "y0", "y1", "y2"]);
}

#[test]
fn r1cs_emits_wire0_pinned_to_one() {
    // Doc spec: "Wire 0 pinned to 1. … backends still observe `x_0`
    // as a ring variable and need an equality to pin it." Even with
    // no source constraints, an `x_0 - 1 = 0` equality must appear.
    let r1cs = r1cs(p7(), 3, vec![0], Vec::new());
    let ir = r1cs_to_uniqueness_query(&r1cs, &HashSet::new(), 1).unwrap();
    assert!(
        !ir.ir.equalities.is_empty(),
        "must emit at least the x_0 = 1 pin"
    );
}

#[test]
fn r1cs_disequality_at_target() {
    // The target disequality is materialised by `set_target`; after it,
    // the underlying PolySystem carries a single `(target_x, target_y)` pair.
    let r1cs = r1cs(p7(), 4, vec![0], Vec::new());
    let mut ir = r1cs_to_uniqueness_query(&r1cs, &HashSet::new(), 2).unwrap();
    ir.set_target(2);
    assert_eq!(ir.ir.disequalities, vec![(2, 6)]);
}

#[test]
fn r1cs_small_prime_enables_field_polys() {
    // Doc spec: "field polys enabled iff the prime is small" — gate
    // is `prime <= 1000`. GF(7) is small.
    let r1cs = r1cs(p7(), 3, vec![0], Vec::new());
    let ir = r1cs_to_uniqueness_query(&r1cs, &HashSet::new(), 1).unwrap();
    assert!(ir.ir.add_field_polys, "GF(7) ≤ 1000 ⇒ add_field_polys=true");
}

#[test]
fn r1cs_big_prime_disables_field_polys() {
    // Boundary: BN128 prime is way above 1000.
    let big = picus_r1cs::testkit::bn128();
    let r1cs = r1cs(big, 3, vec![0], Vec::new());
    let ir = r1cs_to_uniqueness_query(&r1cs, &HashSet::new(), 1).unwrap();
    assert!(
        !ir.ir.add_field_polys,
        "BN128 > 1000 ⇒ add_field_polys=false"
    );
}

#[test]
fn r1cs_threshold_at_1000() {
    // Exact boundary: prime == 1000 must satisfy `prime <= 1000` and
    // enable field polys (note 1000 is not prime, but the gate uses
    // BigUint comparison, not primality). Test just verifies the
    // `<=` direction.
    let p = BigUint::from(1000u32);
    let r1cs = r1cs(p, 3, vec![0], Vec::new());
    let ir = r1cs_to_uniqueness_query(&r1cs, &HashSet::new(), 1).unwrap();
    assert!(ir.ir.add_field_polys, "1000 ≤ 1000 boundary");
}

#[test]
fn r1cs_above_threshold_disables_field_polys() {
    // 1001 exceeds the gate.
    let p = BigUint::from(1001u32);
    let r1cs = r1cs(p, 3, vec![0], Vec::new());
    let ir = r1cs_to_uniqueness_query(&r1cs, &HashSet::new(), 1).unwrap();
    assert!(!ir.ir.add_field_polys, "1001 > 1000 boundary");
}

#[test]
fn r1cs_inputs_propagated() {
    let r1cs = r1cs(p7(), 5, vec![0, 1, 3], Vec::new());
    let ir = r1cs_to_uniqueness_query(&r1cs, &HashSet::new(), 2).unwrap();
    for w in [0usize, 1, 3] {
        assert!(ir.input_indices.contains(&w), "wire {} is an input", w);
    }
    assert!(!ir.input_indices.contains(&2));
    assert!(!ir.input_indices.contains(&4));
}

#[test]
fn r1cs_known_signals_seeded_from_argument() {
    let mut known = HashSet::new();
    known.insert(3usize);
    let r1cs = r1cs(p7(), 5, vec![0], Vec::new());
    let ir = r1cs_to_uniqueness_query(&r1cs, &known, 2).unwrap();
    assert!(ir.known_signals.contains(&3));
}

#[test]
fn r1cs_copy_symmetry_emits_two_constraints_per_block() {
    // Doc spec (copy-symmetry invariant): "every R1CS constraint is
    // lowered into BOTH copies below". For one non-input constraint
    // we must see at least two equalities (orig + alt) above the
    // wire-0 pin.
    //
    // Build: (1 * x_1) * (1 * x_2) = (1 * x_3) over wires {0..4}
    let cons = Constraint {
        a: blk(1, 1),
        b: blk(2, 1),
        c: blk(3, 1),
    };
    let r1cs = r1cs(p7(), 4, vec![0], vec![cons]);
    let ir = r1cs_to_uniqueness_query(&r1cs, &HashSet::new(), 1).unwrap();
    // wire-0 pin (1) + orig (1) + alt (1) = 3
    assert!(
        ir.ir.equalities.len() >= 3,
        "expected ≥3 equalities (orig + alt + pin), got {}",
        ir.ir.equalities.len()
    );
}

#[test]
fn r1cs_zero_constraint_dropped() {
    // 0 * 0 = 0 lowers to the zero polynomial; `constraint_to_poly_single`
    // returns Ok(None) so it should NOT be appended.
    let cons = Constraint {
        a: zero_blk(),
        b: zero_blk(),
        c: zero_blk(),
    };
    let r1cs = r1cs(p7(), 3, vec![0], vec![cons]);
    let ir = r1cs_to_uniqueness_query(&r1cs, &HashSet::new(), 1).unwrap();
    // Only the wire-0 pin should be present.
    assert_eq!(
        ir.ir.equalities.len(),
        1,
        "zero constraint dropped, only x_0 = 1 remains"
    );
}

#[test]
fn r1cs_out_of_bounds_wire_id_returns_err() {
    // `block_to_linear_single` must reject `wid >= n_wires`. Build a
    // constraint referencing wire 99 when only 3 wires exist.
    let cons = Constraint {
        a: blk(99, 1),
        b: blk(1, 1),
        c: zero_blk(),
    };
    let r1cs = r1cs(p7(), 3, vec![0], vec![cons]);
    let r = r1cs_to_uniqueness_query(&r1cs, &HashSet::new(), 1);
    assert!(matches!(r, Err(LowerError::WireOutOfBounds { .. })));
}

#[test]
fn r1cs_assignments_and_bitsums_empty_after_lowering() {
    // Doc spec: R1CS lowering does NOT populate assignments / bitsums
    // (those are for SMT2/CDCL(T) producers).
    let r1cs = r1cs(p7(), 3, vec![0], Vec::new());
    let ir = r1cs_to_uniqueness_query(&r1cs, &HashSet::new(), 1).unwrap();
    assert!(ir.ir.assignments.is_empty());
    assert!(ir.ir.bitsums.is_empty());
    assert!(ir.ir.disjunctions.is_empty());
}

#[test]
fn r1cs_n_wires_recorded() {
    let r1cs = r1cs(p7(), 7, vec![0], Vec::new());
    let ir = r1cs_to_uniqueness_query(&r1cs, &HashSet::new(), 1).unwrap();
    assert_eq!(ir.n_wires, 7);
}

#[test]
fn r1cs_target_signal_recorded() {
    let r1cs = r1cs(p7(), 5, vec![0], Vec::new());
    let ir = r1cs_to_uniqueness_query(&r1cs, &HashSet::new(), 3).unwrap();
    assert_eq!(ir.target_signal, 3);
}

// ─── Generic single-copy → two-copy doubling ─────────────────────
//
// `polysystem_to_uniqueness_query` doubles an arbitrary single-copy
// `PolySystem`; `r1cs_to_uniqueness_query` (above) is one caller of it.

/// A single-copy `PolySystem` over GF(7) with `n` variables `v0..v{n-1}`.
fn single_gf7(n: usize) -> PolySystem {
    let field = PrimeField::new(BigUint::from(7u32));
    let names: Vec<String> = (0..n).map(|i| format!("v{}", i)).collect();
    PolySystem::new(Arc::new(FfPolyRing::new(field, names)))
}

#[test]
fn doubler_mirrors_constraints_and_shares_inputs() {
    let mut single = single_gf7(3);
    let ring = Arc::clone(&single.ring);
    single.push_equality(ring.sub(ring.var(1), ring.var(2))); // v1 - v2 = 0

    let inputs: HashSet<usize> = [0usize].into_iter().collect();
    let q = polysystem_to_uniqueness_query(&single, &inputs, &HashSet::new()).unwrap();

    assert_eq!(q.n_wires, 3);
    assert_eq!(q.ir.ring.n_vars(), 6, "doubled ring has 2n variables");
    assert_eq!(q.ir.equalities.len(), 2, "one constraint, emitted in both copies");
    assert_eq!(q.input_indices, inputs);
    assert_eq!(q.x_name(1), "x1");
    assert_eq!(q.y_name(1), "y1");
    assert_eq!(q.orig_var(1), 1);
    assert_eq!(q.alt_var(1), 4);
    assert!(q.base_disequalities.is_empty());
}

#[test]
fn doubler_carries_field_polys_flag() {
    let mut single = single_gf7(2);
    single.set_add_field_polys(true);
    let q = polysystem_to_uniqueness_query(&single, &HashSet::new(), &HashSet::new()).unwrap();
    assert!(q.ir.add_field_polys);
}

#[test]
fn doubler_seeds_known_signals() {
    let single = single_gf7(4);
    let known: HashSet<usize> = [2usize, 3].into_iter().collect();
    let q = polysystem_to_uniqueness_query(&single, &HashSet::new(), &known).unwrap();
    assert_eq!(q.known_signals, known);
}

#[test]
fn doubler_preserves_source_disequalities_as_base() {
    let mut single = single_gf7(3);
    single.add_disequality(1, 2); // v1 != v2, both non-input wires
    let mut q = polysystem_to_uniqueness_query(&single, &HashSet::new(), &HashSet::new()).unwrap();

    // Both copies of the source disequality become `base_disequalities`; the
    // doubled system carries no target disequality until `set_target`.
    assert_eq!(q.base_disequalities, vec![(1, 2), (4, 5)]);
    assert!(q.ir.disequalities.is_empty());

    // set_target preserves the base and appends only the target pair.
    q.set_target(1);
    assert_eq!(q.ir.disequalities, vec![(1, 2), (4, 5), (1, 4)]);
}

#[test]
fn doubler_rejects_out_of_range_input() {
    let single = single_gf7(2);
    let inputs: HashSet<usize> = [5usize].into_iter().collect();
    assert!(matches!(
        polysystem_to_uniqueness_query(&single, &inputs, &HashSet::new()),
        Err(LowerError::WireOutOfBounds {
            wire: 5,
            n_wires: 2,
            ..
        })
    ));
}
