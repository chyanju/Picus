//! Tests for the `UniquenessQuery` wire-bookkeeping overlay.

use std::collections::HashSet;
use std::sync::Arc;

use num_bigint::BigUint;
use picus_core::ff::field::PrimeField;
use picus_core::poly::FfPolyRing;
use picus_smt::poly_ir::PolyIR;

use crate::uniqueness::UniquenessQuery;

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
    let ir = PolyIR {
        ring,
        n_wires,
        input_indices: input_indices.clone(),
        equalities: Vec::new(),
        disjunctions: Vec::new(),
        known_signals: input_indices.clone(),
        target_signal: 0,
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
