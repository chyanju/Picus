//! Test-only local R1CS two-copy lowering for picus-smt's own unit tests.
//!
//! The real R1CS-to-uniqueness lowering lives in the picus-analysis crate
//! (`uniqueness::r1cs_to_uniqueness_query`). picus-smt's
//! *integration* tests (a separate crate) can call it directly, but the lib's
//! own *unit* tests cannot: building the `--test` crate links a *second* copy
//! of picus-smt (through the picus-analysis dev-dependency), so a `PolySystem`
//! obtained via picus-analysis is a *different nominal type* than the
//! crate-under-test's `PolySystem`. This module reproduces the two-copy
//! construction locally, yielding the crate-LOCAL [`crate::poly_system::PolySystem`],
//! so the unit tests need no re-homing and no picus-analysis dependency.
//!
//! It is a faithful port of `r1cs_to_uniqueness_query` (and its private
//! `constraint_to_poly` / `block_to_linear`) with two differences: it produces
//! the slim `PolySystem` (no wire overlay metadata), and it materialises the
//! target disequality directly as `disequalities = [(target, n_wires + target)]`
//! — the fixtures that call this expect the target pair to be present.

use std::collections::HashSet;
use std::sync::Arc;

use num_bigint::BigUint;

use picus_core::ff::field::PrimeField;
use picus_core::poly::{FfPolyRing, IrPoly as Poly};
use picus_r1cs::field_reduce;
use picus_r1cs::grammar::{ConstraintBlock, R1csFile};

use crate::poly_system::PolySystem;

/// Lower a parsed R1CS file into a crate-local [`PolySystem`] laid out as two
/// copies of the circuit wires (`x_0..x_{n-1}`, `y_0..y_{n-1}`), with the
/// target disequality `(target, n_wires + target)` materialised directly.
///
/// Each `A * B = C` constraint becomes `expand(A)*expand(B) - expand(C) = 0`
/// emitted in both copies; input wires reuse `x_i` in both copies; wire 0 is
/// pinned to `1` in both copies. `add_field_polys` is on iff `prime <= 1000`.
pub(crate) fn lower_two_copy(r1cs: &R1csFile, target: usize) -> PolySystem {
    let n_wires = r1cs.n_wires() as usize;
    let input_indices: HashSet<usize> = r1cs.inputs.iter().copied().collect();
    let prime = &r1cs.header.prime_number;

    // Build a ring with 2n variables: x_0..x_{n-1}, y_0..y_{n-1}.
    let mut var_names = Vec::with_capacity(2 * n_wires);
    for i in 0..n_wires {
        var_names.push(format!("x{}", i));
    }
    for i in 0..n_wires {
        var_names.push(format!("y{}", i));
    }
    let field = PrimeField::new(prime.clone());
    let ring = Arc::new(FfPolyRing::new(field, var_names));

    let mut equalities: Vec<Poly> = Vec::new();

    // Original-copy constraints, then alt-copy constraints.
    for c in &r1cs.constraints.constraints {
        if let Some(eq) = constraint_to_poly(&ring, &c.a, &c.b, &c.c, &input_indices, false, prime) {
            equalities.push(eq);
        }
    }
    for c in &r1cs.constraints.constraints {
        if let Some(eq) = constraint_to_poly(&ring, &c.a, &c.b, &c.c, &input_indices, true, prime) {
            equalities.push(eq);
        }
    }

    // Wire 0 pinned to 1 in both copies (folded into constants elsewhere, but
    // backends still observe `x_0` as a ring variable and need the pin).
    let one_el = ring.field().one();
    equalities.push(ring.sub(ring.var(0), ring.constant(one_el)));

    let small_prime_threshold = BigUint::from(1000u32);
    let add_field_polys = prime <= &small_prime_threshold;

    PolySystem {
        ring,
        equalities,
        disjunctions: Vec::new(),
        disequalities: vec![(target, n_wires + target)],
        assignments: Vec::new(),
        bitsums: Vec::new(),
        add_field_polys,
    }
}

/// Lower one `A * B = C` R1CS constraint into `expand(A)*expand(B) - expand(C)`
/// in the given copy. Returns `None` for the zero polynomial.
fn constraint_to_poly(
    ring: &Arc<FfPolyRing>,
    a: &ConstraintBlock,
    b: &ConstraintBlock,
    c: &ConstraintBlock,
    input_indices: &HashSet<usize>,
    is_alt: bool,
    prime: &BigUint,
) -> Option<Poly> {
    let sum_a = block_to_linear(ring, a, input_indices, is_alt, prime);
    let sum_b = block_to_linear(ring, b, input_indices, is_alt, prime);
    let sum_c = block_to_linear(ring, c, input_indices, is_alt, prime);
    let ab = ring.mul(sum_a, sum_b);
    let eq = ring.sub(ab, sum_c);
    if ring.is_zero(&eq) {
        None
    } else {
        Some(eq)
    }
}

/// Build `sum_i coeff_i * var_i` for one R1CS constraint block. Inputs use the
/// original `x_i` index in both copies; non-inputs use `x_i` in the orig copy
/// and `y_i` in the alt copy. Wire 0 folds `coeff * x_0` into the constant.
fn block_to_linear(
    ring: &Arc<FfPolyRing>,
    block: &ConstraintBlock,
    input_indices: &HashSet<usize>,
    is_alt: bool,
    prime: &BigUint,
) -> Poly {
    let n_wires = ring.n_vars() / 2;
    let mut acc = ring.zero();
    for (&wire_id, factor) in block.wire_ids.iter().zip(block.factors.iter()) {
        let wid = wire_id as usize;
        let coeff = field_reduce(factor, prime);
        let coeff_el = ring.field().from_biguint(&coeff);
        let term = if wid == 0 {
            ring.constant(coeff_el)
        } else {
            let var_idx = if is_alt && !input_indices.contains(&wid) {
                n_wires + wid
            } else {
                wid
            };
            ring.scale(coeff_el, ring.var(var_idx))
        };
        acc = ring.add(acc, term);
    }
    acc
}
