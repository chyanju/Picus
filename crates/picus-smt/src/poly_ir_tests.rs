//! Tests for `poly_ir.rs` — the slim `PolyIR`'s own accessors:
//! `linear_term`, `constant`, `poly_terms`, and `poly_terms_idx`.
//!
//! These exercise only the use-agnostic constraint system, so they build a
//! bare `PolyIR` locally (a ring plus empty constraint vectors). The R1CS
//! two-copy lowering and the wire/uniqueness overlay are tested in the
//! picus-analysis crate's `uniqueness` module.

use std::sync::Arc;

use num_bigint::BigUint;
use picus_core::ff::field::PrimeField;
use picus_core::poly::FfPolyRing;

use crate::poly_ir::PolyIR;

/// GF(7) prime.
fn p7() -> BigUint {
    BigUint::from(7u32)
}

/// Build a bare `PolyIR` over GF(p) with `n_vars` variables named
/// `x0..x{n-1}` and no constraints — enough to exercise the `PolyIR`
/// accessor methods.
fn empty_ir(p: BigUint, n_vars: usize) -> PolyIR {
    let field = PrimeField::new(p);
    let names: Vec<String> = (0..n_vars).map(|i| format!("x{}", i)).collect();
    let ring = Arc::new(FfPolyRing::new(field, names));
    PolyIR {
        ring,
        equalities: Vec::new(),
        disjunctions: Vec::new(),
        disequalities: Vec::new(),
        assignments: Vec::new(),
        bitsums: Vec::new(),
        add_field_polys: false,
    }
}

// ─── linear_term / constant ─────────────────────────────────────

#[test]
fn test_linear_term_constructs_nonzero_poly() {
    // Structural: builds without panicking and the result is non-zero.
    let ir = empty_ir(p7(), 3);
    let t = ir.linear_term(&BigUint::from(3u32), 1);
    assert!(!ir.ring.is_zero(&t));
}

#[test]
fn test_linear_term_zero_coeff_is_zero_poly() {
    // 0 * x_1 = 0 in GF(7).
    let ir = empty_ir(p7(), 3);
    let t = ir.linear_term(&BigUint::from(0u32), 1);
    assert!(ir.ring.is_zero(&t));
}

#[test]
fn test_linear_term_coeff_reduced_mod_p() {
    // In GF(7), 7 ≡ 0; the term 7*x_1 must equal 0.
    let ir = empty_ir(p7(), 3);
    let t = ir.linear_term(&BigUint::from(7u32), 1);
    assert!(ir.ring.is_zero(&t), "7*x_1 over GF(7) should be 0");
}

#[test]
fn test_constant_zero_is_zero_poly() {
    let ir = empty_ir(p7(), 3);
    let c = ir.constant(&BigUint::from(0u32));
    assert!(ir.ring.is_zero(&c));
}

#[test]
fn test_constant_nonzero() {
    let ir = empty_ir(p7(), 3);
    let c = ir.constant(&BigUint::from(3u32));
    assert!(!ir.ring.is_zero(&c));
}

// ─── poly_terms / poly_terms_idx (consistency) ──────────────────

#[test]
fn prop_poly_terms_and_idx_agree_on_term_count() {
    // Spec: both iterators yield one entry per nonzero term.
    let ir = empty_ir(p7(), 4);
    let a = ir.linear_term(&BigUint::from(2u32), 1);
    let b = ir.linear_term(&BigUint::from(3u32), 2);
    let poly = ir.ring.add(a, b);
    let n_named: usize = ir.poly_terms(&poly).count();
    let n_idx: usize = ir.poly_terms_idx(&poly).count();
    assert_eq!(n_named, n_idx);
    assert!(n_named >= 1);
}

#[test]
fn prop_poly_terms_idx_constant_has_empty_var_list() {
    // Doc spec: "a constant term yields an empty `Vec`".
    let ir = empty_ir(p7(), 3);
    let c = ir.constant(&BigUint::from(5u32));
    let terms: Vec<_> = ir.poly_terms_idx(&c).collect();
    assert_eq!(terms.len(), 1);
    let (coeff, vars) = &terms[0];
    assert_eq!(coeff, &BigUint::from(5u32));
    assert!(vars.is_empty(), "constant term has empty var list");
}

#[test]
fn prop_poly_terms_idx_linear_has_single_var_degree_one() {
    // Doc spec: linear monomial `x` yields `[(x_idx, 1)]`.
    let ir = empty_ir(p7(), 3);
    let t = ir.linear_term(&BigUint::from(2u32), 1);
    let terms: Vec<_> = ir.poly_terms_idx(&t).collect();
    assert_eq!(terms.len(), 1);
    let (_, vars) = &terms[0];
    assert_eq!(vars.len(), 1);
    let (idx, exp) = vars[0];
    assert_eq!(idx, 1);
    assert_eq!(exp, 1);
}

#[test]
fn prop_poly_terms_named_for_quadratic_expands_each_degree() {
    // Doc spec for `poly_terms`: "`x*x` ⇒ `["x", "x"]`".
    let ir = empty_ir(p7(), 3);
    let x1 = ir.linear_term(&BigUint::from(1u32), 1);
    let sq = ir.ring.mul(ir.ring.clone_poly(&x1), x1);
    let terms: Vec<_> = ir.poly_terms(&sq).collect();
    assert_eq!(terms.len(), 1);
    let (_, atoms) = &terms[0];
    assert_eq!(atoms.len(), 2, "x_1*x_1 ⇒ two atoms");
    assert_eq!(atoms[0], atoms[1]);
}

// ─── constant reduction across primes ───────────────────────────

// Sweep small primes — field arithmetic invariants hold for any prime.
#[test]
fn prop_constant_reduces_modulo_prime_across_primes() {
    for &p in &[2u32, 7, 101] {
        let ir = empty_ir(BigUint::from(p), 3);
        // p ≡ 0 mod p, so `constant(p)` must be zero.
        let c = ir.constant(&BigUint::from(p));
        assert!(ir.ring.is_zero(&c), "p={} mod p ≠ 0?", p);
        // p+1 ≡ 1 (nonzero) mod p.
        let c1 = ir.constant(&BigUint::from(p + 1));
        assert!(!ir.ring.is_zero(&c1), "p={} ⇒ (p+1) mod p = 1", p);
    }
}
