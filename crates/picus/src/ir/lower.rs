//! The single place where the ring-free [`crate::ir`] surface meets the
//! low-level `Arc`/`FfPolyRing`/`Poly`/`FieldElem` machinery. Everything else
//! in the module is ring-agnostic; here a [`PolyIR`] is materialised into a
//! [`PolySystem`] over GF(p) that the existing solver can decide.

use std::sync::Arc;

use num_bigint::{BigInt, BigUint};

use picus_core::poly::{FfPolyRing, Poly};
use picus_smt::poly_system::PolySystem;

use super::expr::Expr;
use super::PolyIR;

/// Materialise the ring-free builder into a concrete GF(p) [`PolySystem`].
pub(crate) fn lower(builder: &PolyIR) -> PolySystem {
    let field = picus_core::ff::field::PrimeField::new(builder.prime.clone());
    let ring = Arc::new(FfPolyRing::new(field, builder.names.clone()));
    let n = ring.n_vars();
    let mut ps = PolySystem::new(Arc::clone(&ring));

    for e in &builder.eqs {
        ps.push_equality(lower_expr(e, &ring, &builder.prime, n));
    }
    for clause in &builder.ors {
        let polys: Vec<Poly> = clause
            .iter()
            .map(|e| lower_expr(e, &ring, &builder.prime, n))
            .collect();
        ps.push_disjunction(polys);
    }
    for &(a, b) in &builder.diseq_vars {
        ps.add_disequality(a as usize, b as usize);
    }
    for (idx, val) in &builder.assigns {
        ps.add_assignment(*idx as usize, reduce(&val.0, &builder.prime));
    }
    for bits in &builder.bitsums {
        ps.add_bitsum(bits.iter().map(|&i| i as usize).collect());
    }
    ps.set_add_field_polys(builder.add_field_polys);
    ps
}

/// Lower one ring-free [`Expr`] into a ring [`Poly`], reducing each signed
/// coefficient into `[0, prime)`.
fn lower_expr(e: &Expr, ring: &FfPolyRing, prime: &BigUint, n: usize) -> Poly {
    let terms = e.terms.iter().map(|(mono, coeff)| {
        let mut exps = vec![0usize; n];
        for &(v, k) in mono {
            exps[v as usize] += k as usize;
        }
        let m = ring.ring.create_monomial(exps);
        let el = ring.field().from_biguint(&reduce(coeff, prime));
        (el, m)
    });
    ring.ring.from_terms(terms)
}

/// Reduce a signed integer coefficient into the canonical `[0, prime)`
/// representative.
fn reduce(c: &BigInt, p: &BigUint) -> BigUint {
    let pi = BigInt::from(p.clone());
    let r = ((c % &pi) + &pi) % &pi;
    r.to_biguint()
        .expect("reduced coefficient is non-negative and < prime")
}
