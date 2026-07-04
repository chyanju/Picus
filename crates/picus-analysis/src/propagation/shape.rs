//! Shared polynomial-shape primitives for the propagation lemmas.
//!
//! Several lemmas parse a constraint polynomial as a linear combination. The
//! per-term triage ("constant, single linear variable, or nonlinear?") was
//! hand-rolled in each; [`linear_form`] centralises it. It is deliberately
//! *descriptive* — it returns the raw terms plus the accumulated constant and
//! makes no policy decision, because the lemmas intentionally differ on what a
//! nonzero constant means (e.g. `bim` rejects it; `aboz` ignores it) and on
//! how variables map to wires.

use num_bigint::BigUint;

use picus_core::poly::Poly;

use crate::uniqueness::UniquenessQuery;

/// Parse `poly` as a linear combination over **raw variable indices**:
/// `Some((terms, constant))` where `terms` are the degree-1 `(var, coeff)`
/// entries and `constant` is the accumulated constant coefficient, or `None`
/// if any term is nonlinear (a variable of exponent ≥ 2, or a product of two
/// or more variables).
///
/// The caller decides the policy: whether a nonzero `constant` is acceptable,
/// and how to map `var` → wire (`q.var_to_wire`).
pub(crate) fn linear_form(
    q: &UniquenessQuery,
    poly: &Poly,
) -> Option<(Vec<(usize, BigUint)>, BigUint)> {
    let mut terms: Vec<(usize, BigUint)> = Vec::new();
    let mut constant = BigUint::from(0u32);
    for (coeff, vars) in q.ir.poly_terms_idx(poly) {
        if vars.is_empty() {
            constant += coeff;
        } else if vars.len() == 1 && vars[0].1 == 1 {
            terms.push((vars[0].0, coeff));
        } else {
            return None;
        }
    }
    Some((terms, constant))
}
