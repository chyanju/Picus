//! Gröbner-basis and root-finding engines over the GF(p) algebra defined in
//! [`picus_core::ff`].
//!
//! - Buchberger's algorithm with Gebauer-Möller / sugar pair management and
//!   geobucket reduction, plus the F4-lite matrix path.
//! - Hilbert numerator + quotient-dimension oracle over finished bases.
//! - Univariate root finding via Cantor-Zassenhaus.

// Algebra primitives (field, dense/sparse polynomials, reduction) live in
// picus-core; re-bound here so the in-crate engine refers to them as
// `crate::ff::*`.
pub(crate) use picus_core::ff::*;

pub(crate) mod buchberger;
pub(crate) mod f4;
pub(crate) mod hilbert;
pub(crate) mod spair;
pub(crate) mod spair_criteria;
pub(crate) mod sparse_gb;
pub(crate) mod univariate;

#[cfg(test)]
#[path = "repr_oracle_tests.rs"]
mod repr_oracle;

