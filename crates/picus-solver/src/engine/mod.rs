//! Gröbner-basis and root-finding engines over the GF(p) algebra defined
//! in `picus_core::ff` (the algebra lives there; this module owns the
//! algorithms that run on it).
//!
//! - Buchberger's algorithm with Gebauer-Möller / sugar pair management and
//!   geobucket reduction, plus the F4-lite matrix path.
//! - Sparse-representation Buchberger (`sparse_gb`), the default engine.
//! - Hilbert numerator + quotient-dimension oracle over finished bases.
//! - Univariate root finding via Cantor-Zassenhaus.

// Algebra primitives re-bound from picus-core: one explicit list (not a
// glob) so "what does the engine consume from the algebra crate" is
// greppable here, and each type has one in-crate spelling.
pub(crate) use picus_core::ff::{
    divmask, field, linalg, matrix_order, monomial, polynomial, repr,
    sparse_monomial, sparse_polynomial,
};
pub(crate) use picus_core::ff::polynomial::DensePoly;

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

