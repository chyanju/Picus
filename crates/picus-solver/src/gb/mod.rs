//! Higher-level Gröbner-basis orchestration, layered over the low-level
//! engine in [`crate::ff`]. The split: [`crate::ff`] holds the algorithms
//! (Buchberger, F4, sparse GB, Cantor-Zassenhaus root finding) over
//! [`picus_core::ff`]'s GF(p) data types; this `gb` module groups the
//! work that drives them — the ideal API ([`ideal`]), model construction
//! ([`model`]), root extraction ([`roots`]), the FGLM order change
//! ([`fglm`]), homogenisation ([`gb_homog`] / [`homog_ring`]), and
//! UNSAT-core tracing ([`tracer`]). Both
//! are named for GF(p) algebra but sit at different layers.


#[cfg(test)]
mod tests;

// Submodules: ideal operations, incremental GB, root finding, homogenization
// pipeline, model construction, branching, and UNSAT-core tracing.
pub(crate) mod fglm;
pub mod ideal;
pub mod linsolve;
pub mod roots;
pub(crate) mod gb_homog;
pub(crate) mod homog_ring;
pub(crate) mod model;
pub(crate) mod brancher;
pub(crate) mod tracer;
