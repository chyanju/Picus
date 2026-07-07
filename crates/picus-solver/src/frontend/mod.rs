//! Frontend: lowering a polynomial system to the GB-solvable encoding.
//!
//! - [`encoder`]: constraint system to GB polynomials.
//! - `rewriter`: FF term canonicalization.
//! - `bitprop`: bit-propagation from known bitsum structure.
//! - [`uf`]: uninterpreted-function lowering (eager Ackermann) and
//!   model-side congruence certification.
//! - [`bench_fixtures`]: SMT-LIB QF_FF source builders for benches/tools.

pub mod bench_fixtures;
pub mod encoder;
pub mod formula;
pub(crate) mod rewriter;
pub mod uf;
