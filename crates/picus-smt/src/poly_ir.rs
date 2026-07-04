//! Solver-agnostic polynomial IR: a use-agnostic GF(p) constraint system
//! that the SMT backends lower and solve. `PolyIR` knows nothing about
//! "wires", "copies", or "uniqueness" — it is purely a ring plus a set of
//! polynomial constraints. The uniqueness/determinism overlay that Picus's
//! under-constrained analysis builds on top of it lives in
//! `picus_analysis::uniqueness::UniquenessQuery`, which owns a `PolyIR` and
//! adds the wire bookkeeping and the R1CS two-copy lowering.
//!
//! A [`PolyIR`] bundles a polynomial ring over GF(p) with:
//! - a flat `Vec<Poly>` of `(poly = 0)` equalities,
//! - a list of `(p_1 = 0 ∨ p_2 = 0 ∨ ...)` disjunctions,
//! - disequality witness sites `(a_idx, b_idx)` (each a Rabinowitsch
//!   `(x_a − x_b)·w − 1 = 0` at encoding time),
//! - variable assignments `(idx, val)` (each `x_idx − val = 0`),
//! - bitsum chain declarations, and
//! - the `add_field_polys` flag.
//!
//! Indices in `disequalities` / `assignments` / `bitsums` are into
//! `ring.var_names()`. The native engine's lowering (to `ConstraintSystem` /
//! `BooleanQuery` / `EncodedSystem`) lives in the native backend, so this
//! module depends only on `picus-core`.

use std::sync::Arc;

use num_bigint::BigUint;
use picus_core::poly::{FfPolyRing, IrPoly as Poly};

/// A use-agnostic polynomial constraint system over GF(p).
pub struct PolyIR {
    pub ring: Arc<FfPolyRing>,
    pub equalities: Vec<Poly>,
    pub disjunctions: Vec<Vec<Poly>>,
    /// Disequality witness sites: each `(a_idx, b_idx)` pair becomes a
    /// Rabinowitsch polynomial `(x_a - x_b) · w_i - 1 = 0` at encoding time.
    /// Indices are into `ring.var_names()`.
    pub disequalities: Vec<(usize, usize)>,
    /// Variable assignments: `(idx, val)` emits `x_idx - val = 0`.
    pub assignments: Vec<(usize, BigUint)>,
    /// Bitsum chain declarations: each `[b_0, ..., b_{k-1}]` defines an
    /// auxiliary `__bitsum_N = sum(2^i · x_{b_i})`, routed into
    /// `bitsum_polys` (basis-0 only for split-GB).
    pub bitsums: Vec<Vec<usize>>,
    /// Append `x^p - x = 0` field polynomials for every ring variable when
    /// `prime <= 1000` (the encoder still gates on the prime size; this flag
    /// just opts in).
    pub add_field_polys: bool,
}

impl PolyIR {
    /// An empty constraint system over `ring`: no equalities, disjunctions,
    /// disequalities, assignments, or bitsums, with `add_field_polys` off.
    ///
    /// This is the entry point for callers that build a `PolyIR` directly
    /// (rather than lowering an R1CS uniqueness query). Assemble it with the
    /// `push_equality` / `add_disequality` / `add_assignment` / `add_bitsum` /
    /// `push_disjunction` / `set_add_field_polys` mutators, then hand it to a
    /// solver backend (or `picus::solve`).
    pub fn new(ring: Arc<FfPolyRing>) -> Self {
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

    /// Append an equality constraint `poly = 0`. Returns `&mut self` for
    /// chaining.
    pub fn push_equality(&mut self, poly: Poly) -> &mut Self {
        self.equalities.push(poly);
        self
    }

    /// Append a disjunction `p_1 = 0 ∨ … ∨ p_k = 0` (`clause = [p_1, …, p_k]`).
    pub fn push_disjunction(&mut self, clause: Vec<Poly>) -> &mut Self {
        self.disjunctions.push(clause);
        self
    }

    /// Append a disequality: the ring variables at indices `a` and `b` must
    /// differ. Lowered to a Rabinowitsch polynomial at encoding time.
    pub fn add_disequality(&mut self, a: usize, b: usize) -> &mut Self {
        self.disequalities.push((a, b));
        self
    }

    /// Pin the ring variable at index `var` to `val` (emits `x_var - val = 0`).
    pub fn add_assignment(&mut self, var: usize, val: BigUint) -> &mut Self {
        self.assignments.push((var, val));
        self
    }

    /// Declare a bitsum chain: `bits = [b_0, …, b_{k-1}]` defines an auxiliary
    /// `sum(2^i · x_{b_i})`.
    pub fn add_bitsum(&mut self, bits: Vec<usize>) -> &mut Self {
        self.bitsums.push(bits);
        self
    }

    /// Opt into field polynomials `x^p - x = 0` for every ring variable
    /// (needed for exact reasoning over small primes; the encoder still gates
    /// on `prime <= 1000`). See `picus::solve` for the soundness implications.
    pub fn set_add_field_polys(&mut self, on: bool) -> &mut Self {
        self.add_field_polys = on;
        self
    }

    /// Build a `Poly` representing the linear polynomial `coeff * x` for
    /// variable index `var`. Used by callers that need to emit a learned
    /// constraint from a `(var, value)` pair.
    pub fn linear_term(&self, coeff: &BigUint, var: usize) -> Poly {
        let coeff_el = self.ring.field().from_biguint(coeff);
        self.ring.scale(coeff_el, self.ring.var(var))
    }

    /// Build a `Poly` representing the constant `c`.
    pub fn constant(&self, c: &BigUint) -> Poly {
        let el = self.ring.field().from_biguint(c);
        self.ring.constant(el)
    }

    /// Iterate every term of `poly` as `(coeff, monomial_vars)`, where
    /// `monomial_vars` is a flat `Vec<String>` listing each variable's
    /// canonical name once per degree (e.g. `x*x` ⇒ `["x", "x"]`,
    /// `x*y` ⇒ `["x", "y"]`). Constant terms yield an empty `Vec`.
    ///
    /// SMT-LIB emitters (cvc5 / z3 backends) use this form because they need
    /// variable names anyway. New backends that don't need names should
    /// prefer [`Self::poly_terms_idx`], which avoids O(degree) String clones
    /// per monomial.
    pub fn poly_terms<'a>(
        &'a self,
        poly: &'a Poly,
    ) -> impl Iterator<Item = (BigUint, Vec<String>)> + 'a {
        let names = self.ring.var_names();
        self.poly_terms_idx(poly).map(move |(coeff, vars)| {
            let mut atoms = Vec::new();
            for (v, e) in vars {
                for _ in 0..e {
                    atoms.push(names[v].clone());
                }
            }
            (coeff, atoms)
        })
    }

    /// Iterate every term of `poly` as `(coeff, vars_with_exp)` where
    /// `vars_with_exp` lists the variables that actually appear in this
    /// monomial together with their exponents. The list is sparse: a
    /// constant term yields an empty `Vec`; `x * x` yields `[(x_idx, 2)]`;
    /// `x * y` yields `[(x_idx, 1), (y_idx, 1)]`.
    ///
    /// Preferred over [`Self::poly_terms`] for new backends and
    /// pattern-matching code: no String allocation, no `0..n_vars` scan.
    pub fn poly_terms_idx<'a>(
        &'a self,
        poly: &'a Poly,
    ) -> impl Iterator<Item = (BigUint, Vec<(usize, u16)>)> + 'a {
        // Representation-native: the sparse arm yields nonzero `(var, exp)`
        // pairs in O(nnz) without ever materialising a full-length exponent
        // vector; the dense arm scans `n_vars` per term as before.
        poly.collect_terms_idx(self.ring.ctx()).into_iter()
    }
}

#[cfg(test)]
#[path = "poly_ir_tests.rs"]
mod tests;
