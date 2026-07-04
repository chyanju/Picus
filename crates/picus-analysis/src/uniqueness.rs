//! Uniqueness (determinism) query — the analysis-layer overlay on top of a
//! plain [`PolySystem`] constraint system, plus the R1CS two-copy lowering that
//! produces it.
//!
//! [`PolySystem`] is a use-agnostic GF(p) polynomial constraint system: a ring, a
//! list of `(poly = 0)` equalities, disjunctions, disequalities, assignments,
//! bitsum chains, and a field-poly flag. It knows nothing about "wires",
//! "copies", or "uniqueness". Everything specific to Picus's under-constrained
//! analysis lives here instead.
//!
//! A [`UniquenessQuery`] wraps a `PolySystem` whose ring is laid out as two copies
//! of the circuit wires — for an R1CS with `n_wires` wires the ring carries
//! `2 * n_wires` variables, index `i` (`i < n_wires`) being the original copy
//! `x_i` and index `n_wires + i` the alt copy `y_i` — together with the wire
//! bookkeeping (inputs, known-unique wires, current target) that the DPVL loop
//! and the propagation lemmas read. Asking whether wire `s` is uniquely
//! determined is asking whether the constraints force `x_s = y_s`; the query
//! records this as a single disequality `(x_s, y_s)` on the underlying
//! `PolySystem`, which every solver backend decides generically.

use std::collections::HashSet;
use std::sync::Arc;

use num_bigint::BigUint;
use thiserror::Error;

use picus_r1cs::field_reduce;
use picus_r1cs::grammar::{ConstraintBlock, R1csFile};
use picus_core::ff::field::PrimeField;
use picus_core::poly::{FfPolyRing, Poly};
use picus_smt::poly_system::PolySystem;

/// Reasons the R1CS-to-`UniquenessQuery` lowering can fail. Surfacing these as
/// errors (rather than logging a warning and silently skipping the offending
/// constraint block) guarantees the caller sees a well-formed query or a
/// definite failure — never an under-constrained query whose verdict would be
/// untrustworthy.
#[derive(Debug, Error)]
pub enum LowerError {
    #[error("wire id {wire} out of bounds (n_wires = {n_wires}) in {ctx}")]
    WireOutOfBounds {
        wire: usize,
        n_wires: usize,
        ctx: &'static str,
    },
}

/// A uniqueness query: a two-copy [`PolySystem`] plus the wire-level bookkeeping
/// that makes it a *uniqueness* question rather than a bare constraint system.
pub struct UniquenessQuery {
    /// The underlying use-agnostic constraint system (2 * `n_wires` variables).
    pub ir: PolySystem,
    /// Number of circuit wires; the ring holds `2 * n_wires` variables.
    pub n_wires: usize,
    /// Wires that are circuit inputs (shared across both copies).
    pub input_indices: HashSet<usize>,
    /// Wires currently believed uniquely determined by the inputs. The DPVL
    /// loop seeds this with `input_indices`.
    pub known_signals: HashSet<usize>,
    /// Wire whose uniqueness is being tested this round; a SAT verdict means a
    /// witness pair exists with `x_target != y_target`.
    pub target_signal: usize,
}

impl UniquenessQuery {
    /// Index of the `x_i` (original-copy) variable in the underlying ring.
    pub fn orig_var(&self, wire: usize) -> usize {
        debug_assert!(wire < self.n_wires);
        wire
    }

    /// Index of the `y_i` (alt-copy) variable in the underlying ring.
    pub fn alt_var(&self, wire: usize) -> usize {
        debug_assert!(wire < self.n_wires);
        self.n_wires + wire
    }

    /// Map a ring variable index back to its underlying wire index. `x_i`
    /// (index `i`) and `y_i` (index `n_wires + i`) both map to wire `i`, so
    /// lemmas pattern-matching on polynomial structure normally don't care
    /// which copy a variable belongs to.
    pub fn var_to_wire(&self, var: usize) -> usize {
        if var < self.n_wires {
            var
        } else {
            var - self.n_wires
        }
    }

    /// Canonical name for the original-copy variable of `wire` (e.g. `x5`).
    pub fn x_name(&self, wire: usize) -> &str {
        &self.ir.ring.var_names()[wire]
    }

    /// Canonical name for the alt-copy variable of `wire` (e.g. `y5`).
    pub fn y_name(&self, wire: usize) -> &str {
        &self.ir.ring.var_names()[self.n_wires + wire]
    }

    /// Set the current uniqueness target: updates `target_signal` and rebuilds
    /// the underlying `PolySystem`'s single disequality to point at the new
    /// target's `(x, y)` pair. The constraint set is otherwise unaffected.
    ///
    /// An input wire shares one value across both copies (its `y_w` is never
    /// emitted as a distinct variable), so targeting one would build a
    /// disequality over a free `y_w` — trivially SAT, i.e. a spurious
    /// "two-witness" counter-example. The DPVL driver never targets an input
    /// (inputs are seeded into `known`), but the assert guards direct callers.
    pub fn set_target(&mut self, wire: usize) {
        debug_assert!(wire < self.n_wires);
        assert!(
            !self.input_indices.contains(&wire),
            "uniqueness target must not be an input wire (its copies are shared)"
        );
        self.target_signal = wire;
        self.ir.disequalities = vec![(self.orig_var(wire), self.alt_var(wire))];
    }

    /// Record that `wire` has been proved uniquely determined. Appends
    /// `x_w - y_w = 0` to the underlying `PolySystem` so the next backend call
    /// sees it as a regular constraint. Input wires reuse `x_i` across both
    /// copies at lowering, so only non-input wires need a fresh equality.
    pub fn add_known_wire(&mut self, wire: usize) {
        if self.known_signals.insert(wire) && !self.input_indices.contains(&wire) {
            let x = self.ir.ring.var(self.orig_var(wire));
            let y = self.ir.ring.var(self.alt_var(wire));
            let diff = self.ir.ring.sub(x, y);
            self.ir.equalities.push(diff);
        }
    }
}

/// Lower a parsed R1CS file into a [`UniquenessQuery`] in a single pass over
/// the constraint blocks: each `A * B = C` constraint becomes one polynomial
/// equality `(sum_a)(sum_b) - sum_c = 0`, emitted in BOTH copies (`x_i`, `y_i`)
/// side-by-side. Input wires reuse `x_i` in both copies (no `x_i = y_i`
/// equality); wire 0 is pinned to `1` in both copies; the target-signal
/// disequality is *not* materialised here — the DPVL driver calls
/// [`UniquenessQuery::set_target`] before each solve.
///
/// The prime comes from `r1cs.header.prime_number` (no hard-coded curve). An
/// out-of-bounds wire id in any constraint block surfaces as
/// [`LowerError::WireOutOfBounds`] rather than a silent skip.
pub fn r1cs_to_uniqueness_query(
    r1cs: &R1csFile,
    known_signals: &HashSet<usize>,
    target_signal: usize,
) -> Result<UniquenessQuery, LowerError> {
    let n_wires = r1cs.n_wires() as usize;
    // The target indexes both copies; an out-of-range value would build a
    // disequality over a non-existent ring variable. Reject explicitly.
    if target_signal >= n_wires {
        return Err(LowerError::WireOutOfBounds {
            wire: target_signal,
            n_wires,
            ctx: "target signal",
        });
    }
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

    // Copy-symmetry invariant (load-bearing for wire-keyed propagation):
    // every R1CS constraint is lowered into BOTH copies below — the original
    // over `x_*` and the alt over `y_*` (input wires share `x_*` in both; see
    // `block_to_linear`). The wire-keyed propagation lemmas (linear, binary01,
    // bim, basis2) match a structural pattern in one copy and promote a *wire*
    // — both copies at once — to "known"; their soundness relies on the matched
    // structure having an identical mirror in the other copy. Emitting a
    // constraint for only one copy, or asymmetrically, breaks that assumption
    // and can make those lemmas unsound.

    // Original-copy constraints.
    for c in &r1cs.constraints.constraints {
        if let Some(eq) = constraint_to_poly(&ring, &c.a, &c.b, &c.c, &input_indices, /*is_alt=*/ false, prime)? {
            equalities.push(eq);
        }
    }
    // Alt-copy constraints.
    for c in &r1cs.constraints.constraints {
        if let Some(eq) = constraint_to_poly(&ring, &c.a, &c.b, &c.c, &input_indices, /*is_alt=*/ true, prime)? {
            equalities.push(eq);
        }
    }

    // Wire 0 pinned to 1. `block_to_linear` already folds `c * x_0` straight
    // into a constant, so the polynomials never reference wire 0 — but backends
    // still observe `x_0` as a ring variable and need an equality to pin it.
    let one_el = ring.field().one();
    equalities.push(ring.sub(ring.var(0), ring.constant(one_el)));

    let small_prime_threshold = BigUint::from(1000u32);
    let add_field_polys = prime <= &small_prime_threshold;

    let ir = PolySystem {
        ring,
        equalities,
        disjunctions: Vec::new(),
        disequalities: Vec::new(),
        assignments: Vec::new(),
        bitsums: Vec::new(),
        add_field_polys,
    };

    Ok(UniquenessQuery {
        ir,
        n_wires,
        input_indices,
        known_signals: known_signals.clone(),
        target_signal,
    })
}

/// Lower one R1CS constraint `A * B = C` into a polynomial equality
/// `expand(A) * expand(B) - expand(C) = 0` in the given copy. Returns
/// `Ok(None)` when the resulting polynomial is the zero polynomial, `Err`
/// when any block references an out-of-bounds wire id.
fn constraint_to_poly(
    ring: &Arc<FfPolyRing>,
    a: &ConstraintBlock,
    b: &ConstraintBlock,
    c: &ConstraintBlock,
    input_indices: &HashSet<usize>,
    is_alt: bool,
    prime: &BigUint,
) -> Result<Option<Poly>, LowerError> {
    let sum_a = block_to_linear(ring, a, input_indices, is_alt, prime, "A")?;
    let sum_b = block_to_linear(ring, b, input_indices, is_alt, prime, "B")?;
    let sum_c = block_to_linear(ring, c, input_indices, is_alt, prime, "C")?;
    let ab = ring.mul(sum_a, sum_b);
    let eq = ring.sub(ab, sum_c);
    if ring.is_zero(&eq) {
        Ok(None)
    } else {
        Ok(Some(eq))
    }
}

/// Build the linear polynomial `sum_i coeff_i * var_i` for one R1CS constraint
/// block. Inputs use the original `x_i` index in both copies (they share the
/// same value); non-inputs use `x_i` in the orig copy and `y_i` in the alt
/// copy. Wire 0 (the R1CS one-wire) is `1` by definition, so every
/// `coeff * x_0` term folds straight into the constant.
fn block_to_linear(
    ring: &Arc<FfPolyRing>,
    block: &ConstraintBlock,
    input_indices: &HashSet<usize>,
    is_alt: bool,
    prime: &BigUint,
    ctx: &'static str,
) -> Result<Poly, LowerError> {
    let n_wires = ring.n_vars() / 2;
    let mut acc = ring.zero();
    for (&wire_id, factor) in block.wire_ids.iter().zip(block.factors.iter()) {
        let wid = wire_id as usize;
        if wid >= n_wires {
            return Err(LowerError::WireOutOfBounds {
                wire: wid,
                n_wires,
                ctx,
            });
        }
        let coeff = field_reduce(factor, prime);
        let coeff_el = ring.field().from_biguint(&coeff);
        let term = if wid == 0 {
            // x_0 = y_0 = 1 (R1CS one-wire); fold the coefficient directly
            // into the constant term.
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
    Ok(acc)
}

#[cfg(test)]
#[path = "uniqueness_tests.rs"]
mod tests;
