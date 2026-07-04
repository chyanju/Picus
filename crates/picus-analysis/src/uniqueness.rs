//! Uniqueness (determinism) query — the analysis-layer overlay on top of a
//! plain [`PolyIR`] constraint system.
//!
//! [`PolyIR`] is a use-agnostic GF(p) polynomial constraint system: a ring, a
//! list of `(poly = 0)` equalities, disjunctions, disequalities, assignments,
//! bitsum chains, and a field-poly flag. It knows nothing about "wires",
//! "copies", or "uniqueness". Everything specific to Picus's under-constrained
//! analysis lives here instead.
//!
//! A [`UniquenessQuery`] wraps a `PolyIR` whose ring is laid out as two copies
//! of the circuit wires — for an R1CS with `n_wires` wires the ring carries
//! `2 * n_wires` variables, index `i` (`i < n_wires`) being the original copy
//! `x_i` and index `n_wires + i` the alt copy `y_i` — together with the wire
//! bookkeeping (inputs, known-unique wires, current target) that the DPVL loop
//! and the propagation lemmas read. Asking whether wire `s` is uniquely
//! determined is asking whether the constraints force `x_s = y_s`; the query
//! records this as a single disequality `(x_s, y_s)` on the underlying
//! `PolyIR`, which every solver backend decides generically.

use std::collections::HashSet;

use picus_r1cs::grammar::R1csFile;
use picus_smt::poly_ir::PolyIR;

// Re-export the lowering error during coexistence; Step C moves the lowering
// (and this error type) fully into this module once `PolyIR` is slimmed.
pub use picus_smt::poly_ir::LowerError;

/// A uniqueness query: a two-copy [`PolyIR`] plus the wire-level bookkeeping
/// that makes it a *uniqueness* question rather than a bare constraint system.
pub struct UniquenessQuery {
    /// The underlying use-agnostic constraint system (2 * `n_wires` variables).
    pub ir: PolyIR,
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
    /// the underlying `PolyIR`'s single disequality to point at the new
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
    /// `x_w - y_w = 0` to the underlying `PolyIR` so the next backend call
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

/// Lower a parsed R1CS file into a [`UniquenessQuery`]: build the two-copy
/// `PolyIR` and wrap it with the wire bookkeeping. The disequality is *not*
/// materialised here — the DPVL driver calls [`UniquenessQuery::set_target`]
/// before each solve.
///
/// During coexistence this delegates to the (still fat) `PolyIR` lowering and
/// copies the wire metadata out; Step C inlines the two-copy construction here
/// and slims `PolyIR` to the bare constraint system.
pub fn r1cs_to_uniqueness_query(
    r1cs: &R1csFile,
    known_signals: &HashSet<usize>,
    target_signal: usize,
) -> Result<UniquenessQuery, LowerError> {
    let ir = picus_smt::poly_ir::r1cs_to_poly_ir(r1cs, known_signals, target_signal)?;
    Ok(UniquenessQuery {
        n_wires: ir.n_wires,
        input_indices: ir.input_indices.clone(),
        known_signals: ir.known_signals.clone(),
        target_signal: ir.target_signal,
        ir,
    })
}

#[cfg(test)]
#[path = "uniqueness_tests.rs"]
mod tests;
