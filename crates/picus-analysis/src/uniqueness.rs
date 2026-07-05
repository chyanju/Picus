//! Uniqueness (determinism) query — the analysis-layer overlay on top of a
//! plain [`PolySystem`] constraint system, plus the two-copy lowering that
//! produces it. [`polysystem_to_uniqueness_query`] doubles an arbitrary
//! single-copy `PolySystem`; [`r1cs_to_uniqueness_query`] is the R1CS-specific
//! wrapper over it.
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
    /// Disequalities carried by the source circuit itself (already doubled into
    /// both copies), kept separate from the per-round target disequality that
    /// [`Self::set_target`] appends. Empty for an R1CS lowering (R1CS is pure
    /// equalities); non-empty only when the source `PolySystem` had its own
    /// disequality constraints.
    pub base_disequalities: Vec<(usize, usize)>,
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
        // Rebuild as the source circuit's own disequalities (if any) plus the
        // single target disequality. For an R1CS lowering `base_disequalities`
        // is empty, so this reduces to `vec![(x_target, y_target)]`.
        self.ir.disequalities = self.base_disequalities.clone();
        self.ir
            .disequalities
            .push((self.orig_var(wire), self.alt_var(wire)));
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

/// Rebuild `poly` — a polynomial over the single-copy `src` ring — into `dst`
/// (the doubled `2 * n_wires`-variable ring) under the variable remap `f`,
/// which sends each single-copy variable index to its index in `dst`.
///
/// Works purely from the sparse `(coeff, [(var, exp)])` term view, so it is
/// representation-agnostic and needs no per-variable substitution support from
/// the ring itself.
fn remap_poly(
    src: &PolySystem,
    poly: &Poly,
    dst: &Arc<FfPolyRing>,
    f: impl Fn(usize) -> usize,
) -> Poly {
    let n_dst = dst.n_vars();
    let terms = src.poly_terms_idx(poly).map(|(coeff, vars)| {
        let mut exps = vec![0usize; n_dst];
        for (v, e) in vars {
            exps[f(v)] += e as usize;
        }
        let mono = dst.ring.create_monomial(exps);
        (dst.field().from_biguint(&coeff), mono)
    });
    dst.ring.from_terms(terms)
}

/// Build a [`UniquenessQuery`] from an arbitrary single-copy [`PolySystem`] by
/// duplicating it into two independent copies of the circuit — the original
/// over `x_*` and the alt over `y_*` — sharing the `inputs` wires across both.
///
/// This is the ring-agnostic core of the two-copy uniqueness lowering:
/// [`r1cs_to_uniqueness_query`] is a thin R1CS-specific wrapper over it, and
/// callers holding a `PolySystem` (e.g. from `picus::ir::PolyIR::lower`) reach
/// the DPVL uniqueness analysis through here directly.
///
/// `single` carries `n` variables `v_0..v_{n-1}`; the result carries `2n`
/// variables `x_0..x_{n-1}, y_0..y_{n-1}`. Every constraint (equality,
/// disjunction, assignment, bitsum, disequality) is emitted in BOTH copies —
/// input wires reuse `x_i` in the alt copy so their value is shared — which is
/// exactly the copy-symmetry invariant the wire-keyed propagation lemmas rely
/// on. Unlike R1CS this injects no one-wire pin: a bare `PolySystem` has no
/// reserved constant wire, so pin one via an `assignments` entry if needed.
///
/// `inputs` are the shared wires; `known` names wires already believed unique
/// (the DPVL driver materialises their `x_w - y_w = 0` on entry). Every index
/// in `inputs` and `known` must be `< n`, else [`LowerError::WireOutOfBounds`].
pub fn polysystem_to_uniqueness_query(
    single: &PolySystem,
    inputs: &HashSet<usize>,
    known: &HashSet<usize>,
) -> Result<UniquenessQuery, LowerError> {
    let n_wires = single.ring.n_vars();
    for &w in inputs.iter().chain(known.iter()) {
        if w >= n_wires {
            return Err(LowerError::WireOutOfBounds {
                wire: w,
                n_wires,
                ctx: "input/known wire",
            });
        }
    }

    // Doubled ring: x_0..x_{n-1}, y_0..y_{n-1}, same field as the source.
    let mut var_names = Vec::with_capacity(2 * n_wires);
    for i in 0..n_wires {
        var_names.push(format!("x{}", i));
    }
    for i in 0..n_wires {
        var_names.push(format!("y{}", i));
    }
    let ring = Arc::new(FfPolyRing::new(single.ring.field().clone(), var_names));

    // Copy remaps. The original copy is identity; the alt copy shifts every
    // non-input wire by `n_wires` (input wires stay shared). Both closures are
    // `Copy` (they capture only `&inputs` and `n_wires`), so they can be reused
    // across the equality / disjunction / assignment / bitsum passes.
    let orig = |v: usize| v;
    let alt = |v: usize| if inputs.contains(&v) { v } else { n_wires + v };

    // Equalities: all original-copy constraints first, then all alt-copy.
    let mut equalities = Vec::with_capacity(2 * single.equalities.len());
    for eq in &single.equalities {
        equalities.push(remap_poly(single, eq, &ring, orig));
    }
    for eq in &single.equalities {
        equalities.push(remap_poly(single, eq, &ring, alt));
    }

    let mut disjunctions = Vec::with_capacity(2 * single.disjunctions.len());
    for clause in &single.disjunctions {
        disjunctions.push(clause.iter().map(|p| remap_poly(single, p, &ring, orig)).collect());
    }
    for clause in &single.disjunctions {
        disjunctions.push(clause.iter().map(|p| remap_poly(single, p, &ring, alt)).collect());
    }

    let mut assignments = Vec::with_capacity(2 * single.assignments.len());
    for (idx, val) in &single.assignments {
        assignments.push((orig(*idx), val.clone()));
    }
    for (idx, val) in &single.assignments {
        assignments.push((alt(*idx), val.clone()));
    }

    let mut bitsums = Vec::with_capacity(2 * single.bitsums.len());
    for bits in &single.bitsums {
        bitsums.push(bits.iter().map(|&b| orig(b)).collect());
    }
    for bits in &single.bitsums {
        bitsums.push(bits.iter().map(|&b| alt(b)).collect());
    }

    // Source disequalities become `base_disequalities` (doubled). The per-round
    // target disequality is added later by `set_target`, which preserves these.
    let mut base_disequalities = Vec::with_capacity(2 * single.disequalities.len());
    for &(a, b) in &single.disequalities {
        base_disequalities.push((orig(a), orig(b)));
    }
    for &(a, b) in &single.disequalities {
        base_disequalities.push((alt(a), alt(b)));
    }

    let ir = PolySystem {
        ring,
        equalities,
        disjunctions,
        // Target-only; `set_target` rebuilds this from `base_disequalities`.
        disequalities: Vec::new(),
        assignments,
        bitsums,
        add_field_polys: single.add_field_polys,
    };

    Ok(UniquenessQuery {
        ir,
        n_wires,
        input_indices: inputs.clone(),
        known_signals: known.clone(),
        base_disequalities,
        target_signal: 0,
    })
}

/// Lower a parsed R1CS file into a [`UniquenessQuery`]: each `A * B = C`
/// constraint becomes one polynomial
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

    // Build the SINGLE-copy constraint system first: one variable per wire
    // (`x_0..x_{n-1}`), each R1CS `A * B = C` lowered to one polynomial
    // `expand(A) * expand(B) - expand(C) = 0`. Wire 0 (the R1CS one-wire) folds
    // into constants here, so no polynomial references it. The two-copy
    // expansion — and the copy-symmetry invariant the wire-keyed lemmas depend
    // on — is then applied uniformly by `polysystem_to_uniqueness_query`.
    let mut single_names = Vec::with_capacity(n_wires);
    for i in 0..n_wires {
        single_names.push(format!("x{}", i));
    }
    let field = PrimeField::new(prime.clone());
    let single_ring = Arc::new(FfPolyRing::new(field, single_names));

    let mut single = PolySystem::new(Arc::clone(&single_ring));
    for c in &r1cs.constraints.constraints {
        if let Some(eq) = constraint_to_poly_single(&single_ring, &c.a, &c.b, &c.c)? {
            single.equalities.push(eq);
        }
    }
    let small_prime_threshold = BigUint::from(1000u32);
    single.add_field_polys = prime <= &small_prime_threshold;

    // Double into two copies (input wires shared) via the generic lowering,
    // then re-attach the R1CS-specific policy the doubler stays agnostic to.
    let mut q = polysystem_to_uniqueness_query(&single, &input_indices, known_signals)?;

    // Wire 0 pinned to 1. `constraint_to_poly_single` already folds `c * x_0`
    // into a constant, so no polynomial references wire 0 — but the backend
    // still observes `x_0` as a ring variable and needs an equality to pin it.
    // Wire 0's value is shared, so a single `x_0 - 1 = 0` covers both copies.
    let one_el = q.ir.ring.field().one();
    let pin = q.ir.ring.sub(q.ir.ring.var(0), q.ir.ring.constant(one_el));
    q.ir.equalities.push(pin);

    q.target_signal = target_signal;
    Ok(q)
}

/// Lower one R1CS constraint `A * B = C` into a single-copy polynomial equality
/// `expand(A) * expand(B) - expand(C) = 0`. Returns `Ok(None)` when the result
/// is the zero polynomial, `Err` on an out-of-bounds wire id. The two-copy
/// expansion is applied afterwards by [`polysystem_to_uniqueness_query`].
fn constraint_to_poly_single(
    ring: &Arc<FfPolyRing>,
    a: &ConstraintBlock,
    b: &ConstraintBlock,
    c: &ConstraintBlock,
) -> Result<Option<Poly>, LowerError> {
    let sum_a = block_to_linear_single(ring, a, "A")?;
    let sum_b = block_to_linear_single(ring, b, "B")?;
    let sum_c = block_to_linear_single(ring, c, "C")?;
    let ab = ring.mul(sum_a, sum_b);
    let eq = ring.sub(ab, sum_c);
    if ring.is_zero(&eq) {
        Ok(None)
    } else {
        Ok(Some(eq))
    }
}

/// Build the single-copy linear polynomial `sum_i coeff_i * x_{wire_i}` for one
/// R1CS constraint block. Wire 0 (the R1CS one-wire) is `1` by definition, so
/// every `coeff * x_0` term folds straight into the constant.
fn block_to_linear_single(
    ring: &Arc<FfPolyRing>,
    block: &ConstraintBlock,
    ctx: &'static str,
) -> Result<Poly, LowerError> {
    let n_wires = ring.n_vars();
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
        let coeff_el = ring.field().from_biguint(factor);
        let term = if wid == 0 {
            // x_0 = 1 (R1CS one-wire); fold the coefficient into the constant.
            ring.constant(coeff_el)
        } else {
            ring.scale(coeff_el, ring.var(wid))
        };
        acc = ring.add(acc, term);
    }
    Ok(acc)
}

#[cfg(test)]
#[path = "uniqueness_tests.rs"]
mod tests;
