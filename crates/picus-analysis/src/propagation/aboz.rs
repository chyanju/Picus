//! All-But-One-Zero (ABOZ) propagation lemma.
//!
//! In R1CS shape the original pattern is two `A * B = 0` constraints
//! plus a linear "constant-and-mux-bits" sum that ties them together;
//! after polynomial lowering each `A * B = 0` is a single bilinear
//! monomial. The lemma looks for triples
//!     `x * y0 = 0`,  `x * y1 = 0`,  `x + y0 + y1 + c = 0`
//! where `x` and `c` are known. From `x * y_i = 0` and `x ≠ 0` we
//! conclude `y_i = 0`. The lemma only fires when `x`'s range proves
//! `x ≠ 0`; without that gate, two witnesses with `x = 0` can disagree
//! on `y_0` / `y_1` (the bilinear constraints become vacuous and the
//! linear sum admits a one-parameter family of solutions), so marking
//! them as uniquely determined would be unsound.

use std::collections::HashSet;

use num_traits::Zero;
use picus_core::poly::Poly;

use super::lemma::{LemmaDescriptor, PropagationCtx, PropagationLemma};
use crate::uniqueness::UniquenessQuery;

pub struct AbozLemma {
    /// Zero-product disjunctions already emitted this run, keyed by the
    /// `(selector_wire, other_wire)` pair, so re-running the lemma to a
    /// fixed point does not flood `learned_disjunctions` with dupes.
    emitted: HashSet<(usize, usize)>,
    /// Whether to emit the entailed zero-product disjunctions. Set from the
    /// analysis knob `DpvlConfig::aboz_emit_disjunctions` via [`Self::configure`];
    /// on by default.
    emit_disjunctions: bool,
}

impl Default for AbozLemma {
    fn default() -> Self {
        Self {
            emitted: HashSet::new(),
            emit_disjunctions: true,
        }
    }
}

impl PropagationLemma for AbozLemma {
    fn configure(&mut self, config: &crate::dpvl::DpvlConfig) {
        self.emit_disjunctions = config.aboz_emit_disjunctions;
    }

    fn run(&mut self, q: &UniquenessQuery, ctx: &mut PropagationCtx) -> bool {
        let products = collect_bilinear_zero(q);
        if products.len() < 2 {
            return false;
        }
        let linear_sums = collect_linear_sums(q);
        if linear_sums.is_empty() {
            return false;
        }

        let mut progress = false;
        for (i, (a0, b0)) in products.iter().enumerate() {
            for (a1, b1) in products.iter().skip(i + 1) {
                // Candidate quadruple (x, y0, y1, ...) — x is one wire
                // shared between the two products (typically the
                // selector), y0 / y1 are the other side of each.
                let shared = if a0 == a1 {
                    Some((*a0, *b0, *b1))
                } else if a0 == b1 {
                    Some((*a0, *b0, *a1))
                } else if b0 == a1 {
                    Some((*b0, *a0, *b1))
                } else if b0 == b1 {
                    Some((*b0, *a0, *a1))
                } else {
                    None
                };
                let Some((x, y0, y1)) = shared else {
                    continue;
                };
                if y0 == y1 {
                    continue;
                }

                // Find a linear sum that mentions {x, y0, y1, c} for
                // some additional known wire c (any wire other than
                // x/y0/y1 that's already in ks).
                for lin in &linear_sums {
                    if !lin.contains(&x) || !lin.contains(&y0) || !lin.contains(&y1) {
                        continue;
                    }
                    let has_known_partner = lin
                        .iter()
                        .any(|&w| w != x && w != y0 && w != y1 && ctx.known.contains(&w));
                    if !has_known_partner {
                        continue;
                    }
                    if !ctx.known.contains(&x) {
                        continue;
                    }
                    // Soundness gate: `x * y_i = 0` only forces
                    // `y_i = 0` when `x ≠ 0`. Without a range proving
                    // `x` cannot be zero, two witnesses with `x = 0`
                    // can disagree on `y_0` / `y_1` while satisfying
                    // every constraint.
                    let selector_nonzero = ctx
                        .ranges
                        .get(&x)
                        .map_or(false, |r| r.excludes_zero());
                    if !selector_nonzero {
                        // Selector not provably non-zero ⇒ `y0`/`y1` are
                        // not forced unique here. Optionally hand the
                        // disjunction-aware solver path the (entailed)
                        // zero-product clauses `x_s = 0 ∨ x_o = 0` so it
                        // can case-split. Sound — each follows from a
                        // `s * o = 0` equality already in the IR — and on
                        // by default.
                        if self.emit_disjunctions {
                            if self.emit_zero_product(q, ctx, x, y0) {
                                progress = true;
                            }
                            if self.emit_zero_product(q, ctx, x, y1) {
                                progress = true;
                            }
                        }
                        continue;
                    }
                    // Promote y0, y1 to known if they were unknown.
                    if ctx.mark_known(y0) {
                        progress = true;
                    }
                    if ctx.mark_known(y1) {
                        progress = true;
                    }
                }
            }
        }
        progress
    }
}

impl AbozLemma {
    /// Push the zero-product disjunction `(var_s = 0) ∨ (var_o = 0)` for
    /// both the original and alt copies, deduplicating on `(s, o)` so
    /// fixed-point re-runs don't flood `learned_disjunctions`. Each clause
    /// is entailed by the `s * o = 0` equality already in the IR for that
    /// copy, so adding it never changes the solution set. Returns whether a
    /// new clause was emitted.
    ///
    /// Copy-awareness: an input wire reuses `x_w` in both copies (see
    /// `polysystem_to_uniqueness_query`), so its alt-copy constraint is `x_s · y_o = 0`,
    /// not `y_s · y_o = 0`. Emitting `alt_var` (a fresh, unconstrained
    /// `y_s`) for an input would push a clause not entailed by any equality.
    /// `copy_var` therefore selects the variable that actually appears in
    /// the constraint: `orig_var` for inputs, `alt_var` otherwise — keeping
    /// soundness resting on entailment rather than on `y_s` happening to be
    /// free.
    fn emit_zero_product(
        &mut self,
        q: &UniquenessQuery,
        ctx: &mut PropagationCtx,
        s: usize,
        o: usize,
    ) -> bool {
        if !self.emitted.insert((s, o)) {
            return false;
        }
        let alt_copy_var = |w: usize| {
            if q.input_wires.contains(&w) {
                q.orig_var(w)
            } else {
                q.alt_var(w)
            }
        };
        ctx.learned_disjunctions
            .push(vec![q.ir.ring.var(q.orig_var(s)), q.ir.ring.var(q.orig_var(o))]);
        ctx.learned_disjunctions
            .push(vec![q.ir.ring.var(alt_copy_var(s)), q.ir.ring.var(alt_copy_var(o))]);
        true
    }
}

/// Wire indices `(a, b)` for every equality of the form `c * x_a * x_b
/// = 0`. Skips constraints that have any other terms beyond the
/// single bilinear monomial.
fn collect_bilinear_zero(q: &UniquenessQuery) -> Vec<(usize, usize)> {
    let mut out = Vec::new();
    for poly in &q.ir.equalities {
        if let Some((a, b)) = match_bilinear(q, poly) {
            out.push((a, b));
        }
    }
    out
}

fn match_bilinear(q: &UniquenessQuery, poly: &Poly) -> Option<(usize, usize)> {
    let mut bilinear: Option<(usize, usize)> = None;
    // Sparse-native: each term as nonzero (var, exp) pairs. After the
    // (e > 1) reject, the nonzero count IS the total degree, so a term is
    // the zero constant, or exactly the bilinear `x_a·x_b` monomial.
    for (coeff, vars) in q.ir.poly_terms_idx(poly) {
        if vars.iter().any(|&(_, e)| e > 1) {
            return None;
        }
        match vars.len() {
            0 => {
                if !coeff.is_zero() {
                    return None;
                }
            }
            2 => {
                if bilinear.is_some() {
                    return None;
                }
                let a = q.var_to_wire(vars[0].0);
                let b = q.var_to_wire(vars[1].0);
                bilinear = Some((a.min(b), a.max(b)));
            }
            _ => return None,
        }
    }
    bilinear
}

/// Wire-index sets for every equality whose terms are all linear
/// monomials (no quadratic terms). Constants are ignored.
fn collect_linear_sums(q: &UniquenessQuery) -> Vec<HashSet<usize>> {
    let mut out = Vec::new();
    // Accept a poly only if every term is a constant or a single linear
    // variable; the constant, if any, is ignored here.
    for poly in &q.ir.equalities {
        let Some((terms, _constant)) = super::shape::linear_form(q, poly) else {
            continue; // nonlinear / product term
        };
        let wires: HashSet<usize> = terms.iter().map(|(v, _)| q.var_to_wire(*v)).collect();
        if !wires.is_empty() {
            out.push(wires);
        }
    }
    out
}

inventory::submit! {
    LemmaDescriptor {
        name: "aboz",
        factory: || Box::new(AbozLemma::default()),
    }
}

#[cfg(test)]
#[path = "aboz_tests.rs"]
mod tests;
