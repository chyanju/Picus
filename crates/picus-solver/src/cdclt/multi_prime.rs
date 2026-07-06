//! Multi-prime FF theory router.
//!
//! Wraps one [`AtomTable`] per distinct GF(p) and routes
//! [`Theory::notify_fact`] / [`Theory::post_check`] to the matching
//! per-prime [`check_full_with_atoms`] slot. Mirrors cvc5's
//! `unordered_map<TypeNode, SubTheory>` layout in `theory_ff.cpp`.
//!
//! Additive to [`super::ff_theory::FfTheory`]: the single-prime path is
//! unchanged. Use the router when the input mixes primes that must be
//! solved independently and joined.

use std::collections::HashMap;

use num_bigint::BigUint;

use crate::sat::Var;
use crate::timeout::CancelToken;

use super::atoms::AtomTable;
use super::ff_theory::check_full_with_atoms;
use super::theory::{CheckOutcome, Theory};

/// Per-prime slot in the router. Owns the prime's atom table and trail.
pub(crate) struct PrimeSlot {
    pub atoms: AtomTable,
    facts: Vec<(Var, bool)>,
    levels: Vec<usize>,
}

/// Multi-prime FF theory router. One [`PrimeSlot`] per distinct GF(p).
pub(crate) struct FfTheoryRouter<'a> {
    slots: Vec<PrimeSlot>,
    #[allow(dead_code)] // parked with the multi-prime pipeline
    prime_to_idx: HashMap<BigUint, usize>,
    /// Atom variable → slot index (the prime its atom belongs to).
    /// Populated by the caller via [`FfTheoryRouter::assign_var`].
    var_to_slot: HashMap<Var, usize>,
    cancel: &'a CancelToken,
    /// Sticky flag set whenever [`Theory::notify_fact`] arrives with a
    /// variable not [`assign_var`]'d to any slot. While set,
    /// [`post_check`] returns [`CheckOutcome::Unknown`] unconditionally:
    /// the per-slot trails no longer reflect the full asserted set, so
    /// no verdict from their union is safe. Snapshotted via
    /// `degraded_levels` for symmetric `pop` rollback.
    degraded: bool,
    /// Per-push snapshot of `degraded`, parallel to every slot's
    /// `levels` stack. Length must equal each slot's `levels.len()`
    /// after every matched [`push`] / [`pop`] pair (debug-asserted).
    degraded_levels: Vec<bool>,
}

impl<'a> FfTheoryRouter<'a> {
    /// Construct a router from a list of per-prime atom tables. Each
    /// table must use a distinct prime; later duplicates overwrite the
    /// `prime → idx` mapping but the slot itself stays separate.
    pub(crate) fn new(atoms_by_prime: Vec<AtomTable>, cancel: &'a CancelToken) -> Self {
        let mut prime_to_idx = HashMap::new();
        let mut slots = Vec::with_capacity(atoms_by_prime.len());
        for (i, at) in atoms_by_prime.into_iter().enumerate() {
            prime_to_idx.insert(at.prime().clone(), i);
            slots.push(PrimeSlot {
                atoms: at,
                facts: Vec::new(),
                levels: Vec::new(),
            });
        }
        FfTheoryRouter {
            slots,
            prime_to_idx,
            var_to_slot: HashMap::new(),
            cancel,
            degraded: false,
            degraded_levels: Vec::new(),
        }
    }

    #[cfg(test)]
    pub(crate) fn n_primes(&self) -> usize {
        self.slots.len()
    }

    /// Return the slot index for a given prime, or `None` if not registered.
    #[cfg(test)]
    pub(crate) fn slot_idx_for(&self, prime: &BigUint) -> Option<usize> {
        self.prime_to_idx.get(prime).copied()
    }

    /// Mutable borrow of a slot's atom table for atom interning by the caller.
    pub(crate) fn slot_atoms_mut(&mut self, slot_idx: usize) -> &mut AtomTable {
        &mut self.slots[slot_idx].atoms
    }

    /// Register that the SAT variable `var` belongs to the prime at
    /// `slot_idx`. A [`Theory::notify_fact`] for a `var` without prior
    /// registration trips the `degraded` flag (a per-slot mis-routing
    /// would silently change the verdict union).
    pub(crate) fn assign_var(&mut self, var: Var, slot_idx: usize) {
        self.var_to_slot.insert(var, slot_idx);
    }
}

impl<'a> Theory for FfTheoryRouter<'a> {
    fn notify_fact(&mut self, atom: Var, polarity: bool) {
        match self.var_to_slot.get(&atom) {
            Some(&idx) => {
                if self.slots[idx].atoms.is_auxiliary(atom) {
                    return;
                }
                self.slots[idx].facts.push((atom, polarity));
            }
            None => {
                // Tseitin auxiliaries have no source prime and are not
                // theory facts; drop them silently regardless of which
                // slot's atom table they happen to fall under. Any
                // unassigned non-aux atom trips the degraded
                // flag — the per-slot trail no longer reflects the full
                // asserted set so post_check returns Unknown.
                for slot in &self.slots {
                    if slot.atoms.is_auxiliary(atom) {
                        return;
                    }
                }
                self.degraded = true;
            }
        }
    }

    /// Run each slot's FF check independently and combine: any UNSAT
    /// short-circuits to UNSAT (with concatenated core from every UNSAT
    /// slot); else if any UNKNOWN → UNKNOWN; else SAT. The combined core
    /// concatenates per-prime cores so the orchestrator learns the union.
    fn post_check(&mut self) -> CheckOutcome {
        if self.degraded {
            return CheckOutcome::Unknown;
        }
        let mut combined_core: Vec<Var> = Vec::new();
        let mut any_unknown = false;
        let mut slot_models: Vec<HashMap<String, BigUint>> = Vec::new();
        for slot in &mut self.slots {
            match check_full_with_atoms(&slot.atoms, &slot.facts, self.cancel) {
                CheckOutcome::Sat(model) => slot_models.push(model),
                CheckOutcome::Unsat { core } => {
                    combined_core.extend(core);
                }
                CheckOutcome::Unknown => {
                    any_unknown = true;
                }
            }
        }
        if !combined_core.is_empty() {
            CheckOutcome::Unsat {
                core: combined_core,
            }
        } else if any_unknown {
            CheckOutcome::Unknown
        } else {
            // Every slot was Sat in this check. Per-prime variable sets
            // are expected to be disjoint (an equality between fields of
            // different sizes is ill-typed SMT-LIB, and the parser
            // rejects cross-prime asserts) — but nothing upstream
            // *enforces* name disjointness across slots, and a silent
            // last-writer-wins union would return a witness violating
            // the overwritten slot's constraints. Guard: a colliding
            // name with a conflicting value degrades to Unknown.
            let mut combined: HashMap<String, BigUint> = HashMap::new();
            for m in slot_models {
                for (name, value) in m {
                    match combined.get(&name) {
                        Some(prev) if *prev != value => {
                            log::warn!(
                                "multi-prime model join: variable {} bound in \
                                 two slots with different values; degrading \
                                 to Unknown",
                                name
                            );
                            return CheckOutcome::Unknown;
                        }
                        _ => {
                            combined.insert(name, value);
                        }
                    }
                }
            }
            CheckOutcome::Sat(combined)
        }
    }

    fn push(&mut self) {
        for slot in &mut self.slots {
            slot.levels.push(slot.facts.len());
        }
        self.degraded_levels.push(self.degraded);
        if let Some(slot) = self.slots.first() {
            debug_assert_eq!(
                self.degraded_levels.len(),
                slot.levels.len(),
                "degraded_levels must stay in lockstep with per-slot levels stacks"
            );
        }
    }

    fn pop(&mut self) {
        for slot in &mut self.slots {
            if let Some(h) = slot.levels.pop() {
                slot.facts.truncate(h);
            }
        }
        if let Some(prev) = self.degraded_levels.pop() {
            self.degraded = prev;
        }
        if let Some(slot) = self.slots.first() {
            debug_assert_eq!(
                self.degraded_levels.len(),
                slot.levels.len(),
                "degraded_levels must stay in lockstep with per-slot levels stacks"
            );
        }
    }

}

#[cfg(test)]
#[path = "multi_prime_tests.rs"]
mod tests;
