//! `UfCombinedTheory<T>` — the UF equality hub wrapped OUTERMOST
//! around the FF theory pipeline (optionally around
//! `EeFilteredTheory<T>`): forwards every fact to the inner theory
//! first (FF completeness never depends on the hub), mirrors
//! equality-shaped atoms into the congruence-closure e-graph, and
//! certifies every Sat exit against the applications.
//!
//! The UF-outermost ordering is required: the equality engine's
//! Redundant-drop filter must not starve the hub of facts; hub
//! re-assertions are idempotent, so seeing every notify costs nothing.

use std::cell::Cell;
use std::collections::HashMap;
use std::rc::Rc;

use num_bigint::BigUint;
use num_traits::Zero;

use crate::frontend::encoder::UfApp;
use crate::frontend::uf::{verify_uf_congruence, UfViolation};
use crate::metric;
use crate::sat::Var;

use super::egraph::{EGraph, TermId, TermNode};
use super::theory::{CheckOutcome, Theory};

/// Post-solve cause refinement, shared between the theory (which can
/// only return `CheckOutcome::Unknown`) and the orchestrator entry
/// (which rewrites the surfaced `UnknownCause`).
#[derive(Default)]
pub(crate) struct UfOutcomeFlags {
    /// A degraded care prefix (`uf_pair_cap`) produced a candidate the
    /// certification rejected — the expected budget outcome
    /// (`Unknown(UfCap)`), not a defect.
    pub degraded_by_cap: Cell<bool>,
    /// Model completion was infeasible (tiny-p fresh-value exhaustion
    /// whose 0-fill fallback failed certification) —
    /// `Unknown(UfIncomplete)`.
    pub infeasible: Cell<bool>,
}

/// Everything the hub needs beyond the inner theory. Built by the
/// orchestrator's lazy-pipeline setup.
pub(crate) struct UfSetup {
    pub eg: EGraph,
    /// Equality-shaped atoms the hub mirrors: atom var -> the two
    /// e-graph nodes it equates.
    pub atom_view: HashMap<Var, (TermId, TermId)>,
    /// The applications (frame-level), for table certification.
    pub apps: Vec<UfApp>,
    pub symbols: Vec<String>,
    /// The solve's variable frame (owned; names for model completion).
    pub var_names: Vec<String>,
    pub prime: BigUint,
    /// False when `uf_pair_cap` truncated care-atom interning.
    pub care_complete: bool,
    pub flags: Rc<UfOutcomeFlags>,
}

pub(crate) struct UfCombinedTheory<T: Theory> {
    inner: T,
    eg: EGraph,
    atom_view: HashMap<Var, (TermId, TermId)>,
    apps: Vec<UfApp>,
    symbols: Vec<String>,
    var_names: Vec<String>,
    prime: BigUint,
    care_complete: bool,
    flags: Rc<UfOutcomeFlags>,
    /// Explanations for hub-produced propagations, keyed by
    /// `(atom, polarity)`; `explain` routes here first (ownership),
    /// then to the inner theory.
    prop_explanations: HashMap<(Var, bool), Vec<(Var, bool)>>,
}

impl<T: Theory> UfCombinedTheory<T> {
    pub(crate) fn new(inner: T, setup: UfSetup) -> Self {
        UfCombinedTheory {
            inner,
            eg: setup.eg,
            atom_view: setup.atom_view,
            apps: setup.apps,
            symbols: setup.symbols,
            var_names: setup.var_names,
            prime: setup.prime,
            care_complete: setup.care_complete,
            flags: setup.flags,
            prop_explanations: HashMap::new(),
        }
    }

    /// Complete the atom-var-only FF model over the e-graph classes,
    /// then certify congruence. The ONLY Sat exit of the lazy pipeline
    /// (inner early-check Sats are downgraded in `early_check`, so
    /// nothing bypasses this).
    ///
    /// Completion: a class with a valued member (model value or a
    /// constant node) donates its value to every variable member; two
    /// valued members disagreeing is a defect only under complete
    /// care — under a degraded prefix the e-graph legitimately merged
    /// uncovered pairs, so it is the expected `UfCap` outcome. Pure-UF
    /// classes receive pairwise-distinct fresh values (injective
    /// completion — collision-free by construction while distinct
    /// values remain; the tiny-p fallback 0-fills and lets the table
    /// check certify).
    fn finalize_uf_sat(&mut self, mut model: HashMap<String, BigUint>) -> CheckOutcome {
        let mut pure_classes: Vec<Vec<String>> = Vec::new();
        for (_root, members) in self.eg.classes() {
            let mut names: Vec<String> = Vec::new();
            let mut value: Option<BigUint> = None;
            let mut disagreement = false;
            for &m in &members {
                match self.eg.node(m) {
                    TermNode::Var(frame_idx) => {
                        let name = match self.var_names.get(*frame_idx as usize) {
                            Some(n) => n.clone(),
                            None => continue,
                        };
                        if let Some(v) = model.get(&name) {
                            match &value {
                                Some(prev) if prev != v => disagreement = true,
                                _ => value = Some(v.clone()),
                            }
                        }
                        names.push(name);
                    }
                    TermNode::Const(c) => match &value {
                        Some(prev) if prev != c => disagreement = true,
                        _ => value = Some(c.clone()),
                    },
                    TermNode::App { .. } => {}
                }
            }
            if disagreement {
                return self.classify_failure("class members disagree on a value");
            }
            match value {
                Some(v) => {
                    for name in names {
                        model.entry(name).or_insert_with(|| v.clone());
                    }
                }
                None => {
                    if !names.is_empty() {
                        pure_classes.push(names);
                    }
                }
            }
        }

        // Injective fresh-value completion for pure-UF classes.
        if !pure_classes.is_empty() {
            let mut used: std::collections::HashSet<BigUint> =
                model.values().cloned().collect();
            let mut candidate = BigUint::zero();
            let mut exhausted = false;
            for class in &pure_classes {
                while used.contains(&candidate) {
                    candidate += 1u32;
                    if candidate >= self.prime {
                        exhausted = true;
                        break;
                    }
                }
                if exhausted || candidate >= self.prime {
                    exhausted = true;
                    break;
                }
                used.insert(candidate.clone());
                for name in class {
                    model.entry(name.clone()).or_insert_with(|| candidate.clone());
                }
            }
            if exhausted {
                // Tiny-p fallback: 0-fill whatever is left and let the
                // table check certify (or reject as infeasible).
                for class in &pure_classes {
                    for name in class {
                        model.entry(name.clone()).or_insert_with(BigUint::zero);
                    }
                }
                match verify_uf_congruence(&self.apps, &self.symbols, &self.var_names, &model)
                {
                    Ok(_) => return CheckOutcome::Sat(model),
                    Err(_) => {
                        self.flags.infeasible.set(true);
                        return CheckOutcome::Unknown;
                    }
                }
            }
        }

        match verify_uf_congruence(&self.apps, &self.symbols, &self.var_names, &model) {
            Ok(table) => {
                log::debug!(
                    target: "picus::gb_stats",
                    "uf hub: model certified; function table has {} entries",
                    table.len()
                );
                CheckOutcome::Sat(model)
            }
            Err(UfViolation::Collision { .. }) if !self.care_complete => {
                self.flags.degraded_by_cap.set(true);
                CheckOutcome::Unknown
            }
            Err(v) => self.classify_failure(&v.to_string()),
        }
    }

    /// A certification failure under COMPLETE care: the completeness
    /// theorem says this is impossible modulo the documented
    /// propagation-skip fallbacks (which are legitimately reachable),
    /// so it is counted on a dedicated counter — distinct from the
    /// generic theory-degradation signal, so skip-path noise never
    /// masks real defects — and degrades to Unknown, never Sat.
    fn classify_failure(&self, what: &str) -> CheckOutcome {
        if self.eg.explain_overflowed() {
            // An explanation walk overflowed earlier in this solve, so
            // conflicts/propagations were dropped fail-closed and the
            // completeness theorem's premises do not hold: this is the
            // completeness envelope, not a defect.
            self.flags.infeasible.set(true);
            return CheckOutcome::Unknown;
        }
        if self.care_complete {
            log::warn!(
                "uf hub: Sat candidate failed congruence certification under complete \
                 care ({}); defect or propagation-skip artifact — degrading to Unknown",
                what
            );
            metric::incr!(crate::profile::NATIVE_FF.uf_g3_complete_care_failures);
        } else {
            self.flags.degraded_by_cap.set(true);
        }
        CheckOutcome::Unknown
    }
}

impl<T: Theory> Theory for UfCombinedTheory<T> {
    fn notify_fact(&mut self, atom: Var, polarity: bool) {
        // Inner first: FF completeness never depends on the hub.
        self.inner.notify_fact(atom, polarity);
        if let Some(&(t1, t2)) = self.atom_view.get(&atom) {
            if polarity {
                self.eg.assert_equal(t1, t2, atom);
            } else {
                self.eg.assert_diseq(t1, t2, atom);
            }
        }
    }

    fn early_check(&mut self) -> Option<CheckOutcome> {
        if let Some(core) = self.eg.pending_conflict.take() {
            metric::incr!(crate::profile::NATIVE_FF.uf_hub_early_conflicts);
            return Some(CheckOutcome::Unsat { core });
        }
        match self.inner.early_check() {
            // An inner early Sat is terminal at the orchestrator (it
            // returns without reaching post_check), so forwarding it
            // would bypass congruence certification entirely. The
            // trait's early-Sat license is FF-only, never congruence;
            // downgrade to None and force the decision to post_check.
            // No shipped theory returns early Sat, so this only guards
            // against future inner-theory changes.
            Some(CheckOutcome::Sat(_)) => None,
            other => other,
        }
    }

    fn propagate(&mut self) -> Vec<(Var, bool)> {
        // Explanations live exactly one round: the orchestrator calls
        // explain() for this round's propagations immediately. Clearing
        // here prevents a stale hub explanation (whose reason atoms a
        // backjump may have unassigned) from shadowing a fresh inner-
        // theory explanation for the same atom in a later round.
        self.prop_explanations.clear();
        let mut out: Vec<(Var, bool)> = Vec::new();
        for (v, pol, explanation) in self.eg.pending_props.drain(..) {
            debug_assert!(!explanation.is_empty(), "hub propagation with empty reason");
            if explanation.is_empty() {
                // Release-mode fallback: skip — sound, the atom gets
                // decided by the SAT engine instead.
                continue;
            }
            self.prop_explanations.insert((v, pol), explanation);
            out.push((v, pol));
        }
        out.extend(self.inner.propagate());
        out
    }

    fn explain(&self, atom: Var, polarity: bool) -> Vec<(Var, bool)> {
        match self.prop_explanations.get(&(atom, polarity)) {
            Some(e) => e.clone(),
            None => self.inner.explain(atom, polarity),
        }
    }

    fn post_check(&mut self) -> CheckOutcome {
        match self.inner.post_check() {
            CheckOutcome::Sat(model) => self.finalize_uf_sat(model),
            other => other,
        }
    }

    fn push(&mut self) {
        self.eg.push();
        self.inner.push();
    }

    fn pop(&mut self) {
        self.inner.pop();
        self.eg.pop();
        self.prop_explanations.clear();
    }
}

#[cfg(test)]
#[path = "uf_theory_tests.rs"]
mod tests;
