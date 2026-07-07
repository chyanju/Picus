use num_bigint::BigUint;

use super::*;
use crate::sat::Var;

fn v(i: u32) -> Var {
    Var(i)
}

/// Non-backtracking scratch oracle: recompute the congruence closure
/// from a list of surviving equalities + app definitions from scratch
/// (fixpoint over a naive partition), independent of the e-graph's
/// union/undo machinery.
struct ScratchCc {
    apps: Vec<(usize, u32, Vec<usize>)>, // (node, sym, args)
    class: Vec<usize>,
}

impl ScratchCc {
    fn new(n: usize, apps: &[(usize, u32, Vec<usize>)]) -> Self {
        ScratchCc { apps: apps.to_vec(), class: (0..n).collect() }
    }

    fn root(&self, mut x: usize) -> usize {
        while self.class[x] != x {
            x = self.class[x];
        }
        x
    }

    fn union(&mut self, a: usize, b: usize) {
        let (ra, rb) = (self.root(a), self.root(b));
        if ra != rb {
            self.class[ra.max(rb)] = ra.min(rb);
        }
    }

    fn close(&mut self, eqs: &[(usize, usize)]) {
        for &(a, b) in eqs {
            self.union(a, b);
        }
        loop {
            let mut changed = false;
            for i in 0..self.apps.len() {
                for j in (i + 1)..self.apps.len() {
                    let (ni, si, ref ai) = self.apps[i];
                    let (nj, sj, ref aj) = self.apps[j];
                    if si != sj || ai.len() != aj.len() {
                        continue;
                    }
                    if ai.iter().zip(aj.iter()).all(|(&x, &y)| self.root(x) == self.root(y))
                        && self.root(ni) != self.root(nj)
                    {
                        self.union(ni, nj);
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
    }

    fn same(&self, a: usize, b: usize) -> bool {
        self.root(a) == self.root(b)
    }
}

struct Lcg(u64);

impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 33
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

#[test]
fn congruence_detection_basic() {
    let mut eg = EGraph::new();
    let a = eg.add_var(0);
    let b = eg.add_var(1);
    let fa = eg.add_app(7, &[a]);
    let fb = eg.add_app(7, &[b]);
    assert!(!eg.are_equal(fa, fb));
    eg.push();
    eg.assert_equal(a, b, v(0));
    assert!(eg.are_equal(a, b));
    assert!(eg.are_equal(fa, fb), "congruence merges the results");
    let expl = eg.explain_equal(fa, fb);
    assert_eq!(expl, vec![v(0)], "explanation cites the asserted atom");
    eg.pop();
    assert!(!eg.are_equal(a, b));
    assert!(!eg.are_equal(fa, fb));
}

#[test]
fn nested_congruence_explanations_are_nonempty_subsets() {
    let mut eg = EGraph::new();
    let a = eg.add_var(0);
    let b = eg.add_var(1);
    let fa = eg.add_app(1, &[a]);
    let fb = eg.add_app(1, &[b]);
    let gfa = eg.add_app(2, &[fa]);
    let gfb = eg.add_app(2, &[fb]);
    eg.push();
    eg.assert_equal(a, b, v(3));
    assert!(eg.are_equal(gfa, gfb), "two congruence steps chain");
    let expl = eg.explain_equal(gfa, gfb);
    assert!(!expl.is_empty());
    assert!(expl.iter().all(|&x| x == v(3)), "only the asserted atom appears");
}

#[test]
fn transitivity_across_multiple_atoms() {
    let mut eg = EGraph::new();
    let x0 = eg.add_var(0);
    let x1 = eg.add_var(1);
    let x2 = eg.add_var(2);
    let x3 = eg.add_var(3);
    eg.push();
    eg.assert_equal(x0, x1, v(0));
    eg.assert_equal(x2, x3, v(1));
    eg.assert_equal(x1, x2, v(2));
    assert!(eg.are_equal(x0, x3));
    let mut expl = eg.explain_equal(x0, x3);
    expl.sort_by_key(|x| x.index());
    assert_eq!(expl, vec![v(0), v(1), v(2)], "chain needs all three atoms");
}

#[test]
fn merge_then_diseq_same_class_conflicts() {
    let mut eg = EGraph::new();
    let a = eg.add_var(0);
    let b = eg.add_var(1);
    eg.push();
    eg.assert_equal(a, b, v(0));
    assert!(eg.pending_conflict.is_none());
    // Same-class disequality assertion raises the conflict directly
    // (the ordering trigger propagation alone cannot rescue).
    eg.assert_diseq(a, b, v(1));
    let core = eg.pending_conflict.clone().expect("conflict");
    assert!(core.contains(&v(0)) && core.contains(&v(1)));
}

#[test]
fn diseq_then_merge_conflicts_with_witness_in_core() {
    let mut eg = EGraph::new();
    let a = eg.add_var(0);
    let b = eg.add_var(1);
    let c = eg.add_var(2);
    eg.push();
    eg.assert_diseq(a, c, v(9));
    eg.assert_equal(a, b, v(1));
    assert!(eg.pending_conflict.is_none());
    eg.assert_equal(b, c, v(2));
    let core = eg.pending_conflict.clone().expect("conflict");
    assert!(core.contains(&v(9)), "witness atom is in the core: {:?}", core);
    assert!(core.contains(&v(1)) && core.contains(&v(2)));
}

#[test]
fn constant_clash_conflicts() {
    let mut eg = EGraph::new();
    let x = eg.add_var(0);
    let y = eg.add_var(1);
    let c1 = eg.add_const(&BigUint::from(1u32));
    let c2 = eg.add_const(&BigUint::from(2u32));
    eg.push();
    eg.assert_equal(x, c1, v(0));
    eg.assert_equal(y, c2, v(1));
    assert!(eg.pending_conflict.is_none());
    eg.assert_equal(x, y, v(2));
    let core = eg.pending_conflict.clone().expect("constant clash");
    assert!(!core.is_empty());
}

#[test]
fn trigger_atoms_propagate_positive_with_explanations() {
    let mut eg = EGraph::new();
    let a = eg.add_var(0);
    let b = eg.add_var(1);
    let fa = eg.add_app(1, &[a]);
    let fb = eg.add_app(1, &[b]);
    // The result-pair care atom.
    eg.register_trigger_atom(fa, fb, v(5));
    eg.push();
    eg.assert_equal(a, b, v(0));
    let props: Vec<_> = eg.pending_props.drain(..).collect();
    assert_eq!(props.len(), 1);
    let (var, pol, expl) = &props[0];
    assert_eq!((*var, *pol), (v(5), true));
    assert_eq!(expl.as_slice(), &[(v(0), true)], "non-empty, polarity-aware");
}

#[test]
fn trigger_atoms_propagate_negative_through_diseq() {
    let mut eg = EGraph::new();
    let a = eg.add_var(0);
    let b = eg.add_var(1);
    let c = eg.add_var(2);
    eg.register_trigger_atom(a, c, v(5));
    eg.push();
    eg.assert_diseq(b, c, v(7));
    assert!(eg.pending_props.is_empty());
    eg.assert_equal(a, b, v(1));
    let props: Vec<_> = eg.pending_props.drain(..).collect();
    assert_eq!(props.len(), 1);
    let (var, pol, expl) = &props[0];
    assert_eq!((*var, *pol), (v(5), false));
    assert!(expl.contains(&(v(7), false)), "witness at negative polarity");
    assert!(expl.contains(&(v(1), true)));
}

#[test]
fn closure_entailed_triggers_cover_shared_input_shape() {
    // x_r = f(x_in), y_r = f(x_in): syntactically identical argument
    // tuples entail (x_r = y_r) with an empty proof — returned by the
    // setup fixpoint for pre-loop unit assertion, never propagated.
    let mut eg = EGraph::new();
    let x_in = eg.add_var(0);
    let x_r = eg.add_var(1);
    let y_r = eg.add_var(2);
    let f1 = eg.add_app(1, &[x_in]);
    let f2 = eg.add_app(1, &[x_in]);
    // Result variables tied to their application nodes definitionally
    // (input facts, no atoms):
    eg.merge_definitional(f1, x_r);
    eg.merge_definitional(f2, y_r);
    eg.register_trigger_atom(x_r, y_r, v(5));
    let entailed = eg.closure_entailed_triggers();
    assert_eq!(entailed, vec![(v(5), true)]);
}

#[test]
fn deep_congruence_chain_overflows_fail_closed() {
    // Two 600-deep nested application chains linked by one atom at the
    // bottom: explaining the top-level equality exceeds the recursion
    // cap. Nothing partial may surface — no pending conflict with a
    // truncated core, no propagation with a truncated reason — and the
    // sticky overflow flag must be set for the hub's classification.
    let mut eg = EGraph::new();
    let a0 = eg.add_var(0);
    let b0 = eg.add_var(1);
    let mut a = a0;
    let mut b = b0;
    for _ in 0..600 {
        a = eg.add_app(1, &[a]);
        b = eg.add_app(1, &[b]);
    }
    let _ = eg.closure_entailed_triggers();
    eg.push();
    eg.assert_equal(a0, b0, v(0));
    assert!(eg.are_equal(a, b), "congruence cascades the full chain");
    // Same-class diseq at the top: the true core is {v0, v1}, but the
    // explanation walk overflows — the conflict must be DROPPED, not
    // emitted with a partial core.
    eg.assert_diseq(a, b, v(1));
    assert!(
        eg.pending_conflict.is_none(),
        "no partial core may be emitted past the explanation cap"
    );
    assert!(eg.explain_overflowed(), "sticky overflow flag set");
}

#[test]
fn randomized_ops_and_undo_match_scratch_oracle() {
    // Random push/assert/pop sequences: after every pop, class
    // structure must equal a from-scratch closure over the SURVIVING
    // equalities (union/undo exactness), and positive explanations
    // must only cite surviving atoms.
    let mut rng = Lcg(0xE64A);
    for round in 0..40 {
        let n_vars = 4 + rng.below(3) as usize;
        let mut eg = EGraph::new();
        let vars: Vec<TermId> = (0..n_vars).map(|i| eg.add_var(i as u32)).collect();
        let mut apps: Vec<(usize, u32, Vec<usize>)> = Vec::new();
        let mut app_ids: Vec<TermId> = Vec::new();
        for k in 0..(2 + rng.below(3) as usize) {
            let sym = (k % 2) as u32;
            let arg = rng.below(n_vars as u64) as usize;
            let id = eg.add_app(sym, &[vars[arg]]);
            apps.push((id as usize, sym, vec![arg]));
            app_ids.push(id);
        }
        let n_all = eg.n_nodes();
        // Mirror the orchestrator: the setup fixpoint runs before any
        // assertion, so syntactically-identical applications are
        // already merged (as the scratch oracle's closure assumes).
        let _ = eg.closure_entailed_triggers();

        // Level stack of surviving equality lists (node-id pairs plus
        // the asserting atom, so the explanation-liveness check below
        // can distinguish surviving atoms from popped ones).
        let mut level_eqs: Vec<Vec<(usize, usize, u32)>> = vec![Vec::new()];
        let mut next_atom = 0u32;
        for _op in 0..30 {
            match rng.below(4) {
                0 => {
                    eg.push();
                    level_eqs.push(Vec::new());
                }
                1 if level_eqs.len() > 1 => {
                    eg.pop();
                    level_eqs.pop();
                }
                _ => {
                    if level_eqs.len() == 1 {
                        // Stay above root level for assertions so pops
                        // can always be checked.
                        eg.push();
                        level_eqs.push(Vec::new());
                    }
                    let a = rng.below(n_all as u64) as usize;
                    let b = rng.below(n_all as u64) as usize;
                    if a == b {
                        continue;
                    }
                    let atom = v(next_atom);
                    next_atom += 1;
                    eg.assert_equal(a as TermId, b as TermId, atom);
                    if eg.pending_conflict.is_some() {
                        // Constant-free graphs cannot conflict here
                        // (no diseqs asserted in this harness).
                        panic!("unexpected conflict in round {}", round);
                    }
                    level_eqs.last_mut().unwrap().push((a, b, atom.0));
                }
            }

            // Oracle comparison over every node pair.
            let surviving: Vec<(usize, usize)> = level_eqs
                .iter()
                .flatten()
                .map(|&(a, b, _)| (a, b))
                .collect();
            let mut oracle = ScratchCc::new(n_all, &apps);
            oracle.close(&surviving);
            for x in 0..n_all {
                for y in (x + 1)..n_all {
                    assert_eq!(
                        eg.are_equal(x as TermId, y as TermId),
                        oracle.same(x, y),
                        "round {} class divergence on ({}, {}) after {:?} eqs",
                        round,
                        x,
                        y,
                        surviving.len()
                    );
                }
            }

            // Explanations for a few random equal pairs must cite only
            // atoms asserted at SURVIVING levels — an explanation
            // referencing a popped atom would mean the proof forest
            // was not exactly restored.
            let alive: std::collections::HashSet<u32> =
                level_eqs.iter().flatten().map(|&(_, _, atom)| atom).collect();
            for _ in 0..3 {
                let x = rng.below(n_all as u64) as usize;
                let y = rng.below(n_all as u64) as usize;
                if x != y && eg.are_equal(x as TermId, y as TermId) {
                    for a in eg.explain_equal(x as TermId, y as TermId) {
                        assert!(
                            alive.contains(&(a.0)),
                            "explanation cites popped atom v{}",
                            a.0
                        );
                    }
                }
            }
        }
    }
}
