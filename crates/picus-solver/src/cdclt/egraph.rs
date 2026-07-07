//! Backtrackable congruence-closure e-graph — the term-level equality
//! hub for the UF theory (Nieuwenhuis–Oliveras congruence closure with
//! an explanation forest).
//!
//! NOT an extension of `equality_engine.rs`: that engine's union-find
//! is SAT-Var-indexed (atom polarities), its no-undo-union argument is
//! load-bearing, and neither fits term-level congruence. This graph is
//! term-indexed (variables, constants, applications), unions are
//! trailed and exactly undoable (union by rank, NO path compression —
//! the compression-free walk is what makes `pop` restoration exact),
//! and every equality consequence carries an explanation in terms of
//! trail-asserted atom variables.
//!
//! Conflict cores and propagation explanations cite only atoms that
//! were asserted to the hub (satisfying `enqueue_theory`'s
//! currently-True requirement and `apply_theory_conflict`'s
//! assigned-core requirement) and are never empty for queued
//! propagations — setup-time syntactic entailments are handled by the
//! orchestrator as pre-loop unit clauses instead (`enqueue_theory`
//! rejects empty reason sets).

use std::collections::HashMap;

use num_bigint::BigUint;

use crate::frontend::encoder::UfSymbolId;
use crate::sat::Var;

/// Index into [`EGraph::nodes`].
pub(crate) type TermId = u32;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum TermNode {
    /// Index into the solve's `var_names` frame.
    Var(u32),
    /// A field constant (from `var = const` atoms).
    Const(BigUint),
    /// One node per UF application occurrence.
    App { sym: UfSymbolId, args: Vec<TermId> },
}

/// Why two terms were merged (an edge in the explanation forest).
#[derive(Debug, Clone, Copy)]
enum EdgeReason {
    /// A positive equality atom asserted to the hub.
    Atom(Var),
    /// Congruence between two App nodes with pairwise-equal argument
    /// classes; explaining it recurses on the argument pairs.
    Congruence(TermId, TermId),
    /// A definitional input fact (`r = f(args)` ties the application
    /// node to its result variable at setup). Always true — it
    /// contributes no atoms to explanations, exactly like the
    /// syntactic congruence the setup fixpoint derives from it.
    Definition,
}

/// Trail records for exact `pop` restoration.
enum Undo {
    /// `child_root` was linked under `parent_root`.
    Union {
        child_root: TermId,
        parent_root: TermId,
        rank_bumped: bool,
        parent_use_len: usize,
        /// Diseq keys added to the parent's map by the migration.
        parent_diseq_added: Vec<TermId>,
        /// The parent gained a class constant from the child.
        const_taken_from_child: bool,
        /// Explanation-forest edge inserted at `child_end` (the path
        /// from `child_end` to its old forest root was reversed
        /// first). Undo removes the edge and re-reverses from the
        /// recorded old root — reversal is an involution over the
        /// path's endpoints, so this restores the exact orientation.
        child_end: TermId,
        child_old_forest_root: TermId,
    },
    CongInsert {
        key: (UfSymbolId, Vec<TermId>),
    },
    DiseqAdd {
        a_root: TermId,
        b_root: TermId,
    },
    Notify {
        var: Var,
        prev: Option<bool>,
    },
}

/// A recorded disequality between two classes: the witness atom
/// (asserted False) plus the original endpoint terms, kept so
/// explanations can connect precisely to where the disequality was
/// asserted even after further merges move the roots.
#[derive(Debug, Clone, Copy)]
struct DiseqRecord {
    witness: Var,
    end_a: TermId,
    end_b: TermId,
}

pub(crate) struct EGraph {
    nodes: Vec<TermNode>,
    parent: Vec<TermId>,
    rank: Vec<u32>,
    /// Class-root -> App nodes with an argument in this class.
    use_lists: Vec<Vec<TermId>>,
    /// `(sym, arg class reps)` -> canonical App node.
    cong_table: HashMap<(UfSymbolId, Vec<TermId>), TermId>,
    /// Explanation forest (Nieuwenhuis–Oliveras): per-node optional
    /// edge toward its forest parent.
    proof_parent: Vec<Option<(TermId, EdgeReason)>>,
    /// Class-root -> recorded disequalities to other class roots.
    diseqs: Vec<HashMap<TermId, DiseqRecord>>,
    /// Class-root -> the class's constant member, if any.
    class_const: HashMap<TermId, TermId>,
    /// Registered equality atoms between two nodes, keyed `(min, max)`.
    trigger_atoms: HashMap<(TermId, TermId), Var>,
    /// Polarities the hub has been notified of, per atom.
    notified: HashMap<Var, bool>,
    trail: Vec<Undo>,
    levels: Vec<usize>,
    /// Equality-atom propagations awaiting the theory's `propagate`,
    /// paired with their (non-empty) explanations.
    pub(crate) pending_props: Vec<(Var, bool, Vec<(Var, bool)>)>,
    /// An explained conflict core (atom vars only), set at the first
    /// inconsistency and consumed by the theory's `early_check`.
    pub(crate) pending_conflict: Option<Vec<Var>>,
    /// Sticky: an explanation walk hit the recursion depth cap and
    /// would have been INCOMPLETE. Nothing partial is ever emitted
    /// (the conflict/propagation is dropped instead); the hub reads
    /// this to classify subsequent certification failures as the
    /// completeness envelope (`Unknown`), never as Sat/Unsat evidence.
    explain_overflow: std::cell::Cell<bool>,
}

impl EGraph {
    pub(crate) fn new() -> Self {
        EGraph {
            nodes: Vec::new(),
            parent: Vec::new(),
            rank: Vec::new(),
            use_lists: Vec::new(),
            cong_table: HashMap::new(),
            proof_parent: Vec::new(),
            diseqs: Vec::new(),
            class_const: HashMap::new(),
            trigger_atoms: HashMap::new(),
            notified: HashMap::new(),
            trail: Vec::new(),
            levels: Vec::new(),
            pending_props: Vec::new(),
            pending_conflict: None,
            explain_overflow: std::cell::Cell::new(false),
        }
    }

    fn push_node(&mut self, node: TermNode) -> TermId {
        let id = self.nodes.len() as TermId;
        self.nodes.push(node);
        self.parent.push(id);
        self.rank.push(0);
        self.use_lists.push(Vec::new());
        self.proof_parent.push(None);
        self.diseqs.push(HashMap::new());
        id
    }

    pub(crate) fn add_var(&mut self, frame_idx: u32) -> TermId {
        self.push_node(TermNode::Var(frame_idx))
    }

    pub(crate) fn add_const(&mut self, value: &BigUint) -> TermId {
        // Dedup constants by value so two `= c` atoms share a node
        // (linear scan: constants per solve are few).
        for (i, n) in self.nodes.iter().enumerate() {
            if let TermNode::Const(v) = n {
                if v == value {
                    return i as TermId;
                }
            }
        }
        let id = self.push_node(TermNode::Const(value.clone()));
        self.class_const.insert(id, id);
        id
    }

    /// Add an App node (one per application occurrence — congruence
    /// merges result classes rather than deduping nodes) and register
    /// it in its arguments' use lists and the congruence table.
    /// Setup-time only (level 0), so no trail records are needed for
    /// the use-list registration itself.
    pub(crate) fn add_app(&mut self, sym: UfSymbolId, args: &[TermId]) -> TermId {
        let id = self.push_node(TermNode::App { sym, args: args.to_vec() });
        for &a in args {
            let ra = self.find(a);
            self.use_lists[ra as usize].push(id);
        }
        let sig = self.signature(id);
        self.cong_table.entry(sig).or_insert(id);
        id
    }

    fn signature(&self, app: TermId) -> (UfSymbolId, Vec<TermId>) {
        match &self.nodes[app as usize] {
            TermNode::App { sym, args } => {
                (*sym, args.iter().map(|&a| self.find(a)).collect())
            }
            _ => unreachable!("signature of a non-App node"),
        }
    }

    pub(crate) fn node(&self, t: TermId) -> &TermNode {
        &self.nodes[t as usize]
    }

    #[cfg(test)]
    pub(crate) fn n_nodes(&self) -> usize {
        self.nodes.len()
    }

    /// Compression-free find: the parent chain is left intact so undo
    /// can restore it exactly.
    pub(crate) fn find(&self, t: TermId) -> TermId {
        let mut cur = t;
        while self.parent[cur as usize] != cur {
            cur = self.parent[cur as usize];
        }
        cur
    }

    pub(crate) fn are_equal(&self, a: TermId, b: TermId) -> bool {
        self.find(a) == self.find(b)
    }

    /// Register the equality atom `v` denoting `t1 = t2`. Setup-time
    /// only; idempotent.
    pub(crate) fn register_trigger_atom(&mut self, t1: TermId, t2: TermId, v: Var) {
        let key = (t1.min(t2), t1.max(t2));
        self.trigger_atoms.entry(key).or_insert(v);
    }

    fn record_notify(&mut self, v: Var, polarity: bool) {
        let prev = self.notified.insert(v, polarity);
        self.trail.push(Undo::Notify { var: v, prev });
    }

    /// Setup-time definitional merge (`r = f(args)`): ties two terms
    /// with no atom justification. Level 0 only, before any trail
    /// assertion; consequences that decide registered trigger atoms
    /// are collected by [`Self::closure_entailed_triggers`] and
    /// unit-asserted by the orchestrator (never propagated — their
    /// explanations are empty by construction).
    pub(crate) fn merge_definitional(&mut self, t1: TermId, t2: TermId) {
        if self.pending_conflict.is_some() || self.are_equal(t1, t2) {
            return;
        }
        self.merge_cascade(t1, t2, EdgeReason::Definition);
    }

    /// Assert the positive equality atom `reason`: merge the classes of
    /// `t1` and `t2`. Conflicts (constant clash, recorded disequality)
    /// land in `pending_conflict`; consequences land in
    /// `pending_props`. Idempotent on already-equal classes.
    pub(crate) fn assert_equal(&mut self, t1: TermId, t2: TermId, reason: Var) {
        self.record_notify(reason, true);
        if self.pending_conflict.is_some() {
            return;
        }
        if self.are_equal(t1, t2) {
            return;
        }
        self.merge_cascade(t1, t2, EdgeReason::Atom(reason));
        if self.pending_conflict.is_none() {
            self.scan_triggers();
        }
    }

    /// Assert the negative polarity of atom `witness` for `t1 != t2`.
    /// A same-class assertion raises the conflict immediately. This is
    /// required for merge-then-diseq assertion orders, which trigger
    /// propagation alone cannot rescue: the release-mode propagation
    /// skip and `enqueue_theory`'s stale-reason skip can both suppress
    /// the positive push. Re-recording an existing disequality is a
    /// no-op.
    pub(crate) fn assert_diseq(&mut self, t1: TermId, t2: TermId, witness: Var) {
        self.record_notify(witness, false);
        if self.pending_conflict.is_some() {
            return;
        }
        let r1 = self.find(t1);
        let r2 = self.find(t2);
        if r1 == r2 {
            let mut core = self.explain_equal(t1, t2);
            if self.explain_overflow.get() {
                // Incomplete core: dropping the conflict is sound —
                // the model-level gates (class disagreement / table
                // certification) still reject any candidate, and the
                // hub degrades to Unknown instead of trusting a
                // partial core.
                return;
            }
            core.push(witness);
            core.sort_by_key(|v| v.index());
            core.dedup();
            self.pending_conflict = Some(core);
            return;
        }
        if self.diseqs[r1 as usize].contains_key(&r2) {
            return;
        }
        self.diseqs[r1 as usize]
            .insert(r2, DiseqRecord { witness, end_a: t1, end_b: t2 });
        self.diseqs[r2 as usize]
            .insert(r1, DiseqRecord { witness, end_a: t2, end_b: t1 });
        self.trail.push(Undo::DiseqAdd { a_root: r1, b_root: r2 });
        self.scan_triggers();
    }

    /// Merge the classes of `u` and `v` for `reason`, then process the
    /// congruence worklist to its fixpoint.
    fn merge_cascade(&mut self, u: TermId, v: TermId, reason: EdgeReason) {
        let mut worklist: Vec<(TermId, TermId, EdgeReason)> = vec![(u, v, reason)];
        while let Some((a, b, why)) = worklist.pop() {
            if self.pending_conflict.is_some() {
                return;
            }
            let ra = self.find(a);
            let rb = self.find(b);
            if ra == rb {
                continue;
            }

            // Constant clash: the merged class would hold two distinct
            // constants. Explain via the would-be merge edge.
            if let (Some(&ca), Some(&cb)) =
                (self.class_const.get(&ra), self.class_const.get(&rb))
            {
                if self.nodes[ca as usize] != self.nodes[cb as usize] {
                    // Install the edge temporarily so one explain pass
                    // covers a ~ b; then undo it via the normal trail
                    // (the union is recorded like any other and the
                    // conflict aborts the cascade).
                    self.union(a, b, ra, rb, why);
                    let mut core = self.explain_equal(ca, cb);
                    if self.explain_overflow.get() {
                        return;
                    }
                    core.sort_by_key(|x| x.index());
                    core.dedup();
                    self.pending_conflict = Some(core);
                    return;
                }
            }

            // Recorded disequality between the two classes: conflict.
            if let Some(rec) = self.diseqs[ra as usize].get(&rb).copied() {
                self.union(a, b, ra, rb, why);
                let mut core = self.explain_equal(rec.end_a, rec.end_b);
                if self.explain_overflow.get() {
                    return;
                }
                core.push(rec.witness);
                core.sort_by_key(|x| x.index());
                core.dedup();
                self.pending_conflict = Some(core);
                return;
            }

            let moved_apps = self.union(a, b, ra, rb, why);

            // Re-canonicalize the moved class's App signatures; a hit
            // on a different class queues a congruence merge.
            for app in moved_apps {
                let sig = self.signature(app);
                match self.cong_table.get(&sig) {
                    Some(&other) => {
                        if !self.are_equal(app, other) {
                            worklist.push((app, other, EdgeReason::Congruence(app, other)));
                        }
                    }
                    None => {
                        self.cong_table.insert(sig.clone(), app);
                        self.trail.push(Undo::CongInsert { key: sig });
                    }
                }
            }
        }
    }

    /// Union by rank with full trail bookkeeping. Returns the App
    /// nodes whose signatures must be re-canonicalized (the moved
    /// class's use list).
    fn union(
        &mut self,
        end_a: TermId,
        end_b: TermId,
        ra: TermId,
        rb: TermId,
        reason: EdgeReason,
    ) -> Vec<TermId> {
        // Orient by rank: `child` is linked under `parent`.
        let (child, parent, end_child, rank_bumped) =
            if self.rank[ra as usize] < self.rank[rb as usize] {
                (ra, rb, end_a, false)
            } else if self.rank[ra as usize] > self.rank[rb as usize] {
                (rb, ra, end_b, false)
            } else {
                self.rank[ra as usize] += 1;
                (rb, ra, end_b, true)
            };

        // Explanation forest: the edge lives between the ASSERTED
        // endpoints, oriented from the child side. Reverse the child
        // end's path to its forest root first so the new edge becomes
        // its (unique) parent edge. The old root is recorded so undo
        // can re-reverse from there (an exact involution).
        let child_old_forest_root = *self.forest_path(end_child).last().expect("non-empty");
        self.reverse_proof_path(end_child);
        let end_parent = if end_child == end_a { end_b } else { end_a };
        self.proof_parent[end_child as usize] = Some((end_parent, reason));

        self.parent[child as usize] = parent;

        // Splice use lists (child's into parent's).
        let moved: Vec<TermId> = self.use_lists[child as usize].clone();
        let parent_use_len = self.use_lists[parent as usize].len();
        let moved_clone = moved.clone();
        self.use_lists[parent as usize].extend(moved_clone);

        // Migrate the child's disequalities to the parent root.
        let child_diseqs: Vec<(TermId, DiseqRecord)> =
            self.diseqs[child as usize].iter().map(|(k, v)| (*k, *v)).collect();
        let mut parent_diseq_added = Vec::new();
        for (other, rec) in child_diseqs {
            if !self.diseqs[parent as usize].contains_key(&other) {
                self.diseqs[parent as usize].insert(other, rec);
                parent_diseq_added.push(other);
            }
            // The reverse entry keyed by `child` in `other`'s map is
            // left in place: lookups go through `find`, and the merged
            // class is checked via the parent key added here. Stale
            // keys are harmless (they never match a live root) and
            // vanish on undo.
            if let Some(r) = self.diseqs[other as usize].get(&child).copied() {
                self.diseqs[other as usize].entry(parent).or_insert(r);
                // Recorded for symmetry; removal on undo keyed off
                // `parent_diseq_added` via the paired entry below.
            }
        }

        // Class constant migrates upward.
        let mut const_taken = false;
        if let Some(&c) = self.class_const.get(&child) {
            if !self.class_const.contains_key(&parent) {
                self.class_const.insert(parent, c);
                const_taken = true;
            }
        }

        self.trail.push(Undo::Union {
            child_root: child,
            parent_root: parent,
            rank_bumped,
            parent_use_len,
            parent_diseq_added,
            const_taken_from_child: const_taken,
            child_end: end_child,
            child_old_forest_root,
        });
        moved
    }

    /// Reverse the explanation-forest path from `t` to its forest
    /// root, making `t` the root of its tree.
    fn reverse_proof_path(&mut self, t: TermId) {
        let mut prev: Option<(TermId, EdgeReason)> = None;
        let mut cur = t;
        loop {
            let next = self.proof_parent[cur as usize];
            self.proof_parent[cur as usize] = prev;
            match next {
                Some((n, reason)) => {
                    prev = Some((cur, reason));
                    cur = n;
                }
                None => break,
            }
        }
    }

    /// After any merge or new disequality: push trigger atoms decided
    /// by the current classes. Positive pushes fire for atoms not yet
    /// notified to the hub whose two nodes now share a class; negative
    /// pushes fire when the two classes hold a recorded disequality.
    /// Explanations
    /// are computed eagerly (they cite only asserted atoms and are
    /// never empty — setup-time syntactic entailments never reach this
    /// path, they are unit-asserted pre-loop by the orchestrator).
    fn scan_triggers(&mut self) {
        let triggers: Vec<((TermId, TermId), Var)> =
            self.trigger_atoms.iter().map(|(&k, &v)| (k, v)).collect();
        for ((t1, t2), v) in triggers {
            if self.notified.contains_key(&v) {
                continue;
            }
            if self.pending_props.iter().any(|&(pv, _, _)| pv == v) {
                continue;
            }
            let r1 = self.find(t1);
            let r2 = self.find(t2);
            if r1 == r2 {
                let overflow_before = self.explain_overflow.get();
                let explanation: Vec<(Var, bool)> = self
                    .explain_equal(t1, t2)
                    .into_iter()
                    .map(|a| (a, self.notified.get(&a).copied().unwrap_or(true)))
                    .collect();
                if self.explain_overflow.get() && !overflow_before {
                    // Incomplete reason set: never enqueue it.
                    continue;
                }
                if explanation.is_empty() {
                    // A queued propagation must carry a non-empty
                    // explanation (`enqueue_theory` rejects empty
                    // reasons). Entailments with empty proofs are
                    // setup-time facts the orchestrator unit-asserts;
                    // skipping here is sound — the atom gets decided by
                    // the SAT engine instead.
                    debug_assert!(
                        false,
                        "empty explanation for a trigger propagation (setup entailment leaked)"
                    );
                    continue;
                }
                self.pending_props.push((v, true, explanation));
            } else if let Some(rec) = self.diseqs[r1 as usize].get(&r2).copied() {
                let overflow_before = self.explain_overflow.get();
                let mut explanation: Vec<(Var, bool)> = Vec::new();
                // t1 ~ end_a and t2 ~ end_b (or crosswise) plus the
                // witness at negative polarity.
                let (ea, eb) = if self.are_equal(t1, rec.end_a) {
                    (rec.end_a, rec.end_b)
                } else {
                    (rec.end_b, rec.end_a)
                };
                for a in self.explain_equal(t1, ea) {
                    explanation.push((a, self.notified.get(&a).copied().unwrap_or(true)));
                }
                for a in self.explain_equal(t2, eb) {
                    explanation.push((a, self.notified.get(&a).copied().unwrap_or(true)));
                }
                if self.explain_overflow.get() && !overflow_before {
                    continue;
                }
                explanation.push((rec.witness, false));
                explanation.sort_by_key(|&(a, _)| a.index());
                explanation.dedup();
                self.pending_props.push((v, false, explanation));
            }
        }
    }

    /// Explain why `a` and `b` are in the same class: a (possibly
    /// non-minimal) set of asserted atom variables whose equalities
    /// entail `a = b`. Walks the explanation forest to the common
    /// ancestor; congruence edges recurse pairwise on arguments.
    /// Precondition: `are_equal(a, b)`.
    pub(crate) fn explain_equal(&self, a: TermId, b: TermId) -> Vec<Var> {
        let mut out: Vec<Var> = Vec::new();
        let mut seen_pairs: std::collections::HashSet<(TermId, TermId)> =
            std::collections::HashSet::new();
        self.explain_rec(a, b, &mut out, &mut seen_pairs, 0);
        out
    }

    fn forest_path(&self, t: TermId) -> Vec<TermId> {
        let mut path = vec![t];
        let mut cur = t;
        while let Some((n, _)) = self.proof_parent[cur as usize] {
            path.push(n);
            cur = n;
        }
        path
    }

    pub(crate) fn explain_overflowed(&self) -> bool {
        self.explain_overflow.get()
    }

    fn explain_rec(
        &self,
        a: TermId,
        b: TermId,
        out: &mut Vec<Var>,
        seen: &mut std::collections::HashSet<(TermId, TermId)>,
        depth: usize,
    ) {
        if a == b {
            return;
        }
        if depth > 512 {
            // The walk would be incomplete. Never return a partial
            // explanation silently: mark the sticky overflow so every
            // caller drops the conflict/propagation it was building
            // (fail-closed; the certification gates still hold).
            self.explain_overflow.set(true);
            return;
        }
        let key = (a.min(b), a.max(b));
        if !seen.insert(key) {
            return;
        }
        // Common ancestor in the explanation forest.
        let path_a = self.forest_path(a);
        let path_b = self.forest_path(b);
        let set_a: std::collections::HashSet<TermId> = path_a.iter().copied().collect();
        let lca = match path_b.iter().find(|t| set_a.contains(t)) {
            Some(&t) => t,
            None => {
                debug_assert!(false, "explain_equal on terms with disjoint proof trees");
                return;
            }
        };
        for path in [&path_a, &path_b] {
            for w in path.windows(2) {
                let (from, to) = (w[0], w[1]);
                if from == lca {
                    break;
                }
                match self.proof_parent[from as usize] {
                    Some((p, reason)) => {
                        debug_assert_eq!(p, to);
                        match reason {
                            EdgeReason::Atom(v) => out.push(v),
                            EdgeReason::Definition => {}
                            EdgeReason::Congruence(x, y) => {
                                if let (
                                    TermNode::App { args: ax, .. },
                                    TermNode::App { args: ay, .. },
                                ) = (&self.nodes[x as usize], &self.nodes[y as usize])
                                {
                                    let (ax, ay) = (ax.clone(), ay.clone());
                                    for (u, v2) in ax.iter().zip(ay.iter()) {
                                        self.explain_rec(*u, *v2, out, seen, depth + 1);
                                    }
                                }
                            }
                        }
                    }
                    None => break,
                }
                if to == lca {
                    break;
                }
            }
        }
    }

    /// Setup-time congruence fixpoint over the syntactic facts alone
    /// (identical argument tuples merge results). Returns every
    /// registered trigger atom entailed by the closure, with its
    /// polarity — the orchestrator asserts these as pre-loop unit
    /// clauses (level 0), which is what makes empty-explanation
    /// propagation unnecessary.
    pub(crate) fn closure_entailed_triggers(&mut self) -> Vec<(Var, bool)> {
        // Merge same-signature Apps via the congruence table.
        let apps: Vec<TermId> = (0..self.nodes.len() as TermId)
            .filter(|&t| matches!(self.nodes[t as usize], TermNode::App { .. }))
            .collect();
        for app in apps {
            if self.pending_conflict.is_some() {
                break;
            }
            let sig = self.signature(app);
            match self.cong_table.get(&sig) {
                Some(&other) if !self.are_equal(app, other) => {
                    self.merge_cascade(app, other, EdgeReason::Congruence(app, other));
                }
                Some(_) => {}
                None => {
                    self.cong_table.insert(sig, app);
                }
            }
        }
        let mut out = Vec::new();
        for (&(t1, t2), &v) in &self.trigger_atoms {
            if self.are_equal(t1, t2) {
                out.push((v, true));
            }
        }
        // Deregister the entailed triggers: their truth is fixed by
        // the caller's pre-loop unit clauses, and leaving them
        // registered would let a loop-time scan fire before their
        // notification arrives — with an EMPTY explanation (the proof
        // is purely definitional), which `enqueue_theory` rejects.
        for &(v, _) in &out {
            self.trigger_atoms.retain(|_, tv| *tv != v);
        }
        out.sort_by_key(|&(v, _)| v.index());
        out
    }

    /// Class members grouped by root, for model completion.
    pub(crate) fn classes(&self) -> HashMap<TermId, Vec<TermId>> {
        let mut map: HashMap<TermId, Vec<TermId>> = HashMap::new();
        for t in 0..self.nodes.len() as TermId {
            map.entry(self.find(t)).or_default().push(t);
        }
        map
    }

    pub(crate) fn push(&mut self) {
        self.levels.push(self.trail.len());
    }

    pub(crate) fn pop(&mut self) {
        let mark = self.levels.pop().unwrap_or(0);
        while self.trail.len() > mark {
            match self.trail.pop().expect("trail length checked") {
                Undo::Union {
                    child_root,
                    parent_root,
                    rank_bumped,
                    parent_use_len,
                    parent_diseq_added,
                    const_taken_from_child,
                    child_end,
                    child_old_forest_root,
                } => {
                    self.parent[child_root as usize] = child_root;
                    if rank_bumped {
                        self.rank[parent_root as usize] -= 1;
                    }
                    self.use_lists[parent_root as usize].truncate(parent_use_len);
                    for other in parent_diseq_added {
                        self.diseqs[parent_root as usize].remove(&other);
                        self.diseqs[other as usize].remove(&parent_root);
                    }
                    if const_taken_from_child {
                        self.class_const.remove(&parent_root);
                    }
                    // Remove the forest edge, then re-reverse from the
                    // recorded old root: later unions' reversals have
                    // already been undone (reverse trail order), so
                    // this restores the exact pre-union orientation.
                    self.proof_parent[child_end as usize] = None;
                    self.reverse_proof_path(child_old_forest_root);
                }
                Undo::CongInsert { key } => {
                    self.cong_table.remove(&key);
                }
                Undo::DiseqAdd { a_root, b_root } => {
                    self.diseqs[a_root as usize].remove(&b_root);
                    self.diseqs[b_root as usize].remove(&a_root);
                }
                Undo::Notify { var, prev } => match prev {
                    Some(p) => {
                        self.notified.insert(var, p);
                    }
                    None => {
                        self.notified.remove(&var);
                    }
                },
            }
        }
        // Anything still pending was derived from state above the
        // popped level; conservatively discard (facts re-asserted
        // after the backjump re-derive their consequences).
        self.pending_props.clear();
        self.pending_conflict = None;
    }

}

#[cfg(test)]
#[path = "egraph_tests.rs"]
mod tests;
