//! Wire-selection strategies for the DPVL outer loop.
//!
//! Strategies register via `inventory` (like the propagation lemmas), so a new
//! selector is added by linking a crate that `submit!`s a [`SelectorDescriptor`]
//! — no central enum or dispatch `match` to edit, and `--selector <name>` is
//! validated against the live registry rather than a hardcoded list.

use std::collections::{HashMap, HashSet};

/// A wire-selection strategy for the DPVL loop.
pub trait Selector {
    /// Pick the next wire from `uspool` (the unknown pool) to send to the
    /// solver; `connectivity` maps each wire to how many constraints it
    /// participates in. Returns `None` when the pool is empty. Must be
    /// deterministic across runs (HashSet iteration order is not).
    fn select(
        &mut self,
        uspool: &HashSet<usize>,
        connectivity: &HashMap<usize, usize>,
    ) -> Option<usize>;

    /// Record the outcome of a solver call on `wire`.
    fn feedback(&mut self, wire: usize, result: SolverFeedback);
}

/// Registry entry for a selection strategy. Downstream crates ship a selector
/// by `inventory::submit!`ing one of these.
pub struct SelectorDescriptor {
    /// Name matched by `--selector <name>` and `DpvlConfig::selector`.
    pub name: &'static str,
    /// Build a fresh strategy instance.
    pub factory: fn() -> Box<dyn Selector>,
}

inventory::collect!(SelectorDescriptor);

/// Every registered selector name, sorted and de-duplicated.
pub fn all_selector_names() -> Vec<&'static str> {
    let mut v: Vec<&'static str> = inventory::iter::<SelectorDescriptor>
        .into_iter()
        .map(|d| d.name)
        .collect();
    v.sort_unstable();
    v.dedup();
    v
}

/// Whether `name` is a registered selector.
pub fn is_selector_name(name: &str) -> bool {
    inventory::iter::<SelectorDescriptor>
        .into_iter()
        .any(|d| d.name == name)
}

/// Build a strategy by name, or `None` if no descriptor matches.
pub fn create_selector_by_name(name: &str) -> Option<Box<dyn Selector>> {
    inventory::iter::<SelectorDescriptor>
        .into_iter()
        .find(|d| d.name == name)
        .map(|d| (d.factory)())
}

/// Per-DPVL-run selection state: a boxed strategy plus the connectivity map it
/// reads, built by name from the registry. Driven through `select` / `feedback`.
pub struct SelectorState {
    selector: Box<dyn Selector>,
    connectivity: HashMap<usize, usize>,
}

impl SelectorState {
    /// Build from a registered strategy `name`. Panics on an unregistered
    /// name — callers validate it (via [`is_selector_name`] /
    /// `DpvlConfig::apply_overlay`) before constructing.
    pub fn new(name: &str, connectivity: HashMap<usize, usize>) -> Self {
        let selector = create_selector_by_name(name)
            .unwrap_or_else(|| panic!("unknown selector: {name}"));
        SelectorState {
            selector,
            connectivity,
        }
    }

    /// Pick the next wire from the unknown pool.
    pub fn select(&mut self, uspool: &HashSet<usize>) -> Option<usize> {
        self.selector.select(uspool, &self.connectivity)
    }

    /// Record a solver outcome on `wire`.
    pub fn feedback(&mut self, wire: usize, result: SolverFeedback) {
        self.selector.feedback(wire, result);
    }
}

// ── first: smallest wire index ─────────────────────────────────────
#[derive(Default)]
struct FirstSelector;

impl Selector for FirstSelector {
    fn select(
        &mut self,
        uspool: &HashSet<usize>,
        _connectivity: &HashMap<usize, usize>,
    ) -> Option<usize> {
        // Smallest index, not `iter().next()`: HashSet iteration order is
        // nondeterministic across runs/builds, which would make the `first`
        // selector irreproducible.
        uspool.iter().copied().min()
    }

    fn feedback(&mut self, _wire: usize, _result: SolverFeedback) {}
}

inventory::submit!(SelectorDescriptor {
    name: "first",
    factory: || Box::new(FirstSelector),
});

// ── counter: highest (connectivity + weight) ───────────────────────
#[derive(Default)]
struct CounterSelector {
    /// Negative weights for wires we've skipped this run; used to
    /// deprioritise them on the next pick.
    weights: HashMap<usize, i64>,
}

impl Selector for CounterSelector {
    fn select(
        &mut self,
        uspool: &HashSet<usize>,
        connectivity: &HashMap<usize, usize>,
    ) -> Option<usize> {
        // Highest (connectivity + weight) wins; ties broken by smallest wire
        // index. Folding the index into the key makes every key unique, so the
        // pick is deterministic regardless of the (nondeterministic) HashSet
        // iteration order — matching the reproducibility `first` gets from
        // `.min()`.
        uspool.iter().copied().max_by_key(|&wire| {
            let c = connectivity.get(&wire).copied().unwrap_or(0) as i64;
            let w = self.weights.get(&wire).copied().unwrap_or(0);
            (c + w, std::cmp::Reverse(wire))
        })
    }

    fn feedback(&mut self, wire: usize, result: SolverFeedback) {
        if let SolverFeedback::Skip = result {
            *self.weights.entry(wire).or_insert(0) -= 1;
        }
    }
}

inventory::submit!(SelectorDescriptor {
    name: "counter",
    factory: || Box::new(CounterSelector::default()),
});

/// Feedback from a solver call.
pub enum SolverFeedback {
    /// Wire was verified as unique (UNSAT).
    Verified,
    /// Wire was skipped (SAT for non-target, timeout, or error).
    Skip,
}

#[cfg(test)]
#[path = "selector_tests.rs"]
mod tests;
