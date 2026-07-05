//! Clause storage and references.

use super::lit::Lit;

/// Reference to a clause in a `ClauseArena`.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Ord, PartialOrd)]
pub(crate) struct ClauseRef(pub u32);

impl ClauseRef {
    pub(crate) fn index(self) -> usize {
        self.0 as usize
    }
}

/// A clause is a disjunction of literals. The first two positions are
/// the watched literals (maintained by the solver); the remaining
/// positions are stored in arbitrary order.
#[derive(Clone, Debug)]
pub(crate) struct Clause {
    pub lits: Vec<Lit>,
    /// `true` for learnt clauses (created by conflict analysis),
    /// `false` for input clauses.
    #[allow(dead_code)]
    pub learnt: bool,
}

impl Clause {
    pub(crate) fn new(lits: Vec<Lit>, learnt: bool) -> Self {
        Clause { lits, learnt }
    }
}

/// Arena that owns every clause kept by the solver.
#[derive(Default)]
pub(crate) struct ClauseArena {
    clauses: Vec<Clause>,
}

impl ClauseArena {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn add(&mut self, clause: Clause) -> ClauseRef {
        let idx = self.clauses.len();
        self.clauses.push(clause);
        ClauseRef(idx as u32)
    }

    pub(crate) fn get(&self, cref: ClauseRef) -> &Clause {
        &self.clauses[cref.index()]
    }

    pub(crate) fn get_mut(&mut self, cref: ClauseRef) -> &mut Clause {
        &mut self.clauses[cref.index()]
    }

    /// Returns the number of clauses stored in the arena.
    /// Used by SAT-layer test assertions; the production solver tracks
    /// clause count via observer hooks rather than polling the arena.
    #[cfg(test)]
    pub(crate) fn len(&self) -> usize {
        self.clauses.len()
    }
}

#[cfg(test)]
#[path = "clause_tests.rs"]
mod tests;
