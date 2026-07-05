//! CDCL Boolean SAT solver. The `cdclt` module composes [`Solver`] with
//! a theory plug-in for CDCL(T).
//!
//! Algorithm: two-literal watching for unit propagation, 1-UIP conflict
//! analysis with clause learning, VSIDS variable-order heap with phase
//! saving, and Luby restarts (base 100). Learnt clauses are not deleted.

pub(crate) mod clause;
pub(crate) mod lit;
pub(crate) mod solver;

pub(crate) use lit::{LBool, Lit, Var};
pub(crate) use solver::Solver;
