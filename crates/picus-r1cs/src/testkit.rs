//! Shared R1CS test-fixture builders.
//!
//! `pub` and gated behind the `testkit` feature (not `#[cfg(test)]`) so it is
//! reachable from other crates' unit and integration tests. Builders use the
//! standard fixture layout: wire 0 is the constant one-wire, `field_size = 32`,
//! all public-I/O counts zero.

use num_bigint::BigUint;

use crate::grammar::{
    Constraint, ConstraintBlock, ConstraintSection, HeaderSection, R1csFile, W2lSection,
};

/// GF(7) prime — the field most fixtures are built over.
#[must_use]
pub fn p7() -> BigUint {
    BigUint::from(7u32)
}

/// The BN128 scalar-field prime — the single source of truth for the constant
/// across test fixtures.
#[must_use]
pub fn bn128() -> BigUint {
    "21888242871839275222246405745257275088548364400416034343698204186575808495617"
        .parse()
        .unwrap()
}

/// Build a constraint block from `(wire_id, factor)` pairs.
#[must_use]
pub fn block(pairs: &[(u32, u32)]) -> ConstraintBlock {
    let wire_ids: Vec<u32> = pairs.iter().map(|&(w, _)| w).collect();
    let factors: Vec<BigUint> = pairs.iter().map(|&(_, f)| BigUint::from(f)).collect();
    ConstraintBlock { wire_ids, factors }
}

/// Empty (zero) constraint block.
#[must_use]
pub fn empty_block() -> ConstraintBlock {
    ConstraintBlock {
        wire_ids: vec![],
        factors: vec![],
    }
}

/// Single-term constraint block: `factor * x_wid`.
#[must_use]
pub fn blk(wid: u32, factor: u32) -> ConstraintBlock {
    ConstraintBlock {
        wire_ids: vec![wid],
        factors: vec![BigUint::from(factor)],
    }
}

/// Empty (zero) constraint block — alias for [`empty_block`].
#[must_use]
pub fn zero_blk() -> ConstraintBlock {
    empty_block()
}

/// Assemble a single constraint from its three blocks.
#[must_use]
pub fn constraint(a: ConstraintBlock, b: ConstraintBlock, c: ConstraintBlock) -> Constraint {
    Constraint { a, b, c }
}

/// Build a minimal in-memory `R1csFile` with the supplied prime, `n_wires`,
/// `inputs`, and constraints. All public-io counts and the label table are
/// left empty; `m_constraints` is derived from `constraints.len()`.
#[must_use]
pub fn r1cs(
    prime: BigUint,
    n_wires: u32,
    inputs: Vec<usize>,
    constraints: Vec<Constraint>,
) -> R1csFile {
    let m = constraints.len() as u32;
    R1csFile {
        magic: *b"r1cs",
        version: 1,
        n_sections: 3,
        header: HeaderSection {
            field_size: 32,
            prime_number: prime,
            n_wires,
            n_pub_out: 0,
            n_pub_in: 0,
            n_prv_in: 0,
            n_labels: 0,
            m_constraints: m,
        },
        constraints: ConstraintSection { constraints },
        w2l: W2lSection { labels: Vec::new() },
        inputs,
        outputs: Vec::new(),
    }
}
