//! The index-keyed `ConstraintSystem` type family — the canonical system
//! shape consumed by the encoder ([`super::encode`]): [`PolyTerm`],
//! [`ConstraintSystem`], and the producer-side [`ConstraintSystemBuilder`].
//! Re-exported from `encoder` so `encoder::ConstraintSystem` etc. resolve here.

use std::collections::HashMap;

use num_bigint::BigUint;

use super::VarIdx;

/// A term in an [`ConstraintSystem`] equality.
///
/// Sparse representation: `vars` lists only variables with non-zero
/// exponent, paired with their exponent. An empty `vars` denotes a
/// constant term.
#[derive(Clone, Debug)]
pub struct PolyTerm {
    pub coeff: BigUint,
    pub vars: Vec<(VarIdx, u16)>,
}

/// Index of an interned UF symbol within one system's
/// [`ConstraintSystem::uf_symbols`].
pub type UfSymbolId = u32;

/// One uninterpreted-function application `result = symbol(args...)`.
/// Args and result are indices into the owning system's `var_names`
/// frame — plain variables only; producers bind compound arguments to
/// fresh variables first. The ONLY axiom the solver assumes is
/// congruence: equal argument tuples imply equal results.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct UfApp {
    pub symbol: UfSymbolId,
    pub args: Vec<VarIdx>,
    pub result: VarIdx,
}

/// Index-keyed constraint system for callers that produce term lists
/// in integer form via [`ConstraintSystemBuilder`].
#[derive(Clone, Debug)]
pub struct ConstraintSystem {
    pub prime: BigUint,
    /// Authoritative variable-name list. `var_names[i as usize]` is
    /// the canonical String name of variable `i`. The encoder uses
    /// this to construct the polynomial ring; downstream model
    /// extraction surfaces the same names back to the caller.
    pub var_names: Vec<String>,
    /// Each equality is `sum(terms) = 0`.
    pub equalities: Vec<Vec<PolyTerm>>,
    /// Each disequality `(a, b)` means `a ≠ b`. The encoder
    /// reserves one Rabinowitsch witness variable per entry,
    /// appended to `var_names` at encoding time.
    pub disequalities: Vec<(VarIdx, VarIdx)>,
    /// Each assignment `(v, val)` means `v = val`.
    pub assignments: Vec<(VarIdx, BigUint)>,
    /// Each bitsum `[b_0, b_1, ..., b_k]` defines an auxiliary
    /// variable `__bitsum_N = sum(2^i · b_i)`. The encoder appends
    /// the aux variable to `var_names`.
    pub bitsums: Vec<Vec<VarIdx>>,
    /// Add `x^p - x = 0` for every ring variable. Honoured by
    /// `encode` only when `prime <= 1000` (matching
    /// `encode_impl`).
    pub add_field_polys: bool,
    /// Authoritative UF symbol table: `uf_symbols[id as usize]` is the
    /// canonical name of [`UfSymbolId`] `id`. Symbols are global to the
    /// system: the same name always denotes the same function.
    pub uf_symbols: Vec<String>,
    /// UF applications riding on the system. They contribute no
    /// polynomial constraints at encode time; the solve entries route
    /// UF-bearing systems to a congruence-aware path, and every Sat
    /// exit re-verifies congruence against these apps.
    pub uf_apps: Vec<UfApp>,
    /// False when a bounded UF expansion (`uf_pair_cap`) covered only a
    /// prefix of the congruence pairs: a Sat model then needs table
    /// certification, and a certification failure is an expected
    /// budget outcome (`Unknown(UfCap)`), not an engine defect.
    /// `true` whenever `uf_apps` is empty.
    pub uf_care_complete: bool,
    /// Set when the producing builder recorded an ill-formed UF
    /// section (arity mismatch). `encode` refuses such a system with
    /// `EngineError::Encoding` instead of solving a different problem.
    pub uf_poisoned: Option<String>,
}

impl ConstraintSystem {
    /// True when the system carries UF applications.
    pub fn has_uf(&self) -> bool {
        !self.uf_apps.is_empty()
    }
}

/// Producer-side builder for [`ConstraintSystem`]. Each
/// producer constructs one builder, interns variable names through
/// [`Self::var`] (deduplicating against the running `var_names`),
/// emits terms as `Vec<PolyTerm>` over the returned indices, and
/// finalises with [`Self::build`]. [`Clone`] so callers like
/// `BooleanQuery::to_disjunct_systems` can fan out per-disjunct
/// builders from a query-level scaffold.
#[derive(Clone, Debug)]
pub struct ConstraintSystemBuilder {
    prime: BigUint,
    var_names: Vec<String>,
    name_to_idx: HashMap<String, VarIdx>,
    equalities: Vec<Vec<PolyTerm>>,
    disequalities: Vec<(VarIdx, VarIdx)>,
    assignments: Vec<(VarIdx, BigUint)>,
    bitsums: Vec<Vec<VarIdx>>,
    add_field_polys: bool,
    uf_symbols: Vec<String>,
    uf_symbol_to_id: HashMap<String, UfSymbolId>,
    /// First-use arity per symbol; a later application with a
    /// different arity poisons the builder (see `uf_poisoned`).
    uf_arity: HashMap<UfSymbolId, usize>,
    uf_apps: Vec<UfApp>,
    uf_care_complete: bool,
    uf_poisoned: Option<String>,
}

impl ConstraintSystemBuilder {
    pub fn new(prime: BigUint) -> Self {
        Self {
            prime,
            var_names: Vec::new(),
            name_to_idx: HashMap::new(),
            equalities: Vec::new(),
            disequalities: Vec::new(),
            assignments: Vec::new(),
            bitsums: Vec::new(),
            add_field_polys: false,
            uf_symbols: Vec::new(),
            uf_symbol_to_id: HashMap::new(),
            uf_arity: HashMap::new(),
            uf_apps: Vec::new(),
            uf_care_complete: true,
            uf_poisoned: None,
        }
    }

    /// Intern a variable name, returning its index. Repeated calls
    /// with the same name return the same index.
    pub fn var(&mut self, name: &str) -> VarIdx {
        if let Some(&idx) = self.name_to_idx.get(name) {
            return idx;
        }
        let idx = self.var_names.len() as VarIdx;
        self.var_names.push(name.to_string());
        self.name_to_idx.insert(name.to_string(), idx);
        idx
    }

    /// Number of variables interned so far.
    pub fn n_vars(&self) -> usize {
        self.var_names.len()
    }

    /// Variable-name frame interned so far. Used by callers like
    /// `BooleanQuery` to feed the SAT-side `AtomTable` for
    /// reverse-resolving `PolyTerm` indices to canonical names.
    pub fn var_names(&self) -> &[String] {
        &self.var_names
    }

    pub fn prime(&self) -> &BigUint {
        &self.prime
    }

    /// Update the builder's prime in place. Used by long-lived
    /// builders (e.g. `SmtSession::builder`) whose prime is only
    /// known after a `define-sort` or first FF-sorted `declare-fun`.
    pub fn set_prime(&mut self, prime: BigUint) {
        self.prime = prime;
    }

    pub fn add_equality(&mut self, terms: Vec<PolyTerm>) {
        self.equalities.push(terms);
    }

    pub fn add_disequality(&mut self, a: VarIdx, b: VarIdx) {
        self.disequalities.push((a, b));
    }

    /// Introduce the witness pair for encoding `lhs != 0`: a fresh
    /// `__diseq_d_{seq}` variable `d` (the caller then constrains
    /// `d = lhs` via [`Self::add_equality`]) and a shared, lazily-created
    /// `__zero` pinned to `0`. Returns `(d, zero)`; the caller asserts the
    /// disequality with `add_disequality(d, zero)`. Centralises the
    /// synthetic-variable naming and the `__zero` lazy-init shared by the
    /// DNF (`BooleanQuery`) and CDCL(T) (`FfTheory`) disequality encoders
    /// so the two cannot drift. `seq` is the caller's per-system
    /// disequality counter (incremented here).
    pub fn fresh_disequality_vars(
        &mut self,
        seq: &mut usize,
        zero_idx: &mut Option<VarIdx>,
    ) -> (VarIdx, VarIdx) {
        let d_idx = self.var(&format!("__diseq_d_{}", *seq));
        *seq += 1;
        let zero = match *zero_idx {
            Some(z) => z,
            None => {
                let z = self.var("__zero");
                self.add_assignment(z, BigUint::from(0u32));
                *zero_idx = Some(z);
                z
            }
        };
        (d_idx, zero)
    }

    pub fn add_assignment(&mut self, v: VarIdx, val: BigUint) {
        self.assignments.push((v, val));
    }

    pub fn add_bitsum(&mut self, bits: Vec<VarIdx>) {
        self.bitsums.push(bits);
    }

    pub fn set_add_field_polys(&mut self, on: bool) {
        self.add_field_polys = on;
    }

    /// Intern a UF symbol name, returning its id. Repeated calls with
    /// the same name return the same id (one function per name — the
    /// invariant cross-copy congruence rests on).
    pub fn uf_symbol(&mut self, name: &str) -> UfSymbolId {
        if let Some(&id) = self.uf_symbol_to_id.get(name) {
            return id;
        }
        let id = self.uf_symbols.len() as UfSymbolId;
        self.uf_symbols.push(name.to_string());
        self.uf_symbol_to_id.insert(name.to_string(), id);
        id
    }

    /// Record the application `result = symbol(args...)`. Args and
    /// result must be plain interned variables (bind compound
    /// arguments to fresh variables first). The first application
    /// fixes the symbol's arity; a mismatched later arity poisons the
    /// builder and `encode` refuses the built system (typed refusal,
    /// never a silent drop).
    pub fn add_uf_app(&mut self, symbol: UfSymbolId, args: Vec<VarIdx>, result: VarIdx) {
        match self.uf_arity.get(&symbol) {
            Some(&k) if k != args.len() => {
                let name = self
                    .uf_symbols
                    .get(symbol as usize)
                    .map(String::as_str)
                    .unwrap_or("<unknown>");
                self.uf_poisoned.get_or_insert_with(|| {
                    format!(
                        "symbol '{}' applied with arity {} after first use with arity {}",
                        name,
                        args.len(),
                        k
                    )
                });
            }
            Some(_) => {}
            None => {
                self.uf_arity.insert(symbol, args.len());
            }
        }
        self.uf_apps.push(UfApp { symbol, args, result });
    }

    pub fn uf_apps(&self) -> &[UfApp] {
        &self.uf_apps
    }

    pub fn uf_symbols(&self) -> &[String] {
        &self.uf_symbols
    }

    /// True when at least one UF application has been recorded.
    pub fn has_uf(&self) -> bool {
        !self.uf_apps.is_empty()
    }

    /// Mark the built system's UF expansion as a bounded prefix (see
    /// [`ConstraintSystem::uf_care_complete`]).
    pub fn set_uf_care_complete(&mut self, complete: bool) {
        self.uf_care_complete = complete;
    }

    /// The ill-formed-UF-section marker, if set (see
    /// [`ConstraintSystem::uf_poisoned`]). Solve entries that bypass
    /// `encode` on the full system (the Boolean/CDCL(T) route) must
    /// consult this and refuse rather than solve a different problem.
    pub fn uf_poisoned(&self) -> Option<&str> {
        self.uf_poisoned.as_deref()
    }

    /// Current UF-section marks `(n_apps, n_symbols)` — the snapshot a
    /// long-lived builder (the SMT session) records at `(push)`.
    pub(crate) fn uf_section_marks(&self) -> (usize, usize) {
        (self.uf_apps.len(), self.uf_symbols.len())
    }

    /// Truncate the UF section back to marks from
    /// [`Self::uf_section_marks`] (the `(pop)` counterpart). Arity
    /// records and the poison marker are recomputed from the surviving
    /// applications, so a mismatch introduced entirely above the mark
    /// is forgotten with it.
    pub(crate) fn truncate_uf_section(&mut self, n_apps: usize, n_symbols: usize) {
        self.uf_apps.truncate(n_apps);
        for name in self.uf_symbols.drain(n_symbols..) {
            self.uf_symbol_to_id.remove(&name);
        }
        self.uf_arity.clear();
        self.uf_poisoned = None;
        let apps = std::mem::take(&mut self.uf_apps);
        for app in &apps {
            match self.uf_arity.get(&app.symbol) {
                Some(&k) if k != app.args.len() => {
                    let name = self
                        .uf_symbols
                        .get(app.symbol as usize)
                        .map(String::as_str)
                        .unwrap_or("<unknown>");
                    self.uf_poisoned.get_or_insert_with(|| {
                        format!(
                            "symbol '{}' applied with arity {} after first use with arity {}",
                            name,
                            app.args.len(),
                            k
                        )
                    });
                }
                Some(_) => {}
                None => {
                    self.uf_arity.insert(app.symbol, app.args.len());
                }
            }
        }
        self.uf_apps = apps;
    }

    pub fn build(self) -> ConstraintSystem {
        ConstraintSystem {
            prime: self.prime,
            var_names: self.var_names,
            equalities: self.equalities,
            disequalities: self.disequalities,
            assignments: self.assignments,
            bitsums: self.bitsums,
            add_field_polys: self.add_field_polys,
            uf_symbols: self.uf_symbols,
            uf_apps: self.uf_apps,
            uf_care_complete: self.uf_care_complete,
            uf_poisoned: self.uf_poisoned,
        }
    }

}

#[cfg(test)]
#[path = "constraint_system_tests.rs"]
mod tests;
