//! Solver-side state cache for amortising fixed work across multiple
//! `solve` calls with the same constraint side.
//!
//! The constraint side of a [`ConstraintSystem`] is hashed via
//! [`digest_constraint_side`]; a matching cache reuses the
//! prior split-GB and encodes only the per-query disequalities
//! (Rabinowitsch polynomials). Sub-iter resumability: when a fresh
//! cache build is cancelled mid-build, the per-partition
//! `IncrementalGB` in-flight state is preserved as a
//! `PartialBuild` and resumed on the next solve call with the
//! matching digest.

use std::collections::HashMap;
use std::sync::Arc;

use crate::split_gb::bitprop::{BitProp, BitPropState};
use crate::solve::{SolveOutcome, UnknownCause};
use crate::frontend::encoder::{
    encode, encode_constraint_side, ConstraintSystem,
};
use crate::gb::ideal::{incremental_engine, IncrementalGB};
use crate::gb::ideal::{interreduce_basis, ring_for_order, unwrap_dense_vec, wrap_dense_vec, Ideal};
use crate::gb::model;
use crate::metric;
use crate::profile::NATIVE_FF;
use crate::poly::{FfPolyRing, Poly};
use crate::split_gb::{
    build_partitions, classify_propagation, max_fixpoint_iters, seed_self_membership,
    split_find_zero_cancel, split_gb_cancel, split_gb_extend_cancel, Propagate, SplitFindZeroOutcome,
};
use crate::timeout::CancelToken;

/// Snapshot of the knobs baked into a cached artifact: the ring's
/// representation and order (`poly_repr`, `dynamic_order`,
/// `matrix_elim_order` shape the encoded ring) and the build-shaping
/// engine selection (`gb_strategy`, `use_f4`). A cache entry built
/// under one snapshot must not serve a solve running under another —
/// query-time knobs would read the new config while the basis
/// reflects the old one (a torn config, invalidating in-process A/B
/// flips). Knobs whose effect is re-read fresh on every query-time
/// extend (`reducer_index_cache`, the F4 sub-knobs, `frobenius_cache`,
/// …) are deliberately NOT fingerprinted: flipping them already takes
/// effect on the next call, and fingerprinting them would only force
/// spurious rebuilds.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct BasisKnobs {
    poly_repr: crate::config::ReprKind,
    gb_strategy: crate::config::GbStrategy,
    use_f4: bool,
    dynamic_order: bool,
    matrix_elim_order: bool,
}

impl BasisKnobs {
    fn current() -> Self {
        crate::config::with(|c| BasisKnobs {
            poly_repr: c.poly_repr,
            gb_strategy: c.gb_strategy,
            use_f4: c.use_f4,
            dynamic_order: c.dynamic_order,
            matrix_elim_order: c.matrix_elim_order,
        })
    }
}

/// Cached state computed from the constraint side of one
/// [`ConstraintSystem`] (everything except `disequalities`).
///
/// UF-bearing digests reach this cache only through
/// [`IncrementalSolverContext::probe_unsat_uf`] (the `solve` entry
/// routes them to the Boolean path), so the UF fields below are empty
/// on every base a plain `solve` can consult. Once the closure pass
/// has run, `split_gb_owned` is extended with congruence-derived
/// polynomials — entailed by FF ∧ congruence, NOT by FF alone — which
/// is sound precisely because only the Unsat-only probe reads such a
/// base.
pub(crate) struct CachedBase {
    pub poly_ring: Arc<FfPolyRing>,
    pub var_map: HashMap<String, usize>,
    /// Polynomials encoded from equalities, assignments, bitsum-defs,
    /// and (optionally) field polys — but NOT from disequalities.
    pub constraint_polys: Vec<Poly>,
    pub bitsum_polys: Vec<Poly>,
    /// Per-partition basis polys: `split_gb_owned[0]` = partition 0
    /// (linear), `split_gb_owned[1]` = partition 1 (full).
    pub split_gb_owned: Vec<Vec<Poly>>,
    pub bit_prop_state: BitPropState,
    pub digest: u128,
    knobs: BasisKnobs,
    /// UF applications in the cached ring frame (digest-covered).
    pub uf_apps: Vec<crate::frontend::encoder::UfApp>,
    /// Congruence-derived polys `r_i − r_j` appended by the closure
    /// pass (bookkeeping; the polys also live in `split_gb_owned`
    /// after the extend).
    pub uf_derived: Vec<Poly>,
    /// True once the closure fixpoint ran to completion (or its round
    /// cap); a cancelled closure leaves this false and discards its
    /// partial work so the retry is deterministic.
    pub closure_done: bool,
}

/// Partial GB build state preserved across solve calls. Used when the
/// fast-path build is cancelled mid-build; subsequent calls with the
/// same digest resume via `continue_partial`, which keeps the
/// in-flight [`IncrementalGB`] per partition so the open S-pair queue
/// is not lost.
struct PartialBuild {
    digest: u128,
    knobs: BasisKnobs,
    poly_ring: Arc<FfPolyRing>,
    var_map: HashMap<String, usize>,
    constraint_polys: Vec<Poly>,
    bitsum_polys: Vec<Poly>,
    bit_prop_state: BitPropState,
    inflight: Vec<IncrementalGB>,
    pending: Vec<Vec<Poly>>,
    contains_memo: std::collections::HashSet<(u64, usize)>,
    /// Consecutive resume attempts that made no progress (no extend work,
    /// no new propagations). At [`NO_PROGRESS_RESUME_CAP`] the build is
    /// declared failed so the query falls back to the stateless path
    /// instead of returning Unknown on every future call.
    no_progress_resumes: u32,
}

/// See [`PartialBuild::no_progress_resumes`].
const NO_PROGRESS_RESUME_CAP: u32 = 3;

#[derive(Default)]
pub struct IncrementalSolverContext {
    cached_base: Option<CachedBase>,
    /// Digest of the most recent `solve` call's constraint side.
    /// The cache builds only when two consecutive calls share a
    /// digest; circuits whose per-call constraint sides never repeat
    /// skip the cache-build cost entirely.
    last_digest: Option<u128>,
    /// In-flight partial GB build saved from a cancelled call. Resumed
    /// on the next call with the same digest.
    partial_build: Option<PartialBuild>,
    /// The UF probe's own base + streak slots, fully separate from the
    /// UF-free fields above: a UF-bearing probe must never evict a
    /// UF-free base or perturb its build-on-second-sighting streak
    /// (mixed workloads would otherwise lose UF-free caching).
    uf_cached_base: Option<CachedBase>,
    uf_last_digest: Option<u128>,
}

impl IncrementalSolverContext {
    pub fn new() -> Self {
        Self {
            cached_base: None,
            last_digest: None,
            partial_build: None,
            uf_cached_base: None,
            uf_last_digest: None,
        }
    }

    pub fn invalidate(&mut self) {
        self.cached_base = None;
        self.partial_build = None;
        self.uf_cached_base = None;
    }

    pub fn solve(&mut self, cs: &ConstraintSystem, cancel: &CancelToken) -> SolveOutcome {
        // The GB pipeline behind this cache cannot host UF congruence;
        // route UF-bearing systems to the Boolean/CDCL(T) entry at full
        // capability instead of refusing (near-dead under the native
        // seam's own routing; kept as a fail-closed guard for direct
        // facade callers).
        if cs.has_uf() {
            let query = crate::frontend::formula::boolean_query_from_constraint_system(cs);
            return crate::boolean::solve_boolean_query(&query, cancel);
        }
        let digest = digest_constraint_side(cs);

        // A digest hit only counts when the basis-shaping knobs still
        // match the snapshot the artifact was built under; a config
        // flip between solves forces a rebuild instead of running the
        // query on a stale-config basis.
        let knobs = BasisKnobs::current();
        let cache_matches =
            matches!(&self.cached_base, Some(c) if c.digest == digest && c.knobs == knobs);
        let partial_matches =
            matches!(&self.partial_build, Some(p) if p.digest == digest && p.knobs == knobs);
        let prev_digest_matches = self.last_digest == Some(digest);
        let should_build = !cache_matches && !partial_matches && prev_digest_matches;
        self.last_digest = Some(digest);

        // First-time digest with no prior repeats: skip the cache-build
        // cost.
        if !cache_matches && !partial_matches && !should_build {
            self.cached_base = None;
            self.partial_build = None;
            return stateless_solve(cs, cancel);
        }

        // Resume an in-flight partial build.
        if !cache_matches && partial_matches {
            metric::incr!(NATIVE_FF.cache_partial_resumes);
            let mut partial = self.partial_build.take().unwrap();
            let outcome = {
                metric::timer!(NATIVE_FF.cache_rebuild_time_ns);
                continue_partial(&mut partial, cancel)
            };
            match outcome {
                ResumeOutcome::Complete(cached) => {
                    metric::incr!(NATIVE_FF.cache_partial_completions);
                    self.cached_base = Some(cached);
                }
                ResumeOutcome::StillPartial => {
                    self.partial_build = Some(partial);
                    return SolveOutcome::Unknown(UnknownCause::Cancelled);
                }
                ResumeOutcome::Failed => {
                    return stateless_solve(cs, cancel);
                }
            }
        } else if !cache_matches {
            // Fresh build attempt via the fast path.
            metric::incr!(NATIVE_FF.distinct_cs_digests);
            {
                metric::timer!(NATIVE_FF.cache_rebuild_time_ns);
                match self.rebuild_base(cs, digest, cancel) {
                    Ok(()) => {}
                    Err(()) => {
                        return stateless_solve(cs, cancel);
                    }
                }
            }
            // If the rebuild was cancelled, `rebuild_base` left
            // `partial_build` populated for resumption.
            if self.partial_build.is_some() && self.cached_base.is_none() {
                return SolveOutcome::Unknown(UnknownCause::Cancelled);
            }
        } else {
            metric::incr!(NATIVE_FF.cache_hits);
        }

        let cached = self.cached_base.as_ref().expect("cache must be built");
        let outcome = {
            metric::timer!(NATIVE_FF.cache_query_diff_time_ns);
            solve_with_cached(cached, cs, cancel)
        };
        outcome
    }

    /// UNSAT-only propagation-stage probe for UF-bearing systems:
    /// returns `Some(Unsat(None))` or `None` — never Sat, never a
    /// surfaced Unknown. Sound to consult under ANY disjunction state:
    /// it reads only the conjunctive constraint side plus the query
    /// disequalities, and UNSAT of a constraint subset implies UNSAT
    /// of the whole.
    ///
    /// Mechanics: the same digest / build-on-second-consecutive-digest
    /// policy as [`Self::solve`] (UF digests never collide with UF-free
    /// ones — the digest covers the UF section); then a one-time
    /// congruence-closure pass over the finalized base — every
    /// same-symbol application pair whose argument differences all
    /// reduce to zero against the cached bases contributes the derived
    /// poly `r_i − r_j` (entailed by FF ∧ congruence), extended into
    /// the split-GB and iterated to fixpoint. Query time is one
    /// membership reduction per disequality. Gated by the `uf_closure`
    /// knob (read only when applications are present; deliberately NOT
    /// in `BasisKnobs` — the derived artifact is a deterministic
    /// function of digest-covered input, so a flip cannot create
    /// staleness and must not evict UF-free caches).
    pub fn probe_unsat_uf(
        &mut self,
        cs: &ConstraintSystem,
        cancel: &CancelToken,
    ) -> Option<SolveOutcome> {
        if !cs.has_uf() || cs.uf_poisoned.is_some() {
            return None;
        }
        if !crate::config::with(|c| c.uf_enabled) {
            // Kill switch: with UF support off no congruence-derived
            // verdict may surface from any entry, this one included.
            return None;
        }
        if !crate::config::with(|c| c.uf_closure) {
            return None;
        }
        let digest = digest_constraint_side(cs);
        let knobs = BasisKnobs::current();
        let cache_matches =
            matches!(&self.uf_cached_base, Some(c) if c.digest == digest && c.knobs == knobs);
        if !cache_matches {
            let prev_digest_matches = self.uf_last_digest == Some(digest);
            self.uf_last_digest = Some(digest);
            if !prev_digest_matches {
                // First sighting of this constraint side: skip the
                // build cost, exactly like `solve`.
                return None;
            }
            let encoded = encode_constraint_side(cs).ok()?;
            if cancel.is_cancelled() {
                return None;
            }
            let (gens, _prov) = build_partitions(
                &encoded.poly_ring,
                &encoded.polynomials,
                &encoded.bitsum_polys,
            );
            let mut bit_prop = BitProp::new(&encoded.poly_ring);
            bit_prop.scan_polys(&encoded.polynomials);
            bit_prop.scan_polys(&encoded.bitsum_polys);
            match split_gb_cancel(&encoded.poly_ring, gens, &mut bit_prop, cancel) {
                Ok(split_basis) => {
                    let split_gb_owned: Vec<Vec<Poly>> = split_basis
                        .into_iter()
                        .map(|ideal| {
                            ideal
                                .basis
                                .iter()
                                .map(|p| encoded.poly_ring.ring.clone_el(p))
                                .collect()
                        })
                        .collect();
                    let bit_prop_state = bit_prop.to_state();
                    self.uf_cached_base = Some(CachedBase {
                        poly_ring: Arc::new(encoded.poly_ring),
                        var_map: encoded.var_map,
                        constraint_polys: encoded.polynomials,
                        bitsum_polys: encoded.bitsum_polys,
                        split_gb_owned,
                        bit_prop_state,
                        digest,
                        knobs,
                        uf_apps: encoded.uf_apps,
                        uf_derived: Vec::new(),
                        closure_done: false,
                    });
                }
                // A cancelled probe build is simply not cached (no
                // partial-build plumbing on this path); the retry is
                // deterministic.
                Err(_) => return None,
            }
        }
        let cached = self.uf_cached_base.as_mut().expect("built or matched above");
        if cached.closure_done {
            metric::incr!(NATIVE_FF.uf_closure_reuses);
        } else if !run_uf_closure(cached, cancel) {
            return None;
        }
        // Whole-ring after the congruence extend: FF ∧ congruence is
        // already unsatisfiable, before any disequality.
        if cached
            .split_gb_owned
            .iter()
            .flatten()
            .any(|p| !p.is_zero() && p.is_constant())
        {
            metric::incr!(NATIVE_FF.uf_probe_fastpath_unsat);
            return Some(SolveOutcome::Unsat(None));
        }
        let hit = membership_fastpath_unsat(cached, cs, cancel);
        if hit.is_some() {
            metric::incr!(NATIVE_FF.uf_probe_fastpath_unsat);
        }
        hit
    }

    /// Build the cache via the fast path ([`split_gb_cancel`]). On
    /// cancellation, save a `PartialBuild` so the next solve call with
    /// matching digest can resume via [`continue_partial`].
    fn rebuild_base(
        &mut self,
        cs: &ConstraintSystem,
        digest: u128,
        cancel: &CancelToken,
    ) -> Result<(), ()> {
        self.cached_base = None;
        self.partial_build = None;

        // Encode the constraint side only: the cache entry is keyed on
        // `digest_constraint_side(cs)`, so the encoded ring must contain
        // everything *except* the per-query Rabinowitsch polynomials.
        // `encode_constraint_side` still reserves the `__w_diseq_i`
        // variable slots so [`encode_query_disequalities`] can build the
        // Rabinowitsch polynomial in this ring later.
        let encoded = match encode_constraint_side(cs) {
            Ok(e) => e,
            Err(_) => return Err(()),
        };
        if cancel.is_cancelled() {
            return Err(());
        }

        // partition 0 (linear) = bitsum polys + admitted originals; partition 1
        // (nonlinear) = all originals. The provenance is unused here: the
        // cached path does not extract an UNSAT core.
        let (gens, _prov) =
            build_partitions(&encoded.poly_ring, &encoded.polynomials, &encoded.bitsum_polys);

        let mut bit_prop = BitProp::new(&encoded.poly_ring);
        // Both sets are scanned, matching the stateless path (BitProp
        // facts feed the split-GB fixpoint and model search). Order
        // matters: phase 1 populates the bit-hint set that phase 2 chain
        // parsing depends on, so originals go first.
        bit_prop.scan_polys(&encoded.polynomials);
        bit_prop.scan_polys(&encoded.bitsum_polys);

        // Fast-path build. On cancel, `split_gb_cancel` returns
        // `Cancelled` and we transition to the resumable path.
        match split_gb_cancel(&encoded.poly_ring, gens.clone(), &mut bit_prop, cancel) {
            Ok(split_basis) => {
                let split_gb_owned: Vec<Vec<Poly>> = split_basis
                    .into_iter()
                    .map(|ideal| {
                        ideal
                            .basis
                            .iter()
                            .map(|p| encoded.poly_ring.ring.clone_el(p))
                            .collect()
                    })
                    .collect();
                let bit_prop_state = bit_prop.to_state();
                self.cached_base = Some(CachedBase {
                    poly_ring: Arc::new(encoded.poly_ring),
                    var_map: encoded.var_map,
                    constraint_polys: encoded.polynomials,
                    bitsum_polys: encoded.bitsum_polys,
                    split_gb_owned,
                    bit_prop_state,
                    digest,
                    knobs: BasisKnobs::current(),
                    uf_apps: encoded.uf_apps,
                    uf_derived: Vec::new(),
                    closure_done: false,
                });
                Ok(())
            }
            Err(_) => {
                // Build was cancelled. Save the encoding artifacts plus
                // initial generators as a `PartialBuild` so the next
                // call can resume via `continue_partial`. The S-pair
                // work from this attempt is lost (the IGBs inside
                // `split_gb_cancel` are dropped); subsequent resume
                // calls accumulate progress.
                let ring =
                    ring_for_order(&encoded.poly_ring, crate::gb::ideal::solve_order(&encoded.poly_ring));
                // The front-door constructor pins the incremental policy
                // (use_f4 off): a resumed build must not run a different
                // inner engine than the same build uncancelled. The token
                // is re-attached per resume by `continue_partial`.
                let inflight = vec![
                    incremental_engine(ring.clone(), None),
                    incremental_engine(ring, None),
                ];
                let pending = gens;
                let bit_prop_state = bit_prop.to_state();
                self.partial_build = Some(PartialBuild {
                    digest,
                    knobs: BasisKnobs::current(),
                    poly_ring: Arc::new(encoded.poly_ring),
                    var_map: encoded.var_map,
                    constraint_polys: encoded.polynomials,
                    bitsum_polys: encoded.bitsum_polys,
                    bit_prop_state,
                    inflight,
                    pending,
                    contains_memo: std::collections::HashSet::new(),
                    no_progress_resumes: 0,
                });
                // Returning Ok here lets the caller know the rebuild
                // attempt is captured (in partial_build); the solve()
                // entry point will return Unknown for this query.
                Ok(())
            }
        }
    }
}

/// One-time congruence-closure pass over a finalized UF-bearing base
/// (see [`IncrementalSolverContext::probe_unsat_uf`]). Returns `true`
/// when the fixpoint completed (or hit its round cap — the closure is
/// then merely incomplete, still sound); `false` when cancelled or the
/// extend failed, in which case ALL partial work is rolled back
/// (bases, derived list, bit-prop state) so the retry is
/// deterministic.
fn run_uf_closure(cached: &mut CachedBase, cancel: &CancelToken) -> bool {
    // Same-symbol, same-arity application pairs, deterministic order.
    let mut pairs: Vec<(usize, usize)> = Vec::new();
    for i in 0..cached.uf_apps.len() {
        for j in (i + 1)..cached.uf_apps.len() {
            let (ai, aj) = (&cached.uf_apps[i], &cached.uf_apps[j]);
            if ai.symbol == aj.symbol && ai.args.len() == aj.args.len() {
                pairs.push((i, j));
            }
        }
    }
    if pairs.is_empty() {
        cached.closure_done = true;
        return true;
    }
    // The same budget that bounds Ackermann expansion and care-atom
    // interning bounds the closure's pair set (deterministic prefix;
    // fewer pairs only means fewer derived polys — still sound).
    let pair_cap = crate::config::with(|c| c.uf_pair_cap) as usize;
    if pairs.len() > pair_cap {
        pairs.truncate(pair_cap);
    }
    let rounds_cap = std::cmp::min(64, pairs.len());
    let poly_ring = Arc::clone(&cached.poly_ring);
    let ring = poly_ring.ctx();
    // Snapshot for the cancel rollback.
    let snapshot: Vec<Vec<Poly>> = cached
        .split_gb_owned
        .iter()
        .map(|part| part.iter().map(|p| poly_ring.ring.clone_el(p)).collect())
        .collect();
    let bp_snapshot = cached.bit_prop_state.clone();
    let mut bit_prop = BitProp::from_state(&poly_ring, cached.bit_prop_state.clone());
    let mut derived_pairs: std::collections::HashSet<(usize, usize)> =
        std::collections::HashSet::new();

    let mut cancelled = false;
    'rounds: for _round in 0..rounds_cap {
        let mut new_polys: Vec<Poly> = Vec::new();
        {
            let mut divisors: Vec<&Poly> = Vec::new();
            for part in &cached.split_gb_owned {
                for p in part {
                    divisors.push(p);
                }
            }
            for p in &cached.bitsum_polys {
                divisors.push(p);
            }
            for &(i, j) in &pairs {
                if cancel.is_cancelled() {
                    cancelled = true;
                    break 'rounds;
                }
                if derived_pairs.contains(&(i, j)) {
                    continue;
                }
                let (ai, aj) = (&cached.uf_apps[i], &cached.uf_apps[j]);
                let mut all_zero = true;
                for (&x, &y) in ai.args.iter().zip(aj.args.iter()) {
                    if x == y {
                        continue;
                    }
                    if divisors.is_empty() {
                        all_zero = false;
                        break;
                    }
                    let diff =
                        poly_ring.sub(poly_ring.var(x as usize), poly_ring.var(y as usize));
                    let rem = diff.reduce_by_refs_cancel(&divisors, ring, cancel);
                    if cancel.is_cancelled() {
                        cancelled = true;
                        break 'rounds;
                    }
                    if !rem.is_zero() {
                        all_zero = false;
                        break;
                    }
                }
                if !all_zero {
                    continue;
                }
                derived_pairs.insert((i, j));
                if ai.result == aj.result {
                    continue;
                }
                // Entailed by FF ∧ congruence: equal argument tuples
                // (proved by membership) force equal results.
                let dp = poly_ring
                    .sub(poly_ring.var(ai.result as usize), poly_ring.var(aj.result as usize));
                new_polys.push(dp);
            }
        }
        if new_polys.is_empty() {
            break;
        }
        for p in &new_polys {
            cached.uf_derived.push(poly_ring.ring.clone_el(p));
        }
        let starting: Vec<Ideal> = cached
            .split_gb_owned
            .iter()
            .map(|polys| {
                let cloned: Vec<Poly> =
                    polys.iter().map(|p| poly_ring.ring.clone_el(p)).collect();
                Ideal::from_gb(&poly_ring, cloned)
            })
            .collect();
        let k = starting.len();
        let routed = crate::split_gb::route_query_polys(&poly_ring, k, &new_polys);
        match split_gb_extend_cancel(&poly_ring, starting, routed, &mut bit_prop, cancel) {
            Ok(new_basis) => {
                // A GB engine failure surfaces here as Ok with an
                // EMPTY partition (`GbOutcome::Failed` maps to an
                // empty basis inside the extend). Extending a
                // non-empty partition can never legitimately empty it
                // (reduced-to-zero inputs leave it unchanged; a
                // whole-ring result contains a constant), so
                // empty-after-non-empty is exactly the failure
                // sentinel — roll back instead of persisting a gutted
                // base that every later probe would trust.
                let gutted = new_basis
                    .iter()
                    .zip(cached.split_gb_owned.iter())
                    .any(|(ideal, before)| ideal.basis.is_empty() && !before.is_empty());
                if gutted {
                    log::warn!(
                        "uf closure: extend emptied a non-empty partition (engine                          failure); rolling back the closure pass"
                    );
                    cancelled = true;
                    break;
                }
                cached.split_gb_owned = new_basis
                    .into_iter()
                    .map(|ideal| {
                        ideal
                            .basis
                            .iter()
                            .map(|p| poly_ring.ring.clone_el(p))
                            .collect()
                    })
                    .collect();
            }
            Err(_) => {
                cancelled = true;
                break;
            }
        }
    }

    if cancelled {
        cached.split_gb_owned = snapshot;
        cached.uf_derived.clear();
        cached.bit_prop_state = bp_snapshot;
        return false;
    }
    cached.bit_prop_state = bit_prop.to_state();
    cached.closure_done = true;
    true
}

enum ResumeOutcome {
    Complete(CachedBase),
    StillPartial,
    Failed,
}

/// Resume a partial build. Re-attaches the new cancel token to all
/// in-flight `IncrementalGB`s, runs the fixpoint loop. On completion,
/// produces a `CachedBase`. On further cancellation (timeout), the
/// partial state is updated in place and `StillPartial` is returned.
/// Non-timeout engine errors, fixpoint-cap exhaustion, and
/// [`NO_PROGRESS_RESUME_CAP`] consecutive stalled resumes return
/// `Failed`, dropping the partial so the query is answered statelessly
/// instead of pinning every future identical query to Unknown.
fn continue_partial(partial: &mut PartialBuild, cancel: &CancelToken) -> ResumeOutcome {
    let mut made_progress = false;
    let out = continue_partial_inner(partial, cancel, &mut made_progress);
    if matches!(out, ResumeOutcome::StillPartial) {
        if made_progress {
            partial.no_progress_resumes = 0;
        } else {
            partial.no_progress_resumes += 1;
            if partial.no_progress_resumes >= NO_PROGRESS_RESUME_CAP {
                log::warn!(
                    "continue_partial: {} consecutive resumes made no progress; \
                     dropping the partial build",
                    partial.no_progress_resumes
                );
                return ResumeOutcome::Failed;
            }
        }
    }
    out
}

fn continue_partial_inner(
    partial: &mut PartialBuild,
    cancel: &CancelToken,
    made_progress: &mut bool,
) -> ResumeOutcome {
    for igb in partial.inflight.iter_mut() {
        igb.set_cancel_token(Some(cancel.clone()));
    }
    let poly_ring: &FfPolyRing = &partial.poly_ring;
    let k = partial.inflight.len();
    let bit_prop = BitProp::from_state(poly_ring, partial.bit_prop_state.clone());

    let iter_cap = max_fixpoint_iters(k);
    let mut fixpoint_iter: u64 = 0;
    loop {
        if cancel.is_cancelled() {
            partial.bit_prop_state = bit_prop.to_state();
            return ResumeOutcome::StillPartial;
        }
        fixpoint_iter += 1;
        if fixpoint_iter > iter_cap {
            // Same digest ⇒ same cap: retrying the resume can never get
            // further, so a StillPartial here would be a permanent
            // per-digest Unknown. The stateless path has its own cap
            // semantics and still produces a verdict.
            log::warn!("continue_partial: fixpoint cap reached; falling back to stateless solve");
            return ResumeOutcome::Failed;
        }

        let mut any_extend_work = false;
        for i in 0..k {
            if cancel.is_cancelled() {
                partial.bit_prop_state = bit_prop.to_state();
                return ResumeOutcome::StillPartial;
            }
            let pending_i = std::mem::take(&mut partial.pending[i]);
            let has_pending = !pending_i.is_empty();
            let has_open = !partial.inflight[i].is_quiescent();
            if !has_pending && !has_open {
                continue;
            }
            any_extend_work = true;
            *made_progress = true;
            let surviving: Vec<Poly> = if has_pending {
                let basis = wrap_dense_vec(partial.inflight[i].basis());
                if basis.is_empty() {
                    pending_i
                } else {
                    let basis_refs: Vec<&Poly> = basis.iter().collect();
                    let ring = poly_ring.ctx();
                    pending_i
                        .into_iter()
                        .map(|p| p.reduce_by_refs_cancel(&basis_refs, ring, cancel))
                        .filter(|p| !p.is_zero())
                        .collect()
                }
            } else {
                Vec::new()
            };
            if cancel.is_cancelled() {
                partial.pending[i] = surviving;
                partial.bit_prop_state = bit_prop.to_state();
                return ResumeOutcome::StillPartial;
            }

            let res = if !surviving.is_empty() {
                partial.inflight[i].add_generators(unwrap_dense_vec(surviving, poly_ring.ctx()))
            } else {
                partial.inflight[i].run_only()
            };
            if let Err(e) = res {
                if matches!(e, crate::EngineError::Timeout) {
                    partial.bit_prop_state = bit_prop.to_state();
                    return ResumeOutcome::StillPartial;
                }
                // A non-timeout engine failure is not resumable: the
                // same input will fail the same way on every retry.
                log::warn!("continue_partial: engine error, dropping the partial build: {}", e);
                return ResumeOutcome::Failed;
            }
        }

        if cancel.is_cancelled() {
            partial.bit_prop_state = bit_prop.to_state();
            return ResumeOutcome::StillPartial;
        }
        if partial.inflight.iter().any(|igb| igb.is_trivial()) {
            break;
        }

        let split_basis: Vec<Ideal> = partial
            .inflight
            .iter()
            .map(|igb| Ideal::from_gb(poly_ring, wrap_dense_vec(igb.basis())))
            .collect();
        seed_self_membership(&mut partial.contains_memo, &split_basis);

        let bit_eqs = bit_prop.get_bit_equalities_with_cancel(&split_basis, Some(cancel));
        if cancel.is_cancelled() {
            partial.bit_prop_state = bit_prop.to_state();
            return ResumeOutcome::StillPartial;
        }
        // Candidates by reference; cloned only in the NewGenerator arm
        // (mirroring `run_fixpoint`).
        let mut to_propagate: Vec<&Poly> = bit_eqs.iter().collect();
        for b in &split_basis {
            for p in &b.basis {
                to_propagate.push(p);
            }
        }

        let mut any_new = false;
        for &p in &to_propagate {
            if cancel.is_cancelled() {
                partial.bit_prop_state = bit_prop.to_state();
                return ResumeOutcome::StillPartial;
            }
            let p_hash = p.content_hash();
            for j in 0..k {
                if classify_propagation(
                    poly_ring, &split_basis[j], j, p, p_hash, &mut partial.contains_memo, cancel,
                ) == Propagate::NewGenerator {
                    partial.pending[j].push(poly_ring.ring.clone_el(p));
                    any_new = true;
                    *made_progress = true;
                }
            }
        }

        if !any_new && !any_extend_work {
            break;
        }
        if !any_new {
            continue;
        }
    }

    if partial.inflight.iter().all(|igb| igb.is_quiescent())
        && partial.pending.iter().all(|p| p.is_empty())
    {
        // Build the CachedBase. Take ownership of all the partial's
        // fields via std::mem::replace.
        let dummy_partial = PartialBuild {
            digest: 0,
            knobs: partial.knobs,
            poly_ring: partial.poly_ring.clone(),
            var_map: HashMap::new(),
            constraint_polys: Vec::new(),
            bitsum_polys: Vec::new(),
            bit_prop_state: partial.bit_prop_state.clone(),
            inflight: Vec::new(),
            pending: Vec::new(),
            contains_memo: std::collections::HashSet::new(),
            no_progress_resumes: 0,
        };
        let owned = std::mem::replace(partial, dummy_partial);
        match finalize_partial(owned) {
            Some(c) => ResumeOutcome::Complete(c),
            None => ResumeOutcome::Failed,
        }
    } else {
        partial.bit_prop_state = bit_prop.to_state();
        ResumeOutcome::StillPartial
    }
}

/// Convert a quiescent partial build into a `CachedBase`. Performs a
/// final inter-reduce on each partition's basis to produce the
/// canonical reduced GB.
///
/// Deliberately token-free: the input bases are quiescent, so the
/// remaining work is one bounded inter-reduce per partition, and a
/// cancellable inter-reduce that aborted midway must not be cached — a
/// half-reduced basis persisted into `CachedBase` would feed later
/// verdicts. Run to completion instead.
fn finalize_partial(partial: PartialBuild) -> Option<CachedBase> {
    let cancel = CancelToken::none();
    let poly_ring: &FfPolyRing = &partial.poly_ring;
    let mut split_gb_owned: Vec<Vec<Poly>> = Vec::with_capacity(partial.inflight.len());
    for igb in partial.inflight.iter() {
        let basis = wrap_dense_vec(igb.basis());
        let reduced = interreduce_basis(poly_ring, basis, &cancel);
        split_gb_owned.push(reduced);
    }
    Some(CachedBase {
        poly_ring: partial.poly_ring,
        var_map: partial.var_map,
        constraint_polys: partial.constraint_polys,
        bitsum_polys: partial.bitsum_polys,
        split_gb_owned,
        bit_prop_state: partial.bit_prop_state,
        digest: partial.digest,
        // The artifact keeps the snapshot it was BUILT under, not the
        // config at finalization time — a flip mid-resume must
        // invalidate on the next digest check.
        knobs: partial.knobs,
        // Partial builds exist only on the UF-free `solve` path (the
        // probe never saves partials), so the UF section is empty.
        uf_apps: Vec::new(),
        uf_derived: Vec::new(),
        closure_done: false,
    })
}

fn encode_query_disequalities(
    cs: &ConstraintSystem,
    poly_ring: &FfPolyRing,
    var_map: &HashMap<String, usize>,
) -> Result<Vec<Poly>, String> {
    let mut out = Vec::with_capacity(cs.disequalities.len());
    for (i, &(a, b)) in cs.disequalities.iter().enumerate() {
        // Translate the query's producer-frame VarIdx into the
        // cached ring's frame via name lookup. The ring's slot order is
        // `cs.var_names` order followed by appended aux vars
        // (`__w_diseq_*` / `__bitsum_*`); `encode_impl` does not sort.
        // The integer `a`/`b` index `cs.var_names`, not ring slots, so
        // they must be re-resolved by name through `var_map`.
        let a_name = cs
            .var_names
            .get(a as usize)
            .ok_or_else(|| format!("disequality refs var_idx {} but cs.var_names has {} entries", a, cs.var_names.len()))?;
        let b_name = cs
            .var_names
            .get(b as usize)
            .ok_or_else(|| format!("disequality refs var_idx {} but cs.var_names has {} entries", b, cs.var_names.len()))?;
        let a_idx = *var_map
            .get(a_name)
            .ok_or_else(|| format!("cached var_map missing: {}", a_name))?;
        let b_idx = *var_map
            .get(b_name)
            .ok_or_else(|| format!("cached var_map missing: {}", b_name))?;
        let w_name = format!("__w_diseq_{}", i);
        let w_idx = *var_map
            .get(&w_name)
            .ok_or_else(|| format!("cached var_map missing: {}", w_name))?;
        let diff = poly_ring.sub(poly_ring.var(a_idx), poly_ring.var(b_idx));
        let prod = poly_ring.mul(diff, poly_ring.var(w_idx));
        let rabinowitsch = poly_ring.sub(prod, poly_ring.one());
        out.push(rabinowitsch);
    }
    Ok(out)
}

/// Ideal-membership Safe fast-path (config `membership_fastpath`).
///
/// For each query disequality `(a, b)`, reduce `x_a − x_b` against the
/// cached constraint-side basis. A zero remainder proves
/// `x_a − x_b ∈ I` (reduction to zero against constraint generators is a
/// membership proof, GB or not), so the two copies are forced equal on
/// every solution and the disequality is unsatisfiable — the query is
/// UNSAT, returned without the Rabinowitsch extend. Returns `Some(Unsat)`
/// on the first forced disequality, `None` if none reduce to zero (the
/// full solve then runs). Never changes a verdict: a nonzero remainder is
/// inconclusive and a zero remainder is a sound UNSAT.
fn membership_fastpath_unsat(
    cached: &CachedBase,
    cs: &ConstraintSystem,
    cancel: &CancelToken,
) -> Option<SolveOutcome> {
    let poly_ring: &FfPolyRing = &cached.poly_ring;
    let ring = poly_ring.ctx();
    // Constraint-side generators: both partition bases plus the bitsum
    // definitions — all subsets of the constraint ideal `I`.
    let mut divisors: Vec<&Poly> = Vec::new();
    for part in &cached.split_gb_owned {
        for p in part {
            divisors.push(p);
        }
    }
    for p in &cached.bitsum_polys {
        divisors.push(p);
    }
    if divisors.is_empty() {
        return None;
    }
    for &(a, b) in &cs.disequalities {
        // Resolve the producer-frame VarIdx to the cached ring frame by
        // name (the mapping `encode_query_disequalities` uses). A name the
        // compacted ring dropped means the difference cannot be tested
        // here; defer the whole query to the full path.
        let a_idx = cs.var_names.get(a as usize).and_then(|n| cached.var_map.get(n)).copied();
        let b_idx = cs.var_names.get(b as usize).and_then(|n| cached.var_map.get(n)).copied();
        let (a_idx, b_idx) = match (a_idx, b_idx) {
            (Some(a), Some(b)) => (a, b),
            _ => return None,
        };
        let diff = poly_ring.sub(poly_ring.var(a_idx), poly_ring.var(b_idx));
        let rem = diff.reduce_by_refs_cancel(&divisors, ring, cancel);
        if cancel.is_cancelled() {
            // A cancelled reduction may falsely look nonzero; do not trust it.
            return None;
        }
        if rem.is_zero() {
            return Some(SolveOutcome::Unsat(None));
        }
    }
    None
}

fn solve_with_cached(
    cached: &CachedBase,
    cs: &ConstraintSystem,
    cancel: &CancelToken,
) -> SolveOutcome {
    let poly_ring: &FfPolyRing = &cached.poly_ring;

    // Opt-in membership Safe fast-path: may resolve the query UNSAT by a
    // single reduction, skipping the Rabinowitsch extend below.
    if crate::config::with(|c| c.membership_fastpath) {
        if let Some(outcome) = membership_fastpath_unsat(cached, cs, cancel) {
            return outcome;
        }
    }

    let query_polys = match encode_query_disequalities(cs, poly_ring, &cached.var_map) {
        Ok(polys) => polys,
        // The cache key (digest) excludes disequalities, so a hit can occur
        // for a query whose disequality references a variable the cached ring
        // dropped during compaction (compaction keeps disequality endpoints,
        // but only those of the query that originally built the cache).
        // Rather than return Unknown, fall back to a fresh stateless solve for
        // this query — sound, just without the cache reuse.
        Err(_) => return stateless_solve(cs, cancel),
    };

    // Opt-in monolithic radical-membership Safe fast-path: decide the query
    // UNSAT by one whole-ring check on the combined system, skipping the split
    // extend and the model search (which enumerates exponentially on
    // forced-equal curve outputs the partition reduction cannot see).
    if crate::config::with(|c| c.radical_membership) {
        let combined: Vec<Poly> = cached
            .constraint_polys
            .iter()
            .chain(cached.bitsum_polys.iter())
            .chain(query_polys.iter())
            .map(|p| poly_ring.ring.clone_el(p))
            .collect();
        if let Some(outcome) = crate::solve::radical_membership_unsat(
            poly_ring,
            combined,
            cancel,
        ) {
            return outcome;
        }
    }

    let starting: Vec<Ideal> = cached
        .split_gb_owned
        .iter()
        .map(|polys| {
            let cloned: Vec<Poly> = polys
                .iter()
                .map(|p| poly_ring.ring.clone_el(p))
                .collect();
            Ideal::from_gb(poly_ring, cloned)
        })
        .collect();

    let k = starting.len();
    let new_polys_per_split = crate::split_gb::route_query_polys(poly_ring, k, &query_polys);

    let mut bit_prop = BitProp::from_state(poly_ring, cached.bit_prop_state.clone());

    let new_basis = match split_gb_extend_cancel(
        poly_ring,
        starting,
        new_polys_per_split,
        &mut bit_prop,
        cancel,
    ) {
        Ok(b) => b,
        Err(_) => {
            return SolveOutcome::Unknown(if cancel.is_cancelled() {
                UnknownCause::Cancelled
            } else {
                UnknownCause::EngineFailure
            });
        }
    };

    if new_basis.iter().any(|b| b.is_whole_ring()) {
        return SolveOutcome::Unsat(None);
    }

    let outcome = match split_find_zero_cancel(poly_ring, new_basis, &mut bit_prop, cancel) {
        Ok(SplitFindZeroOutcome::Sat(point)) => {
            let mut model_map = HashMap::new();
            let field = &poly_ring.field();
            for (idx, val) in point.iter().enumerate() {
                if idx < poly_ring.var_names().len() {
                    model_map.insert(poly_ring.var_names()[idx].clone(), field.to_biguint(val));
                }
            }
            let mut full_polys: Vec<Poly> = cached
                .constraint_polys
                .iter()
                .map(|p| poly_ring.ring.clone_el(p))
                .collect();
            for p in &query_polys {
                full_polys.push(poly_ring.ring.clone_el(p));
            }
            // Verify against the bitsum definitions as well, matching the
            // non-cached path (core::solve_split_gb_cancel): the model
            // search extends bases seeded with these, so a sound model must
            // satisfy them too.
            for p in &cached.bitsum_polys {
                full_polys.push(poly_ring.ring.clone_el(p));
            }
            if model::verify_model(poly_ring, &full_polys, &model_map) {
                // Unreachable under the entry routing (UF-bearing
                // systems never reach the cached path), kept as a
                // guard — no Sat that can observe UF apps may surface
                // without congruence certification.
                if cs.has_uf() {
                    crate::frontend::uf::certify_uf_sat(
                        model_map,
                        &cs.uf_apps,
                        &cs.uf_symbols,
                        &cs.var_names,
                        cs.uf_care_complete,
                        // GB route: full ring points, no completion
                        // (the G1/G2 contract).
                        false,
                    )
                } else {
                    SolveOutcome::Sat(model_map)
                }
            } else {
                // Same engine-defect signal as the stateless path's
                // gate (solve.rs); the cached path names itself so a
                // cache-related defect is attributable.
                log::warn!("cached-path model validation failed; reporting Unknown");
                metric::incr!(crate::profile::UNKNOWNS.model_validation_failures);
                SolveOutcome::Unknown(UnknownCause::ModelValidation)
            }
        }
        Ok(SplitFindZeroOutcome::Unsat) => {
            SolveOutcome::Unsat(None)
        }
        Ok(SplitFindZeroOutcome::Unknown) => {
            SolveOutcome::Unknown(if cancel.is_cancelled() {
                UnknownCause::Cancelled
            } else {
                UnknownCause::BoundedSearch
            })
        }
        Err(_) => SolveOutcome::Unknown(if cancel.is_cancelled() {
            UnknownCause::Cancelled
        } else {
            UnknownCause::EngineFailure
        }),
    };
    outcome
}

fn stateless_solve(cs: &ConstraintSystem, cancel: &CancelToken) -> SolveOutcome {
    // Same routing guard as `IncrementalSolverContext::solve`: the
    // stateless GB path cannot host UF congruence.
    if cs.has_uf() {
        let query = crate::frontend::formula::boolean_query_from_constraint_system(cs);
        return crate::boolean::solve_boolean_query(&query, cancel);
    }
    match encode(cs) {
        Ok(encoded) => crate::solve::solve_encoded_with_cancel(&encoded, cancel),
        Err(e) => {
            // An encoder rejection is a property of the input, not a
            // timeout; log the actionable message and classify it so
            // the seam does not report it as retryable.
            log::warn!("encode failed; reporting Unknown: {}", e);
            metric::incr!(crate::profile::UNKNOWNS.encoding_failures);
            SolveOutcome::Unknown(UnknownCause::EncodingFailure)
        }
    }
}

/// Hash an [`ConstraintSystem`]'s constraint side (everything
/// except `disequalities`) into a 128-bit cache key. Self-consistent:
/// two systems agreeing on `(prime, var_names, equalities,
/// assignments, bitsums, add_field_polys)` produce the same digest.
///
/// The key is 128 bits, not 64, because a digest match is trusted to
/// reuse a prior split-GB without re-deriving it, and an UNSAT result
/// from a cache hit is returned without a model re-check (unlike SAT,
/// which `model::verify_model` validates). A two-distinct-constraint-side
/// collision would therefore be an unsound UNSAT. The two SipHash-1-3
/// passes over distinct domain prefixes act as independent 64-bit PRF
/// outputs on benign inputs, so a chance collision is ~2^-128. The
/// hasher uses `std::collections`'s fixed key, so this resistance is
/// against accidental collision on developer-controlled R1CS — not
/// against an adversary tailoring `ConstraintSystem`s to collide.
pub fn digest_constraint_side(cs: &crate::frontend::encoder::ConstraintSystem) -> u128 {
    let lo = hash_constraint_side(cs, 0x01);
    let hi = hash_constraint_side(cs, 0xA5);
    ((hi as u128) << 64) | (lo as u128)
}

fn hash_constraint_side(cs: &crate::frontend::encoder::ConstraintSystem, domain: u64) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    domain.hash(&mut h);
    cs.prime.hash(&mut h);
    cs.add_field_polys.hash(&mut h);
    // `var_names` is part of the system's identity for caching:
    // two systems with identical equalities but different name
    // strings must be treated as distinct (downstream consumers
    // surface names to users).
    cs.var_names.len().hash(&mut h);
    for n in &cs.var_names {
        n.hash(&mut h);
    }
    cs.bitsums.len().hash(&mut h);
    for bs in &cs.bitsums {
        bs.len().hash(&mut h);
        for v in bs {
            v.hash(&mut h);
        }
    }
    cs.assignments.len().hash(&mut h);
    for (v, val) in &cs.assignments {
        v.hash(&mut h);
        val.hash(&mut h);
    }
    cs.equalities.len().hash(&mut h);
    for eq in &cs.equalities {
        eq.len().hash(&mut h);
        for t in eq {
            t.coeff.hash(&mut h);
            t.vars.len().hash(&mut h);
            for &(idx, exp) in &t.vars {
                idx.hash(&mut h);
                exp.hash(&mut h);
            }
        }
    }
    // UF section, appended ONLY when apps are present: the empty guard
    // keeps the UF-free byte stream exactly as before (bit-identical
    // digests, hence identical cache build/hit timing); the domain tag
    // plus length prefixes preclude extension ambiguity. Apps are
    // constraint-side (only the target disequality varies per wire), so
    // per-wire digest reuse is preserved.
    if !cs.uf_apps.is_empty() {
        0x5546_4150_5053u64.hash(&mut h); // "UFAPPS" domain tag
        cs.uf_symbols.len().hash(&mut h);
        for s in &cs.uf_symbols {
            s.hash(&mut h);
        }
        cs.uf_apps.len().hash(&mut h);
        for a in &cs.uf_apps {
            a.symbol.hash(&mut h);
            a.args.len().hash(&mut h);
            for v in &a.args {
                v.hash(&mut h);
            }
            a.result.hash(&mut h);
        }
    }
    h.finish()
}

#[cfg(test)]
#[path = "incremental_context_tests.rs"]
mod tests;
