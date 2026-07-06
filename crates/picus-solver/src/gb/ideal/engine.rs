//! Gröbner-basis engine front-door for [`super::Ideal`]: the pluggable
//! [`GbAlgorithm`] strategy + dispatch, and the `compute_gb_*` family with
//! its dense/sparse representation routing and the shared `finish_gb`
//! cancel/error/backup contract. Re-exported from `ideal` so
//! `gb::ideal::compute_gb_with_order` etc. resolve here.

use std::cell::RefCell;

use crate::config::GbStrategy;
use crate::ff::buchberger::{self, BuchbergerConfig, GBasis};
pub(crate) use crate::ff::buchberger::IncrementalGB;
use crate::ff::monomial::MonomialOrder as FfOrder;
use crate::gb::tracer::GbTracer;
use crate::poly::{FfPolyRing, Poly};
use crate::timeout::CancelToken;
use crate::metric;
use crate::EngineError;

/// Pluggable Groebner-basis algorithm.
///
/// Every public GB entry point (`compute_gb_with_order` and its
/// traced sibling) routes through [`compute_gb_dispatch`], which
/// selects a strategy from [`crate::config::RuntimeConfig::gb_strategy`]
/// and forwards.
///
/// Scope: this trait dispatches the *algorithm strategy* — currently the
/// homogenisation choice ([`BuchbergerDirect`] vs [`BuchbergerByHomog`]),
/// and the extension point for a genuinely different algorithm such as a
/// signature-based F5. It does **not** select the polynomial
/// representation (dense vs sparse — chosen inside `compute` from
/// `config.poly_repr`) nor the F4 matrix batch path (chosen via
/// `BuchbergerConfig.use_f4`): those are orthogonal implementation
/// choices made within a strategy's `compute`, not separate
/// `GbAlgorithm`s. A CoCoA-style F4 improvement lands in the
/// Buchberger/F4 engine, not as a new trait impl.
///
/// Two execution modes are supported. `compute` is the basic call;
/// `compute_traced` feeds a [`GbTracer`] observer for UNSAT-core
/// extraction. Algorithms that don't support tracing leave
/// `supports_tracing` at its default `false`; dispatch then falls back
/// to [`BuchbergerDirect`] for traced requests so UNSAT-core extraction
/// keeps working regardless of the configured strategy.
pub trait GbAlgorithm {
    /// Stable name for logs / telemetry.
    fn name(&self) -> &'static str;

    /// Compute a Groebner basis of `<gens>` over `pr` in `order`.
    /// Honours `cancel` for cooperative time limits.
    fn compute(
        &self,
        pr: &FfPolyRing,
        gens: Vec<Poly>,
        cancel: &CancelToken,
        order: FfOrder,
    ) -> Result<Vec<Poly>, EngineError>;

    /// Whether this algorithm implements [`Self::compute_traced`].
    fn supports_tracing(&self) -> bool {
        false
    }

    /// Traced variant. Only called when `supports_tracing()` is
    /// `true`. The default implementation panics — implementors that
    /// flip `supports_tracing` to `true` must override this method.
    fn compute_traced(
        &self,
        _pr: &FfPolyRing,
        _gens: Vec<Poly>,
        _cancel: &CancelToken,
        _order: FfOrder,
        _tracer: &mut GbTracer,
    ) -> Result<Vec<Poly>, EngineError> {
        unreachable!(
            "GbAlgorithm {:?}: supports_tracing() returned true but \
             compute_traced is the default panicking impl",
            self.name()
        )
    }
}

/// Plain Buchberger on `P` in the requested order. The default.
pub struct BuchbergerDirect;

impl GbAlgorithm for BuchbergerDirect {
    fn name(&self) -> &'static str {
        "buchberger-direct"
    }

    fn compute(
        &self,
        pr: &FfPolyRing,
        gens: Vec<Poly>,
        cancel: &CancelToken,
        order: FfOrder,
    ) -> Result<Vec<Poly>, EngineError> {
        compute_gb_buchberger(pr, gens, cancel, order)
    }

    fn supports_tracing(&self) -> bool {
        true
    }

    fn compute_traced(
        &self,
        pr: &FfPolyRing,
        gens: Vec<Poly>,
        cancel: &CancelToken,
        order: FfOrder,
        tracer: &mut GbTracer,
    ) -> Result<Vec<Poly>, EngineError> {
        compute_gb_buchberger_traced(pr, gens, cancel, order, tracer)
    }
}

/// Homogenise → Buchberger on `P[h]` (DegRevLex) → dehomogenise →
/// interreduce. Wins on bit-decomposition shaped ideals where sugar
/// mis-prediction stalls the direct path.
///
/// Only meaningful for `DegRevLex` requests. Lex / other orders fall
/// back to plain `BuchbergerDirect` for that call.
pub struct BuchbergerByHomog;

impl GbAlgorithm for BuchbergerByHomog {
    fn name(&self) -> &'static str {
        "buchberger-by-homog"
    }

    fn compute(
        &self,
        pr: &FfPolyRing,
        gens: Vec<Poly>,
        cancel: &CancelToken,
        order: FfOrder,
    ) -> Result<Vec<Poly>, EngineError> {
        if order == FfOrder::DegRevLex {
            match crate::gb::gb_homog::compute_gb_by_homog(pr, gens, cancel) {
                GbOutcome::Basis(b) => Ok(b),
                GbOutcome::Cancelled => Err(EngineError::Timeout),
                GbOutcome::Failed => {
                    Err(EngineError::Internal("by-homog GB failed".into()))
                }
            }
        } else {
            // ByHomog only makes sense for DegRevLex; for Lex etc.
            // route through plain Buchberger so the contract of
            // returning a basis in `order` holds.
            BuchbergerDirect.compute(pr, gens, cancel, order)
        }
    }
}

fn is_total_deg_homogeneous(pr: &FfPolyRing, p: &Poly) -> bool {
    let ring = &pr.ring;
    let n = pr.n_vars();
    let mut iter = ring.terms(p);
    let Some((_, m0)) = iter.next() else { return true; };
    let d0: usize = (0..n).map(|i| ring.exponent_at(&m0, i)).sum();
    for (_, m) in iter {
        let d: usize = (0..n).map(|i| ring.exponent_at(&m, i)).sum();
        if d != d0 { return false; }
    }
    true
}

fn resolve_auto(pr: &FfPolyRing, gens: &[Poly]) -> GbStrategy {
    let all_homog = gens.iter()
        .filter(|p| !pr.is_zero(p))
        .all(|p| is_total_deg_homogeneous(pr, p));
    if all_homog { GbStrategy::Direct } else { GbStrategy::ByHomog }
}

/// Resolve the configured GB strategy, expanding `Auto` to a concrete
/// choice via [`resolve_auto`]. Both GB dispatch paths select a strategy
/// here: the dense path routes the result through the [`GbAlgorithm`]
/// trait in [`compute_gb_dispatch`]; the sparse path branches on it inline
/// in [`compute_gb_with_order`]. A new `GbStrategy` variant must be handled
/// in both of those dispatch sites.
fn resolve_strategy(pr: &FfPolyRing, gens: &[Poly]) -> GbStrategy {
    match crate::config::with(|c| c.gb_strategy) {
        GbStrategy::Auto => resolve_auto(pr, gens),
        s => s,
    }
}

thread_local! {
    /// Name of the most recent GB algorithm chosen by [`compute_gb_dispatch`]
    /// on this thread. Used by tests to confirm dispatch is actually
    /// honouring the configured strategy.
    static LAST_DISPATCHED: RefCell<Option<&'static str>> = const { RefCell::new(None) };
}

/// Name of the algorithm that last serviced a GB request on the current
/// thread, or `None` if no GB call has run yet. The dense path records the
/// dispatched [`GbAlgorithm`] (`"buchberger-direct"` / `"buchberger-by-homog"`);
/// the sparse path records `"sparse-buchberger"` / `"sparse-by-homog"`.
#[cfg(test)]
pub(crate) fn last_dispatched_algorithm() -> Option<&'static str> {
    LAST_DISPATCHED.with(|c| *c.borrow())
}

fn record_dispatched(name: &'static str) {
    LAST_DISPATCHED.with(|c| *c.borrow_mut() = Some(name));
}

/// Pick the configured [`GbAlgorithm`] and run it. When `tracer` is
/// `Some` but the chosen algorithm cannot honour tracing, falls back
/// to [`BuchbergerDirect`] so UNSAT-core extraction continues to work.
#[metric]
fn compute_gb_dispatch(
    pr: &FfPolyRing,
    gens: Vec<Poly>,
    cancel: &CancelToken,
    order: FfOrder,
    tracer: Option<&mut GbTracer>,
) -> Result<Vec<Poly>, EngineError> {
    if gens.is_empty() {
        return Ok(Vec::new());
    }
    let strat = resolve_strategy(pr, &gens);
    let direct = BuchbergerDirect;
    let by_homog = BuchbergerByHomog;
    let chosen: &dyn GbAlgorithm = match strat {
        GbStrategy::Direct => &direct,
        GbStrategy::ByHomog => &by_homog,
        GbStrategy::Auto => unreachable!("Auto resolved above"),
    };
    match tracer {
        None => {
            record_dispatched(chosen.name());
            chosen.compute(pr, gens, cancel, order)
        }
        Some(t) => {
            if chosen.supports_tracing() {
                record_dispatched(chosen.name());
                chosen.compute_traced(pr, gens, cancel, order, t)
            } else {
                // Drop down to Direct to preserve UNSAT-core extraction.
                if chosen.name() != direct.name() {
                    log::debug!(
                        "GbAlgorithm {:?} does not support tracing; falling back to {:?}",
                        chosen.name(), direct.name()
                    );
                }
                record_dispatched(direct.name());
                direct.compute_traced(pr, gens, cancel, order, t)
            }
        }
    }
}

// ──────────────────── compute_gb_with_order family ────────────────────────

/// Build a per-call `ff::PolyRing` whose monomial order matches `order`.
/// Cheap (an `Arc<PolyRing>` with the same field/var-name data).
pub(crate) fn ring_for_order(poly_ring: &FfPolyRing, order: FfOrder) -> std::sync::Arc<crate::ff::polynomial::PolyRing> {
    let ctx = poly_ring.ctx();
    if ctx.order == order {
        // Dominant case (DegRevLex request on a DegRevLex ring): reuse
        // the existing ring instead of rebuilding it per GB call.
        return ctx.clone();
    }
    // Rebuild under the requested order, carrying the source ring's
    // representation (never the ambient config's).
    crate::ff::polynomial::PolyRing::new_with_repr(
        poly_ring.field().clone(),
        poly_ring.var_names().to_vec(),
        order,
        ctx.repr,
    )
}

/// True when the configured IR representation is sparse, so native GB
/// computation should be routed through the sparse engine.
#[inline]
/// Route GB work by the representation recorded on the ring at its
/// construction — the single source of truth after construction — so a
/// ring pinned via `new_with_repr` is honoured and routing cannot drift
/// with ambient config changes between calls.
pub(crate) fn use_sparse_gb(poly_ring: &FfPolyRing) -> bool {
    poly_ring.ctx().repr == crate::config::ReprKind::Sparse
}

/// Compute a Gröbner basis through the sparse engine (`ff::sparse_gb`)
/// when the ring's representation is sparse: extract each generator's
/// sparse arm, compute and inter-reduce sparsely, and return a sparse-arm
/// basis (the polynomials stay resident-sparse, no dense materialisation).
///
/// Contract: on **cancellation** the sparse engine returns the basis built
/// so far — a valid generating set of the same ideal but NOT a complete
/// Gröbner basis — surfaced here as `Ok(partial)`, so every caller MUST
/// re-check `cancel.is_cancelled()` and discard it before trusting it as a
/// GB. A panic in the sparse engine is caught by [`catch_engine_panic`]
/// (mirroring the dense path), so a malformed query degrades to an empty
/// basis → Unknown via `finish_gb` rather than aborting the process.
fn sparse_gb_route(
    poly_ring: &FfPolyRing,
    generators: Vec<Poly>,
    order: FfOrder,
    cancel: &CancelToken,
) -> Result<Vec<Poly>, EngineError> {
    let ring = ring_for_order(poly_ring, order);
    catch_engine_panic("sparse Buchberger", || {
        let sparse: Vec<crate::ff::sparse_polynomial::SparsePolynomial> =
            generators.iter().map(|p| p.to_sparse(&ring)).collect();
        let gb = crate::ff::sparse_gb::groebner_basis(sparse, &ring, Some(cancel));
        let reduced = crate::ff::sparse_gb::interreduce(gb, &ring, Some(cancel));
        Ok(reduced.into_iter().map(Poly::Sparse).collect::<Vec<Poly>>())
    })
}

/// Unwrap a vector of solve-core `Poly` to the dense `DensePoly` the
/// Gröbner engine consumes. On the dense path every element is already
/// the `Dense` arm; a stray sparse element is materialised to dense.
pub(crate) fn unwrap_dense_vec(v: Vec<Poly>, ring: &crate::ff::polynomial::PolyRing) -> Vec<crate::ff::DensePoly> {
    v.into_iter()
        .map(|p| match p {
            Poly::Dense(d) => d,
            Poly::Sparse(s) => s.to_dense(ring),
        })
        .collect()
}

/// Wrap dense engine output back into solve-core `Poly`.
pub(crate) fn wrap_dense_vec(v: Vec<crate::ff::DensePoly>) -> Vec<Poly> {
    v.into_iter().map(Poly::Dense).collect()
}

/// Outcome of a GB entry point.
///
/// Replaces the former tri-state `Vec<Poly>` sentinel (trusted basis /
/// cancelled backup / error empty) whose discrimination lived out of
/// band in the `CancelToken` plus caller discipline. Mistaking a
/// cancelled or failed result for a Gröbner basis would let
/// `is_zero_dim`/`min_poly`/FGLM emit a false UNSAT; this enum makes the
/// protocol compiler-enforced and removes the defensive backup clone of
/// all generators every entry point used to pay.
#[derive(Debug)]
pub enum GbOutcome {
    /// A trusted Gröbner basis (the token did not fire during the run).
    Basis(Vec<Poly>),
    /// Cooperative cancellation fired; no trusted basis exists.
    Cancelled,
    /// Genuine engine failure (details were logged); the ideal is
    /// undetermined — callers map this to an empty basis / Unknown,
    /// never to a trusted GB.
    Failed,
}

impl GbOutcome {
    /// The basis, or `None` on `Cancelled`/`Failed`.
    pub fn into_basis(self) -> Option<Vec<Poly>> {
        match self {
            GbOutcome::Basis(b) => Some(b),
            GbOutcome::Cancelled | GbOutcome::Failed => None,
        }
    }

    /// Unwrap a `Basis`; panics on `Cancelled`/`Failed`. For callers
    /// running under a never-firing token (tests, bounded utilities).
    #[track_caller]
    pub fn expect_basis(self, msg: &str) -> Vec<Poly> {
        match self {
            GbOutcome::Basis(b) => b,
            other => panic!("{}: expected GbOutcome::Basis, got {:?}", msg, other),
        }
    }
}

/// Resolve a GB `Result` under the soundness contract shared by every
/// public GB entry point: a fired token means the basis (even an `Ok`
/// one — the sparse engine returns its partial progress) is not a
/// complete GB, so it is discarded as `Cancelled`; a genuine engine
/// error becomes `Failed`. `what` names the call site for the log.
fn finish_gb(
    result: Result<Vec<Poly>, EngineError>,
    cancel: &CancelToken,
    what: &str,
) -> GbOutcome {
    match result {
        Ok(basis) => {
            if cancel.is_cancelled() {
                GbOutcome::Cancelled
            } else {
                GbOutcome::Basis(basis)
            }
        }
        Err(e) => {
            if cancel.is_cancelled() {
                GbOutcome::Cancelled
            } else {
                log::warn!("{} failed ({:?}); treating the ideal as undetermined", what, e);
                GbOutcome::Failed
            }
        }
    }
}

/// Front-door constructor for a long-lived incremental engine. Owns the
/// `BuchbergerConfig` policy for incremental use, so a future knob
/// cannot silently skip the incremental paths by hand-assembling a
/// config elsewhere. Incremental extends are tiny-batch (a few S-pairs
/// per call), so F4 never amortizes: `use_f4` is pinned off —
/// result-identical to per-pair by the engine's contract — for every
/// incremental consumer (the engine's own extend entries, the resumable
/// cache, and the cdclt incremental theory).
pub(crate) fn incremental_engine(
    ring: std::sync::Arc<crate::ff::polynomial::PolyRing>,
    cancel: Option<CancelToken>,
) -> IncrementalGB {
    IncrementalGB::new(
        ring,
        BuchbergerConfig {
            cancel_token: cancel,
            abort_on_trivial: true,
            use_f4: false,
            ..BuchbergerConfig::default()
        },
    )
}

/// Run `f` under `catch_unwind`, converting a panic into
/// [`EngineError::EnginePanic`] with the payload text and call site
/// preserved. A caught panic means the engine has a bug: it is logged at
/// error level and counted (`IDEAL.engine_panics`) before the caller's
/// fail-closed handling (empty basis → Unknown) takes over. This is the
/// crate's only in-crate unwind boundary.
pub(crate) fn catch_engine_panic<T>(
    site: &'static str,
    f: impl FnOnce() -> Result<T, EngineError>,
) -> Result<T, EngineError> {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)) {
        Ok(r) => r,
        Err(payload) => {
            let message = if let Some(s) = payload.downcast_ref::<&str>() {
                (*s).to_string()
            } else if let Some(s) = payload.downcast_ref::<String>() {
                s.clone()
            } else {
                "non-string panic payload".to_string()
            };
            metric::incr!(picus_core::profile::IDEAL.engine_panics);
            log::error!("engine panic at {}: {}", site, message);
            Err(EngineError::EnginePanic { site, message })
        }
    }
}

/// Compute a Groebner basis of `generators` in the requested monomial
/// order, routed through [`compute_gb_dispatch`] (dense) or the sparse
/// engine ([`sparse_gb_route`]) per the ring's representation. See
/// [`GbOutcome`] for the cancellation/failure contract.
#[metric]
pub fn compute_gb_with_order(
    poly_ring: &FfPolyRing,
    generators: Vec<Poly>,
    cancel: &CancelToken,
    order: FfOrder,
) -> GbOutcome {
    if generators.is_empty() {
        return GbOutcome::Basis(Vec::new());
    }
    if use_sparse_gb(poly_ring) {
        // Honour the configured strategy on the sparse path too: ByHomog
        // (DegRevLex only, mirroring BuchbergerByHomog) runs the
        // homogenize → GB → dehomogenize pipeline with a sparse inner GB;
        // everything else is plain sparse Buchberger.
        let strat = resolve_strategy(poly_ring, &generators);
        if strat == GbStrategy::ByHomog && order == FfOrder::DegRevLex {
            record_dispatched("sparse-by-homog");
            return crate::gb::gb_homog::compute_gb_by_homog(poly_ring, generators, cancel);
        }
        record_dispatched("sparse-buchberger");
        let result = sparse_gb_route(poly_ring, generators, order, cancel);
        return finish_gb(result, cancel, "sparse GB");
    }
    let n_gens = generators.len();
    let n_vars = poly_ring.n_vars();
    let result = compute_gb_dispatch(poly_ring, generators, cancel, order, None);
    let out = finish_gb(result, cancel, "GB dispatch");
    if let GbOutcome::Basis(basis) = &out {
        log::trace!(
            "GB call: {} gens, {} vars → {} basis elems",
            n_gens, n_vars, basis.len()
        );
    }
    out
}

/// Raw Buchberger entry point. Bypasses [`compute_gb_dispatch`] and
/// is used by algorithm implementations themselves (e.g.
/// `BuchbergerByHomog` calls this from its inner GB step on `P[h]`).
/// External callers should prefer [`compute_gb_with_order`].
#[metric]
pub(crate) fn compute_gb_buchberger(
    poly_ring: &FfPolyRing,
    generators: Vec<Poly>,
    cancel: &CancelToken,
    order: FfOrder,
) -> Result<Vec<Poly>, EngineError> {
    if generators.is_empty() {
        return Ok(Vec::new());
    }
    let ring = ring_for_order(poly_ring, order);
    let cfg = BuchbergerConfig {
        cancel_token: Some(cancel.clone()),
        abort_on_trivial: true,
        use_f4: crate::ff::buchberger::use_f4_default(),
        ..BuchbergerConfig::default()
    };
    let dense_gens = unwrap_dense_vec(generators, &ring);
    catch_engine_panic("Buchberger", || {
        buchberger::groebner_basis(dense_gens, &ring, &cfg)
            .map(|GBasis { basis, .. }| wrap_dense_vec(basis))
    })
}

/// Raw *direct* Gröbner basis (plain Buchberger, no strategy dispatch) on
/// `poly_ring`, routed to the sparse or dense engine per the active
/// representation. The inner homogeneous-GB step of the by-homog pipeline
/// uses this so it never re-enters strategy dispatch. Empty input →
/// empty basis; see [`GbOutcome`] for the cancellation/failure contract.
pub(crate) fn compute_gb_direct(
    poly_ring: &FfPolyRing,
    generators: Vec<Poly>,
    cancel: &CancelToken,
    order: FfOrder,
) -> GbOutcome {
    if generators.is_empty() {
        return GbOutcome::Basis(Vec::new());
    }
    if use_sparse_gb(poly_ring) {
        let result = sparse_gb_route(poly_ring, generators, order, cancel);
        return finish_gb(result, cancel, "inner direct sparse GB");
    }
    let result = compute_gb_buchberger(poly_ring, generators, cancel, order);
    finish_gb(result, cancel, "inner direct GB")
}

/// Incremental GB extension. Computes GB of `<known_gb> + <new_polys>`
/// using `known_gb` as a trusted reduced GB seed: S-pairs internal to
/// `known_gb` are skipped (Buchberger criterion), and only S-pairs
/// between `known_gb` × `new_polys` and among `new_polys` themselves
/// are generated and discharged.
#[metric]
pub fn compute_gb_incremental_with_order(
    poly_ring: &FfPolyRing,
    known_gb: Vec<Poly>,
    new_polys: Vec<Poly>,
    cancel: &CancelToken,
    order: FfOrder,
) -> GbOutcome {
    if new_polys.is_empty() {
        return GbOutcome::Basis(known_gb);
    }
    if known_gb.is_empty() {
        return compute_gb_with_order(poly_ring, new_polys, cancel, order);
    }
    if use_sparse_gb(poly_ring) {
        // Incremental seeding: trust `known_gb` as a reduced GB (the same
        // contract the dense path relies on via `seed_reduced_basis`) and
        // process only the cross / intra-new S-pairs, then inter-reduce —
        // identical to recomputing the union, but skips the O(n²) seed
        // pairs. A panic is caught and mapped to `Failed` via
        // `finish_gb`, mirroring the dense incremental path.
        let ring = ring_for_order(poly_ring, order);
        let result = catch_engine_panic("incremental sparse Buchberger", || {
            let known: Vec<crate::ff::sparse_polynomial::SparsePolynomial> =
                known_gb.iter().map(|p| p.to_sparse(&ring)).collect();
            let fresh: Vec<crate::ff::sparse_polynomial::SparsePolynomial> =
                new_polys.iter().map(|p| p.to_sparse(&ring)).collect();
            let gb = crate::ff::sparse_gb::groebner_basis_incremental(known, fresh, &ring, Some(cancel));
            let reduced = crate::ff::sparse_gb::interreduce(gb, &ring, Some(cancel));
            Ok(reduced.into_iter().map(Poly::Sparse).collect::<Vec<Poly>>())
        });
        return finish_gb(result, cancel, "incremental sparse GB");
    }
    let ring = ring_for_order(poly_ring, order);

    let dense_known = unwrap_dense_vec(known_gb, &ring);
    let dense_new = unwrap_dense_vec(new_polys, &ring);
    let result = catch_engine_panic("incremental Buchberger", || {
        let mut igb = incremental_engine(ring.clone(), Some(cancel.clone()));
        // Seed with the trusted reduced GB via the pair-free fast path.
        // `add_generators` would have generated O(n²) S-pairs among the
        // seeded elements (each of which then walks the M-criterion list,
        // O(n³)/O(n⁴) total); since the seed is already a reduced GB,
        // every one of those pairs reduces to zero by Buchberger's
        // criterion. We skip them entirely.
        igb.seed_reduced_basis(dense_known);
        // Genuinely incremental: only the cross-pairs (known_gb × new) and
        // intra-new pairs are processed by add_generators below.
        igb.add_generators(dense_new)?;
        Ok(wrap_dense_vec(igb.basis()))
    });
    finish_gb(result, cancel, "incremental GB")
}

/// Traced sibling of [`compute_gb_with_order`]: feeds Buchberger steps
/// to `tracer` for UNSAT-core extraction. Routes through
/// [`compute_gb_dispatch`] with `Some(tracer)`; if the dispatched
/// algorithm doesn't support tracing, dispatch silently falls back to
/// [`BuchbergerDirect`] for that call.
///
/// `tracer` must have been constructed with `n_inputs >= generators.len()`
/// and be in a fresh state (or have been previously fed exactly
/// `tracer.basis_count()` initial-basis events corresponding to earlier
/// generators in the same global input numbering).
#[metric]
pub fn compute_gb_with_order_traced(
    poly_ring: &FfPolyRing,
    generators: Vec<Poly>,
    cancel: &CancelToken,
    order: FfOrder,
    tracer: &mut crate::gb::tracer::GbTracer,
) -> GbOutcome {
    if generators.is_empty() {
        return GbOutcome::Basis(Vec::new());
    }
    let result = compute_gb_dispatch(poly_ring, generators, cancel, order, Some(tracer));
    finish_gb(result, cancel, "traced GB dispatch")
}

/// Raw traced Buchberger entry point. Counterpart to
/// [`compute_gb_buchberger`]. Used by [`BuchbergerDirect::compute_traced`]
/// and by future algorithms that opt into tracing.
#[metric]
pub(crate) fn compute_gb_buchberger_traced(
    poly_ring: &FfPolyRing,
    generators: Vec<Poly>,
    cancel: &CancelToken,
    order: FfOrder,
    tracer: &mut crate::gb::tracer::GbTracer,
) -> Result<Vec<Poly>, EngineError> {
    if generators.is_empty() {
        return Ok(Vec::new());
    }
    let ring = ring_for_order(poly_ring, order);
    let cfg = BuchbergerConfig {
        cancel_token: Some(cancel.clone()),
        abort_on_trivial: true,
        use_f4: crate::ff::buchberger::use_f4_default(),
        ..BuchbergerConfig::default()
    };
    let dense_gens = unwrap_dense_vec(generators, &ring);
    catch_engine_panic("traced Buchberger", || {
        buchberger::groebner_basis_observed(dense_gens, &ring, &cfg, tracer)
            .map(|GBasis { basis, .. }| wrap_dense_vec(basis))
    })
}

/// Traced incremental variant.  Mirrors `compute_gb_incremental_with_order`
/// but feeds `tracer` with observer events.  The tracer's `n_inputs` must
/// be at least `known_gb.len() + new_polys.len()` for the dependency
/// numbering to remain in-range.
///
/// Each generator pushed to the basis is registered against the tracer
/// in order — first all `known_gb` elements, then all `new_polys` —
/// matching the ordinal used by a fresh `GbTracer`.
#[metric]
pub fn compute_gb_incremental_with_order_traced(
    poly_ring: &FfPolyRing,
    known_gb: Vec<Poly>,
    new_polys: Vec<Poly>,
    cancel: &CancelToken,
    order: FfOrder,
    tracer: &mut crate::gb::tracer::GbTracer,
) -> GbOutcome {
    if new_polys.is_empty() {
        return GbOutcome::Basis(known_gb);
    }
    if known_gb.is_empty() {
        return compute_gb_with_order_traced(poly_ring, new_polys, cancel, order, tracer);
    }
    let ring = ring_for_order(poly_ring, order);
    let dense_known = unwrap_dense_vec(known_gb, &ring);
    let dense_new = unwrap_dense_vec(new_polys, &ring);
    let result = catch_engine_panic("traced incremental Buchberger", || {
        let mut igb = incremental_engine(ring.clone(), Some(cancel.clone()));
        igb.add_generators_observed(dense_known, tracer)?;
        igb.add_generators_observed(dense_new, tracer)?;
        Ok(wrap_dense_vec(igb.basis()))
    });
    finish_gb(result, cancel, "traced incremental GB")
}

#[cfg(test)]
#[path = "engine_tests.rs"]
mod tests;
