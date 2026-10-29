//! Approximate specs. `approximates(M / Z_kl, p, δ)` says
//! E_{M/Z}[ℰ] ≤ E_p[ℰ] + δ for every ℰ ∈ [0, 1], and then any layout of
//! M / Z_kl samples p up to δ:
//!
//! ```text
//!   ε ≥ E_p[ℰ]     approximates(M / Z_kl, p, δ)     ℰ ∈ [0, 1]
//!   ----------------------------------------------------------
//!   [{ ↯(ε + δ) }] sample_approx(w) [{ r. ↯(ℰ(r)) }]
//! ```
//!
//! δ = TV(p, M/Z) suffices (`lemma_approximates`), and so does n / (2Z)
//! when |M_r − Z p_r| ≤ 1 (Theorem 4.17, `lemma_approximates_tv`).

use vstd::prelude::*;

verus! {

use crate::ec::*;
#[cfg(verus_keep_ghost)]
use crate::ec::ErrorCreditCarrier::Value;
use crate::optas::tree::OptasSpec;
use crate::ddg_walk::walk;
use crate::ddg_walk::walk::DdgWalk;
#[cfg(verus_keep_ghost)]
use crate::ddg_walk::walk::DdgSpec;
#[cfg(verus_keep_ghost)]
use crate::optas::ztype::{wsum, wsum_nat, ddg_exp};
#[cfg(verus_keep_ghost)]
use crate::optas::divergences::{pos, tv_pos, psum};
#[cfg(verus_keep_ghost)]
use crate::optas::utils::{zkl, wf_kl, normalize_vector, lemma_zkl};

/// Σ_{r' ∈ [r, n)} p(r')·ℰ(r') = E_p[ℰ] (from r).
pub open spec fn pexp(p: spec_fn(nat) -> real, e: spec_fn(nat) -> real, n: nat, r: nat) -> real
    decreases n - r,
{
    if r >= n { 0real } else { p(r) * e(r) + pexp(p, e, n, r + 1) }
}

/// ℰ(i) ∈ [0, 1] for every label i: the TV slack only covers credits up to 1.
pub open spec fn credit_alloc_bound(e: spec_fn(nat) -> real) -> bool {
    forall |i: nat| 0real <= #[trigger] e(i) <= 1real
}

// ── E_q[ℰ] ≤ E_p[ℰ] + TV ─────────────────────────────────────────────────────

/// q·ℰ ≤ p·ℰ + max(0, q − p) for ℰ ∈ [0, 1].
proof fn lemma_term(qv: real, pv: real, ev: real)
    requires 0real <= ev <= 1real,
    ensures qv * ev <= pv * ev + pos(qv - pv),
{
    if qv - pv > 0real {
        assert((qv - pv) * ev <= qv - pv) by(nonlinear_arith) requires qv - pv > 0real, ev <= 1real;
    } else {
        assert((qv - pv) * ev <= 0real) by(nonlinear_arith) requires qv - pv <= 0real, ev >= 0real;
    }
    assert(qv * ev - pv * ev == (qv - pv) * ev) by(nonlinear_arith);
}

/// E_q[ℰ] ≤ E_p[ℰ] + Σ max(0, q − p).
pub proof fn lemma_transport(q: spec_fn(nat) -> real, p: spec_fn(nat) -> real, e: spec_fn(nat) -> real, n: nat, r: nat)
    requires credit_alloc_bound(e),
    ensures pexp(q, e, n, r) <= pexp(p, e, n, r) + tv_pos(q, p, n, r),
    decreases n - r,
{
    if r < n {
        lemma_transport(q, p, e, n, r + 1);
        lemma_term(q(r), p(r), e(r));
    }
}

/// E_{M/Z}[ℰ] as a sum over the distribution M / Z.
pub proof fn lemma_ddg_exp_pexp(ms: Seq<u128>, z: nat, e: spec_fn(nat) -> real)
    requires z > 0,
    ensures ddg_exp(ms, z, e) == pexp(normalize_vector(z, ms), e, ms.len(), 0),
{
    lemma_wsum_pexp(ms, z, e, 0);
}

proof fn lemma_wsum_pexp(ms: Seq<u128>, z: nat, e: spec_fn(nat) -> real, r: nat)
    requires z > 0,
    ensures wsum(ms, e, r) / (z as real) == pexp(normalize_vector(z, ms), e, ms.len(), r),
    decreases ms.len() - r,
{
    let zr = z as real;
    if r < ms.len() {
        lemma_wsum_pexp(ms, z, e, r + 1);
        let x = ms[r as int] as real;
        assert(((x * e(r)) + wsum(ms, e, r + 1)) / zr == (x / zr) * e(r) + wsum(ms, e, r + 1) / zr) by(nonlinear_arith)
            requires zr > 0real;
    } else {
        assert(0real / zr == 0real);
    }
}

// ── Theorem 4.17: TV ≤ n / (2Z) ───────────────────────────────────────────────

proof fn lemma_tv_term(d: real, pk: real)
    requires pk > 0real, -1real <= d * pk <= 1real,
    ensures pos(d) - pos(-d) == d, pos(d) + pos(-d) <= 1real / pk,
{
    if d > 0real {
        assert(d <= 1real / pk) by(nonlinear_arith) requires d * pk <= 1real, pk > 0real;
    } else {
        assert(-d <= 1real / pk) by(nonlinear_arith) requires -1real <= d * pk, pk > 0real;
    }
}

proof fn lemma_tv_sums(ms: Seq<u128>, z: nat, p: spec_fn(nat) -> real, r: nat)
    requires
        z > 0, r <= ms.len(),
        forall |i: nat| i < ms.len() ==> -1real <= (ms[i as int] as real) - (z as real) * #[trigger] p(i) <= 1real,
    ensures
        tv_pos(normalize_vector(z, ms), p, ms.len(), r) - tv_pos(p, normalize_vector(z, ms), ms.len(), r)
            == (wsum_nat(ms, r) as real) / (z as real) - psum(p, ms.len(), r),
        tv_pos(normalize_vector(z, ms), p, ms.len(), r) + tv_pos(p, normalize_vector(z, ms), ms.len(), r)
            <= ((ms.len() - r) as real) / (z as real),
    decreases ms.len() - r,
{
    let pk = z as real;
    let q = normalize_vector(z, ms);
    if r < ms.len() {
        lemma_tv_sums(ms, z, p, r + 1);
        let x = ms[r as int] as real;
        let d = q(r) - p(r);
        assert(d * pk == x - pk * p(r)) by(nonlinear_arith) requires q(r) == x / pk, pk > 0real, d == q(r) - p(r);
        lemma_tv_term(d, pk);
        assert(p(r) - q(r) == -d);
        let ws1 = wsum_nat(ms, r + 1) as real;
        assert((x + ws1) / pk == x / pk + ws1 / pk) by(nonlinear_arith) requires pk > 0real;
        let n1 = (ms.len() - (r + 1)) as real;
        assert((n1 + 1real) / pk == n1 / pk + 1real / pk) by(nonlinear_arith) requires pk > 0real;
    } else {
        assert(0real / pk == 0real);
    }
}

/// Theorem 4.17: if Σ M = Z, p sums to 1 and |M_r − Z p_r| ≤ 1, then
/// TV(p, M/Z) ≤ n / (2Z).
pub proof fn lemma_tv_bound(ms: Seq<u128>, z: nat, p: spec_fn(nat) -> real)
    requires
        z > 0, wsum_nat(ms, 0) == z, psum(p, ms.len(), 0) == 1real,
        forall |i: nat| i < ms.len() ==> -1real <= (ms[i as int] as real) - (z as real) * #[trigger] p(i) <= 1real,
    ensures tv_pos(normalize_vector(z, ms), p, ms.len(), 0) <= (ms.len() as real) / (2real * (z as real)),
{
    lemma_tv_sums(ms, z, p, 0);
    let pk = z as real;
    assert(pk / pk == 1real) by(nonlinear_arith) requires pk > 0real;
    let n = ms.len() as real;
    assert(n / (2real * pk) == (n / pk) / 2real) by(nonlinear_arith) requires pk > 0real;
}

// ── The approximate sampler ──────────────────────────────────────────────────

/// M / Z_kl is within δ of p: E_{M/Z}[ℰ] ≤ E_p[ℰ] + δ for every ℰ ∈ [0, 1].
pub open spec fn approximates(s: OptasSpec, p: spec_fn(nat) -> real, delta: real) -> bool {
    forall |e: spec_fn(nat) -> real| credit_alloc_bound(e) ==>
        #[trigger] s.target(e) <= pexp(p, e, s.ms.len(), 0) + delta
}

/// δ ≥ Σ_r max(0, M_r/Z − p_r) is enough.
pub proof fn lemma_approximates(s: OptasSpec, p: spec_fn(nat) -> real, delta: real)
    requires
        wf_kl(s.ms, s.k, s.l),
        delta >= tv_pos(normalize_vector(zkl(s.k, s.l), s.ms), p, s.ms.len(), 0),
    ensures approximates(s, p, delta),
{
    lemma_zkl(s.k, s.l);
    assert forall |e: spec_fn(nat) -> real| credit_alloc_bound(e) implies
        #[trigger] s.target(e) <= pexp(p, e, s.ms.len(), 0) + delta by {
        lemma_ddg_exp_pexp(s.ms, zkl(s.k, s.l), e);
        lemma_transport(normalize_vector(zkl(s.k, s.l), s.ms), p, e, s.ms.len(), 0);
    }
}

/// Theorem 4.17: for |M_r − Z p_r| ≤ 1 the slack is n / (2 Z_kl).
pub proof fn lemma_approximates_tv(s: OptasSpec, p: spec_fn(nat) -> real)
    requires
        wf_kl(s.ms, s.k, s.l),
        psum(p, s.ms.len(), 0) == 1real,
        forall |i: nat| i < s.ms.len() ==>
            -1real <= (s.ms[i as int] as real) - (zkl(s.k, s.l) as real) * #[trigger] p(i) <= 1real,
    ensures approximates(s, p, (s.ms.len() as real) / (2real * (zkl(s.k, s.l) as real))),
{
    lemma_zkl(s.k, s.l);
    lemma_tv_bound(s.ms, zkl(s.k, s.l), p);
    lemma_approximates(s, p, (s.ms.len() as real) / (2real * (zkl(s.k, s.l) as real)));
}

/// Sample p up to δ with any layout of an M / Z_kl that approximates it.
pub fn sample_approx<W: DdgWalk<Spec = OptasSpec>>(
    w: &W,
    Ghost(p): Ghost<spec_fn(nat) -> real>,
    Ghost(delta): Ghost<real>,
    Ghost(e): Ghost<spec_fn(nat) -> real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(eps): Ghost<real>,
) -> ((value, out_credit): (u64, Tracked<ErrorCreditResource>))
    requires
        w.wf(),
        approximates(w.spec(), p, delta),
        credit_alloc_bound(e),
        eps >= pexp(p, e, w.spec().ms.len(), 0),
        input_credit@ =~= (Value { car: eps + delta }),
    ensures
        (value as nat) < w.spec().ms.len(),
        out_credit@@ =~= (Value { car: e(value as nat) }),
{
    proof { assert(w.spec().target(e) <= eps + delta); }
    let (v, out) = walk::sample(w, Ghost(e), Tracked(input_credit), Ghost(eps + delta));
    proof { assert(w.spec().ddg().n == w.spec().ms.len()); }
    (v, out)
}

} // verus!
