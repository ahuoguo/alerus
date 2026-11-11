//! Divergences: total variation only, exact (no floats).
//!
//! The original computes f-divergences in floating point (with `mpmath` for
//! stability). Error credits bound total variation, so only `kernel_tv` is
//! ported, as an exact real-valued spec. `tv_pos` is the form the error-credit
//! specs use (the positive part of q − p); `lemma_tv_pos_eq_tv` shows it is
//! the same number for two distributions.

use vstd::prelude::*;

verus! {

/// max(0, x).
pub open spec fn pos(x: real) -> real {
    if x > 0real { x } else { 0real }
}

pub open spec fn rabs(x: real) -> real {
    if x >= 0real { x } else { -x }
}

/// `kernel_tv(a, b) = 1/2 * abs(a - b)`.
pub open spec fn kernel_tv(a: real, b: real) -> real {
    rabs(a - b) / 2real
}

/// `compute_divergence_kernel(p, q, kernel_tv)`: Σ_{i ∈ [r, n), p_i > 0}
/// kernel_tv(p_i, q_i). Like the original, labels with p_i = 0 are skipped.
pub open spec fn compute_divergence_kernel_tv(p: spec_fn(nat) -> real, q: spec_fn(nat) -> real, n: nat, r: nat) -> real
    decreases n - r,
{
    if r >= n {
        0real
    } else {
        (if p(r) > 0real { kernel_tv(p(r), q(r)) } else { 0real })
            + compute_divergence_kernel_tv(p, q, n, r + 1)
    }
}

/// TV(p, q) = Σ_{i ∈ [r, n)} ½|p_i − q_i|.
pub open spec fn tv(p: spec_fn(nat) -> real, q: spec_fn(nat) -> real, n: nat, r: nat) -> real
    decreases n - r,
{
    if r >= n { 0real } else { kernel_tv(p(r), q(r)) + tv(p, q, n, r + 1) }
}

/// Σ_{i ∈ [r, n)} max(0, q_i − p_i).
pub open spec fn tv_pos(q: spec_fn(nat) -> real, p: spec_fn(nat) -> real, n: nat, r: nat) -> real
    decreases n - r,
{
    if r >= n { 0real } else { pos(q(r) - p(r)) + tv_pos(q, p, n, r + 1) }
}

/// Σ_{i ∈ [r, n)} q_i.
pub open spec fn psum(q: spec_fn(nat) -> real, n: nat, r: nat) -> real
    decreases n - r,
{
    if r >= n { 0real } else { q(r) + psum(q, n, r + 1) }
}

proof fn lemma_tv_parts(q: spec_fn(nat) -> real, p: spec_fn(nat) -> real, n: nat, r: nat)
    ensures
        2real * tv_pos(q, p, n, r) == 2real * tv(p, q, n, r) + psum(q, n, r) - psum(p, n, r),
    decreases n - r,
{
    if r < n {
        lemma_tv_parts(q, p, n, r + 1);
        let d = q(r) - p(r);
        assert(2real * pos(d) == rabs(-d) + d);
        assert(rabs(p(r) - q(r)) == rabs(-d));
    }
}

/// For two distributions (equal total mass), Σ max(0, q − p) = TV(p, q).
pub proof fn lemma_tv_pos_eq_tv(q: spec_fn(nat) -> real, p: spec_fn(nat) -> real, n: nat)
    requires psum(q, n, 0) == psum(p, n, 0),
    ensures tv_pos(q, p, n, 0) == tv(p, q, n, 0),
{
    lemma_tv_parts(q, p, n, 0);
}

/// The original's divergence equals TV when q vanishes wherever p does.
pub proof fn lemma_compute_divergence_kernel_tv(p: spec_fn(nat) -> real, q: spec_fn(nat) -> real, n: nat, r: nat)
    requires forall |i: nat| r <= i < n && #[trigger] p(i) <= 0real ==> p(i) == 0real && q(i) == 0real,
    ensures compute_divergence_kernel_tv(p, q, n, r) == tv(p, q, n, r),
    decreases n - r,
{
    if r < n {
        lemma_compute_divergence_kernel_tv(p, q, n, r + 1);
        if !(p(r) > 0real) {
            assert(p(r) == 0real && q(r) == 0real);
            assert(kernel_tv(p(r), q(r)) == 0real);
        }
    }
}

} // verus!
