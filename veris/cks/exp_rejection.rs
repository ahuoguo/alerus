//! Exponential-rejection sampler producing rejection_dist(u) = e^{−u/d} / N
//! on {0, …, d−1}, where N = Σ_{u<d} e^{−u/d}.
//!
//! Algorithm:
//! ```text
//!   loop:
//!     u ← Uniform({0, …, d−1})
//!     b ← Bernoulli(e^{−u/d})
//!     if b: return u
//! ```
//!
//! Expectation Preservation Rule:
//!
//! ```text
//!   eps_avg ≥ E_{u ~ rejection_dist}[ℰ(u)] = (1/N) · Σ_{u<d} e^{−u/d} · ℰ(u)
//!   ─────────────────────────────────────────────────────────────────────────
//!   [{ ↯(eps_avg) }] sample_exp_rejection(d) [{ u. ↯(ℰ(u)) }]
//! ```
//!
//! Credit derivation:
//!
//! ```text
//!   alloc(w)        = e^{−w/d} · flip_accept(w) + (1 − e^{−w/d}) · flip_reject
//!   flip_accept(w)  = ℰ(w)                                    // accept arm
//!   flip_reject     = E_{l ~ rejection_dist}[ℰ(l)]            // recursive expected value
//! ```
//!
//! the average over the uniform step exactly equals the target expectation:
//!
//!   E_{u ~ rejection_dist}[ℰ(u)]  =  (1/d) · Σ_w alloc(w).
//!
//! To close the while-loop in Hoare logic we add thin-air slack ε and amplify:
//!   rej_credit  = amp·ε + eps_avg     (amp = 1/R, R = 1 − N/d)
//!   alloc(w)    = e^{−w/d}·ℰ(w) + (1 − e^{−w/d})·rej_credit
//!   average(d, alloc) ≤ ε + eps_avg                         (`lemma_rej_average`)
//! On rejection the carried credit is `rej_credit`; the next iteration uses
//! ε ↦ amp·ε.  Since amp > 1 the slack grows geometrically and the
//! Archimedean property bounds the number of iterations.

use vstd::prelude::*;

verus! {

use crate::ec::*;
#[cfg(verus_keep_ghost)]
use crate::math::pow::{pow, archimedean_exp_growth};
#[cfg(verus_keep_ghost)]
use crate::math::real::real_assoc_mult;
#[cfg(verus_keep_ghost)]
use crate::math::exp::{exp, axiom_exp_zero, axiom_exp_neg_range, axiom_exp_neg_strict, axiom_exp_add};
use crate::rand_primitives::{thin_air, rand_ubig};
#[cfg(verus_keep_ghost)]
use crate::rand_primitives::{average_nat, sum_credit};
use crate::cks::bernoulli_exp::sample_bernoulli_exp_ubig;
use random::{UBig, ubig_from_u64};
use crate::extern_spec::ubig_lt;
#[cfg(verus_keep_ghost)]
use crate::extern_spec::ubig_view;
#[cfg(verus_keep_ghost)]
use crate::cks::bernoulli_rational::bernoulli_weighted_sum;

/// e^{−u/d}.
pub open spec fn rej_weight(d: nat, u: nat) -> real {
    exp(-(u as real / d as real))
}

/// Σ_{i<n} e^{−i/d}.
pub open spec fn rej_weight_sum(d: nat, n: nat) -> real
    decreases n,
{
    if n == 0 { 0real }
    else { rej_weight_sum(d, (n - 1) as nat) + rej_weight(d, (n - 1) as nat) }
}

/// N := Σ_{i<d} e^{−i/d}.
pub open spec fn rej_norm_const(d: nat) -> real {
    rej_weight_sum(d, d)
}

/// Σ_{i<n} e^{−i/d} · ℰ(i).
pub open spec fn rej_weighted_sum(d: nat, e: spec_fn(nat) -> real, n: nat) -> real
    decreases n,
{
    if n == 0 { 0real }
    else {
        rej_weighted_sum(d, e, (n - 1) as nat)
            + rej_weight(d, (n - 1) as nat) * e((n - 1) as nat)
    }
}

/// E_{u ~ rejection_dist}[ℰ(u)] = (1/N) · Σ_{u<d} e^{−u/d} · ℰ(u).
pub open spec fn rej_weighted_avg(d: nat, e: spec_fn(nat) -> real) -> real {
    rej_weighted_sum(d, e, d) / rej_norm_const(d)
}

/// Average rejection rate:  R = 1 − N/d.
/// (P(accept) = Σ_u (1/d)·e^{−u/d} = N/d.)
pub open spec fn rej_rate(d: nat) -> real {
    1real - rej_norm_const(d) / d as real
}

/// Slack amplification factor:  amp = 1/R.
pub open spec fn rej_amp(d: nat) -> real {
    1real / rej_rate(d)
}

// ============================================================================
// Credit allocation
// ============================================================================

/// Per-outcome credit for the uniform rand_u64 step:
///   h(u) = e^{−u/d} · ℰ(u) + (1 − e^{−u/d}) · rej_credit.
pub open spec fn rej_credit_alloc(
    d: nat, e: spec_fn(nat) -> real, rej_credit: real,
) -> spec_fn(real) -> real {
    |u_real: real| {
        let w = exp(-(u_real / d as real));
        w * e(u_real.floor() as nat) + (1real - w) * rej_credit
    }
}

/// Bernoulli flip postcondition:
///   true  arm: ℰ(u)
///   false arm: rej_credit
pub open spec fn rej_flip_e(
    e: spec_fn(nat) -> real, u: nat, rej_credit: real,
) -> spec_fn(bool) -> real {
    |b: bool| if b { e(u) } else { rej_credit }
}

// ============================================================================
// Helper lemmas about e^{−u/d} and Σ_{u<n} e^{−u/d}
// ============================================================================

/// 0 < e^{−u/d} ≤ 1.
proof fn lemma_rej_weight_pos(d: nat, u: nat)
    requires d > 0,
    ensures 0real < rej_weight(d, u), rej_weight(d, u) <= 1real,
{
    assert((u as real) / (d as real) >= 0real) by(nonlinear_arith) requires d > 0;
    axiom_exp_neg_range(u as real / d as real);
}

/// e^{−u/d} < 1 for u > 0.
proof fn lemma_rej_weight_lt1(d: nat, u: nat)
    requires d > 0, u > 0,
    ensures rej_weight(d, u) < 1real,
{
    assert((u as real) / (d as real) > 0real) by(nonlinear_arith) requires u > 0, d > 0;
    axiom_exp_neg_strict(u as real / d as real);
}

/// e^{−0/d} = 1.
proof fn lemma_rej_weight_zero(d: nat)
    requires d > 0,
    ensures rej_weight(d, 0nat) == 1real,
{
    axiom_exp_zero();
    assert((0nat as real) / (d as real) == 0real) by(nonlinear_arith) requires d > 0;
}

/// 0 ≤ Σ_{i<n} e^{−i/d} ≤ n.
pub proof fn lemma_rej_weight_sum_bounds(d: nat, n: nat)
    requires d > 0,
    ensures
        rej_weight_sum(d, n) >= 0real,
        rej_weight_sum(d, n) <= n as real,
    decreases n,
{
    if n > 0 {
        lemma_rej_weight_sum_bounds(d, (n - 1) as nat);
        lemma_rej_weight_pos(d, (n - 1) as nat);
        assert(rej_weight_sum(d, n) <= n as real) by(nonlinear_arith)
            requires
                rej_weight_sum(d, n)
                    == rej_weight_sum(d, (n - 1) as nat) + rej_weight(d, (n - 1) as nat),
                rej_weight_sum(d, (n - 1) as nat) <= (n - 1) as real,
                rej_weight(d, (n - 1) as nat) <= 1real;
    }
}

/// Σ_{i<n} e^{−i/d} > 0 for n ≥ 1.
proof fn lemma_rej_weight_sum_pos(d: nat, n: nat)
    requires d > 0, n >= 1,
    ensures rej_weight_sum(d, n) > 0real,
    decreases n,
{
    if n == 1 {
        lemma_rej_weight_zero(d);
        assert(rej_weight_sum(d, 1nat) == rej_weight_sum(d, 0nat) + rej_weight(d, 0nat));
    } else {
        lemma_rej_weight_sum_pos(d, (n - 1) as nat);
        lemma_rej_weight_pos(d, (n - 1) as nat);
        assert(rej_weight_sum(d, n)
            == rej_weight_sum(d, (n - 1) as nat) + rej_weight(d, (n - 1) as nat));
    }
}

/// Σ_{i<n} e^{−i/d} < n for d ≥ 2.
proof fn lemma_rej_weight_sum_lt_d(d: nat, n: nat)
    requires d > 1, n >= 2, n <= d,
    ensures rej_weight_sum(d, n) < n as real,
    decreases n,
{
    if n == 2 {
        // Σ_{i<2} = e^{−0/d} + e^{−1/d} = 1 + e^{−1/d} < 2 since e^{−1/d} < 1.
        lemma_rej_weight_zero(d);
        lemma_rej_weight_lt1(d, 1nat);
        assert(rej_weight_sum(d, 1nat)
            == rej_weight_sum(d, 0nat) + rej_weight(d, 0nat));
        assert(rej_weight_sum(d, 2nat)
            == rej_weight_sum(d, 1nat) + rej_weight(d, 1nat));
    } else {
        lemma_rej_weight_sum_lt_d(d, (n - 1) as nat);
        lemma_rej_weight_pos(d, (n - 1) as nat);
        assert(rej_weight_sum(d, n) < n as real) by(nonlinear_arith)
            requires
                rej_weight_sum(d, n) == rej_weight_sum(d, (n - 1) as nat) + rej_weight(d, (n - 1) as nat),
                rej_weight_sum(d, (n - 1) as nat) < (n - 1) as real,
                rej_weight(d, (n - 1) as nat) <= 1real;
    }
}

/// e^{−(i+1)/d} = e^{−i/d} · e^{−1/d}.  From axiom_exp_add.
pub proof fn lemma_rej_weight_step(d: nat, i: nat)
    requires d > 0,
    ensures rej_weight(d, i + 1) == rej_weight(d, i) * rej_weight(d, 1),
{
    let x = i as real / d as real;
    let y = 1real / d as real;
    assert(x >= 0real) by(nonlinear_arith)
        requires d > 0, x == i as real / d as real;
    assert(y >= 0real) by(nonlinear_arith)
        requires d > 0, y == 1real / d as real;
    axiom_exp_add(x, y);
    // (i+1)/d = i/d + 1/d, so e^{−(i+1)/d} = e^{−x} · e^{−y}.
    assert((i + 1) as real / d as real == x + y) by(nonlinear_arith)
        requires d > 0, x == i as real / d as real, y == 1real / d as real;
}

/// Telescoping closed form:  (Σ_{i<n} e^{−i/d}) · (1 − e^{−1/d}) = 1 − e^{−n/d}.
///
/// Proof by induction on n.  Each successive term collapses via
/// lemma_rej_weight_step:  writing r1 := e^{−1/d}, w_n := e^{−n/d},
///
///   (Σ_{i<n+1} e^{−i/d}) · (1 − r1)
///     = [(Σ_{i<n} e^{−i/d}) + w_n] · (1 − r1)
///     = (1 − w_n) + w_n − w_n · r1
///     = 1 − w_n · r1
///     = 1 − w_{n+1}                       [by lemma_rej_weight_step]
pub proof fn lemma_rej_weight_sum_telescope(d: nat, n: nat)
    requires d > 0,
    ensures rej_weight_sum(d, n) * (1real - rej_weight(d, 1))
        == 1real - rej_weight(d, n),
    decreases n,
{
    if n == 0 {
        // 0 · (1 − r1) = 0 = 1 − e^{−0/d}.
        lemma_rej_weight_zero(d);
        assert(0real * (1real - rej_weight(d, 1)) == 0real) by(nonlinear_arith);
    } else {
        let k = (n - 1) as nat;
        lemma_rej_weight_sum_telescope(d, k);
        lemma_rej_weight_step(d, k);
        let r1 = rej_weight(d, 1);
        let wk = rej_weight(d, k);
        let sk = rej_weight_sum(d, k);
        // s_n = s_k + w_k;  w_n = w_k · r1;  IH gives s_k · (1 − r1) = 1 − w_k.
        assert(rej_weight_sum(d, n) * (1real - r1) == 1real - rej_weight(d, n))
            by(nonlinear_arith)
            requires
                rej_weight_sum(d, n) == sk + wk,
                rej_weight(d, n) == wk * r1,
                sk * (1real - r1) == 1real - wk;
    }
}

/// Normalizing constant identity:  N · (1 − e^{−1/d}) = 1 − e^{−1}.
/// Special case n = d of lemma_rej_weight_sum_telescope.
pub proof fn lemma_norm_const_identity(d: nat)
    requires d > 0,
    ensures rej_norm_const(d) * (1real - rej_weight(d, 1)) == 1real - exp(-1real),
{
    lemma_rej_weight_sum_telescope(d, d);
    // e^{−d/d} = e^{−1}
    assert(d as real / d as real == 1real) by(nonlinear_arith) requires d > 0;
}

// ============================================================================
// Range of N, R, amp
// ============================================================================

/// 0 < N, 0 < R < 1, amp > 1, for d > 1.
proof fn lemma_rej_rate_range(d: nat)
    requires d > 1,
    ensures
        rej_norm_const(d) > 0real,
        0real < rej_rate(d) < 1real,
        rej_amp(d) > 1real,
{
    lemma_rej_weight_sum_pos(d, d);
    lemma_rej_weight_sum_lt_d(d, d);
    let n = rej_norm_const(d);
    let r = rej_rate(d);
    // From 0 < N < d:  r = 1 − N/d ∈ (0, 1);  amp = 1/r > 1.
    assert(0real < r < 1real) by(nonlinear_arith)
        requires r == 1real - n / d as real, 0real < n < d as real, d > 1;
    assert(rej_amp(d) > 1real) by(nonlinear_arith)
        requires rej_amp(d) == 1real / r, 0real < r < 1real;
}

// ============================================================================
// Structural decomposition of sum_credit(rej_credit_alloc)
// ============================================================================

/// sum_credit(h, n)
///   = Σ_{i<n} e^{−i/d} · ℰ(i)  +  rej_credit · (n − Σ_{i<n} e^{−i/d}).
proof fn lemma_rej_sum_split(
    d: nat, e: spec_fn(nat) -> real, rej_credit: real, n: nat,
)
    requires d > 0,
    ensures
        sum_credit(rej_credit_alloc(d, e, rej_credit), n) ==
            rej_weighted_sum(d, e, n)
                + rej_credit * (n as real - rej_weight_sum(d, n)),
    decreases n,
{
    let alloc = rej_credit_alloc(d, e, rej_credit);
    if n == 0 {
        assert(rej_credit * (0nat as real - 0real) == 0real) by(nonlinear_arith);
    } else {
        let k = (n - 1) as nat;
        let kr = k as real;
        let w = exp(-(kr / d as real));
        lemma_rej_sum_split(d, e, rej_credit, k);

        assert(kr.floor() as nat == k);
        assert(w == rej_weight(d, k));
        assert(sum_credit(alloc, n) == sum_credit(alloc, k) + alloc(kr));
        assert(sum_credit(alloc, n)
            == rej_weighted_sum(d, e, n) + rej_credit * (n as real - rej_weight_sum(d, n)))
            by(nonlinear_arith)
            requires
                sum_credit(alloc, k)
                    == rej_weighted_sum(d, e, k) + rej_credit * (k as real - rej_weight_sum(d, k)),
                alloc(kr) == w * e(k) + (1real - w) * rej_credit,
                rej_weighted_sum(d, e, n) == rej_weighted_sum(d, e, k) + w * e(k),
                rej_weight_sum(d, n) == rej_weight_sum(d, k) + w,
                sum_credit(alloc, n) == sum_credit(alloc, k) + alloc(kr),
                n == k + 1;
    }
}

// ============================================================================
// Non-negativity of the credit allocation
// ============================================================================

/// h(i) ≥ 0 for all i, given ℰ ≥ 0 and rej_credit ≥ 0.
pub proof fn lemma_rej_alloc_nonneg(
    d: nat, e: spec_fn(nat) -> real, rej_credit: real,
)
    requires
        d > 0,
        rej_credit >= 0real,
        forall |u: nat| (#[trigger] e(u)) >= 0real,
    ensures
        forall |i: nat|
            (#[trigger] rej_credit_alloc(d, e, rej_credit)(i as real)) >= 0real,
{
    let alloc = rej_credit_alloc(d, e, rej_credit);
    assert forall |i: nat| (#[trigger] alloc(i as real)) >= 0real by {
        let ir = i as real;
        let w = exp(-(ir / d as real));
        assert(ir.floor() as nat == i);
        lemma_rej_weight_pos(d, i);
        assert(alloc(ir) >= 0real) by(nonlinear_arith)
            requires
                alloc(ir) == w * e(i) + (1real - w) * rej_credit,
                0real < w, w <= 1real,
                e(i) >= 0real, rej_credit >= 0real;
    };
}

// ============================================================================
// Average bound: the central credit equation
// ============================================================================

/// Central credit bound: average(d, rej_credit_alloc) ≤ ε + eps_avg,
/// where rej_credit = amp·ε + eps_avg.
///
/// Algebra:
///   sum_credit(h, d) = Σ_{u<d} e^{−u/d}·ℰ(u) + rej_credit·(d − N)
///                    ≤ N·eps_avg + rej_credit·(d − N)
///                                  [eps_avg ≥ Σ_{u<d} e^{−u/d}·ℰ(u) / N]
///   average = sum / d ≤ (N/d)·eps_avg + (1 − N/d)·rej_credit
///                     = (1−R)·eps_avg + R·(amp·ε + eps_avg)
///                     = eps_avg + R·amp·ε
///                     = eps_avg + ε                  [amp·R = 1]
pub proof fn lemma_rej_average(
    d: nat, e: spec_fn(nat) -> real, eps: real, eps_avg: real,
)
    requires
        d > 1,
        eps > 0real,
        eps_avg >= 0real,
        eps_avg >= rej_weighted_avg(d, e),
        forall |u: nat| (#[trigger] e(u)) >= 0real,
    ensures
        average_nat(d, rej_credit_alloc(
            d, e, rej_amp(d) * eps + eps_avg,
        )) <= eps + eps_avg,
{
    let rej_credit = rej_amp(d) * eps + eps_avg;
    let alloc = rej_credit_alloc(d, e, rej_credit);
    let n_const = rej_norm_const(d);
    let r = rej_rate(d);
    let amp = rej_amp(d);

    lemma_rej_rate_range(d);
    lemma_rej_weight_sum_lt_d(d, d);
    lemma_rej_sum_split(d, e, rej_credit, d);

    let sum = sum_credit(alloc, d);
    let wsum = rej_weighted_sum(d, e, d);

    // Bridge facts:  rej_credit ≥ 0;  wsum ≤ N·eps_avg;  r·amp = 1;
    //                r = (d − N)/d.  Then the final inequality follows.
    assert(rej_credit >= 0real) by(nonlinear_arith)
        requires rej_credit == amp * eps + eps_avg, amp > 1real, eps > 0real, eps_avg >= 0real;
    assert(wsum <= n_const * eps_avg) by(nonlinear_arith)
        requires eps_avg >= wsum / n_const, n_const > 0real;
    assert(r * amp == 1real) by(nonlinear_arith)
        requires amp == 1real / r, r > 0real;
    assert(r == (d as real - n_const) / d as real) by(nonlinear_arith)
        requires r == 1real - n_const / d as real, d > 1;

    assert(average_nat(d, alloc) <= eps + eps_avg) by(nonlinear_arith)
        requires
            sum == wsum + rej_credit * (d as real - n_const),
            wsum <= n_const * eps_avg,
            average_nat(d, alloc) == sum / d as real,
            rej_credit == amp * eps + eps_avg,
            r * amp == 1real,
            r == (d as real - n_const) / d as real,
            0real < r < 1real,
            0real < n_const, n_const < d as real,
            d > 1,
            eps > 0real, eps_avg >= 0real;
}

// ============================================================================
// Proved lemmas used in the sampler
// ============================================================================

/// bws(e^{−u/d}, rej_flip_e) = alloc(u).
proof fn lemma_rej_bws(
    d: nat, u: nat, e: spec_fn(nat) -> real, rej_credit: real,
)
    requires d > 0,
    ensures bernoulli_weighted_sum(
        exp(-(u as real / d as real)),
        rej_flip_e(e, u, rej_credit),
    ) == rej_credit_alloc(d, e, rej_credit)(u as real),
{}

/// rej_credit_alloc(d,e,rc)(0) = e(0):  acceptance at u = 0 is e^{−0/d} = 1.
proof fn lemma_rej_alloc_at_zero(d: nat, e: spec_fn(nat) -> real, rc: real)
    requires d > 0,
    ensures rej_credit_alloc(d, e, rc)(0real) == e(0nat),
{
    let alloc = rej_credit_alloc(d, e, rc);
    assert(0real / d as real == 0real) by(nonlinear_arith) requires d > 0;
    assert(-(0real / d as real) == 0real) by(nonlinear_arith) requires 0real / d as real == 0real;
    axiom_exp_zero();
    assert(exp(-(0real / d as real)) == 1real);
    assert(0real.floor() == 0int);
    assert(alloc(0real) == e(0nat)) by(nonlinear_arith)
        requires
            alloc(0real) == exp(-(0real / d as real)) * e(0real.floor() as nat)
                + (1real - exp(-(0real / d as real))) * rc,
            exp(-(0real / d as real)) == 1real,
            0real.floor() as nat == 0nat;
}

/// average over Uniform{0} (d = 1) of rej_credit_alloc = e(0).
proof fn lemma_rej_avg_one_alloc(e: spec_fn(nat) -> real, rc: real)
    ensures average_nat(1nat, rej_credit_alloc(1nat, e, rc)) == e(0nat),
{
    let alloc = rej_credit_alloc(1nat, e, rc);
    lemma_rej_alloc_at_zero(1nat, e, rc);   // alloc(0) == e(0)
    assert(sum_credit(alloc, 1nat) == alloc(0real)) by {
        reveal_with_fuel(sum_credit, 2);
    }
    assert(average_nat(1nat, alloc) == e(0nat)) by(nonlinear_arith)
        requires average_nat(1nat, alloc) == sum_credit(alloc, 1nat) / (1nat as real),
            sum_credit(alloc, 1nat) == alloc(0real), alloc(0real) == e(0nat);
}

/// For d = 1 the rejection average collapses to e(0):  rej_weighted_avg(1, e) = e(0).
/// (Only outcome is u = 0, with acceptance e^{−0/1} = 1.)
proof fn lemma_rej_avg_one(e: spec_fn(nat) -> real)
    ensures rej_weighted_avg(1nat, e) == e(0nat),
{
    lemma_rej_weight_zero(1nat);   // rej_weight(1, 0) == 1
    assert(rej_weighted_sum(1nat, e, 1nat)
        == rej_weighted_sum(1nat, e, 0nat) + rej_weight(1nat, 0nat) * e(0nat));
    assert(rej_weighted_sum(1nat, e, 1nat) == e(0nat)) by(nonlinear_arith)
        requires rej_weighted_sum(1nat, e, 1nat) == 0real + rej_weight(1nat, 0nat) * e(0nat),
            rej_weight(1nat, 0nat) == 1real;
    assert(rej_weight_sum(1nat, 1nat) == rej_weight_sum(1nat, 0nat) + rej_weight(1nat, 0nat));
    assert(rej_norm_const(1nat) == 1real);
    assert(rej_weighted_avg(1nat, e) == e(0nat)) by(nonlinear_arith)
        requires rej_weighted_avg(1nat, e) == rej_weighted_sum(1nat, e, 1nat) / rej_norm_const(1nat),
            rej_weighted_sum(1nat, e, 1nat) == e(0nat), rej_norm_const(1nat) == 1real;
}

pub fn sample_exp_rejection(
    denom: &UBig,
    Ghost(e): Ghost<spec_fn(nat) -> real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(eps_avg): Ghost<real>,
) -> ((value, out_credit): (UBig, Tracked<ErrorCreditResource>))
    requires
        ubig_view(denom) > 0,
        forall |u: nat| (#[trigger] e(u)) >= 0real,
        eps_avg >= 0real,
        input_credit.view() =~= (ErrorCreditCarrier::Value { car: eps_avg }),
        eps_avg >= rej_weighted_avg(ubig_view(denom), e),
    ensures
        ubig_view(&value) < ubig_view(denom),
        out_credit@.view() =~= (ErrorCreditCarrier::Value { car: e(ubig_view(&value)) }),
{
    let ghost d = ubig_view(denom);

    // d == 1: the only outcome is u = 0, accepted with certainty (e^{−0/1} = 1).
    // No rejection occurs, so the amplification machinery (which needs d > 1) is
    // bypassed — we draw u = 0 directly with the plain credit allocation ℰ.
    let one_ub = ubig_from_u64(1u64);
    if !ubig_lt(&one_ub, denom) {
        proof { assert(d == 1); }
        let ghost alloc = rej_credit_alloc(d, e, 0real);
        proof {
            lemma_rej_avg_one(e);                 // rej_weighted_avg(1,e) == e(0)
            lemma_rej_avg_one_alloc(e, 0real);    // average_nat(1, alloc) == e(0)
            lemma_rej_alloc_nonneg(d, e, 0real);  // forall i. alloc(i as real) >= 0
        }
        let (u_val, Tracked(u_credit)) = rand_ubig(denom, Tracked(input_credit), Ghost(alloc));
        proof {
            assert(ubig_view(&u_val) == 0);                 // < d == 1
            assert(ubig_view(&u_val) as real == 0real);
            lemma_rej_alloc_at_zero(d, e, 0real);           // alloc(0) == e(0)
        }
        return (u_val, Tracked(u_credit));
    }
    proof { assert(d > 1); }

    let ghost amp = rej_amp(d);

    let Tracked(eps_credit) = thin_air();
    let ghost init_eps: real;
    proof {
        init_eps = choose |v: real| v > 0real &&
            (ErrorCreditCarrier::Value { car: v } =~= eps_credit.view());
    }
    let tracked mut credit = ec_combine(input_credit, eps_credit, eps_avg, init_eps);

    let ghost mut g_eps: real = init_eps;
    let ghost mut g_depth: nat;

    proof {
        lemma_rej_rate_range(d);
        archimedean_exp_growth(init_eps, amp);
        g_depth = choose |k: nat| init_eps * pow(amp, k) >= 1real;
    }

    let mut u: UBig = ubig_from_u64(0u64);
    let mut accepted: bool = false;

    while !accepted
        invariant
            ubig_view(denom) > 1,
            d == ubig_view(denom),
            forall |u: nat| (#[trigger] e(u)) >= 0real,
            eps_avg >= 0real,
            eps_avg >= rej_weighted_avg(d, e),
            amp > 1real,
            amp == rej_amp(d),
            // Credit invariant (still rejecting).
            !accepted ==> g_eps > 0real,
            !accepted ==> credit.view() =~= (ErrorCreditCarrier::Value { car: g_eps + eps_avg }),
            !accepted ==> g_eps * pow(amp, g_depth) >= 1real,
            // Accept postcondition.
            accepted ==> ubig_view(&u) < ubig_view(denom),
            accepted ==> credit.view() =~= (ErrorCreditCarrier::Value { car: e(ubig_view(&u)) }),
        decreases g_depth,
    {
        proof {
            if g_depth == 0nat {
                assert(pow(amp, 0nat) == 1real);
                assert(g_eps + eps_avg >= 1real) by(nonlinear_arith)
                    requires g_eps >= 1real, eps_avg >= 0real;
                ec_contradict(&credit);
            }
        }

        let ghost rej_credit = amp * g_eps + eps_avg;
        let ghost alloc = rej_credit_alloc(d, e, rej_credit);

        proof {
            assert(rej_credit >= 0real) by(nonlinear_arith)
                requires rej_credit == amp * g_eps + eps_avg,
                    amp > 1real, g_eps > 0real, eps_avg >= 0real;
            lemma_rej_average(d, e, g_eps, eps_avg);
            lemma_rej_alloc_nonneg(d, e, rej_credit);
        }

        let (u_val, Tracked(u_credit)) = rand_ubig(
            denom, Tracked(credit), Ghost(alloc),
        );

        let ghost uvn = ubig_view(&u_val);
        let ghost g_flip_e = rej_flip_e(e, uvn, rej_credit);
        let ghost g_h_val = alloc(uvn as real);

        proof {
            assert(uvn as real / d as real >= 0real) by(nonlinear_arith)
                requires d > 0;
            axiom_exp_neg_range(uvn as real / d as real);
            lemma_rej_bws(d, uvn, e, rej_credit);
        }

        let (heads, Tracked(flip_out)) = sample_bernoulli_exp_ubig(
            &u_val, denom, Ghost(g_flip_e), Tracked(u_credit), Ghost(g_h_val),
        );

        if heads {
            u = u_val;
            accepted = true;
            proof {
                credit = flip_out;
                g_depth = (g_depth - 1) as nat;
            }
        } else {
            proof {
                let old_eps = g_eps;
                let old_depth = g_depth;
                credit = flip_out;
                g_eps = amp * old_eps;
                g_depth = (old_depth - 1) as nat;

                assert(g_eps > 0real) by(nonlinear_arith)
                    requires g_eps == amp * old_eps, amp > 1real, old_eps > 0real;
                assert(pow(amp, old_depth) == amp * pow(amp, (old_depth - 1) as nat));
                real_assoc_mult(old_eps, amp, pow(amp, (old_depth - 1) as nat));
                assert(g_eps * pow(amp, g_depth) >= 1real) by(nonlinear_arith)
                    requires
                        g_eps == amp * old_eps,
                        old_eps * pow(amp, old_depth) >= 1real,
                        pow(amp, old_depth) == amp * pow(amp, (old_depth - 1) as nat),
                        (old_eps * amp) * pow(amp, (old_depth - 1) as nat)
                            == old_eps * (amp * pow(amp, (old_depth - 1) as nat)),
                        g_depth == (old_depth - 1) as nat,
                        amp > 1real, old_eps > 0real;
            }
        }
    }

    (u, Tracked(credit))
}

} // verus!
