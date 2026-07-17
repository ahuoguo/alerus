use vstd::prelude::*;

verus! {

#[cfg(verus_keep_ghost)]
use crate::cks::exp_rejection::*;
#[cfg(verus_keep_ghost)]
use crate::ec::*;
#[cfg(verus_keep_ghost)]
use crate::math::exp::{
    exp,
    axiom_exp_zero,
    axiom_exp_neg_range,
    axiom_exp_neg_strict,
    axiom_exp_add,
};
#[cfg(verus_keep_ghost)]
use crate::rand_primitives::{average_nat, sum_credit};
#[cfg(verus_keep_ghost)]
use crate::cks::bernoulli_rational::bernoulli_weighted_sum;

// ============================================================================
// Helper lemmas about e^{−u/d} and Σ_{u<n} e^{−u/d}
// ============================================================================

/// 0 < e^{−u/d} ≤ 1.
pub proof fn lemma_rej_weight_pos(d: nat, u: nat)
    requires d > 0,
    ensures 0real < rej_weight(d, u), rej_weight(d, u) <= 1real,
{
    assert((u as real) / (d as real) >= 0real) by(nonlinear_arith) requires d > 0;
    axiom_exp_neg_range(u as real / d as real);
}

/// e^{−u/d} < 1 for u > 0.
pub proof fn lemma_rej_weight_lt1(d: nat, u: nat)
    requires d > 0, u > 0,
    ensures rej_weight(d, u) < 1real,
{
    assert((u as real) / (d as real) > 0real) by(nonlinear_arith) requires u > 0, d > 0;
    axiom_exp_neg_strict(u as real / d as real);
}

/// e^{−0/d} = 1.
pub proof fn lemma_rej_weight_zero(d: nat)
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
pub proof fn lemma_rej_weight_sum_pos(d: nat, n: nat)
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
pub proof fn lemma_rej_weight_sum_lt_d(d: nat, n: nat)
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
pub proof fn lemma_rej_rate_range(d: nat)
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
pub proof fn lemma_rej_sum_split(
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

        assert(w == rej_weight(d, k));
        assert(sum_credit(alloc, n) == sum_credit(alloc, k) + alloc(k));
        assert(sum_credit(alloc, n)
            == rej_weighted_sum(d, e, n) + rej_credit * (n as real - rej_weight_sum(d, n)))
            by(nonlinear_arith)
            requires
                sum_credit(alloc, k)
                    == rej_weighted_sum(d, e, k) + rej_credit * (k as real - rej_weight_sum(d, k)),
                alloc(k) == w * e(k) + (1real - w) * rej_credit,
                rej_weighted_sum(d, e, n) == rej_weighted_sum(d, e, k) + w * e(k),
                rej_weight_sum(d, n) == rej_weight_sum(d, k) + w,
                sum_credit(alloc, n) == sum_credit(alloc, k) + alloc(k),
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
            (#[trigger] rej_credit_alloc(d, e, rej_credit)(i)) >= 0real,
{
    let alloc = rej_credit_alloc(d, e, rej_credit);
    assert forall |i: nat| (#[trigger] alloc(i)) >= 0real by {
        let w = exp(-(i as real / d as real));
        lemma_rej_weight_pos(d, i);
        assert(alloc(i) >= 0real) by(nonlinear_arith)
            requires
                alloc(i) == w * e(i) + (1real - w) * rej_credit,
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
pub proof fn lemma_rej_bws(
    d: nat, u: nat, e: spec_fn(nat) -> real, rej_credit: real,
)
    requires d > 0,
    ensures bernoulli_weighted_sum(
        exp(-(u as real / d as real)),
        rej_flip_e(e, u, rej_credit),
    ) == rej_credit_alloc(d, e, rej_credit)(u),
{}

/// rej_credit_alloc(d,e,rc)(0) = e(0):  acceptance at u = 0 is e^{−0/d} = 1.
pub proof fn lemma_rej_alloc_at_zero(d: nat, e: spec_fn(nat) -> real, rc: real)
    requires d > 0,
    ensures rej_credit_alloc(d, e, rc)(0nat) == e(0nat),
{
    let alloc = rej_credit_alloc(d, e, rc);
    assert(0nat as real / d as real == 0real) by(nonlinear_arith) requires d > 0;
    assert(-(0nat as real / d as real) == 0real) by(nonlinear_arith) requires 0nat as real / d as real == 0real;
    axiom_exp_zero();
    assert(exp(-(0nat as real / d as real)) == 1real);
    assert(alloc(0nat) == e(0nat)) by(nonlinear_arith)
        requires
            alloc(0nat) == exp(-(0nat as real / d as real)) * e(0nat)
                + (1real - exp(-(0nat as real / d as real))) * rc,
            exp(-(0nat as real / d as real)) == 1real;
}

/// average over Uniform{0} (d = 1) of rej_credit_alloc = e(0).
pub proof fn lemma_rej_avg_one_alloc(e: spec_fn(nat) -> real, rc: real)
    ensures average_nat(1nat, rej_credit_alloc(1nat, e, rc)) == e(0nat),
{
    let alloc = rej_credit_alloc(1nat, e, rc);
    lemma_rej_alloc_at_zero(1nat, e, rc);   // alloc(0) == e(0)
    assert(sum_credit(alloc, 1nat) == alloc(0nat)) by {
        reveal_with_fuel(sum_credit, 2);
    }
    assert(average_nat(1nat, alloc) == e(0nat)) by(nonlinear_arith)
        requires average_nat(1nat, alloc) == sum_credit(alloc, 1nat) / (1nat as real),
            sum_credit(alloc, 1nat) == alloc(0nat), alloc(0nat) == e(0nat);
}

/// For d = 1 the rejection average collapses to e(0):  rej_weighted_avg(1, e) = e(0).
/// (Only outcome is u = 0, with acceptance e^{−0/1} = 1.)
pub proof fn lemma_rej_avg_one(e: spec_fn(nat) -> real)
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

} // verus!
