use vstd::prelude::*;

verus! {

#[cfg(verus_keep_ghost)]
use crate::cks::bernoulli_exp1::*;
#[cfg(verus_keep_ghost)]
use crate::ec::*;
#[cfg(verus_keep_ghost)]
use crate::math::pow::pow;
#[cfg(verus_keep_ghost)]
use crate::math::series::{lemma_pow_nonneg, partial_sum};
#[cfg(verus_keep_ghost)]
use crate::math::exp::{exp, factorial, exp_taylor_term, exp_taylor_seq, axiom_exp_taylor_bounds};
#[cfg(verus_keep_ghost)]
use crate::cks::bernoulli_rational::bernoulli_weighted_sum;

// ============================================================================
// Taylor partial sum connection: p_k ∈ [0, 1]
//
// p_k = [k odd] + (k-1)!/x^{k-1} · R_k, where R_k = exp(-x) - T_k(x).
// Since |R_k| ≤ x^k/k! (alternating series), |(k-1)!/x^{k-1} · R_k| ≤ x/k.
// ============================================================================

/// factorial(n) > 0 for all n.
pub proof fn lemma_factorial_pos(n: nat)
    ensures factorial(n) > 0real,
    decreases n,
{
    if n == 0 {
    } else {
        lemma_factorial_pos((n - 1) as nat);
        assert(factorial(n) == n as real * factorial((n - 1) as nat));
        assert(factorial(n) > 0real) by(nonlinear_arith)
            requires n >= 1, factorial((n - 1) as nat) > 0real,
                factorial(n) == n as real * factorial((n - 1) as nat);
    }
}

/// pow(x, n) > 0 for x > 0.
pub proof fn lemma_pow_pos(x: real, n: nat)
    requires x > 0real,
    ensures pow(x, n) > 0real,
    decreases n,
{
    if n == 0 {
    } else {
        lemma_pow_pos(x, (n - 1) as nat);
        assert(pow(x, n) == x * pow(x, (n - 1) as nat));
        assert(pow(x, n) > 0real) by(nonlinear_arith)
            requires x > 0real, pow(x, (n - 1) as nat) > 0real,
                pow(x, n) == x * pow(x, (n - 1) as nat);
    }
}

/// pow(-x, k) = (-1)^k · pow(x, k).
pub proof fn lemma_pow_neg_parity(x: real, k: nat)
    requires x > 0real,
    ensures
        k % 2 == 0 ==> pow(-x, k) == pow(x, k),
        k % 2 == 1 ==> pow(-x, k) == -pow(x, k),
    decreases k,
{
    if k == 0 {
    } else if k == 1 {
        assert(pow(-x, 1nat) == (-x) * pow(-x, 0nat));
        assert(pow(-x, 0nat) == 1real);
        assert(pow(x, 1nat) == x * pow(x, 0nat));
        assert(pow(x, 0nat) == 1real);
    } else {
        lemma_pow_neg_parity(x, (k - 2) as nat);
        // pow(-x, k) = (-x)·(-x)·pow(-x, k-2) = x²·pow(-x, k-2)
        assert(pow(-x, k) == (-x) * pow(-x, (k - 1) as nat));
        assert(pow(-x, (k - 1) as nat) == (-x) * pow(-x, (k - 2) as nat));
        assert(pow(x, k) == x * pow(x, (k - 1) as nat));
        assert(pow(x, (k - 1) as nat) == x * pow(x, (k - 2) as nat));
        // k and k-2 have the same parity
        if k % 2 == 0 {
            // k-2 is even, so pow(-x, k-2) = pow(x, k-2) by IH
            assert(pow(-x, k) == pow(x, k))
                by(nonlinear_arith)
                requires
                    pow(-x, k) == (-x) * ((-x) * pow(-x, (k - 2) as nat)),
                    pow(x, k) == x * (x * pow(x, (k - 2) as nat)),
                    pow(-x, (k - 2) as nat) == pow(x, (k - 2) as nat);
        } else {
            // k-2 is odd, so pow(-x, k-2) = -pow(x, k-2) by IH
            assert(pow(-x, k) == -pow(x, k))
                by(nonlinear_arith)
                requires
                    pow(-x, k) == (-x) * ((-x) * pow(-x, (k - 2) as nat)),
                    pow(x, k) == x * (x * pow(x, (k - 2) as nat)),
                    pow(-x, (k - 2) as nat) == -pow(x, (k - 2) as nat);
        }
    }
}

/// (k-1)!/x^{k-1} · (-x)^k/k! = (-1)^k · x/k.
/// Proved by cross-multiplying to avoid division in nonlinear_arith.
pub proof fn lemma_scale_term_product(x: real, k: nat)
    requires x > 0real, k >= 1,
    ensures ({
        let scale = factorial((k - 1) as nat) / pow(x, (k - 1) as nat);
        let term_k = exp_taylor_term(x, k);
        &&& k % 2 == 0 ==> scale * term_k == x / k as real
        &&& k % 2 == 1 ==> scale * term_k == -x / k as real
    }),
{
    let scale = factorial((k - 1) as nat) / pow(x, (k - 1) as nat);
    let term_k = exp_taylor_term(x, k);
    let fk1 = factorial((k - 1) as nat);
    let pk1 = pow(x, (k - 1) as nat);
    let fk = factorial(k);
    let pk = pow(x, k);
    lemma_factorial_pos((k - 1) as nat);
    lemma_factorial_pos(k);
    lemma_pow_pos(x, (k - 1) as nat);
    lemma_pow_pos(x, k);
    lemma_pow_neg_parity(x, k);

    assert(fk == k as real * fk1);
    assert(pk == x * pk1);

    // Clear denominators: scale·pk1 = fk1 and term_k·fk = pow(-x,k)
    assert(scale * pk1 == fk1)
        by(nonlinear_arith) requires scale == fk1 / pk1, pk1 > 0real;
    assert(term_k * fk == pow(-x, k))
        by(nonlinear_arith) requires term_k == pow(-x, k) / fk, fk > 0real;
    // Combine: scale·term_k·pk1·fk = fk1·pow(-x,k)
    assert(scale * term_k * pk1 * fk == fk1 * pow(-x, k))
        by(nonlinear_arith)
        requires scale * pk1 == fk1, term_k * fk == pow(-x, k);

    // Substitute pow(-x,k) = ±pk = ±x·pk1, cancel to get scale·term_k = ±x/k
    if k % 2 == 0 {
        assert(scale * term_k * pk1 * fk == fk1 * x * pk1)
            by(nonlinear_arith)
            requires scale * term_k * pk1 * fk == fk1 * pow(-x, k),
                pow(-x, k) == pk, pk == x * pk1;
        assert((x / k as real) * pk1 * fk == fk1 * x * pk1)
            by(nonlinear_arith) requires fk == k as real * fk1, k >= 1;
        assert(scale * term_k == x / k as real)
            by(nonlinear_arith)
            requires scale * term_k * pk1 * fk == fk1 * x * pk1,
                (x / k as real) * pk1 * fk == fk1 * x * pk1,
                pk1 > 0real, fk > 0real;
    } else {
        assert(scale * term_k * pk1 * fk == -(fk1 * x * pk1))
            by(nonlinear_arith)
            requires scale * term_k * pk1 * fk == fk1 * pow(-x, k),
                pow(-x, k) == -pk, pk == x * pk1;
        assert((-x / k as real) * pk1 * fk == -(fk1 * x * pk1))
            by(nonlinear_arith) requires fk == k as real * fk1, k >= 1;
        assert(scale * term_k == -x / k as real)
            by(nonlinear_arith)
            requires scale * term_k * pk1 * fk == -(fk1 * x * pk1),
                (-x / k as real) * pk1 * fk == -(fk1 * x * pk1),
                pk1 > 0real, fk > 0real;
    }
}

/// Base case: exp1_p_formula(x, 1) == exp(-x).
///
/// T_1 = 1, R_1 = exp(-x) - 1, scale = 0!/x^0 = 1, so p_1 = 1 + (exp(-x) - 1) = exp(-x).
pub proof fn lemma_exp1_p_formula_base(x: real)
    requires 0real < x <= 1real,
    ensures exp1_p_formula(x, 1) == exp(-x),
{
    let seq = exp_taylor_seq(x);
    // Unfold T_1 = partial_sum(seq, 1) = 0 + seq(0) = pow(-x,0)/factorial(0) = 1
    assert(partial_sum(seq, 1nat) == partial_sum(seq, 0nat) + seq(0nat));
    assert(partial_sum(seq, 0nat) == 0real);
    assert(pow(-x, 0nat) == 1real);
    assert(factorial(0nat) == 1real);
    assert(pow(x, 0nat) == 1real);
    // p_1 = 1 + (1/1)·(exp(-x) - 1) = exp(-x)
    let remainder = exp(-x) - partial_sum(seq, 1nat);
    let scale = factorial(0nat) / pow(x, 0nat);
    assert(1real + scale * remainder == exp(-x))
        by(nonlinear_arith)
        requires scale == 1real, remainder == exp(-x) - 1real;
}

/// exp1_next_p preserves the formula: next_p(k, formula(k)) == formula(k+1).
/// Key identity: R_{k+1} = R_k - (-x)^k/k! (partial sum step).
pub proof fn lemma_exp1_p_formula_step(x: real, k: nat)
    requires
        0real < x <= 1real, k >= 1,
    ensures
        exp1_next_p(x, k, exp1_p_formula(x, k))
            == exp1_p_formula(x, k + 1),
{
    let seq = exp_taylor_seq(x);
    let amp = exp1_amp(x, k);
    let t_k = partial_sum(seq, k);
    let t_k1 = partial_sum(seq, k + 1);
    let r_k = exp(-x) - t_k;
    let r_k1 = exp(-x) - t_k1;
    let s_k = factorial((k - 1) as nat) / pow(x, (k - 1) as nat);
    let s_k1 = factorial(k) / pow(x, k);
    let p_k = exp1_p_formula(x, k);
    let term_k = exp_taylor_term(x, k);

    // Partial sum step: T_{k+1} = T_k + term_k, so R_{k+1} = R_k - term_k
    assert(t_k1 == t_k + seq(k));
    assert(seq(k) == term_k);
    assert(r_k1 == r_k - term_k);

    assert(amp == k as real / x);

    lemma_factorial_pos((k - 1) as nat);
    lemma_factorial_pos(k);
    lemma_pow_pos(x, (k - 1) as nat);
    lemma_pow_pos(x, k);

    // s_k1 = amp · s_k (cross-multiply to avoid division)
    let fk1 = factorial((k - 1) as nat);
    let pk1 = pow(x, (k - 1) as nat);
    let fk = factorial(k);
    let pk = pow(x, k);
    assert(fk == k as real * fk1);
    assert(pk == x * pk1);
    assert(s_k1 * pk == fk)
        by(nonlinear_arith) requires s_k1 == fk / pk, pk > 0real;
    assert(s_k * pk1 == fk1)
        by(nonlinear_arith) requires s_k == fk1 / pk1, pk1 > 0real;
    assert(amp * s_k * pk == amp * fk1 * x)
        by(nonlinear_arith) requires s_k * pk1 == fk1, pk == x * pk1;
    assert(amp * fk1 * x == fk)
        by(nonlinear_arith) requires amp == k as real / x, fk == k as real * fk1, x > 0real;
    assert(s_k1 == amp * s_k)
        by(nonlinear_arith) requires s_k1 * pk == fk, amp * s_k * pk == fk, pk > 0real;

    // s_k1 · term_k = ±1 (cross-multiply: s_k1·term_k·pk = pow(-x,k) = ±pk)
    lemma_pow_neg_parity(x, k);
    assert(s_k1 * term_k * pk == pow(-x, k))
        by(nonlinear_arith)
        requires s_k1 == fk / pk, term_k == pow(-x, k) / fk,
            fk > 0real, pk > 0real;

    if k % 2 == 1 {
        assert(s_k1 * term_k == -1real) by(nonlinear_arith)
            requires s_k1 * term_k * pk == pow(-x, k), pow(-x, k) == -pk, pk > 0real;
        // k odd: next = (p_k-1)·amp + 1 = s_k1·r_k + 1
        //        formula(k+1) [even] = s_k1·r_k1 = s_k1·r_k - s_k1·term_k = s_k1·r_k + 1
        let next = exp1_next_p(x, k, p_k);
        assert(next == s_k1 * r_k + 1real) by(nonlinear_arith)
            requires next == (p_k - 1real) * amp + 1real,
                p_k == 1real + s_k * r_k, s_k1 == amp * s_k;
        assert(exp1_p_formula(x, k + 1) == s_k1 * r_k1);
        assert(s_k1 * r_k1 == s_k1 * r_k - s_k1 * term_k)
            by(nonlinear_arith) requires r_k1 == r_k - term_k;
        assert(s_k1 * r_k1 == next) by(nonlinear_arith)
            requires s_k1 * r_k1 == s_k1 * r_k - s_k1 * term_k,
                s_k1 * term_k == -1real, next == s_k1 * r_k + 1real;
    } else {
        assert(s_k1 * term_k == 1real) by(nonlinear_arith)
            requires s_k1 * term_k * pk == pow(-x, k), pow(-x, k) == pk, pk > 0real;
        // k even: next = p_k·amp = s_k1·r_k
        //         formula(k+1) [odd] = 1 + s_k1·r_k1 = 1 + s_k1·r_k - 1 = s_k1·r_k
        let next = exp1_next_p(x, k, p_k);
        assert(next == s_k1 * r_k) by(nonlinear_arith)
            requires next == p_k * amp, p_k == s_k * r_k, s_k1 == amp * s_k;
        assert(exp1_p_formula(x, k + 1) == 1real + s_k1 * r_k1);
        assert(s_k1 * r_k1 == s_k1 * r_k - s_k1 * term_k)
            by(nonlinear_arith) requires r_k1 == r_k - term_k;
        assert(1real + s_k1 * r_k1 == next) by(nonlinear_arith)
            requires s_k1 * r_k1 == s_k1 * r_k - s_k1 * term_k,
                s_k1 * term_k == 1real, next == s_k1 * r_k;
    }
}

/// exp1_p_formula(x, k) ∈ [0, 1]. Uses axiom_exp_taylor_bounds to bound R_k,
/// then scales by (k-1)!/x^{k-1} to get |scaled remainder| ≤ x/k ≤ 1.
pub proof fn lemma_exp1_p_formula_range(x: real, k: nat)
    requires 0real < x <= 1real, k >= 1,
    ensures
        0real <= exp1_p_formula(x, k) <= 1real,
{
    let seq = exp_taylor_seq(x);
    let t_k = partial_sum(seq, k);
    let t_k1 = partial_sum(seq, k + 1);
    let r_k = exp(-x) - t_k;
    let r_k1 = exp(-x) - t_k1;
    let scale = factorial((k - 1) as nat) / pow(x, (k - 1) as nat);
    let term_k = exp_taylor_term(x, k);

    axiom_exp_taylor_bounds(x, k);
    axiom_exp_taylor_bounds(x, k + 1);

    assert(t_k1 == t_k + seq(k));
    assert(seq(k) == term_k);
    assert(r_k1 == r_k - term_k);

    lemma_factorial_pos((k - 1) as nat);
    lemma_pow_pos(x, (k - 1) as nat);
    assert(scale > 0real)
        by(nonlinear_arith)
        requires scale == factorial((k - 1) as nat) / pow(x, (k - 1) as nat),
            factorial((k - 1) as nat) > 0real, pow(x, (k - 1) as nat) > 0real;
    lemma_scale_term_product(x, k);

    if k % 2 == 0 {
        // k even: 0 ≤ R_k ≤ term_k, so scale·R_k ∈ [0, x/k] ⊂ [0, 1]
        assert(r_k >= 0real) by(nonlinear_arith) requires t_k <= exp(-x), r_k == exp(-x) - t_k;
        assert(r_k1 <= 0real) by(nonlinear_arith) requires exp(-x) <= t_k1, r_k1 == exp(-x) - t_k1;
        assert(r_k <= term_k) by(nonlinear_arith) requires r_k1 == r_k - term_k, r_k1 <= 0real;
        assert(scale * r_k <= scale * term_k) by(nonlinear_arith) requires r_k <= term_k, scale > 0real;
        assert(scale * r_k >= 0real) by(nonlinear_arith) requires r_k >= 0real, scale > 0real;
        assert(x / k as real <= 1real) by(nonlinear_arith) requires x <= 1real, k >= 1;
        assert(exp1_p_formula(x, k) == scale * r_k);
    } else {
        // k odd: term_k ≤ R_k ≤ 0, so 1 + scale·R_k ∈ [1-x/k, 1] ⊂ [0, 1]
        assert(r_k <= 0real) by(nonlinear_arith) requires exp(-x) <= t_k, r_k == exp(-x) - t_k;
        assert(r_k1 >= 0real) by(nonlinear_arith) requires t_k1 <= exp(-x), r_k1 == exp(-x) - t_k1;
        assert(r_k >= term_k) by(nonlinear_arith) requires r_k1 == r_k - term_k, r_k1 >= 0real;
        assert(scale * r_k >= scale * term_k) by(nonlinear_arith) requires r_k >= term_k, scale > 0real;
        assert(scale * r_k <= 0real) by(nonlinear_arith) requires r_k <= 0real, scale > 0real;
        assert(x / k as real <= 1real) by(nonlinear_arith) requires x <= 1real, k >= 1;
        assert(exp1_p_formula(x, k) == 1real + scale * r_k);
        assert(exp1_p_formula(x, k) <= 1real) by(nonlinear_arith)
            requires exp1_p_formula(x, k) == 1real + scale * r_k, scale * r_k <= 0real;
        assert(exp1_p_formula(x, k) >= 0real) by(nonlinear_arith)
            requires exp1_p_formula(x, k) == 1real + scale * r_k,
                scale * r_k >= scale * term_k, scale * term_k == -x / k as real,
                x / k as real <= 1real;
    }
}

// ============================================================================
// Credit conservation lemmas
// ============================================================================

/// prob·new_eps + (1-prob)·e(k%2==1) == eps, where prob = x/k.
/// The key identity is prob·amp == 1.
#[verifier::nonlinear]
pub proof fn lemma_exp1_flip_average(x: real, k: nat, eps: real, e: spec_fn(bool) -> real)
    requires x > 0real, k >= 1,
    ensures ({
        let new_eps = exp1_new_eps(x, k, eps, e);
        let flip_e = exp1_flip_e(e, k, new_eps);
        let prob = x / k as real;
        bernoulli_weighted_sum(prob, flip_e) == eps
    }),
{
}

/// p_k = (x/k)·p_{k+1} + (1-x/k)·[k odd] (law of total probability at step k).
pub proof fn lemma_exp1_next_p_recursion(x: real, k: nat, p_k: real)
    requires x > 0real, k >= 1,
    ensures ({
        let p_next = exp1_next_p(x, k, p_k);
        let prob = x / k as real;
        p_k == prob * p_next + (1real - prob) * (if k % 2 == 1 { 1real } else { 0real })
    }),
{
    let amp = exp1_amp(x, k);
    let prob = x / k as real;
    let p_next = exp1_next_p(x, k, p_k);
    assert(prob * amp == 1real) by(nonlinear_arith)
        requires prob == x / k as real, amp == k as real / x, x > 0real, k >= 1;
    if k % 2 == 1 {
        assert(p_k == prob * p_next + (1real - prob) * 1real)
            by(nonlinear_arith)
            requires p_next == (p_k - 1real) * amp + 1real, prob * amp == 1real;
    } else {
        assert(p_k == prob * p_next + (1real - prob) * 0real)
            by(nonlinear_arith)
            requires p_next == p_k * amp, prob * amp == 1real;
    }
}

/// amp·dist_eps - (amp-1)·e(k%2==1) >= bws(p_next, e), given dist_eps >= bws(p_k, e).
/// Uses: (A) amp·bws(p_k) - (amp-1)·e(k%2==1) == bws(p_next),
///       (B) amp·dist_eps >= amp·bws(p_k) since amp >= 1.
pub proof fn lemma_exp1_shift_bound(
    x: real, k: nat,
    dist_eps: real, e: spec_fn(bool) -> real,
    p_k: real, p_next: real,
)
    requires
        0real < x <= 1real, k >= 1,
        dist_eps >= bernoulli_weighted_sum(p_k, e),
        p_k == (x / k as real) * p_next
             + (1real - x / k as real) * (if k % 2 == 1 { 1real } else { 0real }),
    ensures ({
        let amp = exp1_amp(x, k);
        amp * dist_eps - (amp - 1real) * e(k % 2 == 1) >= bernoulli_weighted_sum(p_next, e)
    }),
{
    let amp = exp1_amp(x, k);
    let prob = x / k as real;
    assert(prob * amp == 1real) by(nonlinear_arith)
        requires prob == x / k as real, amp == k as real / x, x > 0real, k >= 1;

    let eT = e(true);
    let eF = e(false);
    let amp_pk = amp * p_k;

    // (A) amp·bws(p_k) - (amp-1)·e(k%2==1) == bws(p_next)
    //     Uses: amp·p_k = p_next + (amp-1)·[k odd] (from prob·amp == 1)
    if k % 2 == 1 {
        assert(amp_pk == p_next + (amp - 1real)) by(nonlinear_arith)
            requires amp_pk == amp * p_k,
                p_k == prob * p_next + (1real - prob), prob * amp == 1real;
        assert(amp_pk * eT + (amp - amp_pk) * eF - (amp - 1real) * eT
            == p_next * eT + (1real - p_next) * eF)
            by(nonlinear_arith) requires amp_pk == p_next + (amp - 1real);
    } else {
        assert(amp_pk == p_next) by(nonlinear_arith)
            requires amp_pk == amp * p_k,
                p_k == prob * p_next, prob * amp == 1real;
        assert(amp_pk * eT + (amp - amp_pk) * eF - (amp - 1real) * eF
            == p_next * eT + (1real - p_next) * eF)
            by(nonlinear_arith) requires amp_pk == p_next;
    }
    // amp·bws(p_k) = amp_pk·eT + (amp-amp_pk)·eF (distribute, split for solver)
    assert(amp * (p_k * eT) == amp_pk * eT)
        by(nonlinear_arith) requires amp_pk == amp * p_k;
    assert(amp * ((1real - p_k) * eF) == (amp - amp_pk) * eF)
        by(nonlinear_arith) requires amp_pk == amp * p_k;
    assert(amp * (p_k * eT + (1real - p_k) * eF) == amp_pk * eT + (amp - amp_pk) * eF)
        by(nonlinear_arith)
        requires amp * (p_k * eT) == amp_pk * eT,
            amp * ((1real - p_k) * eF) == (amp - amp_pk) * eF;

    let bws_pk = bernoulli_weighted_sum(p_k, e);
    let bws_pn = bernoulli_weighted_sum(p_next, e);
    assert(amp >= 1real) by(nonlinear_arith)
        requires amp == k as real / x, 0real < x <= 1real, k >= 1;
    assert(amp * dist_eps >= amp * bws_pk)
        by(nonlinear_arith) requires dist_eps >= bws_pk, amp >= 1real;

    if k % 2 == 1 {
        assert(amp * bws_pk - (amp - 1real) * eT == bws_pn) by(nonlinear_arith)
            requires amp * (p_k * eT + (1real - p_k) * eF) == amp_pk * eT + (amp - amp_pk) * eF,
                amp_pk * eT + (amp - amp_pk) * eF - (amp - 1real) * eT == bws_pn,
                bws_pk == p_k * eT + (1real - p_k) * eF;
    } else {
        assert(amp * bws_pk - (amp - 1real) * eF == bws_pn) by(nonlinear_arith)
            requires amp * (p_k * eT + (1real - p_k) * eF) == amp_pk * eT + (amp - amp_pk) * eF,
                amp_pk * eT + (amp - amp_pk) * eF - (amp - 1real) * eF == bws_pn,
                bws_pk == p_k * eT + (1real - p_k) * eF;
    }
}

/// slack_product(k, depth) >= 2^depth for k >= 2 (each factor >= 2).
pub proof fn lemma_slack_product_ge_pow2(x: real, k: nat, depth: nat)
    requires 0real < x <= 1real, k >= 2,
    ensures slack_product(x, k, depth) >= pow(2real, depth),
    decreases depth,
{
    if depth == 0 {
    } else {
        lemma_slack_product_ge_pow2(x, k + 1, (depth - 1) as nat);
        let a = exp1_amp(x, k);
        let sp = slack_product(x, k + 1, (depth - 1) as nat);
        assert(a >= 2real) by(nonlinear_arith)
            requires a == k as real / x, 0real < x <= 1real, k >= 2;
        assert(slack_product(x, k, depth) == a * sp);
        lemma_pow_nonneg(2real, (depth - 1) as nat);
        real_mul_ineq(a, sp, 2real, pow(2real, (depth - 1) as nat));
    }
}

/// slack_product(1, depth) >= 2^{depth-1} (first factor >= 1, rest >= 2).
pub proof fn lemma_slack_product_k1_bound(x: real, depth: nat)
    requires 0real < x <= 1real, depth >= 1,
    ensures slack_product(x, 1nat, depth) >= pow(2real, (depth - 1) as nat),
{
    lemma_slack_product_ge_pow2(x, 2nat, (depth - 1) as nat);
    let a = exp1_amp(x, 1nat);
    let sp = slack_product(x, 2nat, (depth - 1) as nat);
    assert(a >= 1real) by(nonlinear_arith)
        requires a == 1real / x, 0real < x <= 1real;
    assert(slack_product(x, 1nat, depth) == a * sp);
    // a · sp >= 1 · 2^{depth-1}
    lemma_pow_nonneg(2real, (depth - 1) as nat);
    real_mul_ineq(a, sp, 1real, pow(2real, (depth - 1) as nat));
}

#[verifier::nonlinear]
pub proof fn real_mul_ineq(a: real, b: real, a_lb: real, b_lb: real)
    requires a >= a_lb, b >= b_lb, a_lb >= 0real, b_lb >= 0real,
    ensures a * b >= a_lb * b_lb,
{}

} // verus!
