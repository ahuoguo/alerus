//! Sample from Bernoulli(exp(-x)) for x ∈ (0, 1].
//!
//! ```text
//!   Loop k = 1, 2, ...: flip Bernoulli(x/k).
//!     Heads → increment k.  Tails → return (k is odd).
//! ```
//!
//! We prove the following Expectation Preservation Rule
//!
//! ```text
//!   ε ≥ exp(-x) · ℰ(true) + (1 - exp(-x)) · ℰ(false)
//!   ---------------------------------------------------
//!   [{ ↯(ε) }] sample_bernoulli_exp1(x) [{ v. ↯(ℰ(v)) }]
//! ```
//!
//! At step k, flip Bernoulli(x/k) via sample_bernoulli_rational.
//!   tails (stop):     credit e(k%2==1)
//!   heads (continue): credit new_eps = amp·eps - (amp-1)·e(k%2==1)
//! where amp = k·denom_x/numer_x = k/x.
//!
//! Slack amplifies by factor amp ≥ 1 at each step.
//! Termination: slack · Π amp_j ≥ 1, tracked via slack_product.

use vstd::prelude::*;
use random::{ubig_from_u64, ubig_succ, ubig_mul_u64, ubig_mul, ubig_is_odd, UBig};

verus! {

use crate::ec::*;
use crate::rand_primitives::thin_air;
#[cfg(verus_keep_ghost)]
use crate::math::pow::{pow, archimedean_exp_growth};
#[cfg(verus_keep_ghost)]
use crate::math::real::real_assoc_mult;
#[cfg(verus_keep_ghost)]
use crate::math::series::{lemma_pow_nonneg, partial_sum};
#[cfg(verus_keep_ghost)]
use crate::math::exp::{exp, factorial, exp_taylor_term, exp_taylor_seq, axiom_exp_taylor_bounds};
#[cfg(verus_keep_ghost)]
use crate::extern_spec::ExUBig;
#[cfg(verus_keep_ghost)]
use crate::extern_spec::ubig_view;
use crate::cks::bernoulli_rational::sample_bernoulli_rational;
#[cfg(verus_keep_ghost)]
use crate::cks::bernoulli_rational::{bernoulli_weighted_sum, lemma_bws_nonneg};

// ============================================================================
// Spec functions (all use nat for step k)
// ============================================================================

// All the credit-bookkeeping spec functions and lemmas below are keyed on the
// real probability `x ∈ (0, 1]` rather than a (numer, denom) representation, so
// the same proof serves both the u64 and the UBig executable wrappers.

/// Amplification factor at step k: k / x.
pub open spec fn exp1_amp(x: real, k: nat) -> real {
    k as real / x
}

/// New eps after the flip: amp · eps - (amp - 1) · e(k%2==1).
pub open spec fn exp1_new_eps(x: real, k: nat, eps: real, e: spec_fn(bool) -> real) -> real {
    let amp = exp1_amp(x, k);
    amp * eps - (amp - 1real) * e(k % 2 == 1)
}

/// Credit allocation for the Bernoulli(x/k) flip at step k.
pub open spec fn exp1_flip_e(e: spec_fn(bool) -> real, k: nat, new_eps: real) -> spec_fn(bool) -> real {
    |b: bool| if b { new_eps } else { e(k % 2 == 1) }
}

/// Next conditional probability: p_k = (x/k)·p_{k+1} + (1-x/k)·[k%2==1].
/// - With prob x/k, we continue to step k+1, where the conditional probability of returning true is p_{k+1}
///  - With prob (1-x)/k, we return [k is odd]
pub open spec fn exp1_next_p(x: real, k: nat, p_k: real) -> real {
    let amp = exp1_amp(x, k);
    if k % 2 == 1 { (p_k - 1real) * amp + 1real }
    else { p_k * amp }
}

/// Product of amplification factors: Π_{j=k}^{k+depth-1} amp_j.
pub open spec fn slack_product(x: real, k: nat, depth: nat) -> real
    decreases depth,
{
    if depth == 0 { 1real }
    else { exp1_amp(x, k) * slack_product(x, k + 1, (depth - 1) as nat) }
}

// ============================================================================
// Taylor partial sum connection: p_k ∈ [0, 1]
//
// p_k = [k odd] + (k-1)!/x^{k-1} · R_k, where R_k = exp(-x) - T_k(x).
// Since |R_k| ≤ x^k/k! (alternating series), |(k-1)!/x^{k-1} · R_k| ≤ x/k.
// ============================================================================

/// factorial(n) > 0 for all n.
proof fn lemma_factorial_pos(n: nat)
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
proof fn lemma_pow_pos(x: real, n: nat)
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
proof fn lemma_pow_neg_parity(x: real, k: nat)
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
proof fn lemma_scale_term_product(x: real, k: nat)
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

/// Solution to the recurrence for p_k (proven in `lemma_exp1_p_formula_step`)
///   p_k = [k odd] + (k-1)! / x^{k-1} · (exp(-x) - T_k(x))
pub open spec fn exp1_p_formula(x: real, k: nat) -> real {
    if k == 0 { 0real }
    else {
        let remainder = exp(-x) - partial_sum(exp_taylor_seq(x), k);
        let scale = factorial((k - 1) as nat) / pow(x, (k - 1) as nat);
        (if k % 2 == 1 { 1real } else { 0real }) + scale * remainder
    }
}

/// Base case: exp1_p_formula(x, 1) == exp(-x).
///
/// T_1 = 1, R_1 = exp(-x) - 1, scale = 0!/x^0 = 1, so p_1 = 1 + (exp(-x) - 1) = exp(-x).
proof fn lemma_exp1_p_formula_base(x: real)
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
proof fn lemma_exp1_p_formula_step(x: real, k: nat)
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
proof fn lemma_exp1_p_formula_range(x: real, k: nat)
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
proof fn lemma_exp1_flip_average(x: real, k: nat, eps: real, e: spec_fn(bool) -> real)
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
proof fn lemma_exp1_next_p_recursion(x: real, k: nat, p_k: real)
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
proof fn lemma_exp1_shift_bound(
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
proof fn lemma_slack_product_ge_pow2(x: real, k: nat, depth: nat)
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
proof fn lemma_slack_product_k1_bound(x: real, depth: nat)
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
proof fn real_mul_ineq(a: real, b: real, a_lb: real, b_lb: real)
    requires a >= a_lb, b >= b_lb, a_lb >= 0real, b_lb >= 0real,
    ensures a * b >= a_lb * b_lb,
{}

// ============================================================================
// Sampler: Bernoulli(exp(-x)) for x ∈ (0, 1]
// ============================================================================

/// Sample from Bernoulli(exp(-x)) where x = numer_x/denom_x ∈ (0, 1].
///
/// Implements the CKS20 algorithm as a loop:
///   k = 1, 2, ...: flip Bernoulli(x/k). Tails → return (k is odd). Heads → k++.
///
/// Ghost state tracks four quantities through the loop:
///   - g_eps:   current error credit (amplified by amp = k/x at each step)
///   - g_slack: gap between eps and the distribution bound (also amplified)
///   - g_pk:    conditional probability P[return true | reached step k].
///              Invariant: g_pk == exp1_p_formula(x, k) == [k odd] + (k-1)!/x^{k-1} · R_k,
///              where R_k = exp(-x) - T_k(x) is the Taylor remainder.
///              This ties g_pk to the alternating partial sums of exp(-x),
///              giving g_pk ∈ [0, 1] via axiom_exp_taylor_bounds.
///   - g_depth: termination fuel (decreases each iteration)
///
/// Termination: slack grows by factor amp ≥ 1 per step. At depth == 0,
/// slack ≥ 1/slack_product ≥ 1
///
pub fn sample_bernoulli_exp1(
    numer_x: u64,
    denom_x: u64,
    Ghost(e): Ghost<spec_fn(bool) -> real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(eps): Ghost<real>,
) -> ((value, out_credit): (bool, Tracked<ErrorCreditResource>))
    requires
        numer_x > 0,
        denom_x > 0,
        numer_x <= denom_x,
        e(true) >= 0real,
        e(false) >= 0real,
        eps >= 0real,
        input_credit.view() =~= (ErrorCreditCarrier::Value { car: eps }),
        eps >= bernoulli_weighted_sum(exp(-(numer_x as real / denom_x as real)), e),
    ensures
        out_credit@.view() =~= (ErrorCreditCarrier::Value { car: e(value) }),
{
    let ghost x = numer_x as real / denom_x as real;

    proof {
        assert(x > 0real) by(nonlinear_arith)
            requires x == numer_x as real / denom_x as real,
                numer_x as real >= 1real, denom_x as real >= 1real;
        assert(x <= 1real) by(nonlinear_arith)
            requires x == numer_x as real / denom_x as real,
                numer_x as real <= denom_x as real, denom_x as real >= 1real;
        lemma_exp1_p_formula_base(x);  // exp1_p_formula(x, 1) == exp(-x)
    }

    // Obtain infinitesimal slack from thin_air for the termination argument
    let Tracked(slack_credit) = thin_air();
    let ghost init_slack: real;
    let ghost init_depth: nat;
    proof {
        init_slack = choose |v: real| v > 0real &&
            (ErrorCreditCarrier::Value { car: v } =~= slack_credit.view());
        archimedean_exp_growth(init_slack, 2real);
        let d0: nat = choose |k: nat| init_slack * pow(2real, k) >= 1real;
        init_depth = d0 + 1;
        lemma_slack_product_k1_bound(x, init_depth);
        assert(init_slack * slack_product(x, 1nat, init_depth) >= 1real)
            by(nonlinear_arith)
            requires init_slack * pow(2real, d0) >= 1real,
                slack_product(x, 1nat, init_depth) >= pow(2real, d0),
                init_slack > 0real;
    }

    // Mutable loop state: two separate credits
    let mut k = ubig_from_u64(1u64);
    let ghost mut g_depth: nat = init_depth;
    let ghost mut g_dist_eps: real = eps;
    let ghost mut g_slack_val: real = init_slack;
    let ghost mut g_pk: real = exp(-x);
    let tracked mut dist_credit: ErrorCreditResource = input_credit;
    let tracked mut slack_credit: ErrorCreditResource = slack_credit;

    loop
        invariant
            numer_x > 0, denom_x > 0, numer_x <= denom_x,
            x == numer_x as real / denom_x as real,
            0real < x <= 1real,
            ubig_view(&k) >= 1,
            e(true) >= 0real,
            e(false) >= 0real,
            g_pk == exp1_p_formula(x, ubig_view(&k)),
            g_dist_eps >= 0real,
            g_slack_val > 0real,
            dist_credit.view() =~= (ErrorCreditCarrier::Value { car: g_dist_eps }),
            slack_credit.view() =~= (ErrorCreditCarrier::Value { car: g_slack_val }),
            g_dist_eps >= bernoulli_weighted_sum(g_pk, e),
            g_slack_val * slack_product(x, ubig_view(&k), g_depth) >= 1real,
        decreases g_depth,
    {
        let ghost kn = ubig_view(&k);

        // depth == 0 is unreachable: slack_val >= 1 contradicts finite credit
        proof {
            if g_depth == 0nat { ec_contradict(&slack_credit); }
        }

        let k_denom = ubig_mul_u64(&k, denom_x);
        let ghost kdn = ubig_view(&k_denom);
        let ghost amp = exp1_amp(x, kn);
        let ghost total_eps = g_dist_eps + g_slack_val;
        let ghost new_eps = exp1_new_eps(x, kn, total_eps, e);
        let ghost flip_e = exp1_flip_e(e, kn, new_eps);
        let ghost p_next = exp1_next_p(x, kn, g_pk);

        // Combine dist + slack into one credit for the flip
        let tracked combined = ec_combine(dist_credit, slack_credit, g_dist_eps, g_slack_val);

        proof {
            // Bernoulli flip preconditions.  The flip probability passed to
            // sample_bernoulli_rational is numer_x/kdn = x/kn.
            assert(kdn == kn * denom_x as nat);
            assert(numer_x as real / (kdn as real) == x / kn as real) by(nonlinear_arith)
                requires kdn == kn * denom_x as nat, kn >= 1, denom_x > 0u64,
                    x == numer_x as real / denom_x as real;
            assert(numer_x as nat <= kdn) by(nonlinear_arith)
                requires numer_x <= denom_x, kn >= 1, kdn == kn * denom_x as nat;
            assert(kdn > 0) by(nonlinear_arith)
                requires kn >= 1, denom_x > 0u64, kdn == kn * denom_x as nat;
            lemma_exp1_flip_average(x, kn, total_eps, e);

            // Distribution bound shifts: new_dist_eps >= bws(p_next)
            lemma_exp1_next_p_recursion(x, kn, g_pk);
            lemma_exp1_shift_bound(x, kn, g_dist_eps, e, g_pk, p_next);
            lemma_exp1_p_formula_step(x, kn);
            lemma_exp1_p_formula_range(x, kn + 1);
            assert(amp >= 1real) by(nonlinear_arith)
                requires amp == kn as real / x, 0real < x <= 1real, kn >= 1;
            // new_eps = amp·total_eps - (amp-1)·e(k%2==1) >= 0 for flip_e(true)
            assert(new_eps >= 0real) by(nonlinear_arith)
                requires
                    amp * g_dist_eps - (amp - 1real) * e(kn % 2 == 1) >= bernoulli_weighted_sum(p_next, e),
                    0real <= exp1_p_formula(x, kn + 1) <= 1real,
                    p_next == exp1_p_formula(x, kn + 1),
                    e(true) >= 0real, e(false) >= 0real,
                    amp >= 1real, g_slack_val > 0real,
                    new_eps == amp * (g_dist_eps + g_slack_val) - (amp - 1real) * e(kn % 2 == 1);
        }

        // Flip Bernoulli(numer_x / k_denom) = Bernoulli(x/k)
        let numer_ubig = ubig_from_u64(numer_x);
        let (heads, Tracked(out_credit)) = sample_bernoulli_rational(
            &numer_ubig,
            &k_denom,
            Ghost(flip_e),
            Tracked(combined),
            Ghost(total_eps),
        );

        let is_odd = ubig_is_odd(&k);

        if !heads {
            // Tails: return with out_credit (value e(k%2==1))
            // Need to give back a credit to the caller — out_credit has the right postcondition
            return (is_odd, Tracked(out_credit));
        }

        // Heads: split out_credit (value new_eps) back into dist + slack
        let ghost new_dist_eps = amp * g_dist_eps - (amp - 1real) * e(kn % 2 == 1);
        let ghost new_slack_val = amp * g_slack_val;

        proof {
            // new_eps = new_dist_eps + new_slack_val
            assert(new_eps == new_dist_eps + new_slack_val)
                by(nonlinear_arith)
                requires
                    new_eps == amp * (g_dist_eps + g_slack_val) - (amp - 1real) * e(kn % 2 == 1),
                    new_dist_eps == amp * g_dist_eps - (amp - 1real) * e(kn % 2 == 1),
                    new_slack_val == amp * g_slack_val;
            // new_dist_eps >= bws(p_next, e) >= 0
            lemma_bws_nonneg(p_next, e);
            assert(new_slack_val > 0real) by(nonlinear_arith)
                requires new_slack_val == amp * g_slack_val, amp >= 1real, g_slack_val > 0real;
            real_assoc_mult(g_slack_val, amp, slack_product(x, kn + 1, (g_depth - 1) as nat));
        }

        let tracked (new_dc, new_sc) = ec_split(out_credit, new_dist_eps, new_slack_val);

        k = ubig_succ(k);
        proof {
            assert(ubig_view(&k) == kn + 1);
            g_dist_eps = new_dist_eps;
            g_slack_val = new_slack_val;
            g_pk = p_next;
            g_depth = (g_depth - 1) as nat;
            dist_credit = new_dc;
            slack_credit = new_sc;
        }
    }
}

/// Bignum variant of [`sample_bernoulli_exp1`]: same Bernoulli(exp(−x)) Hoare
/// rule and same `x:real`-keyed proof, but `x = numer/denom` is given by
/// arbitrary-precision `UBig`s (needed when x's denominator exceeds u64, as in
/// the discrete-gaussian acceptance test).
pub fn sample_bernoulli_exp1_ubig(
    numer: &UBig,
    denom: &UBig,
    Ghost(e): Ghost<spec_fn(bool) -> real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(eps): Ghost<real>,
) -> ((value, out_credit): (bool, Tracked<ErrorCreditResource>))
    requires
        ubig_view(numer) > 0,
        ubig_view(denom) > 0,
        ubig_view(numer) <= ubig_view(denom),
        e(true) >= 0real,
        e(false) >= 0real,
        eps >= 0real,
        input_credit.view() =~= (ErrorCreditCarrier::Value { car: eps }),
        eps >= bernoulli_weighted_sum(exp(-(ubig_view(numer) as real / ubig_view(denom) as real)), e),
    ensures
        out_credit@.view() =~= (ErrorCreditCarrier::Value { car: e(value) }),
{
    let ghost nv = ubig_view(numer);
    let ghost dv = ubig_view(denom);
    let ghost x = nv as real / dv as real;

    proof {
        assert(x > 0real) by(nonlinear_arith)
            requires x == nv as real / dv as real, nv >= 1, dv >= 1;
        assert(x <= 1real) by(nonlinear_arith)
            requires x == nv as real / dv as real, nv <= dv, dv >= 1;
        lemma_exp1_p_formula_base(x);
    }

    let Tracked(slack_credit) = thin_air();
    let ghost init_slack: real;
    let ghost init_depth: nat;
    proof {
        init_slack = choose |v: real| v > 0real &&
            (ErrorCreditCarrier::Value { car: v } =~= slack_credit.view());
        archimedean_exp_growth(init_slack, 2real);
        let d0: nat = choose |kk: nat| init_slack * pow(2real, kk) >= 1real;
        init_depth = d0 + 1;
        lemma_slack_product_k1_bound(x, init_depth);
        assert(init_slack * slack_product(x, 1nat, init_depth) >= 1real)
            by(nonlinear_arith)
            requires init_slack * pow(2real, d0) >= 1real,
                slack_product(x, 1nat, init_depth) >= pow(2real, d0),
                init_slack > 0real;
    }

    let mut k = ubig_from_u64(1u64);
    let ghost mut g_depth: nat = init_depth;
    let ghost mut g_dist_eps: real = eps;
    let ghost mut g_slack_val: real = init_slack;
    let ghost mut g_pk: real = exp(-x);
    let tracked mut dist_credit: ErrorCreditResource = input_credit;
    let tracked mut slack_credit: ErrorCreditResource = slack_credit;

    loop
        invariant
            nv == ubig_view(numer), dv == ubig_view(denom),
            nv > 0, dv > 0, nv <= dv,
            x == nv as real / dv as real,
            0real < x <= 1real,
            ubig_view(&k) >= 1,
            e(true) >= 0real,
            e(false) >= 0real,
            g_pk == exp1_p_formula(x, ubig_view(&k)),
            g_dist_eps >= 0real,
            g_slack_val > 0real,
            dist_credit.view() =~= (ErrorCreditCarrier::Value { car: g_dist_eps }),
            slack_credit.view() =~= (ErrorCreditCarrier::Value { car: g_slack_val }),
            g_dist_eps >= bernoulli_weighted_sum(g_pk, e),
            g_slack_val * slack_product(x, ubig_view(&k), g_depth) >= 1real,
        decreases g_depth,
    {
        let ghost kn = ubig_view(&k);

        proof {
            if g_depth == 0nat { ec_contradict(&slack_credit); }
        }

        let k_denom = ubig_mul(k.clone(), denom.clone());
        let ghost kdn = ubig_view(&k_denom);
        let ghost amp = exp1_amp(x, kn);
        let ghost total_eps = g_dist_eps + g_slack_val;
        let ghost new_eps = exp1_new_eps(x, kn, total_eps, e);
        let ghost flip_e = exp1_flip_e(e, kn, new_eps);
        let ghost p_next = exp1_next_p(x, kn, g_pk);

        let tracked combined = ec_combine(dist_credit, slack_credit, g_dist_eps, g_slack_val);

        proof {
            // Flip probability passed below is nv/kdn = x/kn.
            assert(kdn == kn * dv);
            assert(nv as real / (kdn as real) == x / kn as real) by(nonlinear_arith)
                requires kdn == kn * dv, kn >= 1, dv > 0, x == nv as real / dv as real;
            assert(nv <= kdn) by(nonlinear_arith) requires nv <= dv, kn >= 1, kdn == kn * dv;
            assert(kdn > 0) by(nonlinear_arith) requires kn >= 1, dv > 0, kdn == kn * dv;
            lemma_exp1_flip_average(x, kn, total_eps, e);
            lemma_exp1_next_p_recursion(x, kn, g_pk);
            lemma_exp1_shift_bound(x, kn, g_dist_eps, e, g_pk, p_next);
            lemma_exp1_p_formula_step(x, kn);
            lemma_exp1_p_formula_range(x, kn + 1);
            assert(amp >= 1real) by(nonlinear_arith)
                requires amp == kn as real / x, 0real < x <= 1real, kn >= 1;
            assert(new_eps >= 0real) by(nonlinear_arith)
                requires
                    amp * g_dist_eps - (amp - 1real) * e(kn % 2 == 1) >= bernoulli_weighted_sum(p_next, e),
                    0real <= exp1_p_formula(x, kn + 1) <= 1real,
                    p_next == exp1_p_formula(x, kn + 1),
                    e(true) >= 0real, e(false) >= 0real,
                    amp >= 1real, g_slack_val > 0real,
                    new_eps == amp * (g_dist_eps + g_slack_val) - (amp - 1real) * e(kn % 2 == 1);
        }

        let (heads, Tracked(out_credit)) = sample_bernoulli_rational(
            numer,
            &k_denom,
            Ghost(flip_e),
            Tracked(combined),
            Ghost(total_eps),
        );

        let is_odd = ubig_is_odd(&k);

        if !heads {
            return (is_odd, Tracked(out_credit));
        }

        let ghost new_dist_eps = amp * g_dist_eps - (amp - 1real) * e(kn % 2 == 1);
        let ghost new_slack_val = amp * g_slack_val;

        proof {
            assert(new_eps == new_dist_eps + new_slack_val)
                by(nonlinear_arith)
                requires
                    new_eps == amp * (g_dist_eps + g_slack_val) - (amp - 1real) * e(kn % 2 == 1),
                    new_dist_eps == amp * g_dist_eps - (amp - 1real) * e(kn % 2 == 1),
                    new_slack_val == amp * g_slack_val;
            lemma_bws_nonneg(p_next, e);
            assert(new_slack_val > 0real) by(nonlinear_arith)
                requires new_slack_val == amp * g_slack_val, amp >= 1real, g_slack_val > 0real;
            real_assoc_mult(g_slack_val, amp, slack_product(x, kn + 1, (g_depth - 1) as nat));
        }

        let tracked (new_dc, new_sc) = ec_split(out_credit, new_dist_eps, new_slack_val);

        k = ubig_succ(k);
        proof {
            assert(ubig_view(&k) == kn + 1);
            g_dist_eps = new_dist_eps;
            g_slack_val = new_slack_val;
            g_pk = p_next;
            g_depth = (g_depth - 1) as nat;
            dist_credit = new_dc;
            slack_credit = new_sc;
        }
    }
}

} // verus!
