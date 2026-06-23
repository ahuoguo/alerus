// Axiomatization of the exponential function exp(x) = e^x.
//
// We define exp as an uninterpreted function and axiomatize the properties
// needed for the CKS20 discrete Laplace sampler proofs:
//
//   1. exp(0) = 1
//   2. exp(-x) ∈ [0, 1] for x ≥ 0
//   3. exp(-(a+b)) = exp(-a) · exp(-b)  (multiplicativity)
//   4. Alternating series bounds on partial sums of exp(-x) = Σ (-x)^k/k!.

use vstd::prelude::*;

verus! {
#[cfg(verus_keep_ghost)]
use crate::math::pow::pow;
#[cfg(verus_keep_ghost)]
use crate::math::series::partial_sum;

/// The exponential function exp(x) = e^x, axiomatized as an uninterpreted function.
pub uninterp spec fn exp(x: real) -> real;

// ============================================================================
// Core axioms
// ============================================================================

// TODO: consider using the axiom keyword
/// exp(0) = 1.
#[verifier::external_body]
pub proof fn axiom_exp_zero()
    ensures exp(0real) == 1real,
{}

/// exp(-x) ∈ (0, 1] for x ≥ 0.
#[verifier::external_body]
pub proof fn axiom_exp_neg_range(x: real)
    requires x >= 0real,
    ensures
        0real < exp(-x),
        exp(-x) <= 1real,
{}

/// exp(-x) < 1 for x > 0.
#[verifier::external_body]
pub proof fn axiom_exp_neg_strict(x: real)
    requires x > 0real,
    ensures exp(-x) < 1real,
{}

/// Multiplicativity: exp(-(a + b)) = exp(-a) · exp(-b).
#[verifier::external_body]
pub proof fn axiom_exp_add(a: real, b: real)
    requires a >= 0real, b >= 0real,
    ensures exp(-(a + b)) == exp(-a) * exp(-b),
{}

/// Bernoulli inequality: exp(-x) ≥ 1 - x for 0 < x ≤ 1.
/// Derived from the Taylor series: T_2 = 1 - x ≤ exp(-x) (even partial sum underestimates).
pub proof fn lemma_exp_bernoulli(x: real)
    requires 0real < x <= 1real,
    ensures exp(-x) >= 1real - x,
{
    // T_2 = partial_sum(exp_taylor_seq(x), 2) = term(0) + term(1) = 1 + (-x) = 1-x
    axiom_exp_taylor_bounds(x, 2nat);
    // n=2 is even, so T_2 ≤ exp(-x)
    // Unfold T_2 = partial_sum(exp_taylor_seq(x), 2)
    let s = exp_taylor_seq(x);
    assert(partial_sum(s, 2nat) == partial_sum(s, 1nat) + s(1nat));
    assert(partial_sum(s, 1nat) == partial_sum(s, 0nat) + s(0nat));
    // s(0) = (-x)^0 / 0! = 1, s(1) = (-x)^1 / 1! = -x
    assert(pow(-x, 0nat) == 1real);
    assert(pow(-x, 1nat) == -x) by(nonlinear_arith)
        requires pow(-x, 1nat) == -x * pow(-x, 0nat), pow(-x, 0nat) == 1real;
    assert(factorial(0nat) == 1real);
    assert(factorial(1nat) == 1real) by(nonlinear_arith)
        requires factorial(1nat) == 1real * factorial(0nat), factorial(0nat) == 1real;
    assert(partial_sum(s, 2nat) == 1real - x) by(nonlinear_arith)
        requires
            partial_sum(s, 2nat) == partial_sum(s, 1nat) + s(1nat),
            partial_sum(s, 1nat) == s(0nat),
            s(0nat) == pow(-x, 0nat) / factorial(0nat),
            s(1nat) == pow(-x, 1nat) / factorial(1nat),
            pow(-x, 0nat) == 1real, pow(-x, 1nat) == -x,
            factorial(0nat) == 1real, factorial(1nat) == 1real;
}

// ============================================================================
// Taylor series for exp(-x)
//
// exp(-x) = Σ_{k=0}^∞ (-x)^k / k! = 1 - x + x²/2! - x³/3! + ...
//
// For x ∈ (0, 1], the terms alternate in sign and decrease in absolute
// value, so the alternating series estimation theorem gives: partial sums
// bracket exp(-x) and lie in [0, 1].
// ============================================================================

/// Factorial: n! = 1 · 2 · ... · n.
pub open spec fn factorial(n: nat) -> real
    decreases n,
{
    if n == 0 { 1real } else { n as real * factorial((n - 1) as nat) }
}

/// k-th term of the Taylor series for exp(-x): (-x)^k / k!
pub open spec fn exp_taylor_term(x: real, k: nat) -> real {
    pow(-x, k) / factorial(k)
}

/// The Taylor term sequence as a named spec_fn (avoids lambdas in triggers).
pub open spec fn exp_taylor_seq(x: real) -> spec_fn(nat) -> real {
    |k: nat| exp_taylor_term(x, k)
}

// TODO: formalize this in lean?
/// Alternating series bounds for the partial sums of exp(-x).
///
/// For x ∈ (0, 1] and n ≥ 1 terms, the partial sum T_n = Σ_{k=0}^{n-1} (-x)^k/k!
/// satisfies:
///   - T_n ∈ [0, 1]
///   - n even (even number of terms): T_n ≤ exp(-x)  (underestimate)
///   - n odd (odd number of terms):   exp(-x) ≤ T_n  (overestimate)
///
/// Proof: alternating series estimation theorem applied to exp(-x).
///
/// For x ∈ (0, 1], the terms (-x)^k/k! alternate in sign and decrease in
/// absolute value (since x^{k+1}/(k+1)! = (x/(k+1)) · x^k/k! ≤ x^k/k!).
/// By the alternating series estimation theorem, the remainder after n terms
///   R_n = exp(-x) - T_n = (-x)^n/n! + (-x)^{n+1}/(n+1)! + ...
/// has the same sign as its leading term (-x)^n/n! = (-1)^n · x^n/n!:
///   n even ⟹ R_n ≥ 0 ⟹ T_n ≤ exp(-x)
///   n odd  ⟹ R_n ≤ 0 ⟹ exp(-x) ≤ T_n
///
/// T_n ∈ [0, 1] follows from the bounding and exp(-x) ∈ (0, 1]:
///   n even: 0 ≤ T_n ≤ exp(-x) ≤ 1.
///   n odd:  0 < exp(-x) ≤ T_n ≤ T_1 = 1 (odd partial sums decrease toward exp(-x)).
///
/// Related mathlib4 lemma (gives error magnitude but not sign):
///   `Real.exp_bound`: |x| ≤ 1 ⟹ |exp(x) - Σ_{m<n} x^m/m!| ≤ |x|^n·(n+1)/(n!·n)
///   https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/Exponential.html#Real.exp_bound
#[verifier::external_body]
pub proof fn axiom_exp_taylor_bounds(x: real, n: nat)
    requires 0real < x <= 1real, n >= 1,
    ensures
        0real <= partial_sum(exp_taylor_seq(x), n),
        partial_sum(exp_taylor_seq(x), n) <= 1real,
        n % 2 == 0 ==> partial_sum(exp_taylor_seq(x), n) <= exp(-x),
        n % 2 == 1 ==> exp(-x) <= partial_sum(exp_taylor_seq(x), n),
{}

// ============================================================================
// Derived lemmas
// ============================================================================

/// exp(-x) == exp(-1) · exp(-(x-1)) when x = numer/denom ≥ 1.
pub proof fn lemma_exp_decompose(numer: u64, denom: u64)
    requires denom > 0, numer >= denom,
    ensures
        exp(-(numer as real / denom as real))
            == exp(-1real) * exp(-((numer - denom) as real / denom as real)),
{
    let x = numer as real / denom as real;
    let frac = (numer - denom) as real / denom as real;
    assert(x == 1real + frac) by(nonlinear_arith)
        requires x == numer as real / denom as real,
            frac == (numer - denom) as real / denom as real,
            denom > 0u64, numer >= denom;
    assert(frac >= 0real) by(nonlinear_arith)
        requires frac == (numer - denom) as real / denom as real,
            denom > 0u64, numer >= denom;
    axiom_exp_add(1real, frac);
}

} // verus!
