//! Exponential growth: pow, Bernoulli's inequality, Archimedean properties.
//!
//! Main result: for any eps > 0 and base > 1, there exists k such that
//! eps * base^k >= 1. This is the key lemma that lets bounded samplers
//! recurse: each rejection amplifies the error credit, and after enough
//! amplifications we reach a contradiction (credit >= 1 is impossible).
use vstd::prelude::*;

verus! {

// ============================================================================
// Core definitions
// ============================================================================
pub open spec fn pow(x: real, k: nat) -> real
    decreases k,
{
    if k == 0 {
        1real
    } else {
        x * pow(x, (k - 1) as nat)
    }
}

/// Trigger helper for quantifying over naturals as reals
pub open spec fn nat_to_real(n: nat) -> real {
    n as real
}

// ============================================================================
// Nonlinear arithmetic helpers
// ============================================================================
#[verifier::nonlinear]
proof fn lemma_mul_ge_one(a: real, b: real)
    requires
        a >= 1real,
        b >= 1real,
    ensures
        a * b >= 1real,
{
}

#[verifier::nonlinear]
proof fn lemma_mul_mono(a: real, b: real, c: real)
    requires
        a >= b,
        c > 0real,
    ensures
        c * a >= c * b,
{
}

#[verifier::nonlinear]
proof fn lemma_div_pos(x: real)
    requires
        x > 0real,
    ensures
        1real / x > 0real,
{
}

#[verifier::nonlinear]
proof fn lemma_mul_div_cancel(x: real)
    requires
        x > 0real,
    ensures
        x * (1real / x) == 1real,
{
}

#[verifier::nonlinear]
proof fn lemma_div_nonneg(x: real, y: real)
    requires
        x >= 0real,
        y > 0real,
    ensures
        x / y >= 0real,
{
}

// ============================================================================
// Bernoulli's inequality
// ============================================================================
// pow(r, k) >= 1 when r >= 1
proof fn lemma_pow_ge_one(r: real, k: nat)
    requires
        r >= 1real,
    ensures
        pow(r, k) >= 1real,
    decreases k,
{
    if k > 0 {
        lemma_pow_ge_one(r, (k - 1) as nat);
        lemma_mul_ge_one(r, pow(r, (k - 1) as nat));
    }
}

/// Bernoulli's inequality: pow(r, k) >= 1 + k*(r-1) for r > 1
///
/// Proof by induction on k. The inductive step uses:
///   r * pow(r, k-1) >= r * (1 + (k-1)*delta)
///                    = 1 + k*delta + (k-1)*delta^2
///                    >= 1 + k*delta
proof fn lemma_bernoulli(r: real, k: nat)
    requires
        r > 1real,
    ensures
        pow(r, k) >= 1real + nat_to_real(k) * (r - 1real),
    decreases k,
{
    if k == 0 {
        assert(pow(r, 0nat) == 1real);
        assert(nat_to_real(0nat) == 0real);
    } else {
        let prev = (k - 1) as nat;
        lemma_bernoulli(r, prev);
        lemma_pow_ge_one(r, prev);
        lemma_bernoulli_step(r, prev, r - 1real);
    }
}

#[verifier::nonlinear]
proof fn lemma_bernoulli_step(r: real, prev: nat, delta: real)
    requires
        r > 1real,
        delta == r - 1real,
        pow(r, prev) >= 1real + nat_to_real(prev) * delta,
    ensures
        r * pow(r, prev) >= 1real + nat_to_real(prev + 1) * delta,
{
}

// ============================================================================
// Archimedean properties
// ============================================================================
// For any x >= 0, there exists a natural number n >= x
pub proof fn archimedean_nat(x: real)
    requires
        x >= 0real,
    ensures
        exists|n: nat| #[trigger] nat_to_real(n) >= x,
{
    let a: nat = x.floor() as nat;
    assert(x < nat_to_real(a + 1));
}

/// Archimedean property for powers: for any r > 1 and target > 0,
/// there exists k such that r^k >= target.
///
/// Proof: by Bernoulli, r^k >= 1 + k*(r-1). Choose k >= (target-1)/(r-1).
// TODO: we can reduce the number of lemmas by declaring this as `non_linear`
pub proof fn archimedean_pow(r: real, target: real)
    requires
        r > 1real,
        target > 0real,
    ensures
        exists|k: nat| #[trigger] pow(r, k) >= target,
{
    if target <= 1real {
        assert(pow(r, 0nat) == 1real);
        assert(pow(r, 0nat) >= target);
    } else {
        let delta = r - 1real;
        lemma_div_pos(delta);
        let bound = (target - 1real) / delta;
        lemma_div_nonneg(target - 1real, delta);
        archimedean_nat(bound);
        let k = choose|k: nat| #[trigger] nat_to_real(k) >= bound;
        lemma_bernoulli(r, k);
        lemma_archimedean_final(r, k, target, delta, bound);
    }
}

#[verifier::nonlinear]
proof fn lemma_archimedean_final(r: real, k: nat, target: real, delta: real, bound: real)
    requires
        r > 1real,
        delta == r - 1real,
        target > 1real,
        bound == (target - 1real) / delta,
        nat_to_real(k) >= bound,
        pow(r, k) >= 1real + nat_to_real(k) * delta,
    ensures
        pow(r, k) >= target,
{
}

/// For any eps > 0 and any base > 1, there exists k such that eps * base^k >= 1.
// TODO: we can reduce the number of lemmas by declaring this as `non_linear`
pub proof fn archimedean_exp_growth(eps: real, base: real)
    requires
        eps > 0real,
        base > 1real,
    ensures
        exists|k: nat| eps * pow(base, k) >= 1real,
{
    // By Archimedean property, there exists k such that base^k >= 1/eps
    lemma_div_pos(eps);
    archimedean_pow(base, 1real / eps);
    let k = choose|k: nat| #[trigger] pow(base, k) >= 1real / eps;
    // Since base^k >= 1/eps and eps > 0, we have eps * base^k >= 1
    lemma_mul_mono(pow(base, k), 1real / eps, eps);
    lemma_mul_div_cancel(eps);
}

} // verus!
