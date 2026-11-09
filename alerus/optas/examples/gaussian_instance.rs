//! `sample_gauss` at σ = 3.33, the parameter of Roy, Vercauteren and
//! Verbauwhede (SAC 2013), with total slack δ + gauss_tail ≤ 2^{−90}:
//!
//! ```text
//!   ε ≥ E_{N_ℤ(0, 3.33²)}[ℰ]     ℰ ∈ [0, 1]
//!   ------------------------------------------------------
//!   [{ ↯(ε + 2^{−90}) }] sample_gauss_roy() [{ z. ↯(ℰ(z)) }]
//! ```

use vstd::prelude::*;

verus! {

use crate::ec::*;
#[cfg(verus_keep_ghost)]
use crate::ec::ErrorCreditCarrier::Value;
use crate::optas::examples::gaussian::sample_gauss;
#[cfg(verus_keep_ghost)]
use crate::optas::examples::gaussian::{gauss_delta, exp_tau, exp_split, lemma_exp_le_pow2};
#[cfg(verus_keep_ghost)]
use crate::optas::examples::gaussian_tail::{gauss_x, gauss_tail, gk};
#[cfg(verus_keep_ghost)]
use crate::cks::discrete_gaussian::{gauss_kernel_partial, gauss_expectation_le, gauss_norm};
#[cfg(verus_keep_ghost)]
use crate::cks::discrete_gaussian_helper::lemma_gauss_expectation_iff;
#[cfg(verus_keep_ghost)]
use crate::fldr_helper::lemma_nat_mul_real_cast;
#[cfg(verus_keep_ghost)]
use crate::math::exp::{exp, factorial, exp_taylor_term};
#[cfg(verus_keep_ghost)]
use crate::math::pow::pow;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::{pow2, lemma2_to64, lemma_pow2_pos, lemma_pow2_adds};

/// gauss_tail(x, b) ≤ 2·(16/15)·2^{−n} when (b+1)²x ≥ n and (2b+3)x ≥ 4.
proof fn lemma_tail_le(x: real, b: nat, n: nat)
    requires
        x > 0real,
        ((b + 1) as real) * ((b + 1) as real) * x >= n as real,
        ((2 * b + 3) as nat) as real * x >= 4real,
    ensures 0real <= gauss_tail(x, b) <= 32real / (15real * (pow2(n) as real)),
{
    lemma_exp_le_pow2(((b + 1) as real) * ((b + 1) as real) * x, n);
    lemma_exp_le_pow2(((2 * b + 3) as nat) as real * x, 4);
    lemma2_to64();
    lemma_pow2_pos(n);
    let g = gk(x, b + 1);
    let q = exp(-(((2 * b + 3) as nat) as real * x));
    let p = pow2(n) as real;
    assert(gauss_tail(x, b) == 2real * g / (1real - q));
    assert(0real <= 2real * g / (1real - q) <= 32real / (15real * p)) by(nonlinear_arith)
        requires 0real < g <= 1real / p, 0real < q <= 1real / 16real, p > 0real;
}

/// 0 ≤ x ≤ 1/16 ⟹ 0 ≤ x^n ≤ 2^{−4n}.
proof fn lemma_pow_sixteenth(x: real, n: nat)
    requires 0real <= x <= 1real / 16real,
    ensures 0real <= pow(x, n), pow(x, n) * (pow2(4 * n) as real) <= 1real,
    decreases n,
{
    if n > 0 {
        let m = (n - 1) as nat;
        lemma_pow_sixteenth(x, m);
        lemma_pow2_adds(4 * m, 4);
        lemma2_to64();
        assert(4 * m + 4 == 4 * n);
        assert(pow(x, n) == x * pow(x, m));
        let a = pow(x, m);
        let pa = pow2(4 * m) as real;
        assert(pow2(4 * n) as real == pa * 16real);
        assert(0real <= x * a && (x * a) * (pa * 16real) <= 1real) by(nonlinear_arith)
            requires 0real <= x <= 1real / 16real, 0real <= a, a * pa <= 1real, pa >= 0real;
    } else {
        assert(pow(x, 0) == 1real);
        assert(pow2(0) == 1) by { lemma2_to64(); }
    }
}

/// (−x)^{2j} = x^{2j}.
proof fn lemma_pow_neg_even(x: real, j: nat)
    ensures pow(-x, 2 * j) == pow(x, 2 * j),
    decreases j,
{
    if j > 0 {
        lemma_pow_neg_even(x, (j - 1) as nat);
        let a = (2 * j - 2) as nat;
        assert(pow(-x, a + 1) == (-x) * pow(-x, a));
        assert(pow(-x, a + 2) == (-x) * pow(-x, a + 1));
        assert(pow(x, a + 1) == x * pow(x, a));
        assert(pow(x, a + 2) == x * pow(x, a + 1));
        assert((-x) * ((-x) * pow(-x, a)) == x * (x * pow(-x, a))) by(nonlinear_arith);
        assert(a + 2 == 2 * j);
    }
}

proof fn lemma_factorial_ge_1(n: nat)
    ensures factorial(n) >= 1real,
    decreases n,
{
    if n > 0 {
        lemma_factorial_ge_1((n - 1) as nat);
        assert(factorial(n) == (n as real) * factorial((n - 1) as nat));
        assert((n as real) * factorial((n - 1) as nat) >= 1real) by(nonlinear_arith)
            requires n >= 1, factorial((n - 1) as nat) >= 1real;
    }
}

/// At σ = 3.33 (x = 5000/110889), with B = 45, nt = 32, mb = 112, k = 124:
/// δ + gauss_tail(x, B) ≤ 2^{−90}.
pub proof fn lemma_roy_budget()
    ensures ({
        let x = gauss_x(333real / 100real);
        let slack = gauss_delta(x, 45, 32, 112, 124) + gauss_tail(x, 45);
        0real <= slack <= 1real / (pow2(90) as real)
    }),
{
    let x = gauss_x(333real / 100real);
    assert(2real * (333real / 100real) * (333real / 100real) == 221778real / 10000real) by(nonlinear_arith);
    assert(1real / (221778real / 10000real) == 5000real / 110889real) by(nonlinear_arith);
    assert(x == 5000real / 110889real);
    lemma2_to64();
    // the tail: (B+1)²x = 2116x ≥ 95, (2B+3)x = 93x ≥ 4
    assert(((45nat + 1) as real) == 46real);
    assert(((2 * 45nat + 3) as nat) as real == 93real);
    lemma_tail_le(x, 45, 95);
    // the Taylor remainder: m = 1, τ = x^32 / 32! ≤ (1/16)^32 = 2^{−128}
    assert(x.floor() == 0);
    assert(exp_split(x) == 1);
    assert(x / (1nat as real) == x);
    lemma_pow_neg_even(x, 16);
    lemma_pow_sixteenth(x, 32);
    lemma_factorial_ge_1(32);
    let h = pow(x, 32);
    let tau = exp_tau(x, 32);
    assert(exp_taylor_term(x, 32) == h / factorial(32));
    assert(tau == 1real * exp_taylor_term(x, 32));
    // every power of two in terms of P = 2^90
    lemma_pow2_adds(90, 5);
    lemma_pow2_adds(90, 22);
    lemma_pow2_adds(90, 34);
    lemma_pow2_adds(90, 38);
    lemma_pow2_pos(90);
    let p = pow2(90) as real;
    let p95 = pow2(95) as real;
    let p112 = pow2(112) as real;
    let p124 = pow2(124) as real;
    let p128 = pow2(128) as real;
    lemma_nat_mul_real_cast(pow2(90), pow2(5));
    lemma_nat_mul_real_cast(pow2(90), pow2(22));
    lemma_nat_mul_real_cast(pow2(90), pow2(34));
    lemma_nat_mul_real_cast(pow2(90), pow2(38));
    lemma_pow2_adds(32, 2);
    lemma_pow2_adds(32, 6);
    assert(pow2(5) == 32 && pow2(22) == 4194304 && pow2(34) == 17179869184 && pow2(38) == 274877906944);
    assert(pow2(5) as real == 32real && pow2(22) as real == 4194304real
        && pow2(34) as real == 17179869184real && pow2(38) as real == 274877906944real);
    assert(pow2(95) == pow2(90) * pow2(5) && pow2(112) == pow2(90) * pow2(22)
        && pow2(124) == pow2(90) * pow2(34) && pow2(128) == pow2(90) * pow2(38));
    assert(p95 == p * 32real);
    assert(p112 == p * 4194304real);
    assert(p124 == p * 17179869184real);
    assert(p128 == p * 274877906944real);
    assert(0real <= tau && tau * p128 <= 1real) by(nonlinear_arith)
        requires tau == h / factorial(32), factorial(32) >= 1real, 0real <= h, h * p128 <= 1real, p128 > 0real;
    // all together
    let t = gauss_tail(x, 45);
    assert(gauss_delta(x, 45, 32, 112, 124)
        == 91real * (2025real * tau) + 91real * (1real / p112) + 91real / (2real * p124));
    assert(0real <= 91real * (2025real * tau) + 91real * (1real / p112) + 91real / (2real * p124) + t
        <= 1real / p) by(nonlinear_arith)
        requires
            p > 0real, 0real <= t <= 32real / (15real * p95), 0real <= tau, tau * p128 <= 1real,
            p95 == p * 32real, p112 == p * 4194304real, p124 == p * 17179869184real,
            p128 == p * 274877906944real;
}

/// N_ℤ(0, σ²) with σ = 3.33, z ∈ [−45, 45], for ε + 2^{−90}.
pub fn sample_gauss_roy(
    Ghost(e): Ghost<spec_fn(int) -> real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(eps): Ghost<real>,
) -> ((z, out_credit): (i64, Tracked<ErrorCreditResource>))
    requires
        forall |z: int| 0real <= #[trigger] e(z) <= 1real,
        ({ let sigma = 333real / 100real; gauss_expectation_le(sigma * sigma, e, eps) }),
        input_credit@ =~= (Value { car: eps + 1real / (pow2(90) as real) }),
    ensures
        -45 <= z <= 45,
        out_credit@@ =~= (Value { car: e(z as int) }),
{
    let ghost x = gauss_x(333real / 100real);
    let ghost slack = gauss_delta(x, 45, 32, 112, 124) + gauss_tail(x, 45);
    proof {
        lemma_roy_budget();
        // ε ≥ 0: the bound at n = 0
        let s2 = (333real / 100real) * (333real / 100real);
        assert(s2 > 0real) by(nonlinear_arith) requires s2 == (333real / 100real) * (333real / 100real);
        assert(1real / 1real == 1real);
        lemma_gauss_expectation_iff(exp(-(1real / 1real)), s2, 1real, e, eps);
        let zs = gauss_norm(s2);
        assert(gauss_kernel_partial(s2, e, 0) / zs <= eps);
        assert(gauss_kernel_partial(s2, e, 0) == 0real);
        assert(eps >= 0real) by(nonlinear_arith) requires 0real / zs <= eps, zs > 0real;
        assert((333u64 as real) / (100u64 as real) == 333real / 100real);
    }
    // keep what the sampler needs, drop the rest
    let tracked (c, _rest) = ec_split(input_credit, eps + slack, 1real / (pow2(90) as real) - slack);
    sample_gauss(333, 100, 45, 32, 112, 124, Ghost(e), Tracked(c), Ghost(eps))
}

} // verus!
