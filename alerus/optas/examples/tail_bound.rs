//! A tail bound from `sample_gauss_table`: with ℰ(z) = [|z| > T], an output
//! with |z| > T would hold ↯(1), which is impossible.
//!
//! ```text
//!   [{ ↯(2^{−15}) }] sample_std_gauss_within_5() [{ z. −5 ≤ z ≤ 5 }]
//! ```

use vstd::prelude::*;

verus! {

use crate::ec::*;
#[cfg(verus_keep_ghost)]
use crate::ec::ErrorCreditCarrier::Value;
use crate::optas::tree::OptasSpec;
use crate::ddg_walk::walk::DdgWalk;
use crate::optas::examples::gaussian::{sample_gauss_table, sample_gauss};
#[cfg(verus_keep_ghost)]
use crate::ddg_walk::walk::DdgSpec;
#[cfg(verus_keep_ghost)]
use crate::optas::approx::approximates;
#[cfg(verus_keep_ghost)]
use crate::optas::examples::gaussian::{gauss, gauss_delta, exp_tau, exp_split, lemma_exp_le_pow2, lemma_half_pow};
#[cfg(verus_keep_ghost)]
use crate::math::exp::{factorial, exp_taylor_term};
#[cfg(verus_keep_ghost)]
use crate::math::pow::pow;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::{pow2, lemma2_to64, lemma_pow2_pos};
#[cfg(verus_keep_ghost)]
use crate::optas::examples::gaussian_tail::{gauss_x, gauss_sigma2, gauss_tail, gk, lemma_kp_tail, lemma_gk_range};
#[cfg(verus_keep_ghost)]
use crate::cks::discrete_gaussian::{gauss_kernel_partial, gauss_kernel, gauss_expectation_le, gauss_norm, dg_ones};
#[cfg(verus_keep_ghost)]
use crate::cks::discrete_gaussian_helper::lemma_gauss_expectation_iff;
#[cfg(verus_keep_ghost)]
use crate::math::exp::{exp, axiom_exp_neg_range, axiom_exp_neg_strict};

/// ℰ(z) = 1 if |z| > T, else 0.
pub open spec fn outside(t: nat) -> spec_fn(int) -> real {
    |z: int| if z > t || z < -(t as int) { 1real } else { 0real }
}

/// The kernel sum of [|z| > T] over |z| < n is that of 1 beyond T.
proof fn lemma_kp_outside(s2: real, t: nat, n: nat)
    requires s2 > 0real,
    ensures
        gauss_kernel_partial(s2, outside(t), n) >= 0real,
        n <= t + 1 ==> gauss_kernel_partial(s2, outside(t), n) == 0real,
        n > t + 1 ==> gauss_kernel_partial(s2, outside(t), n)
            == gauss_kernel_partial(s2, dg_ones(), n) - gauss_kernel_partial(s2, dg_ones(), t + 1),
    decreases n,
{
    if n > 1 {
        lemma_kp_outside(s2, t, (n - 1) as nat);
        let k = (n - 1) as nat;
        let kr = k as real;
        assert(kr * kr / (2real * s2) >= 0real) by(nonlinear_arith) requires s2 > 0real;
        axiom_exp_neg_range(kr * kr / (2real * s2));
        assert(gauss_kernel(s2, kr) >= 0real);
        let g = gauss_kernel(s2, kr);
        assert(gauss_kernel_partial(s2, outside(t), n)
            == gauss_kernel_partial(s2, outside(t), k) + g * (outside(t)(k as int) + outside(t)(-(k as int))));
        assert(gauss_kernel_partial(s2, dg_ones(), n)
            == gauss_kernel_partial(s2, dg_ones(), k) + g * (1real + 1real));
        if k > t {
            assert(outside(t)(k as int) == 1real && outside(t)(-(k as int)) == 1real);
            if k == t + 1 {
                assert(gauss_kernel_partial(s2, outside(t), k) == 0real);
            }
        } else {
            assert(outside(t)(k as int) == 0real && outside(t)(-(k as int)) == 0real);
            assert(g * (0real + 0real) == 0real);
        }
    } else if n == 1 {
        assert(outside(t)(0int) == 0real);
        assert(gauss_kernel(s2, 0real) * 0real == 0real);
    }
}

/// Pr_{N_ℤ(0,σ²)}[|z| > T] ≤ gauss_tail(x, T), σ² = 1/(2x).
pub proof fn lemma_outside_le(x: real, t: nat)
    requires x > 0real,
    ensures gauss_expectation_le(gauss_sigma2(x), outside(t), gauss_tail(x, t)),
{
    let s2 = gauss_sigma2(x);
    assert(s2 > 0real) by(nonlinear_arith) requires x > 0real, s2 == 1real / (2real * x);
    // Z_σ ≥ 1 (any valid (p, t) of CKS will do; t = 1)
    assert(1real / 1real == 1real);
    lemma_gauss_expectation_iff(exp(-(1real / 1real)), s2, 1real, outside(t), gauss_tail(x, t));
    let zs = gauss_norm(s2);
    // gauss_tail ≥ 0
    let u = gauss_tail(x, t);
    lemma_gk_range(x, t + 1);
    let q = exp(-(((2 * t + 3) as nat) as real * x));
    assert(((2 * t + 3) as nat) as real * x > 0real) by(nonlinear_arith) requires x > 0real;
    axiom_exp_neg_strict(((2 * t + 3) as nat) as real * x);
    assert(u >= 0real) by(nonlinear_arith) requires u == 2real * gk(x, t + 1) / (1real - q), gk(x, t + 1) > 0real, q < 1real;
    assert forall |n: nat| #[trigger] gauss_kernel_partial(s2, outside(t), n) / zs <= u by {
        lemma_kp_outside(s2, t, n);
        lemma_kp_tail(x, t, n);
        let kp = gauss_kernel_partial(s2, outside(t), n);
        assert(0real <= kp <= u);
        assert(kp / zs <= u) by(nonlinear_arith) requires 0real <= kp <= u, zs >= 1real, u >= 0real;
    }
}

/// One sample of N_ℤ(0, σ²) from a table (`gauss_matrix`,
/// `construct_gauss_encoding`), certainly within [−T, T].
pub fn sample_gauss_within<W: DdgWalk<Spec = OptasSpec>>(
    w: &W,
    b: u64,
    Ghost(t): Ghost<nat>,                   // T: never checked at run time
    Ghost(sigma): Ghost<real>,
    Ghost(delta): Ghost<real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
) -> (z: i64)
    requires
        sigma > 0real,
        w.wf(),
        b <= 1000,
        w.spec().ms.len() == 2 * b + 1,
        approximates(w.spec(), gauss(gauss_x(sigma), b as nat), delta),
        input_credit@ =~= (Value { car: gauss_tail(gauss_x(sigma), t) + delta
            + gauss_tail(gauss_x(sigma), b as nat) }),
    ensures -(t as int) <= z <= t as int,
{
    let ghost x = gauss_x(sigma);
    let ghost e = outside(t);
    proof {
        assert(x > 0real && gauss_sigma2(x) == sigma * sigma) by(nonlinear_arith)
            requires sigma > 0real, x == 1real / (2real * sigma * sigma),
                gauss_sigma2(x) == 1real / (2real * x);
        lemma_outside_le(x, t);
    }
    let (z, Tracked(out)) = sample_gauss_table(w, b, Ghost(sigma), Ghost(delta), Ghost(e),
        Tracked(input_credit), Ghost(gauss_tail(x, t)));
    proof {
        // |z| > T would leave ↯(1)
        if !(-(t as int) <= z <= t as int) {
            assert(e(z as int) == 1real);
            ec_contradict(&out);
        }
    }
    z
}

// ── A concrete instance: σ = 1, |z| ≤ 5 ──────────────────────────────────────

/// gauss_tail(x, b) ≤ 2·(64/63)·2^{−n} when (b+1)²x ≥ n and (2b+3)x ≥ 6.
proof fn lemma_tail_le(x: real, b: nat, n: nat)
    requires
        x > 0real,
        ((b + 1) as real) * ((b + 1) as real) * x >= n as real,
        ((2 * b + 3) as nat) as real * x >= 6real,
    ensures 0real <= gauss_tail(x, b) <= 128real / (63real * (pow2(n) as real)),
{
    lemma_exp_le_pow2(((b + 1) as real) * ((b + 1) as real) * x, n);
    lemma_exp_le_pow2(((2 * b + 3) as nat) as real * x, 6);
    lemma2_to64();
    lemma_pow2_pos(n);
    let g = gk(x, b + 1);
    let q = exp(-(((2 * b + 3) as nat) as real * x));
    let p = pow2(n) as real;
    assert(g <= 1real / p);
    assert(q <= 1real / 64real);
    assert(gauss_tail(x, b) == 2real * g / (1real - q));
    assert(0real <= 2real * g / (1real - q) <= 128real / (63real * p)) by(nonlinear_arith)
        requires 0real < g <= 1real / p, 0real < q <= 1real / 64real, p > 0real;
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

/// For σ = 1 (x = 1/2), B = 20, nt = 40, mb = 112, k = 64:
/// Pr[|z| > 5] + δ + Pr[|z| > 20] ≤ 2^{−15}.
pub proof fn lemma_std_budget()
    ensures
        0real <= gauss_tail(1real / 2real, 5) + gauss_delta(1real / 2real, 20, 40, 112, 64) + gauss_tail(1real / 2real, 20),
        gauss_tail(1real / 2real, 5) + gauss_delta(1real / 2real, 20, 40, 112, 64) + gauss_tail(1real / 2real, 20)
            <= 1real / 32768real,
{
    let x = 1real / 2real;
    lemma2_to64();
    // the two tails: ≤ 2·(64/63)·2^{−18} and ≤ 2·(64/63)·2^{−64}
    assert(((5nat + 1) as real) == 6real && ((20nat + 1) as real) == 21real);
    assert(((2 * 5nat + 3) as nat) as real == 13real && ((2 * 20nat + 3) as nat) as real == 43real);
    lemma_tail_le(x, 5, 18);
    lemma_tail_le(x, 20, 64);
    // taylor_delta: m = 1, τ = (1/2)^40 / 40! ≤ 2^{−40}
    assert(x.floor() == 0);
    assert(exp_split(x) == 1);
    assert(x / (1nat as real) == x);
    lemma_pow_neg_even(x, 20);
    lemma_factorial_ge_1(40);
    lemma_half_pow(40);
    vstd::arithmetic::power2::lemma_pow2_adds(32, 8);
    vstd::arithmetic::power2::lemma_pow2_strictly_increases(64, 112);
    let p18 = pow2(18) as real;
    let p40 = pow2(40) as real;
    let p64 = pow2(64) as real;
    let p112 = pow2(112) as real;
    assert(p18 == 262144real && p40 == 1099511627776real && p64 == 18446744073709551616real && p112 > p64);
    let h = pow(x, 40);
    let tau = exp_tau(x, 40);
    assert(exp_taylor_term(x, 40) == h / factorial(40));
    assert(tau == 1real * exp_taylor_term(x, 40));
    assert(0real <= tau <= 1real / p40) by(nonlinear_arith)
        requires tau == h / factorial(40), factorial(40) >= 1real, h * p40 == 1real, p40 > 0real;
    // all together, with floor_delta ≤ 41·2^{−64}
    let t5 = gauss_tail(x, 5);
    let t20 = gauss_tail(x, 20);
    assert(gauss_delta(x, 20, 40, 112, 64) == 41real * (400real * tau) + 41real * (1real / p112) + 41real / (2real * p64));
    assert(0real <= t5 + (41real * (400real * tau) + 41real * (1real / p112) + 41real / (2real * p64)) + t20 <= 1real / 32768real)
        by(nonlinear_arith)
        requires
            0real <= t5 <= 128real / (63real * p18), 0real <= t20 <= 128real / (63real * p64),
            0real <= tau <= 1real / p40, p112 > p64,
            p18 == 262144real, p40 == 1099511627776real, p64 == 18446744073709551616real;
}

/// N_ℤ(0, 1), certainly within [−5, 5], for ↯(2^{−15}).
///
/// The true Pr[|z| > 5] is about 1.2·10⁻⁸ (2^{−26.3}); with ↯(2^{−15}) the
/// exact tail would already allow |z| ≤ 4. The gap is from bounding e^{−1} by 1/2.
pub fn sample_std_gauss_within_5(Tracked(input_credit): Tracked<ErrorCreditResource>) -> (z: i64)
    requires input_credit@ =~= (Value { car: 1real / 32768real }),
    ensures -5 <= z <= 5,
{
    let ghost x = 1real / 2real;
    let ghost e = outside(5);
    let ghost need = gauss_tail(x, 5) + gauss_delta(x, 20, 40, 112, 64) + gauss_tail(x, 20);
    proof {
        assert(gauss_x(1real / 1real) == x);
        assert(gauss_sigma2(x) == (1real / 1real) * (1real / 1real));
        lemma_outside_le(x, 5);
        lemma_std_budget();
    }
    // keep what the sampler needs, drop the rest
    let tracked (c, _rest) = ec_split(input_credit, need, 1real / 32768real - need);
    let (z, Tracked(out)) = sample_gauss(1, 1, 20, 40, 112, 64, Ghost(e), Tracked(c), Ghost(gauss_tail(x, 5)));
    proof {
        if !(-5 <= z <= 5) {
            assert(e(z as int) == 1real);
            ec_contradict(&out);
        }
    }
    z
}

} // verus!
