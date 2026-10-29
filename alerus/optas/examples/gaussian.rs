//! The discrete Gaussian N_ℤ(0, σ²), x = 1/(2σ²), by optimal approximate
//! sampling (Saad et al., Table 2), every step exact:
//!
//! 1. `taylor`: an exact L with L ≤ e^{−x} ≤ L + τ, τ = x^nt / nt!.
//! 2. `gauss_weights`: integer weights w_z = ⌊2^mb · L^{z²}⌋, z ∈ [−B, B].
//! 3. Algorithm 3 rounds w / Σw to M / 2^k (`gauss_matrix`,
//!    `construct_gauss_encoding`).
//!
//! ```text
//!   ε ≥ E_{N_ℤ(0,σ²)}[ℰ]  (gauss_expectation_le)        ℰ ∈ [0, 1]
//!   --------------------------------------------------------------------------
//!   [{ ↯(ε + gauss_delta + gauss_tail) }] sample_gauss(σ, B, nt, mb, k) [{ z. ↯(ℰ(z)) }]
//! ```
//!
//! `gauss_delta` = `taylor_delta` + `floor_delta` + (2B+1)/2^{k+1} covers
//! steps 1–3, and `gauss_tail` the truncation (`gaussian_tail.rs`).
//! `sample_gauss_table` samples a prebuilt table with the same spec.

use vstd::prelude::*;

use random::{UBig, IBig, ubig_from_u64, ubig_from_u128, ubig_mul, ubig_mul_u64, ubig_div, ubig_to_u128,
    ibig_from_ubig, ibig_from_i64, ibig_add, ibig_mul, ibig_neg, ibig_abs};

verus! {

use crate::ec::*;
#[cfg(verus_keep_ghost)]
use crate::ec::ErrorCreditCarrier::Value;
use crate::optas::utils::pow2_u128;
#[cfg(verus_keep_ghost)]
use crate::optas::utils::lemma_pow2_consts;
use crate::optas::examples::sampling::{optimal_matrix, construct_optimal_encoding};
use crate::optas::approx::sample_approx;
use crate::optas::sample::MatrixWalk;
use crate::optas::tree::OptasSpec;
use crate::ddg_walk::encoding::Encoded;
use crate::ddg_walk::walk::DdgWalk;
#[cfg(verus_keep_ghost)]
use crate::optas::examples::sampling::optimal_slack;
#[cfg(verus_keep_ghost)]
use crate::ddg_walk::walk::DdgSpec;
#[cfg(verus_keep_ghost)]
use crate::optas::sample::sampler_input;
#[cfg(verus_keep_ghost)]
use crate::optas::opt::ratio;
#[cfg(verus_keep_ghost)]
use crate::optas::approx::{pexp, credit_alloc_bound, approximates, lemma_transport};
#[cfg(verus_keep_ghost)]
use crate::optas::divergences::tv_pos;
#[cfg(verus_keep_ghost)]
use crate::optas::examples::gaussian_tail::{gauss_sigma2, gauss_x, gauss_tail, lemma_gauss_truncate};
#[cfg(verus_keep_ghost)]
use crate::cks::discrete_gaussian::gauss_expectation_le;
#[cfg(verus_keep_ghost)]
use crate::optas::utils::zkl;
#[cfg(verus_keep_ghost)]
use crate::optas::ztype::{wsum_nat, lemma_w_le_sum};
#[cfg(verus_keep_ghost)]
use crate::extern_spec::{ubig_view, ibig_view};
#[cfg(verus_keep_ghost)]
use crate::math::exp::{exp, factorial, exp_taylor_term, exp_taylor_seq, axiom_exp_zero, axiom_exp_add,
    axiom_exp_neg_range, axiom_exp_taylor_bounds};
#[cfg(verus_keep_ghost)]
use crate::math::pow::pow;
#[cfg(verus_keep_ghost)]
use crate::math::series::partial_sum;
#[cfg(verus_keep_ghost)]
use crate::cks::bernoulli_exp1_helper::lemma_factorial_pos;
#[cfg(verus_keep_ghost)]
use crate::fldr_helper::lemma_nat_mul_real_cast;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::{pow2, lemma_pow2_pos};

// ── The target ────────────────────────────────────────────────────────────────

/// (r − B)², for label r ↔ z = r − B.
pub open spec fn sq(b: nat, r: nat) -> nat {
    ((r as int - b as int) * (r as int - b as int)) as nat
}

/// The unnormalized Gaussian weight exp(−z² x) of label r.
pub open spec fn gw(x: real, b: nat, r: nat) -> real {
    exp(-((sq(b, r) as real) * x))
}

/// Σ_{r' ∈ [r, 2B]} exp(−(r' − B)² x).
pub open spec fn gsum(x: real, b: nat, r: nat) -> real
    decreases 2 * b + 1 - r,
{
    if r >= 2 * b + 1 { 0real } else { gw(x, b, r) + gsum(x, b, r + 1) }
}

/// The truncated discrete Gaussian on labels 0..2B.
pub open spec fn gauss(x: real, b: nat) -> spec_fn(nat) -> real {
    |r: nat| gw(x, b, r) / gsum(x, b, 0)
}

/// ℰ on labels: label r ↔ z = r − B.
pub open spec fn shift(e: spec_fn(int) -> real, b: nat) -> spec_fn(nat) -> real {
    |r: nat| e(r as int - b as int)
}

/// The loss from using the Taylor bound L ≤ e^{−x} ≤ L + τ (τ = x^nt / nt!)
/// in place of e^{−x}: (2B+1)·B²·τ.
pub open spec fn taylor_delta(x: real, b: nat, nt: nat) -> real {
    ((2 * b + 1) as real) * (((b * b) as real) * exp_taylor_term(x, nt))
}

/// The loss from flooring the weights to mb fractional bits: (2B+1)·2^{−mb}.
/// With `taylor_delta`, it bounds TV(w / Σw, p) (`lemma_weights_tv`).
pub open spec fn floor_delta(b: nat, mb: nat) -> real {
    ((2 * b + 1) as real) * (1real / (pow2(mb) as real))
}

// ── exp facts ─────────────────────────────────────────────────────────────────

/// exp(−N x) = exp(−x)^N.
proof fn lemma_exp_pow(x: real, n: nat)
    requires x > 0real,
    ensures exp(-((n as real) * x)) == pow(exp(-x), n),
    decreases n,
{
    if n == 0 {
        axiom_exp_zero();
        assert((n as real) == 0real);
        assert(-((n as real) * x) == 0real);
    } else {
        let n1 = (n - 1) as nat;
        lemma_exp_pow(x, n1);
        assert((n1 as real) * x >= 0real) by(nonlinear_arith) requires x > 0real;
        axiom_exp_add((n1 as real) * x, x);
        assert((n as real) * x == (n1 as real) * x + x) by(nonlinear_arith) requires n == n1 + 1;
        assert(-((n as real) * x) == -((n1 as real) * x + x));
        let c = exp(-x);
        let pc = pow(c, n1);
        assert(pow(c, n) == c * pc);
        assert(pc * c == c * pc) by(nonlinear_arith);
    }
}

/// The Taylor bracket: 0 ≤ L ≤ exp(−x) ≤ L + τ ≤ … and exp(−x) ≤ 1.
proof fn lemma_bracket(x: real, nt: nat)
    requires 0real < x <= 1real, nt >= 2, nt % 2 == 0,
    ensures
        0real <= partial_sum(exp_taylor_seq(x), nt),
        partial_sum(exp_taylor_seq(x), nt) <= exp(-x),
        exp(-x) <= partial_sum(exp_taylor_seq(x), nt) + exp_taylor_term(x, nt),
        exp(-x) <= 1real,
{
    axiom_exp_taylor_bounds(x, nt);
    axiom_exp_taylor_bounds(x, nt + 1);
    axiom_exp_neg_range(x);
    assert(partial_sum(exp_taylor_seq(x), nt + 1)
        == partial_sum(exp_taylor_seq(x), nt) + exp_taylor_seq(x)(nt));
}

/// 0 ≤ L ≤ c ≤ 1 ⟹ 0 ≤ L^N ≤ c^N ≤ 1 and c^N − L^N ≤ N(c − L).
proof fn lemma_pow_gap(lo: real, c: real, n: nat)
    requires 0real <= lo <= c <= 1real,
    ensures
        0real <= pow(lo, n) <= pow(c, n) <= 1real,
        pow(c, n) - pow(lo, n) <= (n as real) * (c - lo),
    decreases n,
{
    if n > 0 {
        let n1 = (n - 1) as nat;
        lemma_pow_gap(lo, c, n1);
        let a = pow(lo, n1);
        let d = pow(c, n1);
        assert(0real <= lo * a <= c * d <= 1real) by(nonlinear_arith)
            requires 0real <= lo <= c <= 1real, 0real <= a <= d <= 1real;
        assert(c * d - lo * a <= (n1 as real) * (c - lo) + (c - lo)) by(nonlinear_arith)
            requires 0real <= lo <= c <= 1real, 0real <= a <= d <= 1real, d - a <= (n1 as real) * (c - lo);
        assert((n1 as real) * (c - lo) + (c - lo) == (n as real) * (c - lo)) by(nonlinear_arith)
            requires n == n1 + 1;
        assert(pow(c, n) == c * d && pow(lo, n) == lo * a);
    } else {
        assert(pow(c, n) == 1real && pow(lo, n) == 1real);
        assert((n as real) * (c - lo) == 0real) by(nonlinear_arith) requires n == 0;
    }
}

/// One weight: if w ≤ 2^mb·L^N < w + 1 then w/2^mb ≤ exp(−Nx) ≤ w/2^mb + B²τ + 2^{−mb}.
proof fn lemma_weight(x: real, nt: nat, b: nat, nn: nat, mb: nat, w: nat)
    requires
        0real < x <= 1real, nt >= 2, nt % 2 == 0, nn <= b * b,
        (w as real) <= (pow2(mb) as real) * pow(partial_sum(exp_taylor_seq(x), nt), nn),
        (pow2(mb) as real) * pow(partial_sum(exp_taylor_seq(x), nt), nn) < (w + 1) as real,
    ensures
        (w as real) / (pow2(mb) as real) <= exp(-((nn as real) * x)),
        exp(-((nn as real) * x)) - (w as real) / (pow2(mb) as real)
            <= ((b * b) as real) * exp_taylor_term(x, nt) + 1real / (pow2(mb) as real),
{
    let lo = partial_sum(exp_taylor_seq(x), nt);
    let c = exp(-x);
    let tau = exp_taylor_term(x, nt);
    lemma_bracket(x, nt);
    lemma_pow_gap(lo, c, nn);
    lemma_exp_pow(x, nn);
    lemma_pow2_pos(mb);
    let pm = pow2(mb) as real;
    let pl = pow(lo, nn);
    let pc = pow(c, nn);
    assert((w as real) / pm <= pl) by(nonlinear_arith) requires (w as real) <= pm * pl, pm > 0real;
    assert(pl < (w as real) / pm + 1real / pm) by(nonlinear_arith)
        requires pm * pl < (w + 1) as real, pm > 0real, (w + 1) as real == (w as real) + 1real;
    assert((nn as real) * (c - lo) <= ((b * b) as real) * tau) by(nonlinear_arith)
        requires nn <= b * b, 0real <= c - lo <= tau;
}

// ── TV from approximate weights ───────────────────────────────────────────────

/// Σ_r w_r / 2^mb ≤ S and S − Σ_r w_r / 2^mb ≤ (labels left)·η.
proof fn lemma_gap_sum(x: real, b: nat, w: Seq<u128>, pm: real, eta: real, r: nat)
    requires
        w.len() == 2 * b + 1, pm > 0real, r <= w.len(),
        forall |i: nat| i < w.len() ==> (#[trigger] w[i as int] as real) / pm <= gw(x, b, i),
        forall |i: nat| i < w.len() ==> gw(x, b, i) - (#[trigger] w[i as int] as real) / pm <= eta,
    ensures
        (wsum_nat(w, r) as real) / pm <= gsum(x, b, r),
        gsum(x, b, r) - (wsum_nat(w, r) as real) / pm <= ((w.len() - r) as real) * eta,
    decreases w.len() - r,
{
    if r < w.len() {
        lemma_gap_sum(x, b, w, pm, eta, r + 1);
        let wr = w[r as int] as real;
        let ws1 = wsum_nat(w, r + 1) as real;
        assert((wr + ws1) / pm == wr / pm + ws1 / pm) by(nonlinear_arith) requires pm > 0real;
        let n1 = (w.len() - (r + 1)) as real;
        assert(n1 * eta + eta == (n1 + 1real) * eta) by(nonlinear_arith);
    } else {
        assert(0real / pm == 0real);
    }
}

/// Σ_{r' ≥ r} max(0, w_{r'}/W − p_{r'}) ≤ κ·Σ_{r' ≥ r} w_{r'}, where
/// κ = (S·pm − W)/(W·S·pm) and p = gw/S.
proof fn lemma_pos_sum(x: real, b: nat, w: Seq<u128>, pm: real, wt: nat, s: real, kappa: real, r: nat)
    requires
        w.len() == 2 * b + 1, pm > 0real, wt > 0, s > 0real, kappa >= 0real, r <= w.len(),
        kappa == (s * pm - (wt as real)) / ((wt as real) * s * pm),
        gsum(x, b, 0) == s,
        forall |i: nat| i < w.len() ==> (#[trigger] w[i as int] as real) / pm <= gw(x, b, i),
    ensures tv_pos(ratio(w, wt), gauss(x, b), w.len(), r) <= kappa * (wsum_nat(w, r) as real),
    decreases w.len() - r,
{
    if r < w.len() {
        lemma_pos_sum(x, b, w, pm, wt, s, kappa, r + 1);
        let wr = w[r as int] as real;
        let wtr = wt as real;
        let g = gw(x, b, r);
        assert(ratio(w, wt)(r) - gauss(x, b)(r) <= wr * kappa) by(nonlinear_arith)
            requires ratio(w, wt)(r) == wr / wtr, gauss(x, b)(r) == g / s, wr / pm <= g, s > 0real, pm > 0real,
                wtr > 0real, kappa == (s * pm - wtr) / (wtr * s * pm);
        assert(wr * kappa >= 0real) by(nonlinear_arith) requires wr >= 0real, kappa >= 0real;
        assert(kappa * (wsum_nat(w, r) as real) == wr * kappa + kappa * (wsum_nat(w, r + 1) as real)) by(nonlinear_arith)
            requires (wsum_nat(w, r) as real) == wr + (wsum_nat(w, r + 1) as real);
    } else {
        assert(kappa * 0real == 0real);
    }
}

/// TV(w/Σw, p) ≤ (2B+1)·η when each w_r/2^mb is within η below exp(−z²x).
proof fn lemma_weights_tv(x: real, b: nat, w: Seq<u128>, pm: real, eta: real)
    requires
        w.len() == 2 * b + 1, pm > 0real, wsum_nat(w, 0) > 0,
        gw(x, b, b) == 1real,
        forall |i: nat| i < w.len() ==> 0real <= gw(x, b, i),
        forall |i: nat| i < w.len() ==> (#[trigger] w[i as int] as real) / pm <= gw(x, b, i),
        forall |i: nat| i < w.len() ==> gw(x, b, i) - (#[trigger] w[i as int] as real) / pm <= eta,
    ensures
        gsum(x, b, 0) >= 1real,
        tv_pos(ratio(w, wsum_nat(w, 0)), gauss(x, b), w.len(), 0) <= ((2 * b + 1) as real) * eta,
{
    let wt = wsum_nat(w, 0);
    let wtr = wt as real;
    lemma_gsum_ge(x, b, 0);
    let s = gsum(x, b, 0);
    lemma_gap_sum(x, b, w, pm, eta, 0);
    let u = wtr / pm;
    assert(s * pm - wtr >= 0real) by(nonlinear_arith) requires u <= s, u == wtr / pm, pm > 0real;
    let kappa = (s * pm - wtr) / (wtr * s * pm);
    assert(kappa >= 0real) by(nonlinear_arith)
        requires kappa == (s * pm - wtr) / (wtr * s * pm), s * pm - wtr >= 0real, wtr > 0real, s > 0real, pm > 0real;
    lemma_pos_sum(x, b, w, pm, wt, s, kappa, 0);
    // κ·W = (S − W/pm)/S ≤ S − W/pm ≤ (2B+1)·η, using S ≥ 1.
    assert(kappa * wtr == (s - u) / s) by(nonlinear_arith)
        requires kappa == (s * pm - wtr) / (wtr * s * pm), u == wtr / pm, wtr > 0real, s > 0real, pm > 0real;
    assert((s - u) / s <= s - u) by(nonlinear_arith) requires s >= 1real, s - u >= 0real;
}

pub proof fn lemma_gsum_ge(x: real, b: nat, r: nat)
    requires
        gw(x, b, b) == 1real,
        forall |i: nat| i < 2 * b + 1 ==> 0real <= gw(x, b, i),
    ensures
        gsum(x, b, r) >= 0real,
        r <= b ==> gsum(x, b, r) >= 1real,
    decreases 2 * b + 1 - r,
{
    if r < 2 * b + 1 { lemma_gsum_ge(x, b, r + 1); }
}

// ── Exact Taylor sums ─────────────────────────────────────────────────────────

proof fn lemma_int_mul_real_cast(a: int, b: int)
    ensures (a * b) as real == (a as real) * (b as real),
{
    let an: nat = if a >= 0 { a as nat } else { (-a) as nat };
    let bn: nat = if b >= 0 { b as nat } else { (-b) as nat };
    lemma_nat_mul_real_cast(an, bn);
    let p = (an * bn) as real;
    let ar = a as real;
    let br = b as real;
    let anr = an as real;
    let bnr = bn as real;
    if a >= 0 && b >= 0 {
        assert(a * b == an * bn);
    } else if a < 0 && b >= 0 {
        assert(a * b == -(an * bn)) by(nonlinear_arith) requires an == -a, bn == b;
        assert(ar == -anr && br == bnr);
        assert(ar * br == -(anr * bnr)) by(nonlinear_arith) requires ar == -anr, br == bnr;
    } else if a >= 0 && b < 0 {
        assert(a * b == -(an * bn)) by(nonlinear_arith) requires an == a, bn == -b;
        assert(ar == anr && br == -bnr);
        assert(ar * br == -(anr * bnr)) by(nonlinear_arith) requires ar == anr, br == -bnr;
    } else {
        assert(a * b == an * bn) by(nonlinear_arith) requires an == -a, bn == -b;
        assert(ar == -anr && br == -bnr);
        assert(ar * br == anr * bnr) by(nonlinear_arith) requires ar == -anr, br == -bnr;
    }
}

/// term(i+1) = term(i)·(−x)/(i+1).
proof fn lemma_term_step(x: real, i: nat)
    ensures exp_taylor_term(x, i + 1) == exp_taylor_term(x, i) * (-x) / ((i + 1) as real),
{
    lemma_factorial_pos(i);
    let f = factorial(i);
    let p = pow(-x, i);
    assert(pow(-x, i + 1) == (-x) * p);
    assert(factorial(i + 1) == ((i + 1) as real) * f);
    assert(((-x) * p) / (((i + 1) as real) * f) == (p / f) * (-x) / ((i + 1) as real)) by(nonlinear_arith)
        requires f > 0real;
}

/// The even Taylor partial sum T_nt(x) of exp(−x), x = xn/xd, as an exact
/// fraction num/den.
pub fn taylor(xn: u64, xd: u64, nt: u64) -> (r: (UBig, UBig))
    requires 0 < xn <= xd, 2 <= nt <= 64, nt % 2 == 0,
    ensures
        ubig_view(&r.1) > 0,
        ubig_view(&r.0) <= ubig_view(&r.1),
        (ubig_view(&r.0) as real) / (ubig_view(&r.1) as real)
            == partial_sum(exp_taylor_seq(xn as real / xd as real), nt as nat),
{
    let ghost x = xn as real / xd as real;
    let mut snum: IBig = ibig_from_i64(0);
    let mut tnum: IBig = ibig_from_i64(1);
    let mut den: UBig = ubig_from_u64(1);
    let mut i: u64 = 0;
    proof {
        assert(pow(-x, 0) == 1real);
        assert(factorial(0) == 1real);
        assert(exp_taylor_term(x, 0) == 1real);
    }
    while i < nt
        invariant
            i <= nt <= 64, 0 < xn <= xd, x == xn as real / xd as real,
            ubig_view(&den) > 0,
            (ibig_view(&snum) as real) / (ubig_view(&den) as real) == partial_sum(exp_taylor_seq(x), i as nat),
            (ibig_view(&tnum) as real) / (ubig_view(&den) as real) == exp_taylor_term(x, i as nat),
        decreases nt - i,
    {
        let ghost s0 = ibig_view(&snum) as real;
        let ghost t0 = ibig_view(&tnum) as real;
        let ghost d0 = ubig_view(&den) as real;
        let g: UBig = ubig_mul_u64(&ubig_from_u64(xd), i + 1);
        let gi: IBig = ibig_from_ubig(&g);
        let st: IBig = ibig_add(&snum, &tnum);
        let new_snum = ibig_mul(&st, &gi);
        let xi: IBig = ibig_from_ubig(&ubig_from_u64(xn));
        let new_tnum = ibig_neg(&ibig_mul(&tnum, &xi));
        let new_den = ubig_mul(&den, &g);
        proof {
            let gr = ubig_view(&g) as real;
            assert(ubig_view(&g) == (xd as nat) * ((i + 1) as nat));
            lemma_nat_mul_real_cast(xd as nat, (i + 1) as nat);
            lemma_nat_mul_real_cast(ubig_view(&den), ubig_view(&g));
            lemma_int_mul_real_cast(ibig_view(&snum) + ibig_view(&tnum), ubig_view(&g) as int);
            lemma_int_mul_real_cast(ibig_view(&tnum), xn as int);
            assert(ubig_view(&g) > 0) by(nonlinear_arith) requires ubig_view(&g) == (xd as nat) * ((i + 1) as nat), xd > 0;
            let dn = ubig_view(&new_den) as real;
            assert(dn == d0 * gr);
            assert(gr == (xd as real) * ((i + 1) as real));
            assert(ubig_view(&new_den) > 0) by(nonlinear_arith)
                requires ubig_view(&new_den) == ubig_view(&den) * ubig_view(&g), ubig_view(&den) > 0, ubig_view(&g) > 0;
            // partial sums
            assert(partial_sum(exp_taylor_seq(x), (i + 1) as nat)
                == partial_sum(exp_taylor_seq(x), i as nat) + exp_taylor_term(x, i as nat));
            assert((ibig_view(&new_snum) as real) == (s0 + t0) * gr);
            assert(((s0 + t0) * gr) / (d0 * gr) == s0 / d0 + t0 / d0) by(nonlinear_arith)
                requires d0 > 0real, gr > 0real;
            // terms
            lemma_term_step(x, i as nat);
            assert((ibig_view(&new_tnum) as real) == -(t0 * (xn as real)));
            assert((-(t0 * (xn as real))) / (d0 * ((xd as real) * ((i + 1) as real)))
                == (t0 / d0) * (-((xn as real) / (xd as real))) / ((i + 1) as real)) by(nonlinear_arith)
                requires d0 > 0real, xd > 0, i + 1 > 0;
        }
        snum = new_snum;
        tnum = new_tnum;
        den = new_den;
        i = i + 1;
    }
    proof {
        assert(0real < x <= 1real) by(nonlinear_arith) requires x == xn as real / xd as real, 0 < xn <= xd;
        lemma_bracket(x, nt as nat);
        let d0 = ubig_view(&den) as real;
        let s0 = ibig_view(&snum) as real;
        assert(s0 >= 0real) by(nonlinear_arith) requires s0 / d0 >= 0real, d0 > 0real;
        assert(s0 <= d0) by(nonlinear_arith) requires s0 / d0 <= 1real, d0 > 0real;
    }
    let num = ibig_abs(&snum);
    (num, den)
}

// ── The weights ───────────────────────────────────────────────────────────────

/// w_r = ⌊2^mb · L^{(r−B)²}⌋ for r = 0..2B, with L = num/den.
pub fn gauss_weights(num: &UBig, den: &UBig, b: u64, mb: u64) -> (w: Vec<u128>)
    requires
        ubig_view(den) > 0, ubig_view(num) <= ubig_view(den),
        b <= 1000, mb <= 112,
    ensures
        w.len() == 2 * b + 1,
        forall |r: nat| r < w.len() ==> (#[trigger] w@[r as int]) <= pow2(mb as nat),
        forall |r: nat| r < w.len() ==>
            (#[trigger] w@[r as int] as real) <= (pow2(mb as nat) as real)
                * pow((ubig_view(num) as real) / (ubig_view(den) as real), sq(b as nat, r)),
        forall |r: nat| r < w.len() ==>
            (pow2(mb as nat) as real) * pow((ubig_view(num) as real) / (ubig_view(den) as real), sq(b as nat, r))
                < (#[trigger] w@[r as int] + 1) as real,
{
    let ghost lo = (ubig_view(num) as real) / (ubig_view(den) as real);
    let ghost pm = pow2(mb as nat);
    let p = pow2_u128(mb);
    proof {
        lemma_pow2_pos(mb as nat);
        crate::fldr_helper::lemma_pow2_mono(mb as nat, 124);
        lemma_pow2_consts();
    }
    let pu = ubig_from_u128(p);
    let mut w: Vec<u128> = Vec::new();
    let n = 2 * b + 1;
    let mut r: u64 = 0;
    while r < n
        invariant
            n == 2 * b + 1, b <= 1000, r <= n, w.len() == r, pm <= 0x10000000000000000000000000000000,
            ubig_view(den) > 0, ubig_view(num) <= ubig_view(den),
            lo == (ubig_view(num) as real) / (ubig_view(den) as real),
            p as nat == pm, pm > 0, ubig_view(&pu) == pm,
            forall |r: nat| r < w.len() ==> (#[trigger] w@[r as int]) <= pm,
            forall |r: nat| r < w.len() ==> (#[trigger] w@[r as int] as real) <= (pm as real) * pow(lo, sq(b as nat, r)),
            forall |r: nat| r < w.len() ==> (pm as real) * pow(lo, sq(b as nat, r)) < (#[trigger] w@[r as int] + 1) as real,
        decreases n - r,
    {
        let d: u64 = if r >= b { r - b } else { b - r };
        assert(d <= 1000);
        assert((d as int) * (d as int) <= 1000000) by(nonlinear_arith) requires d <= 1000;
        let nn: u64 = d * d;
        proof {
            assert(nn as nat == sq(b as nat, r as nat)) by(nonlinear_arith)
                requires d == (if r >= b { r - b } else { b - r }), nn == d * d;
        }
        // L^nn = acc_n / acc_d
        let mut acc_n: UBig = ubig_from_u64(1);
        let mut acc_d: UBig = ubig_from_u64(1);
        let mut i: u64 = 0;
        proof { assert(pow(lo, 0) == 1real); }
        while i < nn
            invariant
                i <= nn,
                ubig_view(den) > 0, ubig_view(num) <= ubig_view(den),
                lo == (ubig_view(num) as real) / (ubig_view(den) as real),
                ubig_view(&acc_d) > 0,
                ubig_view(&acc_n) <= ubig_view(&acc_d),
                (ubig_view(&acc_n) as real) / (ubig_view(&acc_d) as real) == pow(lo, i as nat),
            decreases nn - i,
        {
            let ghost an = ubig_view(&acc_n);
            let ghost ad = ubig_view(&acc_d);
            acc_n = ubig_mul(&acc_n, num);
            acc_d = ubig_mul(&acc_d, den);
            proof {
                let nu = ubig_view(num);
                let de = ubig_view(den);
                lemma_nat_mul_real_cast(an, nu);
                lemma_nat_mul_real_cast(ad, de);
                assert(ad * de > 0) by(nonlinear_arith) requires ad > 0, de > 0;
                assert(an * nu <= ad * de) by(nonlinear_arith) requires an <= ad, nu <= de;
                assert(pow(lo, (i + 1) as nat) == lo * pow(lo, i as nat));
                assert(((an as real) * (nu as real)) / ((ad as real) * (de as real))
                    == ((nu as real) / (de as real)) * ((an as real) / (ad as real))) by(nonlinear_arith)
                    requires ad > 0, de > 0;
            }
            i = i + 1;
        }
        let scaled = ubig_mul(&acc_n, &pu);
        let wq = ubig_div(&scaled, &acc_d);
        let ghost an = ubig_view(&acc_n);
        let ghost ad = ubig_view(&acc_d);
        proof {
            let sc = ubig_view(&scaled);
            let wv = ubig_view(&wq);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(sc as int, ad as int);
            assert(sc == an * pm);
            assert(wv <= pm) by(nonlinear_arith)
                requires wv == sc / ad, sc == an * pm, an <= ad, ad > 0, sc == ad * (sc / ad) + sc % ad, sc % ad >= 0;
            lemma_nat_mul_real_cast(an, pm);
            lemma_nat_mul_real_cast(ad, wv);
            let rem = sc % ad;
            assert((wv as real) <= (pm as real) * ((an as real) / (ad as real))
                && (pm as real) * ((an as real) / (ad as real)) < (wv as real) + 1real) by(nonlinear_arith)
                requires (sc as real) == (ad as real) * (wv as real) + (rem as real), 0 <= rem < ad, ad > 0,
                    (sc as real) == (an as real) * (pm as real);
        }
        let wv = ubig_to_u128(&wq);
        w.push(wv);
        r = r + 1;
    }
    w
}

// ── The sampler ───────────────────────────────────────────────────────────────

/// Steps 1 and 2: the weights w of the Gaussian on [−B, B], with
/// E_{w/Σw}[ℰ] ≤ E_p[ℰ] + (2B+1)·(B²·τ + 2^{−mb}) for every ℰ ∈ [0, 1].
pub fn gauss_input(xn: u64, xd: u64, b: u64, nt: u64, mb: u64) -> (w: Vec<u128>)
    requires
        0 < xn <= xd,
        2 <= nt <= 64, nt % 2 == 0,
        b <= 1000, mb <= 112,
    ensures
        w.len() == 2 * b + 1,
        0 < wsum_nat(w@, 0) <= 0x10000000000000000000000000000000,
        forall |ee: spec_fn(nat) -> real| credit_alloc_bound(ee) ==> #[trigger] pexp(ratio(w@, wsum_nat(w@, 0)), ee, (2 * b + 1) as nat, 0)
            <= pexp(gauss(xn as real / xd as real, b as nat), ee, (2 * b + 1) as nat, 0)
                + taylor_delta(xn as real / xd as real, b as nat, nt as nat) + floor_delta(b as nat, mb as nat),
{
    let ghost x = xn as real / xd as real;
    let ghost bn = b as nat;
    let (num, den) = taylor(xn, xd, nt);
    let w = gauss_weights(&num, &den, b, mb);
    let ghost pm = pow2(mb as nat) as real;
    let ghost eta = ((bn * bn) as real) * exp_taylor_term(x, nt as nat) + 1real / pm;
    proof {
        assert(0real < x <= 1real) by(nonlinear_arith) requires x == xn as real / xd as real, 0 < xn <= xd;
        lemma_pow2_pos(mb as nat);
        assert forall |i: nat| i < w.len() implies
            (#[trigger] w@[i as int] as real) / pm <= gw(x, bn, i)
            && gw(x, bn, i) - (w@[i as int] as real) / pm <= eta by {
            assert(sq(bn, i) <= bn * bn) by(nonlinear_arith) requires i < 2 * bn + 1, sq(bn, i) == ((i as int - bn as int) * (i as int - bn as int)) as nat;
            lemma_weight(x, nt as nat, bn, sq(bn, i), mb as nat, w@[i as int] as nat);
        }
        assert forall |i: nat| i < w.len() implies 0real <= gw(x, bn, i) by {
            assert((sq(bn, i) as real) * x >= 0real) by(nonlinear_arith) requires x > 0real;
            axiom_exp_neg_range((sq(bn, i) as real) * x);
        }
        assert(sq(bn, bn) == 0);
        axiom_exp_zero();
        assert(-((0 as real) * x) == 0real);
        assert(gw(x, bn, bn) == 1real);
        // w_B = 2^mb > 0, and all weights fit
        lemma_weight(x, nt as nat, bn, 0, mb as nat, w@[bn as int] as nat);
        assert(pow(partial_sum(exp_taylor_seq(x), nt as nat), 0) == 1real);
        assert(w@[bn as int] as real > pm - 1real);
        crate::fldr_helper::lemma_pow2_mono(mb as nat, 112);
        lemma_w_le_sum(w@, 0, bn);
        assert(wsum_nat(w@, 0) > 0) by(nonlinear_arith) requires w@[bn as int] as real > pm - 1real, pm >= 1real, w@[bn as int] <= wsum_nat(w@, 0);
        lemma_wsum_bound(w@, pow2(mb as nat), 0);
        assert(pow2(112) == 0x10000000000000000000000000000) by {
            lemma_pow2_consts();
            vstd::arithmetic::power2::lemma_pow2_adds(112, 12);
            vstd::arithmetic::power2::lemma2_to64();
        }
        assert(wsum_nat(w@, 0) <= 0x10000000000000000000000000000000) by(nonlinear_arith)
            requires wsum_nat(w@, 0) <= w@.len() * pow2(mb as nat), w@.len() <= 2001, pow2(mb as nat) <= 0x10000000000000000000000000000;
        lemma_weights_tv(x, bn, w@, pm, eta);
        assert(taylor_delta(x, bn, nt as nat) + floor_delta(bn, mb as nat) == ((2 * bn + 1) as real) * eta)
            by(nonlinear_arith) requires eta == ((bn * bn) as real) * exp_taylor_term(x, nt as nat) + 1real / pm,
                pm == pow2(mb as nat) as real,
                taylor_delta(x, bn, nt as nat) == ((2 * bn + 1) as real) * (((bn * bn) as real) * exp_taylor_term(x, nt as nat)),
                floor_delta(bn, mb as nat) == ((2 * bn + 1) as real) * (1real / (pow2(mb as nat) as real));
        // E_{w/Σw}[ℰ] ≤ E_p[ℰ] + TV(w/Σw, p) ≤ E_p[ℰ] + taylor_delta + floor_delta
        assert forall |ee: spec_fn(nat) -> real| credit_alloc_bound(ee) implies #[trigger] pexp(ratio(w@, wsum_nat(w@, 0)), ee, (2 * bn + 1) as nat, 0)
            <= pexp(gauss(x, bn), ee, (2 * bn + 1) as nat, 0) + taylor_delta(x, bn, nt as nat) + floor_delta(bn, mb as nat) by {
            lemma_transport(ratio(w@, wsum_nat(w@, 0)), gauss(x, bn), ee, w@.len(), 0);
        }
    }
    w
}

/// The total error δ of the Gaussian sampler, from M / 2^k to the truncated
/// Gaussian: the Taylor bound (`taylor_delta`), the floor (`floor_delta`), and
/// Theorem 4.17's (2B+1) / 2^{k+1} for Algorithm 3.
pub open spec fn gauss_delta(x: real, b: nat, nt: nat, mb: nat, k: nat) -> real {
    taylor_delta(x, b, nt) + floor_delta(b, mb) + ((2 * b + 1) as real) / (2real * (pow2(k) as real))
}

/// The input of the Gaussian samplers.
pub open spec fn gauss_params(xn: u64, xd: u64, b: u64, nt: u64, mb: u64, k: u64) -> bool {
    &&& 0 < xn <= xd
    &&& 2 <= nt <= 64 && nt % 2 == 0
    &&& b <= 1000 && mb <= 112 && 1 <= k <= 124
}

/// The layout of the optimal approximation of the weights approximates the
/// Gaussian within δ: Theorem 4.17's n / (2·2^k) plus the weights' error.
proof fn lemma_gauss_approx(s: OptasSpec, w: Seq<u128>, x: real, b: nat, nt: nat, mb: nat, k: nat)
    requires
        s.ms.len() == 2 * b + 1, w.len() == 2 * b + 1,
        approximates(s, ratio(w, wsum_nat(w, 0)), optimal_slack((2 * b + 1) as nat, k, k)),
        forall |ee: spec_fn(nat) -> real| credit_alloc_bound(ee) ==> #[trigger] pexp(ratio(w, wsum_nat(w, 0)), ee, (2 * b + 1) as nat, 0)
            <= pexp(gauss(x, b), ee, (2 * b + 1) as nat, 0) + taylor_delta(x, b, nt) + floor_delta(b, mb),
    ensures approximates(s, gauss(x, b), gauss_delta(x, b, nt, mb, k)),
{
    assert(zkl(k, k) == pow2(k));
    assert forall |ee: spec_fn(nat) -> real| credit_alloc_bound(ee) implies
        #[trigger] s.target(ee) <= pexp(gauss(x, b), ee, s.ms.len(), 0) + gauss_delta(x, b, nt, mb, k) by {
        assert(s.target(ee) <= pexp(ratio(w, wsum_nat(w, 0)), ee, s.ms.len(), 0) + optimal_slack((2 * b + 1) as nat, k, k));
        assert(pexp(ratio(w, wsum_nat(w, 0)), ee, (2 * b + 1) as nat, 0)
            <= pexp(gauss(x, b), ee, (2 * b + 1) as nat, 0) + taylor_delta(x, b, nt) + floor_delta(b, mb));
    }
}

/// Steps 1–3 as the matrix P of the optimal approximation (`sample_ky_matrix`):
/// x = xn/xd, Taylor terms nt, weight precision mb bits, sampler precision
/// k bits.
pub fn gauss_matrix(xn: u64, xd: u64, b: u64, nt: u64, mb: u64, k: u64) -> (r: (Vec<Vec<u8>>, u64, u64, Ghost<Seq<u128>>))
    requires gauss_params(xn, xd, b, nt, mb, k),
    ensures
        sampler_input(r.0@, r.3@, r.1 as nat, r.2 as nat),
        r.3@.len() == 2 * b + 1,
        approximates(OptasSpec { ms: r.3@, k: r.1 as nat, l: r.2 as nat }, gauss(xn as real / xd as real, b as nat),
            gauss_delta(xn as real / xd as real, b as nat, nt as nat, mb as nat, k as nat)),
{
    let w = gauss_input(xn, xd, b, nt, mb);
    let r = optimal_matrix(&w, k, k);
    proof {
        lemma_gauss_approx(OptasSpec { ms: r.3@, k: r.1 as nat, l: r.2 as nat }, w@, xn as real / xd as real,
            b as nat, nt as nat, mb as nat, k as nat);
    }
    r
}

/// Steps 1–3 as the packed encoding of the original (`construct_sample_ky_encoding`).
pub fn construct_gauss_encoding(xn: u64, xd: u64, b: u64, nt: u64, mb: u64, k: u64) -> (enc: Encoded<OptasSpec>)
    requires gauss_params(xn, xd, b, nt, mb, k),
    ensures
        enc.wf(),
        enc.spec@.ms.len() == 2 * b + 1,
        approximates(enc.spec@, gauss(xn as real / xd as real, b as nat),
            gauss_delta(xn as real / xd as real, b as nat, nt as nat, mb as nat, k as nat)),
{
    let w = gauss_input(xn, xd, b, nt, mb);
    let enc = construct_optimal_encoding(&w, k, k);
    proof {
        lemma_gauss_approx(enc.spec@, w@, xn as real / xd as real, b as nat, nt as nat, mb as nat, k as nat);
    }
    enc
}

/// The discrete Gaussian N_ℤ(0, σ²) from any layout that approximates its
/// truncation to [−B, B] within δ (`gauss_matrix`, `construct_gauss_encoding`
/// with x = 1/(2σ²)); label ret stands for z = ret − B. The precondition on ε
/// (`gauss_expectation_le`) is equivalent to that of CKS's
/// `sample_discrete_gaussian(σ)`; the truncation costs `gauss_tail` more:
///
/// ```text
///   ε ≥ E_{N_ℤ(0,σ²)}[ℰ]        ℰ ∈ [0, 1]
///   ------------------------------------------------------------
///   [{ ↯(ε + δ + gauss_tail(x, B)) }] sample_gauss_table(w, σ) [{ z. ↯(ℰ(z)) }]
/// ```
pub fn sample_gauss_table<W: DdgWalk<Spec = OptasSpec>>(
    w: &W,                                  // any layout of M / Z_kl: matrix, cached or packed
    b: u64,                                 // B: the support is [−B, B]
    Ghost(sigma): Ghost<real>,              // σ, as CKS's `scale`
    Ghost(delta): Ghost<real>,              // how far M / Z_kl is from the truncated Gaussian
    Ghost(e): Ghost<spec_fn(int) -> real>,  // ℰ, indexed by z (not by label)
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(eps): Ghost<real>,                // ε: pays for E[ℰ] under the full Gaussian
) -> ((z, out_credit): (i64, Tracked<ErrorCreditResource>))
    requires
        sigma > 0real,
        // the table encodes its distribution
        w.wf(),
        // label ret ∈ [0, 2B] is z = ret − B; B ≤ 1000 as in `gauss_params`
        b <= 1000,
        // one label ret = z + B per z ∈ [−B, B]
        w.spec().ms.len() == 2 * b + 1,
        // E_{M/Z}[ℰ] ≤ E_B[ℰ] + δ; proved by `gauss_matrix` / `construct_gauss_encoding`
        approximates(w.spec(), gauss(gauss_x(sigma), b as nat), delta),
        // the slack bounds TV, which only pays for credits in [0, 1]
        forall |z: int| 0real <= #[trigger] e(z) <= 1real,
        // ε ≥ E_{N_ℤ(0,σ²)}[ℰ] (equivalent to the precondition of `sample_discrete_gaussian(σ)`)
        gauss_expectation_le(sigma * sigma, e, eps),
        // ε, plus the table's error δ, plus the mass outside [−B, B]
        input_credit@ =~= (Value { car: eps + delta + gauss_tail(gauss_x(sigma), b as nat) }),
    ensures
        // the output is in the support
        -(b as int) <= z <= b as int,
        // ↯(ℰ(z)) for the sampled z
        out_credit@@ =~= (Value { car: e(z as int) }),
{
    let ghost x = gauss_x(sigma);
    let ghost ee = shift(e, b as nat);
    let ghost eps1 = eps + gauss_tail(x, b as nat);
    proof {
        // σ² = 1/(2x)
        assert(x > 0real && gauss_sigma2(x) == sigma * sigma) by(nonlinear_arith)
            requires sigma > 0real, x == 1real / (2real * sigma * sigma),
                gauss_sigma2(x) == 1real / (2real * x);
        assert(credit_alloc_bound(ee));
        lemma_gauss_truncate(x, b as nat, e, eps);
        assert(eps1 + delta == eps + delta + gauss_tail(x, b as nat));
    }
    let (ret, Tracked(out)) = sample_approx(w, Ghost(gauss(x, b as nat)), Ghost(delta), Ghost(ee),
        Tracked(input_credit), Ghost(eps1));
    (ret as i64 - b as i64, Tracked(out))
}

/// σ = sn / sd ≥ 1/√2, so that x = 1/(2σ²) = sd² / (2·sn²) ≤ 1 and both
/// fit in a u64.
pub open spec fn wf_scale(sn: u64, sd: u64) -> bool {
    &&& 0 < sn < 0x80000000 && 0 < sd < 0x80000000
    &&& sd * sd <= 2 * sn * sn
}

/// The approximate discrete Gaussian N_ℤ(0, σ²), σ = sn / sd
pub fn sample_gauss(
    sn: u64, sd: u64,                       // σ = sn / sd
    b: u64,                                 // B: the support is [−B, B]
    nt: u64,                                // Taylor terms for exp(−x): 
                                            // L = Σ_{i=0}^{nt−1} (−x)^i / i! = 1 − x + x²/2! − x³/3! + … − x^{nt−1}/(nt−1)!
                                            // L ≤ e^{−x} ≤ L + τ,  τ = x^nt / nt!
    mb: u64,                                // bits of the integer weights
    k: u64,                                 // bits of the sampler
    Ghost(e): Ghost<spec_fn(int) -> real>,  // credit allocation ℰ
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(eps): Ghost<real>,
) -> ((z, out_credit): (i64, Tracked<ErrorCreditResource>))
    requires
        wf_scale(sn, sd),
        // nt must be even to have L > 0
        2 <= nt <= 64 && nt % 2 == 0, 
        b <= 1000, mb <= 112, 1 <= k <= 124,
        // the slack bounds TV, which only pays for credits in [0, 1]
        forall |z: int| 0real <= #[trigger] e(z) <= 1real,
        // ε ≥ E_{N_ℤ(0,σ²)}[ℰ] (equivalent to the precondition of `sample_discrete_gaussian(σ)`)
        ({ let sigma = sn as real / sd as real; gauss_expectation_le(sigma * sigma, e, eps) }),
        // ε, plus the approximation error δ, plus the mass outside [−B, B]
        ({ let x = gauss_x(sn as real / sd as real);
           input_credit@ =~= (Value { car: eps + gauss_delta(x, b as nat, nt as nat, mb as nat, k as nat) + gauss_tail(x, b as nat) }) }),
    ensures
        -(b as int) <= z <= b as int,
        out_credit@@ =~= (Value { car: e(z as int) }),
{
    let ghost sigma = sn as real / sd as real;
    // x = 1/(2σ²) = sd² / (2·sn²)
    proof {
        assert(0 < sd * sd < 0x4000000000000000) by(nonlinear_arith) requires 0 < sd < 0x80000000u64;
        assert(2 * sn * sn < 0x8000000000000000) by(nonlinear_arith) requires sn < 0x80000000u64;
    }
    let xn = sd * sd;
    let xd = 2 * sn * sn;
    proof {
        crate::fldr_helper::lemma_nat_mul_real_cast(sd as nat, sd as nat);
        crate::fldr_helper::lemma_nat_mul_real_cast(2 * sn as nat, sn as nat);
        crate::fldr_helper::lemma_nat_mul_real_cast(2, sn as nat);
        assert(xn as real / xd as real == gauss_x(sigma)) by(nonlinear_arith)
            requires sigma == sn as real / sd as real, sn > 0u64, sd > 0u64,
                xn as real == (sd as real) * (sd as real), xd as real == 2real * (sn as real) * (sn as real);
        assert(sigma > 0real) by(nonlinear_arith)
            requires sigma == sn as real / sd as real, sn > 0u64, sd > 0u64;
    }
    let (p, k2, l2, ms2) = gauss_matrix(xn, xd, b, nt, mb, k);
    let w = MatrixWalk { p: &p, k: k2, l: l2, ms: ms2 };
    sample_gauss_table(&w, b, Ghost(sigma),
        Ghost(gauss_delta(gauss_x(sigma), b as nat, nt as nat, mb as nat, k as nat)),
        Ghost(e), Tracked(input_credit), Ghost(eps))
}

proof fn lemma_wsum_bound(w: Seq<u128>, bound: nat, r: nat)
    requires r <= w.len(), forall |i: nat| i < w.len() ==> (#[trigger] w[i as int]) <= bound,
    ensures wsum_nat(w, r) <= (w.len() - r) * bound,
    decreases w.len() - r,
{
    if r < w.len() {
        lemma_wsum_bound(w, bound, r + 1);
        assert(w[r as int] + (w.len() - (r + 1)) * bound <= (w.len() - r) * bound) by(nonlinear_arith)
            requires w[r as int] <= bound;
    }
}

} // verus!
