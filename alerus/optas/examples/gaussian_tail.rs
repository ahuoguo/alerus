//! The truncation to [−B, B] against the full N_ℤ(0, σ²), σ² = 1/(2x):
//!
//! ```text
//!   E_{N_ℤ}[ℰ] ≤ ε  (gauss_expectation_le)            ℰ ∈ [0, 1]
//!   ------------------------------------------------------------
//!   E_B[ℰ] ≤ ε + gauss_tail(x, B)                     (lemma_gauss_truncate)
//! ```
//!
//! A geometric bound on the kernel beyond B (`lemma_kp_tail`) shows the
//! full normalizer is at most S + gauss_tail, S the truncated one.

use vstd::prelude::*;

verus! {

#[cfg(verus_keep_ghost)]
use crate::math::exp::{exp, axiom_exp_add, axiom_exp_neg_range, axiom_exp_neg_strict, axiom_exp_zero};
#[cfg(verus_keep_ghost)]
use crate::math::series::{seq_at, is_bounded_above, lemma_limit_le_bound};
#[cfg(verus_keep_ghost)]
use crate::cks::discrete_gaussian::{
    gauss_kernel, gauss_kernel_partial, gauss_kernel_zero, gauss_kernel_sym, gauss_const,
    gauss_accept_prob, accept_mass_seq, gauss_pmf_partial, gauss_expectation_bounded_by, gauss_expectation_le, dg_ones,
};
#[cfg(verus_keep_ghost)]
use crate::cks::discrete_gaussian_helper::{lemma_gauss_pmf_partial_eq, lemma_gauss_accept_prob, lemma_gauss_const_pos,
    lemma_gauss_expectation_iff};
#[cfg(verus_keep_ghost)]
use crate::fldr_helper::lemma_nat_mul_real_cast;
#[cfg(verus_keep_ghost)]
use crate::optas::approx::pexp;
#[cfg(verus_keep_ghost)]
use crate::optas::examples::gaussian::{gw, gsum, gauss, shift, sq};

/// σ² = 1/(2x).
pub open spec fn gauss_sigma2(x: real) -> real {
    1real / (2real * x)
}

/// x = 1/(2σ²).
pub open spec fn gauss_x(sigma: real) -> real {
    1real / (2real * sigma * sigma)
}

/// exp(−k² x).
pub open spec fn gk(x: real, k: nat) -> real {
    exp(-((k as real) * (k as real) * x))
}

/// 2·exp(−(B+1)² x) / (1 − exp(−(2B+3) x)): the mass of |z| > B, relative to
/// that of [−B, B], is at most this.
pub open spec fn gauss_tail(x: real, b: nat) -> real {
    2real * gk(x, b + 1) / (1real - exp(-(((2 * b + 3) as nat) as real * x)))
}

/// Σ_{r' ∈ [r, 2B]} exp(−(r' − B)² x)·ℰ(r' − B).
pub open spec fn gsum_e(x: real, b: nat, e: spec_fn(int) -> real, r: nat) -> real
    decreases 2 * b + 1 - r,
{
    if r >= 2 * b + 1 { 0real } else { gw(x, b, r) * e(r as int - b as int) + gsum_e(x, b, e, r + 1) }
}

// ── The kernel ────────────────────────────────────────────────────────────────

/// CKS's kernel at σ² = 1/(2x) is exp(−k² x).
proof fn lemma_kernel(x: real, k: nat)
    requires x > 0real,
    ensures gauss_kernel(gauss_sigma2(x), k as real) == gk(x, k),
{
    let kr = k as real;
    assert(kr * kr / (2real * gauss_sigma2(x)) == kr * kr * x) by(nonlinear_arith)
        requires x > 0real, gauss_sigma2(x) == 1real / (2real * x);
}

/// The weight of label B ± k is exp(−k² x).
proof fn lemma_gw(x: real, b: nat, k: nat)
    ensures
        gw(x, b, b + k) == gk(x, k),
        k <= b ==> gw(x, b, (b - k) as nat) == gk(x, k),
{
    lemma_nat_mul_real_cast(k, k);
    assert(sq(b, b + k) == k * k) by(nonlinear_arith);
    if k <= b {
        assert(sq(b, (b - k) as nat) == k * k) by(nonlinear_arith) requires k <= b;
    }
}

proof fn lemma_gk_range(x: real, k: nat)
    requires x > 0real,
    ensures 0real < gk(x, k) <= 1real, k == 0 ==> gk(x, k) == 1real,
{
    let kr = k as real;
    assert(kr * kr * x >= 0real) by(nonlinear_arith) requires x > 0real, kr >= 0real;
    axiom_exp_neg_range(kr * kr * x);
    if k == 0 {
        assert(-(kr * kr * x) == 0real) by(nonlinear_arith) requires kr == 0real;
        axiom_exp_zero();
    }
}

proof fn lemma_gw_range(x: real, b: nat)
    requires x > 0real,
    ensures gw(x, b, b) == 1real, forall |r: nat| 0real <= #[trigger] gw(x, b, r),
{
    lemma_gw(x, b, 0);
    lemma_gk_range(x, 0);
    assert forall |r: nat| 0real <= #[trigger] gw(x, b, r) by {
        assert((sq(b, r) as real) * x >= 0real) by(nonlinear_arith) requires x > 0real;
        axiom_exp_neg_range((sq(b, r) as real) * x);
    }
}

/// exp(−(a + d + r)) ≤ exp(−d)·exp(−a) for a, d, r ≥ 0.
proof fn lemma_exp_split(a: real, d: real, r: real)
    requires a >= 0real, d >= 0real, r >= 0real,
    ensures exp(-(a + (d + r))) <= exp(-d) * exp(-a),
{
    axiom_exp_add(a, d + r);
    axiom_exp_add(d, r);
    axiom_exp_neg_range(a);
    axiom_exp_neg_range(d);
    axiom_exp_neg_range(r);
    let ea = exp(-a);
    let ed = exp(-d);
    let er = exp(-r);
    assert(ea * (ed * er) <= ed * ea) by(nonlinear_arith) requires ea > 0real, ed > 0real, 0real < er <= 1real;
}

/// exp(−(k+1)² x) ≤ exp(−(2B+3) x)·exp(−k² x) for k ≥ B + 1.
proof fn lemma_gk_ratio(x: real, b: nat, k: nat)
    requires x > 0real, k >= b + 1,
    ensures gk(x, k + 1) <= exp(-(((2 * b + 3) as nat) as real * x)) * gk(x, k),
{
    let kr = k as real;
    let d = ((2 * b + 3) as nat) as real * x;
    let rest = ((2 * k + 1) as real - ((2 * b + 3) as nat) as real) * x;
    assert(d >= 0real && rest >= 0real) by(nonlinear_arith)
        requires x > 0real, d == ((2 * b + 3) as nat) as real * x,
            rest == ((2 * k + 1) as real - ((2 * b + 3) as nat) as real) * x, k >= b + 1;
    let a = kr * kr * x;
    assert(a >= 0real) by(nonlinear_arith) requires x > 0real, kr >= 0real, a == kr * kr * x;
    // (k+1)² x = k² x + (2B+3) x + rest
    assert(((k + 1) as nat) as real == kr + 1real);
    assert((kr + 1real) * (kr + 1real) * x == a + (d + rest)) by(nonlinear_arith)
        requires d == ((2 * b + 3) as nat) as real * x, a == kr * kr * x,
            rest == ((2 * k + 1) as real - ((2 * b + 3) as nat) as real) * x,
            (2 * k + 1) as real == 2real * kr + 1real;
    lemma_exp_split(a, d, rest);
}

// ── Sums over the labels ──────────────────────────────────────────────────────

/// pexp of the truncated Gaussian is the weighted label sum over S.
proof fn lemma_pexp_gauss(x: real, b: nat, e: spec_fn(int) -> real, r: nat)
    requires gsum(x, b, 0) > 0real,
    ensures pexp(gauss(x, b), shift(e, b), (2 * b + 1) as nat, r) == gsum_e(x, b, e, r) / gsum(x, b, 0),
    decreases 2 * b + 1 - r,
{
    let s = gsum(x, b, 0);
    if r < 2 * b + 1 {
        lemma_pexp_gauss(x, b, e, r + 1);
        let g = gw(x, b, r);
        let ev = e(r as int - b as int);
        let tl = gsum_e(x, b, e, r + 1);
        assert(gauss(x, b)(r) == g / s);
        assert(shift(e, b)(r) == ev);
        assert((g / s) * ev + tl / s == (g * ev + tl) / s) by(nonlinear_arith) requires s > 0real;
    } else {
        assert(0real / s == 0real) by(nonlinear_arith) requires s > 0real;
    }
}

proof fn lemma_gsum_ones(x: real, b: nat, r: nat)
    ensures gsum(x, b, r) == gsum_e(x, b, dg_ones(), r),
    decreases 2 * b + 1 - r,
{
    if r < 2 * b + 1 { lemma_gsum_ones(x, b, r + 1); }
}

/// 0 ≤ Σ gw·ℰ ≤ Σ gw for ℰ ∈ [0, 1].
proof fn lemma_gsum_e_le(x: real, b: nat, e: spec_fn(int) -> real, r: nat)
    requires x > 0real, forall |z: int| 0real <= #[trigger] e(z) <= 1real,
    ensures 0real <= gsum_e(x, b, e, r) <= gsum(x, b, r),
    decreases 2 * b + 1 - r,
{
    if r < 2 * b + 1 {
        lemma_gsum_e_le(x, b, e, r + 1);
        lemma_gw_range(x, b);
        let g = gw(x, b, r);
        let ev = e(r as int - b as int);
        assert(0real <= g * ev <= g) by(nonlinear_arith) requires g >= 0real, 0real <= ev <= 1real;
    }
}

/// The labels in [B − j, B + j] sum to KP_ℰ(j + 1).
proof fn lemma_gsum_e_mid(x: real, b: nat, e: spec_fn(int) -> real, j: nat)
    requires x > 0real, j <= b,
    ensures
        gsum_e(x, b, e, (b - j) as nat) - gsum_e(x, b, e, b + j + 1)
            == gauss_kernel_partial(gauss_sigma2(x), e, j + 1),
    decreases j,
{
    let s2 = gauss_sigma2(x);
    if j == 0 {
        lemma_gw(x, b, 0);
        lemma_kernel(x, 0);
        assert((0nat as real) == 0real);
        assert(gauss_kernel_partial(s2, e, 1) == gauss_kernel_zero(s2, e));
        assert(b as int - b as int == 0int);
    } else {
        let j1 = (j - 1) as nat;
        lemma_gsum_e_mid(x, b, e, j1);
        lemma_gw(x, b, j);
        lemma_kernel(x, j);
        assert(((b - j) as nat) as int - b as int == -(j as int));
        assert((b + j) as int - b as int == j as int);
        assert(gsum_e(x, b, e, (b - j) as nat)
            == gw(x, b, (b - j) as nat) * e(-(j as int)) + gsum_e(x, b, e, (b - j1) as nat));
        assert(gsum_e(x, b, e, b + j1 + 1)
            == gw(x, b, b + j) * e(j as int) + gsum_e(x, b, e, b + j + 1));
        assert(gauss_kernel_partial(s2, e, j + 1)
            == gauss_kernel_partial(s2, e, j) + gauss_kernel_sym(s2, e, j));
        let g = gk(x, j);
        assert(g * e(-(j as int)) + g * e(j as int) == g * (e(j as int) + e(-(j as int)))) by(nonlinear_arith);
    }
}

/// Σ_{r ∈ [0, 2B]} gw·ℰ = KP_ℰ(B + 1).
proof fn lemma_gsum_e_kp(x: real, b: nat, e: spec_fn(int) -> real)
    requires x > 0real,
    ensures gsum_e(x, b, e, 0) == gauss_kernel_partial(gauss_sigma2(x), e, b + 1),
{
    lemma_gsum_e_mid(x, b, e, b);
    assert(gsum_e(x, b, e, 2 * b + 1) == 0real);
}

// ── The tail ──────────────────────────────────────────────────────────────────

/// KP₁(B+1+J) − KP₁(B+1) + 2·gk(B+1+J)/(1−q) ≤ 2·gk(B+1)/(1−q) = U.
proof fn lemma_kp_tail_step(x: real, b: nat, jj: nat)
    requires x > 0real,
    ensures
        gauss_kernel_partial(gauss_sigma2(x), dg_ones(), b + 1 + jj) - gauss_kernel_partial(gauss_sigma2(x), dg_ones(), b + 1)
            + 2real * gk(x, b + 1 + jj) / (1real - exp(-(((2 * b + 3) as nat) as real * x)))
            <= gauss_tail(x, b),
    decreases jj,
{
    let q = exp(-(((2 * b + 3) as nat) as real * x));
    assert(((2 * b + 3) as nat) as real * x > 0real) by(nonlinear_arith) requires x > 0real;
    axiom_exp_neg_strict(((2 * b + 3) as nat) as real * x);
    axiom_exp_neg_range(((2 * b + 3) as nat) as real * x);
    if jj > 0 {
        let j1 = (jj - 1) as nat;
        let k = b + 1 + j1;
        let s2 = gauss_sigma2(x);
        lemma_kp_tail_step(x, b, j1);
        lemma_gk_ratio(x, b, k);
        lemma_kernel(x, k);
        lemma_gk_range(x, k);
        assert(gauss_kernel_partial(s2, dg_ones(), k + 1)
            == gauss_kernel_partial(s2, dg_ones(), k) + gauss_kernel_sym(s2, dg_ones(), k));
        assert(gauss_kernel_sym(s2, dg_ones(), k) == gk(x, k) * (1real + 1real));
        let g = gk(x, k);
        let g1 = gk(x, k + 1);
        assert(2real * g + 2real * g1 / (1real - q) <= 2real * g / (1real - q)) by(nonlinear_arith)
            requires g1 <= q * g, g > 0real, 0real < q < 1real;
    }
}

/// Every symmetric partial sum of the kernel is at most S + U.
proof fn lemma_kp_tail(x: real, b: nat, m: nat)
    requires x > 0real,
    ensures
        gauss_kernel_partial(gauss_sigma2(x), dg_ones(), m)
            <= gauss_kernel_partial(gauss_sigma2(x), dg_ones(), b + 1) + gauss_tail(x, b),
    decreases b + 1 - m,
{
    let s2 = gauss_sigma2(x);
    let q = exp(-(((2 * b + 3) as nat) as real * x));
    assert(((2 * b + 3) as nat) as real * x > 0real) by(nonlinear_arith) requires x > 0real;
    axiom_exp_neg_strict(((2 * b + 3) as nat) as real * x);
    lemma_gk_range(x, b + 1);
    assert(gauss_tail(x, b) >= 0real) by(nonlinear_arith)
        requires gauss_tail(x, b) == 2real * gk(x, b + 1) / (1real - q), gk(x, b + 1) > 0real, q < 1real;
    if m >= b + 1 {
        let jj = (m - (b + 1)) as nat;
        lemma_kp_tail_step(x, b, jj);
        lemma_gk_range(x, m);
        assert(b + 1 + jj == m);
        assert(2real * gk(x, m) / (1real - q) >= 0real) by(nonlinear_arith)
            requires gk(x, m) > 0real, q < 1real;
        assert(gauss_kernel_partial(s2, dg_ones(), m) - gauss_kernel_partial(s2, dg_ones(), b + 1)
            + 2real * gk(x, m) / (1real - q) <= gauss_tail(x, b));
    } else {
        // the partial sums below B + 1 increase towards S
        lemma_kp_tail(x, b, m + 1);
        lemma_kernel(x, m);
        lemma_gk_range(x, m);
        assert(m >= 1 ==> gauss_kernel_partial(s2, dg_ones(), m + 1)
            == gauss_kernel_partial(s2, dg_ones(), m) + gauss_kernel_sym(s2, dg_ones(), m));
        if m == 0 {
            lemma_kernel(x, 0);
            lemma_gk_range(x, 0);
            assert((0nat as real) == 0real);
            assert(gauss_kernel_partial(s2, dg_ones(), 1) == gauss_kernel_zero(s2, dg_ones()));
            assert(gauss_kernel_partial(s2, dg_ones(), 0) == 0real);
            assert(gauss_kernel_zero(s2, dg_ones()) == gk(x, 0) * 1real);
        } else {
            assert(gauss_kernel_sym(s2, dg_ones(), m) == gk(x, m) * (1real + 1real));
            assert(gauss_kernel_sym(s2, dg_ones(), m) >= 0real);
        }
    }
}

// ── Truncation ────────────────────────────────────────────────────────────────

/// E_B[ℰ] ≤ E_{N_ℤ}[ℰ] + gauss_tail(x, B), σ² = 1/(2x).
pub proof fn lemma_gauss_truncate(x: real, b: nat, e: spec_fn(int) -> real, eps: real)
    requires
        x > 0real,
        forall |z: int| 0real <= #[trigger] e(z) <= 1real,
        gauss_expectation_le(gauss_sigma2(x), e, eps),
    ensures
        pexp(gauss(x, b), shift(e, b), (2 * b + 1) as nat, 0) <= eps + gauss_tail(x, b),
{
    // in CKS's form, with any (p, t); t = 1 here
    assert(gauss_sigma2(x) > 0real) by(nonlinear_arith) requires x > 0real, gauss_sigma2(x) == 1real / (2real * x);
    assert(1real / 1real == 1real);
    lemma_gauss_expectation_iff(exp(-(1real / 1real)), gauss_sigma2(x), 1real, e, eps);
    lemma_gauss_truncate_cks(x, b, exp(-(1real / 1real)), 1real, e, eps);
}

/// `lemma_gauss_truncate` with E_{N_ℤ}[ℰ] in CKS's form.
proof fn lemma_gauss_truncate_cks(x: real, b: nat, p: real, t: real, e: spec_fn(int) -> real, eps: real)
    requires
        x > 0real, t > 0real, p == exp(-(1real / t)),
        forall |z: int| 0real <= #[trigger] e(z) <= 1real,
        gauss_expectation_bounded_by(p, gauss_sigma2(x), t, e, eps),
    ensures
        pexp(gauss(x, b), shift(e, b), (2 * b + 1) as nat, 0) <= eps + gauss_tail(x, b),
{
    let s2 = gauss_sigma2(x);
    assert(s2 > 0real) by(nonlinear_arith) requires x > 0real, s2 == 1real / (2real * x);
    assert(1real / t > 0real) by(nonlinear_arith) requires t > 0real;
    axiom_exp_neg_range(1real / t);
    axiom_exp_neg_strict(1real / t);
    let cst = gauss_const(p, s2, t);
    let a = gauss_accept_prob(p, s2, t);
    lemma_gauss_const_pos(p, s2, t);
    lemma_gauss_accept_prob(p, s2, t);
    // S = KP₁(B+1) ≥ 1 and K = KP_ℰ(B+1) ∈ [0, S]
    lemma_gw_range(x, b);
    crate::optas::examples::gaussian::lemma_gsum_ge(x, b, 0);
    lemma_gsum_ones(x, b, 0);
    lemma_gsum_e_kp(x, b, dg_ones());
    lemma_gsum_e_kp(x, b, e);
    lemma_gsum_e_le(x, b, e, 0);
    let s = gsum(x, b, 0);
    let k = gsum_e(x, b, e, 0);
    let u = gauss_tail(x, b);
    lemma_kp_tail(x, b, 0);
    assert(u >= 0real) by {
        lemma_gk_range(x, b + 1);
        let q = exp(-(((2 * b + 3) as nat) as real * x));
        assert(((2 * b + 3) as nat) as real * x > 0real) by(nonlinear_arith) requires x > 0real;
        axiom_exp_neg_strict(((2 * b + 3) as nat) as real * x);
        assert(u >= 0real) by(nonlinear_arith) requires u == 2real * gk(x, b + 1) / (1real - q), gk(x, b + 1) > 0real, q < 1real;
    }
    // a ≤ const·(S + U)
    let seq = accept_mass_seq(p, s2, t);
    assert(is_bounded_above(seq, cst * (s + u))) by {
        assert forall |m: nat| #[trigger] seq_at(seq, m) <= cst * (s + u) by {
            lemma_kp_tail(x, b, m);
            let km = gauss_kernel_partial(s2, dg_ones(), m);
            assert(cst * km <= cst * (s + u)) by(nonlinear_arith) requires km <= s + u, cst > 0real;
        }
    }
    lemma_limit_le_bound(seq, a, cst * (s + u));
    // const·K/a ≤ ε
    lemma_gauss_pmf_partial_eq(p, s2, t, e, b + 1);
    assert(gauss_pmf_partial(p, s2, t, e, b + 1) <= eps);
    // K/S − const·K/a ≤ U
    lemma_pexp_gauss(x, b, e, 0);
    assert(k / s <= cst * k / a + u) by(nonlinear_arith)
        requires s >= 1real, a >= cst, cst > 0real, 0real <= k <= s, u >= 0real, a <= cst * (s + u);
}

} // verus!
