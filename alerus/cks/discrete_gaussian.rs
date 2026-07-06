//! Sample from the Discrete Gaussian N_ℤ(0, σ²)  (CKS20 §5.3), σ = numer/denom.
//!
//! Algorithm — rejection sampling against a discrete-Laplace proposal:
//! ```text
//!   t = ⌊σ⌋ + 1
//!   loop { y ← sample_discrete_laplace(t);          // Y ~ L_ℤ(0, t)
//!          if Bernoulli(exp(−(|y| − σ²/t)²/(2σ²))): return y }
//! ```
//!
//! Expectation Preservation Rule, under the discrete-Gaussian pmf
//!   gauss_pmf(x) := e^{−x²/2σ²} / Z,   Z := Σ_{y∈ℤ} e^{−y²/2σ²}:
//!
//! ```text
//!   ε ≥ Σ_{x∈ℤ} gauss_pmf(x)·ℰ(x)
//!   ───────────────────────────────────────
//!   [{ ↯(ε) }] sample_discrete_gaussian(σ) [{ v. ↯(ℰ(v)) }]
//! ```
//!
//! The proposal weight P_L[y] = (1−p)/(1+p)·e^{−|y|/t}  (p = e^{−1/t})
//! times the acceptance C(y) = e^{−bias(y)},  bias(y) := (|y| − σ²/t)²/(2σ²),  
//! factors through the Gaussian kernel:
//!   P_L[y]·C(y) = const · e^{−y²/2σ²},   const = (1−p)/(1+p)·e^{−σ²/2t²}
//! (the exponent identity |y|/t + bias(y) = y²/2σ² + σ²/2t²).  Summing over y, one
//! loop iteration accepts with probability  a = const·Z,  and conditioned on accepting,
//! returns y with probability const·e^{−y²/2σ²}/a = gauss_pmf(y) — the target pmf.
//! We never need Z in closed form: a is obtained as a limit with const ≤ a ≤ 1 (the
//! accept mass never exceeds the proposal mass ≤ 1), and each rejection amplifies the
//! thin-air slack by 1/(1−const) > 1, forcing termination (using only a ≥ const).
//!
//! Proof outline:
//!   1. Per-term factorization  P_L[y]·C(y) = const·kernel(y)
//!        lemma_gauss_pointwise → lemma_dl_accept_eq_kernel → lemma_dg_accept_term
//!   2. Split the proposal draw's DL partial sum into accept + reject parts
//!        lemma_dg_decomposition
//!   3. Acceptance probability a = const·Z exists, with const ≤ a ≤ 1
//!        lemma_dl_mass_limit, lemma_dg_accept_le_mass → lemma_gauss_accept_prob
//!   4. Credit bound for one proposal draw  (retry credit rc = ε + slack/(1−const))
//!        lemma_dg_dl_bound
//!   5. Rejection loop with slack amplification  (entry: sample_discrete_gaussian_entry)
//!        sample_discrete_gaussian
//!   6. The precondition ε ≥ Σ gauss_pmf·ℰ ⟺ the internal kernel-form bound
//!        gauss_pmf, gauss_pmf_partial, lemma_dg_series_iff

use vstd::prelude::*;

use random::{IBig, ubig_from_u64, ubig_mul, ibig_from_ubig, ibig_sub, ibig_mul, ibig_abs,
    RBig, rbig_into_parts, rbig_floor, rbig_from_parts, ibig_add, ibig_from_i64};
#[cfg(verus_keep_ghost)]
use random::{UBig};

verus! {

use crate::ec::*;
use crate::rand_primitives::thin_air;
use crate::cks::discrete_laplace::sample_discrete_laplace_fast;
use crate::cks::bernoulli_exp::sample_bernoulli_exp_rbig;
#[cfg(verus_keep_ghost)]
use crate::extern_spec::{ibig_view, ubig_view, rbig_view, ExRBig};
#[cfg(verus_keep_ghost)]
use crate::math::pow::archimedean_exp_growth;
#[cfg(verus_keep_ghost)]
use crate::math::exp::{exp, axiom_exp_add, axiom_exp_neg_range, axiom_exp_neg_strict, axiom_exp_zero};
#[cfg(verus_keep_ghost)]
use crate::math::pow::pow;
#[cfg(verus_keep_ghost)]
use crate::math::real::real_assoc_mult;
#[cfg(verus_keep_ghost)]
use crate::math::series::{
    lemma_pow_nonneg, seq_at, is_nondecreasing, is_nonincreasing,
    is_bounded_above, is_bounded_below,
    converges, converges_to, axiom_monotone_convergence,
    lemma_monotone_convergence_decreasing, lemma_monotone_limit_upper_bound,
    lemma_limit_le_bound, lemma_limit_shift, lemma_limit_scale, lemma_limit_add,
    lemma_limit_unique, lemma_limit_pointwise_eq,
    exists_close_suffix, suffix_is_close, dist, abs,
};
#[cfg(verus_keep_ghost)]
use crate::cks::discrete_laplace::{dl_partial_sum, dl_zero_summand, dl_symmetric_summand, dl_series_bounded_by};

/// The acceptance bias for a proposal value with magnitude `a = |y|`:
///   bias(a) = (a − σ²/t)² / (2σ²).
pub open spec fn gauss_bias(sigma2: real, t: real, a: real) -> real {
    (a - sigma2 / t) * (a - sigma2 / t) / (2real * sigma2)
}

/// Pure exponent identity underlying the per-term factorization:
///
///   a/t + (a − σ²/t)²/(2σ²)  =  a²/(2σ²) + σ²/(2t²),     for σ² > 0, t > 0.
///
/// (Here `a = |y|`, and `a² = y²`, so the RHS is the Gaussian kernel arg plus
/// the constant σ²/2t².)
pub proof fn lemma_gauss_pointwise_exponent(sigma2: real, t: real, a: real)
    requires sigma2 > 0real, t > 0real,
    ensures
        a / t + gauss_bias(sigma2, t, a)
            == a * a / (2real * sigma2) + sigma2 / (2real * t * t),
{
    // Expand (a − σ²/t)² = a² − 2a·σ²/t + σ⁴/t² and divide by 2σ²; the ±a/t
    // cancels and σ⁴/t²/(2σ²) = σ²/(2t²).  Pure field arithmetic given σ²,t ≠ 0.
    assert(a / t + gauss_bias(sigma2, t, a)
        == a * a / (2real * sigma2) + sigma2 / (2real * t * t)) by(nonlinear_arith)
        requires
            sigma2 > 0real, t > 0real,
            gauss_bias(sigma2, t, a)
                == (a - sigma2 / t) * (a - sigma2 / t) / (2real * sigma2);
}

/// Per-term factorization through the Gaussian kernel:
///
///   e^{−a/t} · e^{−bias(a)}  =  e^{−a²/2σ²} · e^{−σ²/2t²},     for σ² > 0, t > 0, a ≥ 0.
///
/// Multiplying by the L_ℤ(0,t) normalizer (1−p)/(1+p) turns the LHS into
/// P_L[y]·C(y) and the RHS into const·e^{−y²/2σ²}  (a = |y|, a² = y²).
pub proof fn lemma_gauss_pointwise(sigma2: real, t: real, a: real)
    requires sigma2 > 0real, t > 0real, a >= 0real,
    ensures
        exp(-(a / t)) * exp(-gauss_bias(sigma2, t, a))
            == exp(-(a * a / (2real * sigma2))) * exp(-(sigma2 / (2real * t * t))),
{
    let bias = gauss_bias(sigma2, t, a);
    let karg = a * a / (2real * sigma2);
    let cst = sigma2 / (2real * t * t);

    // All four exponent arguments are ≥ 0 (needed for axiom_exp_add).
    assert(a / t >= 0real) by(nonlinear_arith) requires a >= 0real, t > 0real;
    assert(bias >= 0real) by(nonlinear_arith)
        requires sigma2 > 0real, bias == (a - sigma2 / t) * (a - sigma2 / t) / (2real * sigma2);
    assert(karg >= 0real) by(nonlinear_arith)
        requires sigma2 > 0real, karg == a * a / (2real * sigma2), a >= 0real;
    assert(cst >= 0real) by(nonlinear_arith) requires sigma2 > 0real, t > 0real, cst == sigma2 / (2real * t * t);

    // Fold each product into a single exp via multiplicativity.
    axiom_exp_add(a / t, bias);
    axiom_exp_add(karg, cst);
    // exp(−(a/t)) · exp(−bias) = exp(−(a/t + bias))
    // exp(−karg) · exp(−cst)   = exp(−(karg + cst))

    // The two exponent sums coincide.
    lemma_gauss_pointwise_exponent(sigma2, t, a);
    assert(a / t + bias == karg + cst);
}

// ─────────────────────────────────────────────────────────────────────────────
//  Per-term credit identity (the pointwise lemma with the L_ℤ(0,t) normalizer)
// ─────────────────────────────────────────────────────────────────────────────

/// The unnormalized Gaussian kernel  e^{−x²/2σ²}.
pub open spec fn gauss_kernel(sigma2: real, x: real) -> real {
    exp(-(x * x / (2real * sigma2)))
}

/// The constant relating the (accept-weighted) discrete-Laplace proposal to the
/// Gaussian kernel:  const = (1−p)/(1+p) · e^{−σ²/2t²},  with p = e^{−1/t}.
/// (= the y=0 acceptance term; the loop's acceptance probability is const·Z.)
pub open spec fn gauss_const(p: real, sigma2: real, t: real) -> real {
    (1real - p) / (1real + p) * exp(-(sigma2 / (2real * t * t)))
}

/// Per-term credit identity (the keystone, with the normalizer folded in):
///
///   P_L[k] · C(k)  =  const · e^{−k²/2σ²},
///
/// where the proposal weight is  P_L[k] = (1−p)/(1+p)·e^{−k/t}  (p = e^{−1/t}),
/// C(k) = e^{−bias(k)} the acceptance probability, and k = |y| ≥ 0.
/// This is exactly `dl_zero_summand` / the magnitude factor of
/// `dl_symmetric_summand` from `discrete_laplace`, multiplied by C(k).
#[verifier(spinoff_prover)]
pub proof fn lemma_dl_accept_eq_kernel(p: real, sigma2: real, t: real, a: real)
    requires sigma2 > 0real, t > 0real, a >= 0real, 0real <= p,
    ensures
        ((1real - p) / (1real + p) * exp(-(a / t))) * exp(-gauss_bias(sigma2, t, a))
            == gauss_const(p, sigma2, t) * gauss_kernel(sigma2, a),
{
    let norm = (1real - p) / (1real + p);
    // pointwise:  e^{−a/t}·e^{−bias} = e^{−a²/2σ²}·e^{−σ²/2t²}
    lemma_gauss_pointwise(sigma2, t, a);
    // multiply both sides by `norm` and reassociate
    assert(((1real - p) / (1real + p) * exp(-(a / t))) * exp(-gauss_bias(sigma2, t, a))
        == gauss_const(p, sigma2, t) * gauss_kernel(sigma2, a)) by(nonlinear_arith)
        requires
            exp(-(a / t)) * exp(-gauss_bias(sigma2, t, a))
                == exp(-(a * a / (2real * sigma2))) * exp(-(sigma2 / (2real * t * t))),
            gauss_const(p, sigma2, t) == norm * exp(-(sigma2 / (2real * t * t))),
            gauss_kernel(sigma2, a) == exp(-(a * a / (2real * sigma2))),
            norm == (1real - p) / (1real + p);
}

/// The acceptance kernel is positive:  e^{−bias(a)} > 0  and  e^{−k²/2σ²} > 0.
/// (Used to show the loop's acceptance probability `a = const·Z` is ≥ the y=0
/// term `const > 0`, which drives the geometric slack growth / termination.)
pub proof fn lemma_gauss_kernel_pos(sigma2: real, t: real, a: real)
    requires sigma2 > 0real, t > 0real, a >= 0real,
    ensures
        exp(-gauss_bias(sigma2, t, a)) > 0real,
        gauss_kernel(sigma2, a) > 0real,
{
    assert(gauss_bias(sigma2, t, a) >= 0real) by(nonlinear_arith)
        requires sigma2 > 0real,
            gauss_bias(sigma2, t, a) == (a - sigma2 / t) * (a - sigma2 / t) / (2real * sigma2);
    axiom_exp_neg_range(gauss_bias(sigma2, t, a));
    assert(a * a / (2real * sigma2) >= 0real) by(nonlinear_arith)
        requires sigma2 > 0real, a >= 0real;
    axiom_exp_neg_range(a * a / (2real * sigma2));
}

/// pow(e^{−1/t}, k) = e^{−k/t}.  Bridges the discrete-Laplace proposal weight
/// `pow(p, k)` (p = e^{−1/t}) to the `e^{−k/t}` form used by the credit identity.
pub proof fn lemma_pow_p_eq_exp(t: real, k: nat)
    requires t > 0real,
    ensures pow(exp(-(1real / t)), k) == exp(-(k as real / t)),
    decreases k,
{
    if k == 0 {
        axiom_exp_zero();
        assert(pow(exp(-(1real / t)), 0nat) == 1real);
        assert((0nat as real) / t == 0real) by(nonlinear_arith) requires t > 0real;
    } else {
        lemma_pow_p_eq_exp(t, (k - 1) as nat);
        // pow(p, k) = p · pow(p, k−1) = e^{−1/t} · e^{−(k−1)/t}
        assert(pow(exp(-(1real / t)), k)
            == exp(-(1real / t)) * pow(exp(-(1real / t)), (k - 1) as nat));
        assert(1real / t >= 0real) by(nonlinear_arith) requires t > 0real;
        assert((k - 1) as real / t >= 0real) by(nonlinear_arith) requires t > 0real, k >= 1;
        axiom_exp_add(1real / t, (k - 1) as real / t);
        // 1/t + (k−1)/t == k/t
        assert(1real / t + (k - 1) as real / t == k as real / t) by(nonlinear_arith)
            requires t > 0real, k >= 1;
    }
}

// ─────────────────────────────────────────────────────────────────────────────
//  Gaussian kernel partial sums  (the accept-weighted side of the DL partial sum)
//
//  gauss_kernel_partial(σ², e, n) sums the Gaussian kernel against e over
//  magnitudes |y| < n, symmetrically:
//      n = 0 : 0
//      n = 1 : kernel(0)·e(0)
//      n > 1 : prev + kernel(k)·(e(k) + e(−k))         (k = n−1)
//  By the per-term credit identity, the "accept" part of dl_partial_sum(p, g_dl, n)
//  equals  const · gauss_kernel_partial(σ², e, n).
// ─────────────────────────────────────────────────────────────────────────────

/// e(0)-magnitude term:  kernel(0)·e(0).
pub open spec fn gauss_kernel_zero(sigma2: real, e: spec_fn(int) -> real) -> real {
    gauss_kernel(sigma2, 0real) * e(0int)
}

/// magnitude-k term (k ≥ 1):  kernel(k)·(e(k) + e(−k)).
pub open spec fn gauss_kernel_sym(sigma2: real, e: spec_fn(int) -> real, k: nat) -> real {
    gauss_kernel(sigma2, k as real) * (e(k as int) + e(-(k as int)))
}

/// Σ over magnitudes |y| < n of the Gaussian kernel against e (symmetric).
pub open spec fn gauss_kernel_partial(sigma2: real, e: spec_fn(int) -> real, n: nat) -> real
    decreases n,
{
    if n == 0 { 0real }
    else if n == 1 { gauss_kernel_zero(sigma2, e) }
    else { gauss_kernel_partial(sigma2, e, (n - 1) as nat) + gauss_kernel_sym(sigma2, e, (n - 1) as nat) }
}

/// The Gaussian partial sum is nondecreasing in n when e ≥ 0 (nonneg terms).
pub proof fn lemma_gauss_kernel_partial_nondecreasing(
    sigma2: real, t: real, e: spec_fn(int) -> real, n: nat,
)
    requires
        sigma2 > 0real, t > 0real,
        forall |x: int| (#[trigger] e(x)) >= 0real,
    ensures
        gauss_kernel_partial(sigma2, e, n) <= gauss_kernel_partial(sigma2, e, n + 1),
{
    if n == 0 {
        lemma_gauss_kernel_pos(sigma2, t, 0real);
        assert(gauss_kernel_partial(sigma2, e, 1nat) == gauss_kernel(sigma2, 0real) * e(0int));
        assert(gauss_kernel(sigma2, 0real) * e(0int) >= 0real) by(nonlinear_arith)
            requires gauss_kernel(sigma2, 0real) > 0real, e(0int) >= 0real;
    } else {
        let k = n;
        lemma_gauss_kernel_pos(sigma2, t, k as real);
        assert(gauss_kernel_partial(sigma2, e, n + 1)
            == gauss_kernel_partial(sigma2, e, n) + gauss_kernel_sym(sigma2, e, n));
        assert(gauss_kernel_sym(sigma2, e, n) >= 0real) by(nonlinear_arith)
            requires
                gauss_kernel(sigma2, k as real) > 0real,
                e(k as int) >= 0real, e(-(k as int)) >= 0real,
                gauss_kernel_sym(sigma2, e, n)
                    == gauss_kernel(sigma2, k as real) * (e(k as int) + e(-(k as int)));
    }
}

// ─────────────────────────────────────────────────────────────────────────────
//  The discrete-Laplace postcondition handed to the proposal draw, and the
//  decomposition of its DL partial sums into Gaussian-kernel + reject parts.
// ─────────────────────────────────────────────────────────────────────────────

/// Magnitude |y| of an integer, as a real.
pub open spec fn imag(y: int) -> real {
    if y >= 0 { y as real } else { (-y) as real }
}

/// Acceptance probability at proposal value y:  C(|y|) = e^{−bias(|y|)}.
pub open spec fn gauss_accept(sigma2: real, t: real, y: int) -> real {
    exp(-gauss_bias(sigma2, t, imag(y)))
}

/// Credit allocation for the proposal draw: the per-outcome credit handed to
/// `sample_discrete_laplace` as its postcondition ℰ.
///   gauss_credit_alloc(y) = C(|y|)·ℰ(y) + (1 − C(|y|))·rc
/// (accept ⇒ keep y with credit ℰ(y); reject ⇒ retry with credit rc).
pub open spec fn gauss_credit_alloc(
    sigma2: real, t: real, e: spec_fn(int) -> real, rc: real,
) -> spec_fn(int) -> real {
    |y: int| gauss_accept(sigma2, t, y) * e(y) + (1real - gauss_accept(sigma2, t, y)) * rc
}

/// The constant-1 postcondition (used to express the DL probability mass).
pub open spec fn dg_ones() -> spec_fn(int) -> real {
    |_y: int| 1real
}

/// Per-term accept identity:  pow(p,k)·(1−p)/(1+p)·C(k) = const·kernel(k),
/// with p = e^{−1/t}, k ≥ 0.  (Combines `lemma_pow_p_eq_exp` with the
/// normalizer-folded credit identity `lemma_dl_accept_eq_kernel`.)
#[verifier::spinoff_prover]
pub proof fn lemma_dg_accept_term(p: real, sigma2: real, t: real, k: nat)
    requires sigma2 > 0real, t > 0real, 0real <= p, p == exp(-(1real / t)),
    ensures
        pow(p, k) * ((1real - p) / (1real + p)) * gauss_accept(sigma2, t, k as int)
            == gauss_const(p, sigma2, t) * gauss_kernel(sigma2, k as real),
{
    // imag(k as int) = k as real, so C(k) = e^{−bias(k)}.
    assert(imag(k as int) == k as real);
    // pow(p,k) = e^{−k/t}
    lemma_pow_p_eq_exp(t, k);
    assert(pow(p, k) == exp(-(k as real / t)));
    // ((1−p)/(1+p)·e^{−k/t})·e^{−bias(k)} = const·kernel(k)
    lemma_dl_accept_eq_kernel(p, sigma2, t, k as real);
    assert(pow(p, k) * ((1real - p) / (1real + p)) * gauss_accept(sigma2, t, k as int)
        == gauss_const(p, sigma2, t) * gauss_kernel(sigma2, k as real)) by(nonlinear_arith)
        requires
            pow(p, k) == exp(-(k as real / t)),
            gauss_accept(sigma2, t, k as int) == exp(-gauss_bias(sigma2, t, k as real)),
            ((1real - p) / (1real + p) * exp(-(k as real / t))) * exp(-gauss_bias(sigma2, t, k as real))
                == gauss_const(p, sigma2, t) * gauss_kernel(sigma2, k as real);
}

/// Pure polynomial combine for the zero term (no division, abstract reals):
///   norm·(c·ev + (1−c)·rc) = m·ev + rc·(norm − m),   given m = norm·c.
#[verifier::spinoff_prover]
proof fn lemma_lin_zero(norm: real, c: real, ev: real, rc: real, m: real)
    requires m == norm * c,
    ensures norm * (c * ev + (1real - c) * rc) == m * ev + rc * (norm - m),
{
    // Each step is a small polynomial identity; the per-summand targets match the ensures
    // exactly, so the final combine is addition-congruence (no nonlinear/commutativity left).
    assert(norm * (c * ev + (1real - c) * rc) == norm * c * ev + norm * (1real - c) * rc)
        by(nonlinear_arith);
    assert(norm * c * ev == m * ev) by(nonlinear_arith) requires m == norm * c;
    assert(norm * (1real - c) * rc == rc * (norm - m)) by(nonlinear_arith) requires m == norm * c;
}

/// Pure polynomial combine for the symmetric term (no division, abstract reals):
///   s·(c·(ek+emk) + 2(1−c)·rc) = m·(ek+emk) + rc·(2s − 2m),   given m = s·c.
#[verifier::spinoff_prover]
proof fn lemma_lin_sym(s: real, c: real, ek: real, emk: real, rc: real, m: real)
    requires m == s * c,
    ensures
        s * (c * (ek + emk) + 2real * (1real - c) * rc)
            == m * (ek + emk) + rc * (2real * s - 2real * m),
{
    assert(s * (c * (ek + emk) + 2real * (1real - c) * rc)
        == s * c * (ek + emk) + 2real * s * (1real - c) * rc) by(nonlinear_arith);
    assert(s * c * (ek + emk) == m * (ek + emk)) by(nonlinear_arith) requires m == s * c;
    assert(2real * s * (1real - c) * rc == rc * (2real * s - 2real * m))
        by(nonlinear_arith) requires m == s * c;
}

/// (a·b)/c = a·(b/c)  — regroup the discrete-Laplace coefficient
/// pow(p,k)·(1−p)/(1+p) into pow(p,k)·((1−p)/(1+p)).
#[verifier::nonlinear]
proof fn lemma_mul_div_regroup(a: real, b: real, c: real)
    requires c != 0real,
    ensures a * b / c == a * (b / c),
{}

/// Pure abstract-real linear combine for the decomposition induction step
/// (no closures / no division — keeps the SMT query small and fast).
proof fn lemma_lin_combine(
    cst: real, rc: real,
    pg_k: real, p1_k: real, ke_k: real, k1_k: real,
    sg_k: real, s1_k: real, kse_k: real, ks1_k: real,
    pg_n: real, p1_n: real, ke_n: real, k1_n: real,
)
    requires
        pg_k == cst * ke_k + rc * (p1_k - cst * k1_k),
        sg_k == cst * kse_k + rc * (s1_k - cst * ks1_k),
        pg_n == pg_k + sg_k,
        p1_n == p1_k + s1_k,
        ke_n == ke_k + kse_k,
        k1_n == k1_k + ks1_k,
    ensures
        pg_n == cst * ke_n + rc * (p1_n - cst * k1_n),
{
    // Factor the triple product rc·cst into a single atom `rck`, then every
    // step below is a 2–3 variable distribution; the final combine is linear.
    let rck = rc * cst;
    assert(cst * ke_n == cst * ke_k + cst * kse_k) by(nonlinear_arith) requires ke_n == ke_k + kse_k;
    assert(rc * p1_n == rc * p1_k + rc * s1_k) by(nonlinear_arith) requires p1_n == p1_k + s1_k;
    assert(rck * k1_n == rck * k1_k + rck * ks1_k) by(nonlinear_arith)
        requires k1_n == k1_k + ks1_k;
    assert(rc * (p1_k - cst * k1_k) == rc * p1_k - rck * k1_k) by(nonlinear_arith) requires rck == rc * cst;
    assert(rc * (s1_k - cst * ks1_k) == rc * s1_k - rck * ks1_k) by(nonlinear_arith) requires rck == rc * cst;
    assert(rc * (p1_n - cst * k1_n) == rc * p1_n - rck * k1_n) by(nonlinear_arith) requires rck == rc * cst;
    // Linear: both sides equal  cst·ke_k + cst·kse_k + rc·p1_k + rc·s1_k − rck·k1_k − rck·ks1_k.
}

/// Zero-magnitude term decomposition:
///   dl_zero_summand(p, g_dl) = const·kernel(0)·ℰ(0) + rc·(dl_zero_summand(p,1) − const·kernel(0)).
#[verifier::spinoff_prover]
pub proof fn lemma_dg_zero_term(
    p: real, sigma2: real, t: real, e: spec_fn(int) -> real, rc: real,
)
    requires sigma2 > 0real, t > 0real, 0real <= p, p == exp(-(1real / t)),
    ensures ({
        let cst = gauss_const(p, sigma2, t);
        dl_zero_summand(p, gauss_credit_alloc(sigma2, t, e, rc))
            == cst * gauss_kernel_zero(sigma2, e)
             + rc * (dl_zero_summand(p, dg_ones()) - cst * gauss_kernel_zero(sigma2, dg_ones()))
    }),
{
    let cst = gauss_const(p, sigma2, t);
    let g = gauss_credit_alloc(sigma2, t, e, rc);
    let c0 = gauss_accept(sigma2, t, 0int);
    let norm = (1real - p) / (1real + p);
    let ker0 = gauss_kernel(sigma2, 0real);
    let e0 = e(0int);
    // m := norm·c0 = const·kernel(0)  (from the accept identity at k = 0, pow(p,0)=1).
    lemma_dg_accept_term(p, sigma2, t, 0nat);
    assert(pow(p, 0nat) == 1real);
    let ghost m = norm * c0;
    assert(m == cst * ker0) by(nonlinear_arith)
        requires pow(p, 0nat) * norm * c0 == cst * ker0, pow(p, 0nat) == 1real, m == norm * c0;
    // Definitional unfoldings (no nonlinear reasoning).
    assert(g(0int) == c0 * e0 + (1real - c0) * rc);
    assert(dl_zero_summand(p, g) == norm * g(0int));
    assert(dl_zero_summand(p, dg_ones()) == norm);
    assert(gauss_kernel_zero(sigma2, e) == ker0 * e0);
    assert(gauss_kernel_zero(sigma2, dg_ones()) == ker0);
    // Division-free polynomial combine.
    lemma_lin_zero(norm, c0, e0, rc, m);
    // LHS == m·e0 + rc·(norm − m); RHS likewise (cst·ker0 = m).
    assert(dl_zero_summand(p, g) == m * e0 + rc * (norm - m));
    assert(cst * gauss_kernel_zero(sigma2, e) == m * e0) by(nonlinear_arith)
        requires gauss_kernel_zero(sigma2, e) == ker0 * e0, cst * ker0 == m;
    assert(cst * gauss_kernel_zero(sigma2, dg_ones()) == m) by(nonlinear_arith)
        requires gauss_kernel_zero(sigma2, dg_ones()) == ker0, cst * ker0 == m;
}

/// Symmetric (magnitude-k, k ≥ 1) term decomposition:
///   dl_symmetric_summand(p, g_dl, k)
///     = const·kernel_sym(ℰ,k) + rc·(dl_symmetric_summand(p,1,k) − const·kernel_sym(1,k)).
#[verifier::spinoff_prover]
pub proof fn lemma_dg_sym_term(
    p: real, sigma2: real, t: real, e: spec_fn(int) -> real, rc: real, k: nat,
)
    requires sigma2 > 0real, t > 0real, 0real <= p, p == exp(-(1real / t)),
    ensures ({
        let cst = gauss_const(p, sigma2, t);
        dl_symmetric_summand(p, gauss_credit_alloc(sigma2, t, e, rc), k)
            == cst * gauss_kernel_sym(sigma2, e, k)
             + rc * (dl_symmetric_summand(p, dg_ones(), k)
                     - cst * gauss_kernel_sym(sigma2, dg_ones(), k))
    }),
{
    let cst = gauss_const(p, sigma2, t);
    let g = gauss_credit_alloc(sigma2, t, e, rc);
    let one = dg_ones();
    let ck = gauss_accept(sigma2, t, k as int);
    let norm = (1real - p) / (1real + p);
    let ker = gauss_kernel(sigma2, k as real);
    let pk = pow(p, k);
    let ek = e(k as int);
    let emk = e(-(k as int));
    // s := the dl_symmetric coefficient pow(p,k)·(1−p)/(1+p)  (left-assoc, as in
    //      dl_symmetric_summand);  m := s·ck = const·kernel(k)  (accept identity).
    let ghost s = pk * (1real - p) / (1real + p);
    assert(1real + p != 0real) by(nonlinear_arith) requires 0real <= p;
    lemma_mul_div_regroup(pk, 1real - p, 1real + p);   // s == pk·norm
    lemma_dg_accept_term(p, sigma2, t, k);
    // C(−k) = C(k) since imag(−k) = imag(k) = k.
    assert(gauss_accept(sigma2, t, -(k as int)) == ck) by {
        assert(imag(-(k as int)) == k as real);
        assert(imag(k as int) == k as real);
    }
    let ghost m = s * ck;
    assert(m == cst * ker) by(nonlinear_arith)
        requires pk * (norm) * ck == cst * ker, s == pk * norm, m == s * ck;
    // Definitional unfoldings.
    assert(g(k as int) == ck * ek + (1real - ck) * rc);
    assert(g(-(k as int)) == ck * emk + (1real - ck) * rc);
    assert(dl_symmetric_summand(p, g, k) == s * (g(k as int) + g(-(k as int))));
    assert(dl_symmetric_summand(p, one, k) == s * 2real);
    assert(gauss_kernel_sym(sigma2, e, k) == ker * (ek + emk));
    assert(gauss_kernel_sym(sigma2, one, k) == ker * 2real);
    // dl_sym(g) = s·(ck·(ek+emk) + 2(1−ck)·rc)  — fold the two arms.
    assert(dl_symmetric_summand(p, g, k) == s * (ck * (ek + emk) + 2real * (1real - ck) * rc))
        by(nonlinear_arith)
        requires
            dl_symmetric_summand(p, g, k) == s * (g(k as int) + g(-(k as int))),
            g(k as int) == ck * ek + (1real - ck) * rc,
            g(-(k as int)) == ck * emk + (1real - ck) * rc;
    // Division-free polynomial combine.
    lemma_lin_sym(s, ck, ek, emk, rc, m);
    assert(dl_symmetric_summand(p, g, k) == m * (ek + emk) + rc * (2real * s - 2real * m));
    assert(cst * gauss_kernel_sym(sigma2, e, k) == m * (ek + emk)) by(nonlinear_arith)
        requires gauss_kernel_sym(sigma2, e, k) == ker * (ek + emk), cst * ker == m;
    // kernel_sym(1,k) = ker·2, so const·kernel_sym(1,k) = 2m.
    assert(cst * gauss_kernel_sym(sigma2, one, k) == 2real * m) by(nonlinear_arith)
        requires gauss_kernel_sym(sigma2, one, k) == ker * 2real, cst * ker == m;
    assert(dl_symmetric_summand(p, one, k) == 2real * s);
}

/// Decomposition of the DL partial sum of `g_dl` into the Gaussian-kernel
/// "accept" part and the reject part (light induction over the per-term lemmas):
///
///   dl_partial_sum(p, g_dl, n)
///     = const · gauss_kernel_partial(σ², ℰ, n)
///       + rc · ( dl_partial_sum(p, 1, n) − const · gauss_kernel_partial(σ², 1, n) ).
///
/// (The bracket is the partial DL probability mass not yet "spent" on accepts.)
#[verifier::spinoff_prover]
pub proof fn lemma_dg_decomposition(
    p: real, sigma2: real, t: real, e: spec_fn(int) -> real, rc: real, n: nat,
)
    requires sigma2 > 0real, t > 0real, 0real <= p, p == exp(-(1real / t)),
    ensures ({
        let cst = gauss_const(p, sigma2, t);
        dl_partial_sum(p, gauss_credit_alloc(sigma2, t, e, rc), n)
            == cst * gauss_kernel_partial(sigma2, e, n)
             + rc * (dl_partial_sum(p, dg_ones(), n)
                     - cst * gauss_kernel_partial(sigma2, dg_ones(), n))
    }),
    decreases n,
{
    let cst = gauss_const(p, sigma2, t);
    let g = gauss_credit_alloc(sigma2, t, e, rc);
    let one = dg_ones();
    if n == 0 {
    } else if n == 1 {
        lemma_dg_zero_term(p, sigma2, t, e, rc);
        // dl_partial_sum(_,1) = dl_zero_summand; gauss_kernel_partial(_,1) = gauss_kernel_zero.
        assert(dl_partial_sum(p, g, 1nat) == dl_zero_summand(p, g));
        assert(dl_partial_sum(p, one, 1nat) == dl_zero_summand(p, one));
        assert(gauss_kernel_partial(sigma2, e, 1nat) == gauss_kernel_zero(sigma2, e));
        assert(gauss_kernel_partial(sigma2, one, 1nat) == gauss_kernel_zero(sigma2, one));
    } else {
        let k = (n - 1) as nat;
        lemma_dg_decomposition(p, sigma2, t, e, rc, k);
        lemma_dg_sym_term(p, sigma2, t, e, rc, k);
        // Bind every spec-fn value to a plain real so the combine is atomic/linear.
        let ghost pg_k = dl_partial_sum(p, g, k);
        let ghost p1_k = dl_partial_sum(p, one, k);
        let ghost ke_k = gauss_kernel_partial(sigma2, e, k);
        let ghost k1_k = gauss_kernel_partial(sigma2, one, k);
        let ghost sg_k = dl_symmetric_summand(p, g, k);
        let ghost s1_k = dl_symmetric_summand(p, one, k);
        let ghost kse_k = gauss_kernel_sym(sigma2, e, k);
        let ghost ks1_k = gauss_kernel_sym(sigma2, one, k);
        // Definitional recursion steps (n = k+1), bound to plain reals.
        let ghost pg_n = dl_partial_sum(p, g, n);
        let ghost p1_n = dl_partial_sum(p, one, n);
        let ghost ke_n = gauss_kernel_partial(sigma2, e, n);
        let ghost k1_n = gauss_kernel_partial(sigma2, one, n);
        assert(pg_n == pg_k + sg_k);
        assert(p1_n == p1_k + s1_k);
        assert(ke_n == ke_k + kse_k);
        assert(k1_n == k1_k + ks1_k);
        // IH and per-term identity, restated over the bound reals.
        assert(pg_k == cst * ke_k + rc * (p1_k - cst * k1_k));
        assert(sg_k == cst * kse_k + rc * (s1_k - cst * ks1_k));
        // Pure abstract-real linear combine.
        lemma_lin_combine(cst, rc, pg_k, p1_k, ke_k, k1_k, sg_k, s1_k, kse_k, ks1_k,
            pg_n, p1_n, ke_n, k1_n);
    }
}

// ─────────────────────────────────────────────────────────────────────────────
//  lim_n pⁿ = 0  for 0 ≤ p < 1.
// ─────────────────────────────────────────────────────────────────────────────

/// The geometric sequence  n ↦ pⁿ.
pub open spec fn pow_seq(p: real) -> spec_fn(nat) -> real {
    |n: nat| pow(p, n)
}

/// L = p·L  with p ≠ 1  ⟹  L = 0.
#[verifier::nonlinear]
proof fn lemma_fixed_point_zero(p: real, l: real)
    requires l == p * l, p != 1real,
    ensures l == 0real,
{}

/// lim_n pⁿ = 0  for 0 ≤ p < 1.
#[verifier::spinoff_prover]
pub proof fn lemma_pow_limit_zero(p: real)
    requires 0real <= p < 1real,
    ensures converges_to(pow_seq(p), 0real),
{
    let s = pow_seq(p);
    // s is nonincreasing: pⁿ⁺¹ = p·pⁿ ≤ pⁿ  (0 ≤ p ≤ 1, pⁿ ≥ 0).
    assert(is_nonincreasing(s)) by {
        assert forall |n: nat| #[trigger] seq_at(s, n) >= seq_at(s, n + 1) by {
            lemma_pow_nonneg(p, n);
            assert(pow(p, n + 1) == p * pow(p, n));
            assert(seq_at(s, n) >= seq_at(s, n + 1)) by(nonlinear_arith)
                requires seq_at(s, n) == pow(p, n), seq_at(s, n + 1) == p * pow(p, n),
                    pow(p, n) >= 0real, 0real <= p < 1real;
        }
    }
    // bounded below by 0.
    assert(is_bounded_below(s, 0real)) by {
        assert forall |n: nat| #[trigger] seq_at(s, n) >= 0real by { lemma_pow_nonneg(p, n); }
    }
    lemma_monotone_convergence_decreasing(s, 0real);
    let l = choose |l: real| converges_to(s, l);
    assert(converges_to(s, l));
    // shifted sequence pⁿ⁺¹ → l  and  = p·pⁿ → p·l;  uniqueness ⇒ l = p·l ⇒ l = 0.
    lemma_limit_shift(s, l);
    lemma_limit_scale(s, l, p);
    let shifted = |n: nat| seq_at(s, n + 1);
    let scaled = |n: nat| p * seq_at(s, n);
    assert forall |n: nat| seq_at(shifted, n) == seq_at(scaled, n) by {
        assert(pow(p, n + 1) == p * pow(p, n));
    }
    lemma_limit_pointwise_eq(shifted, scaled, l);   // scaled → l
    lemma_limit_unique(scaled, l, p * l);            // scaled → p·l too
    assert(l == p * l);
    lemma_fixed_point_zero(p, l);
    assert(l == 0real);
}

// ─────────────────────────────────────────────────────────────────────────────
//  DL proposal mass bound:  Σ_{|y|<n} P_L[y] ≤ 1   (the proposal is a sub-distribution
//  on every finite truncation).  Closed form (n ≥ 1):  (1+p)·DM(n) = (1+p) − 2pⁿ.
// ─────────────────────────────────────────────────────────────────────────────

/// c·(a/c) = a  for c ≠ 0  (cancellation; division-free goal once applied).
#[verifier::nonlinear]
proof fn lemma_cancel(a: real, c: real)
    requires c != 0real,
    ensures c * (a / c) == a,
{}

/// Division-free closed form of the DL probability mass (n ≥ 1):
///   (1+p) · dl_partial_sum(p, 1, n)  =  (1+p) − 2·pⁿ.
#[verifier::spinoff_prover]
proof fn lemma_dl_mass_closed(p: real, n: nat)
    requires 0real <= p < 1real, n >= 1,
    ensures
        (1real + p) * dl_partial_sum(p, dg_ones(), n) == (1real + p) - 2real * pow(p, n),
    decreases n,
{
    let one = dg_ones();
    let norm = (1real - p) / (1real + p);
    assert(1real + p != 0real) by(nonlinear_arith) requires 0real <= p;
    if n == 1 {
        // DM(1) = (1−p)/(1+p);  (1+p)·DM(1) = 1−p = (1+p) − 2p.
        assert(dl_partial_sum(p, one, 1nat) == norm);
        lemma_cancel(1real - p, 1real + p);   // (1+p)·((1−p)/(1+p)) = 1−p
        assert(pow(p, 1nat) == p * pow(p, 0nat));
        assert(pow(p, 0nat) == 1real);
        assert((1real + p) * dl_partial_sum(p, one, 1nat) == (1real + p) - 2real * pow(p, 1nat))
            by(nonlinear_arith)
            requires
                (1real + p) * norm == 1real - p,
                dl_partial_sum(p, one, 1nat) == norm,
                pow(p, 1nat) == p;
    } else {
        let k = (n - 1) as nat;
        lemma_dl_mass_closed(p, k);
        // sym term: dl_symmetric_summand(p,1,k) = pow(p,k)·(1−p)/(1+p)·2
        let pk = pow(p, k);
        let ghost coef = pk * (1real - p) / (1real + p);
        assert(dl_symmetric_summand(p, one, k) == coef * 2real);
        // (1+p)·coef = pk·(1−p)·... regroup: coef = (pk·(1−p))/(1+p)
        lemma_cancel(pk * (1real - p), 1real + p);  // (1+p)·((pk(1−p))/(1+p)) = pk(1−p)
        assert((1real + p) * coef == pk * (1real - p));
        assert(dl_partial_sum(p, one, n) == dl_partial_sum(p, one, k) + dl_symmetric_summand(p, one, k));
        assert(pow(p, n) == p * pow(p, k));
        assert((1real + p) * dl_partial_sum(p, one, n) == (1real + p) - 2real * pow(p, n))
            by(nonlinear_arith)
            requires
                (1real + p) * dl_partial_sum(p, one, k) == (1real + p) - 2real * pk,
                dl_partial_sum(p, one, n) == dl_partial_sum(p, one, k) + coef * 2real,
                (1real + p) * coef == pk * (1real - p),
                pow(p, n) == p * pk;
    }
}

/// DL probability mass is ≤ 1 on every truncation.
#[verifier::spinoff_prover]
pub proof fn lemma_dl_mass_le_one(p: real, n: nat)
    requires 0real <= p < 1real,
    ensures dl_partial_sum(p, dg_ones(), n) <= 1real,
{
    if n == 0 {
    } else {
        lemma_dl_mass_closed(p, n);
        lemma_pow_nonneg(p, n);
        assert(1real + p > 0real) by(nonlinear_arith) requires 0real <= p;
        // (1+p)·DM(n) = (1+p) − 2pⁿ ≤ 1+p, and 1+p > 0 ⇒ DM(n) ≤ 1.
        assert(dl_partial_sum(p, dg_ones(), n) <= 1real) by(nonlinear_arith)
            requires
                (1real + p) * dl_partial_sum(p, dg_ones(), n) == (1real + p) - 2real * pow(p, n),
                pow(p, n) >= 0real, 1real + p > 0real;
    }
}

/// lim_n DM(n) = 1:  the DL proposal mass converges to 1.
/// Direct ε-N proof: for n ≥ 1, (1+p)·|DM(n) − 1| = 2pⁿ → 0.
#[verifier::spinoff_prover]
pub proof fn lemma_dl_mass_limit(p: real)
    requires 0real <= p < 1real,
    ensures converges_to(|n: nat| dl_partial_sum(p, dg_ones(), n), 1real),
{
    let dm = |n: nat| dl_partial_sum(p, dg_ones(), n);
    lemma_pow_limit_zero(p);
    assert(1real + p > 0real) by(nonlinear_arith) requires 0real <= p;
    assert forall |eps: real| eps > 0real
        implies #[trigger] exists_close_suffix(dm, 1real, eps) by {
        let delta = eps * (1real + p) / 2real;
        assert(delta > 0real) by(nonlinear_arith) requires eps > 0real, 1real + p > 0real,
            delta == eps * (1real + p) / 2real;
        assert(exists_close_suffix(pow_seq(p), 0real, delta));
        let s0 = choose |s: nat| suffix_is_close(pow_seq(p), 0real, delta, s);
        let start: nat = if s0 >= 1 { s0 } else { 1nat };
        assert(suffix_is_close(dm, 1real, eps, start)) by {
            assert forall |n: nat| n >= start implies dist(#[trigger] seq_at(dm, n), 1real) < eps by {
                lemma_dl_mass_closed(p, n);   // (1+p)·DM(n) = (1+p) − 2pⁿ  (n ≥ 1)
                lemma_pow_nonneg(p, n);
                // pⁿ < delta  (n ≥ s0)
                assert(dist(seq_at(pow_seq(p), n), 0real) < delta);
                assert(seq_at(pow_seq(p), n) == pow(p, n));
                assert(dist(pow(p, n), 0real) == pow(p, n)) by(nonlinear_arith)
                    requires pow(p, n) >= 0real,
                        dist(pow(p, n), 0real) == abs(pow(p, n) - 0real),
                        abs(pow(p, n) - 0real) == (if pow(p, n) - 0real >= 0real { pow(p, n) - 0real } else { -(pow(p, n) - 0real) });
                // 2pⁿ < eps·(1+p), and (1+p)·|DM(n)−1| = 2pⁿ, 1+p > 0 ⇒ |DM(n)−1| < eps
                assert(dist(seq_at(dm, n), 1real) < eps) by(nonlinear_arith)
                    requires
                        (1real + p) * dl_partial_sum(p, dg_ones(), n) == (1real + p) - 2real * pow(p, n),
                        seq_at(dm, n) == dl_partial_sum(p, dg_ones(), n),
                        pow(p, n) < delta, delta == eps * (1real + p) / 2real,
                        1real + p > 0real, pow(p, n) >= 0real,
                        dist(seq_at(dm, n), 1real) == abs(seq_at(dm, n) - 1real),
                        abs(seq_at(dm, n) - 1real) == (if seq_at(dm, n) - 1real >= 0real { seq_at(dm, n) - 1real } else { -(seq_at(dm, n) - 1real) });
            }
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
//  Acceptance mass ≤ proposal mass:  const·gauss_kernel_partial(σ², 1, n) ≤ DM(n).
//  Since C(k) ≤ 1 termwise, the accept mass never exceeds the proposal mass;
//  combined with DM(n) ≤ 1 this bounds the accept mass by 1 (⇒ a := lim exists).
// ─────────────────────────────────────────────────────────────────────────────

/// m = s·c, c ≤ 1, s ≥ 0  ⟹  m ≤ s.
#[verifier::nonlinear]
proof fn lemma_accept_le(s: real, c: real, m: real)
    requires m == s * c, c <= 1real, s >= 0real,
    ensures m <= s,
{}

/// Per-magnitude:  const·kernel(k) ≤ pow(p,k)·(1−p)/(1+p)  ( = P_L[k] ).
#[verifier::spinoff_prover]
proof fn lemma_dg_kernel_le_coef(p: real, sigma2: real, t: real, k: nat)
    requires sigma2 > 0real, t > 0real, 0real <= p < 1real, p == exp(-(1real / t)),
    ensures
        gauss_const(p, sigma2, t) * gauss_kernel(sigma2, k as real)
            <= pow(p, k) * (1real - p) / (1real + p),
{
    let norm = (1real - p) / (1real + p);
    let pk = pow(p, k);
    let coef = pk * (1real - p) / (1real + p);
    let ck = gauss_accept(sigma2, t, k as int);
    assert(1real + p != 0real) by(nonlinear_arith) requires 0real <= p;
    lemma_mul_div_regroup(pk, 1real - p, 1real + p);   // coef == pk·norm
    lemma_dg_accept_term(p, sigma2, t, k);             // pk·norm·ck == const·kernel(k)
    assert(imag(k as int) == k as real);
    // ck = e^{−bias} ≤ 1
    assert(ck <= 1real) by {
        assert(gauss_bias(sigma2, t, k as real) >= 0real) by(nonlinear_arith)
            requires sigma2 > 0real,
                gauss_bias(sigma2, t, k as real)
                    == (k as real - sigma2 / t) * (k as real - sigma2 / t) / (2real * sigma2);
        axiom_exp_neg_range(gauss_bias(sigma2, t, k as real));
    }
    // coef ≥ 0  (norm = (1−p)/(1+p) ≥ 0 since 1−p ≥ 0, 1+p > 0)
    lemma_pow_nonneg(p, k);
    assert(norm >= 0real) by(nonlinear_arith)
        requires norm == (1real - p) / (1real + p), 0real <= p < 1real;
    assert(coef >= 0real) by(nonlinear_arith)
        requires coef == pk * norm, pk >= 0real, norm >= 0real;
    let ghost m = coef * ck;
    assert(m == gauss_const(p, sigma2, t) * gauss_kernel(sigma2, k as real)) by(nonlinear_arith)
        requires pk * norm * ck == gauss_const(p, sigma2, t) * gauss_kernel(sigma2, k as real),
            coef == pk * norm, m == coef * ck;
    lemma_accept_le(coef, ck, m);
}

/// const·gauss_kernel_partial(σ², 1, n) ≤ dl_partial_sum(p, 1, n)  for all n.
#[verifier::spinoff_prover]
pub proof fn lemma_dg_accept_le_mass(p: real, sigma2: real, t: real, n: nat)
    requires sigma2 > 0real, t > 0real, 0real <= p < 1real, p == exp(-(1real / t)),
    ensures
        gauss_const(p, sigma2, t) * gauss_kernel_partial(sigma2, dg_ones(), n)
            <= dl_partial_sum(p, dg_ones(), n),
    decreases n,
{
    let cst = gauss_const(p, sigma2, t);
    let one = dg_ones();
    if n == 0 {
    } else if n == 1 {
        lemma_dg_kernel_le_coef(p, sigma2, t, 0nat);
        assert(pow(p, 0nat) == 1real);
        // const·kernel(0)·1 ≤ (1−p)/(1+p) = dl_zero_summand(p,1)
        assert(gauss_kernel_partial(sigma2, one, 1nat) == gauss_kernel(sigma2, 0real) * 1real);
        assert(dl_partial_sum(p, one, 1nat) == (1real - p) / (1real + p));
        assert(cst * gauss_kernel_partial(sigma2, one, 1nat) <= dl_partial_sum(p, one, 1nat))
            by(nonlinear_arith)
            requires
                cst * gauss_kernel(sigma2, 0real) <= pow(p, 0nat) * (1real - p) / (1real + p),
                pow(p, 0nat) == 1real,
                gauss_kernel_partial(sigma2, one, 1nat) == gauss_kernel(sigma2, 0real),
                dl_partial_sum(p, one, 1nat) == (1real - p) / (1real + p);
    } else {
        let k = (n - 1) as nat;
        lemma_dg_accept_le_mass(p, sigma2, t, k);
        lemma_dg_kernel_le_coef(p, sigma2, t, k);
        let ghost akm_k = cst * gauss_kernel_partial(sigma2, one, k);
        let ghost dm_k = dl_partial_sum(p, one, k);
        // sym terms: const·kernel_sym(1,k)=const·kernel(k)·2;  dl_sym(1,k)=coef·2.
        assert(gauss_kernel_sym(sigma2, one, k) == gauss_kernel(sigma2, k as real) * 2real);
        assert(dl_symmetric_summand(p, one, k) == pow(p, k) * (1real - p) / (1real + p) * 2real);
        assert(gauss_kernel_partial(sigma2, one, n) == gauss_kernel_partial(sigma2, one, k) + gauss_kernel_sym(sigma2, one, k));
        assert(dl_partial_sum(p, one, n) == dm_k + dl_symmetric_summand(p, one, k));
        assert(cst * gauss_kernel_partial(sigma2, one, n) <= dl_partial_sum(p, one, n))
            by(nonlinear_arith)
            requires
                akm_k <= dm_k,
                cst * gauss_kernel(sigma2, k as real) <= pow(p, k) * (1real - p) / (1real + p),
                gauss_kernel_partial(sigma2, one, n)
                    == gauss_kernel_partial(sigma2, one, k) + gauss_kernel(sigma2, k as real) * 2real,
                akm_k == cst * gauss_kernel_partial(sigma2, one, k),
                dl_partial_sum(p, one, n) == dm_k + pow(p, k) * (1real - p) / (1real + p) * 2real;
    }
}

// ─────────────────────────────────────────────────────────────────────────────
//  Acceptance probability  a := lim_n const·gauss_kernel_partial(σ², 1, n)  (= const·Z).
//  The accept-mass sequence is nondecreasing and bounded above by 1, so it
//  converges; the limit `a` satisfies  const ≤ a ≤ 1  (so 1 − a ∈ [0, 1−const)).
// ─────────────────────────────────────────────────────────────────────────────

/// const > 0  (= (1−p)/(1+p)·e^{−σ²/2t²}, both factors positive for 0 ≤ p < 1).
pub proof fn lemma_gauss_const_pos(p: real, sigma2: real, t: real)
    requires sigma2 > 0real, t > 0real, 0real <= p < 1real,
    ensures gauss_const(p, sigma2, t) > 0real,
{
    assert(sigma2 / (2real * t * t) >= 0real) by(nonlinear_arith) requires sigma2 > 0real, t > 0real;
    axiom_exp_neg_range(sigma2 / (2real * t * t));
    assert(gauss_const(p, sigma2, t) > 0real) by(nonlinear_arith)
        requires
            gauss_const(p, sigma2, t) == (1real - p) / (1real + p) * exp(-(sigma2 / (2real * t * t))),
            exp(-(sigma2 / (2real * t * t))) > 0real, 0real <= p < 1real;
}

/// const < 1  for 0 < p < 1:  (1−p)/(1+p) < 1 and e^{−σ²/2t²} ≤ 1.
pub proof fn lemma_gauss_const_lt_one(p: real, sigma2: real, t: real)
    requires sigma2 > 0real, t > 0real, 0real < p < 1real,
    ensures gauss_const(p, sigma2, t) < 1real,
{
    assert(sigma2 / (2real * t * t) >= 0real) by(nonlinear_arith) requires sigma2 > 0real, t > 0real;
    axiom_exp_neg_range(sigma2 / (2real * t * t));
    // (1−p)/(1+p) < 1  (p > 0),  factor ∈ (0,1]  ⇒  product < 1.
    assert((1real - p) / (1real + p) < 1real) by(nonlinear_arith) requires 0real < p < 1real;
    assert((1real - p) / (1real + p) > 0real) by(nonlinear_arith) requires 0real < p < 1real;
    assert(gauss_const(p, sigma2, t) < 1real) by(nonlinear_arith)
        requires
            gauss_const(p, sigma2, t) == (1real - p) / (1real + p) * exp(-(sigma2 / (2real * t * t))),
            (1real - p) / (1real + p) < 1real, (1real - p) / (1real + p) > 0real,
            0real < exp(-(sigma2 / (2real * t * t))) <= 1real;
}

/// The accept-mass sequence  m ↦ const·gauss_kernel_partial(σ², 1, m).
pub open spec fn accept_mass_seq(p: real, sigma2: real, t: real) -> spec_fn(nat) -> real {
    |m: nat| gauss_const(p, sigma2, t) * gauss_kernel_partial(sigma2, dg_ones(), m)
}

/// Acceptance probability  a = lim of the accept-mass sequence.
pub open spec fn gauss_accept_prob(p: real, sigma2: real, t: real) -> real {
    choose |l: real| converges_to(accept_mass_seq(p, sigma2, t), l)
}

/// The accept-mass sequence converges, and its limit a := gauss_accept_prob
/// satisfies  const ≤ a ≤ 1.
#[verifier::spinoff_prover]
pub proof fn lemma_gauss_accept_prob(p: real, sigma2: real, t: real)
    requires sigma2 > 0real, t > 0real, 0real <= p < 1real, p == exp(-(1real / t)),
    ensures
        converges_to(accept_mass_seq(p, sigma2, t), gauss_accept_prob(p, sigma2, t)),
        gauss_const(p, sigma2, t) <= gauss_accept_prob(p, sigma2, t),
        gauss_accept_prob(p, sigma2, t) <= 1real,
{
    let cst = gauss_const(p, sigma2, t);
    let seq = accept_mass_seq(p, sigma2, t);
    lemma_gauss_const_pos(p, sigma2, t);
    // nondecreasing: const > 0 and gauss_kernel_partial(1, ·) nondecreasing.
    assert(is_nondecreasing(seq)) by {
        assert forall |m: nat| #[trigger] seq_at(seq, m) <= seq_at(seq, m + 1) by {
            lemma_gauss_kernel_partial_nondecreasing(sigma2, t, dg_ones(), m);
            assert(seq_at(seq, m) == cst * gauss_kernel_partial(sigma2, dg_ones(), m));
            assert(seq_at(seq, m) <= seq_at(seq, m + 1)) by(nonlinear_arith)
                requires
                    seq_at(seq, m) == cst * gauss_kernel_partial(sigma2, dg_ones(), m),
                    seq_at(seq, m + 1) == cst * gauss_kernel_partial(sigma2, dg_ones(), m + 1),
                    gauss_kernel_partial(sigma2, dg_ones(), m) <= gauss_kernel_partial(sigma2, dg_ones(), m + 1),
                    cst > 0real;
        }
    }
    // bounded above by 1: const·KM(m) ≤ DM(m) ≤ 1.
    assert(is_bounded_above(seq, 1real)) by {
        assert forall |m: nat| #[trigger] seq_at(seq, m) <= 1real by {
            lemma_dg_accept_le_mass(p, sigma2, t, m);
            lemma_dl_mass_le_one(p, m);
        }
    }
    axiom_monotone_convergence(seq, 1real);
    let a = gauss_accept_prob(p, sigma2, t);
    assert(converges_to(seq, a));
    // a ≤ 1 (limit of a ≤ 1 bounded sequence).
    lemma_limit_le_bound(seq, a, 1real);
    // a ≥ seq(1) = const·kernel(0) = const  (limit is an upper bound for nondecreasing).
    lemma_monotone_limit_upper_bound(seq, a);
    assert(dg_ones()(0int) == 1real);
    assert(gauss_kernel_partial(sigma2, dg_ones(), 1nat) == gauss_kernel(sigma2, 0real) * 1real);
    // gauss_kernel(σ²,0) = e^0 = 1
    assert(0real * 0real / (2real * sigma2) == 0real) by(nonlinear_arith) requires sigma2 > 0real;
    axiom_exp_zero();
    assert(gauss_kernel(sigma2, 0real) == 1real);
    // seq(1) = const·(1·1) = const ≤ a.
    assert(seq_at(seq, 1nat) == cst) by(nonlinear_arith)
        requires seq_at(seq, 1nat) == cst * (gauss_kernel(sigma2, 0real) * 1real),
            gauss_kernel(sigma2, 0real) == 1real;
    assert(seq_at(seq, 1nat) <= a);
}

// ─────────────────────────────────────────────────────────────────────────────
//  Final credit bound:  feeding the proposal draw `g_dl` is sound.
//
//  The gaussian precondition (expectation ≤ ε, partial-sum form):
//      dg_series_bounded_by(p,σ²,t,ℰ,ε)  :=  ∀n. const·KP_e(n) ≤ a·ε
//  (a = const·Z, so const·KP_e/a = KP_e/Z = partial sum of gauss_pmf·ℰ ≤ ε.)
//
//  With retry credit  rc = ε + slack/(1−const)  the DL partial sums of
//      g_dl(y) = C(|y|)·ℰ(y) + (1−C(|y|))·rc
//  are bounded by ε+slack:  they are nondecreasing (g_dl ≥ 0), hence ≤ their
//  limit L = const·LKP + rc·(1−a) ≤ a·ε + rc·(1−a) ≤ ε+slack
//  (using const·LKP ≤ a·ε, a ∈ [const,1], (1−a)/(1−const) ≤ 1).
// ─────────────────────────────────────────────────────────────────────────────

/// Gaussian expectation-bound precondition (partial-sum form):
///   ∀n.  const·gauss_kernel_partial(σ²,ℰ,n) ≤ a·ε.
/// `lemma_dg_series_iff` proves this is exactly the genuine expectation bound
/// ε ≥ Σ_x gauss_pmf(x)·ℰ(x) under the true discrete-Gaussian pmf.
pub open spec fn dg_series_bounded_by(
    p: real, sigma2: real, t: real, e: spec_fn(int) -> real, eps: real,
) -> bool {
    forall |n: nat|
        gauss_const(p, sigma2, t) * #[trigger] gauss_kernel_partial(sigma2, e, n)
            <= gauss_accept_prob(p, sigma2, t) * eps
}

// ─────────────────────────────────────────────────────────────────────────────
//  Genuine justification of `dg_series_bounded_by`.
//
//  The true discrete-Gaussian pmf is  gauss_pmf(x) = e^{−x²/2σ²}/Z,  with
//  Z = Σ_y e^{−y²/2σ²}.  No closed form for Z is needed:  the acceptance
//  probability is  a = const·Z  (lemma_gauss_accept_prob, a = lim const·KP_1),
//  so  1/Z = const/a,  hence
//        gauss_pmf(x) = const·e^{−x²/2σ²} / a.
//  gauss_pmf is even, so the pmf-weighted symmetric partial sum collapses to the
//  kernel partial sum:
//        Σ_{|x|<n} gauss_pmf(x)·ℰ(x)  =  const·gauss_kernel_partial(σ²,ℰ,n) / a.
//  Dividing the precondition  ∀n. const·KP_e(n) ≤ a·ε  by a > 0 therefore gives
//        ∀n. Σ_{|x|<n} gauss_pmf(x)·ℰ(x) ≤ ε,
//  i.e. ε ≥ Σ_x gauss_pmf(x)·ℰ(x)  (the partials are nondecreasing for ℰ ≥ 0, so
//  the series sum is their supremum).  We also confirm Σ_x gauss_pmf(x) = 1.
// ─────────────────────────────────────────────────────────────────────────────

/// The true discrete-Gaussian pmf:  gauss_pmf(x) = e^{−x²/2σ²}/Z = const·kernel(x)/a.
pub open spec fn gauss_pmf(p: real, sigma2: real, t: real, x: int) -> real {
    gauss_const(p, sigma2, t) * gauss_kernel(sigma2, x as real)
        / gauss_accept_prob(p, sigma2, t)
}

/// pmf-weighted symmetric partial sum  Σ_{|x|<n} gauss_pmf(x)·ℰ(x)
/// (same shape as gauss_kernel_partial; gauss_pmf is even, so the magnitude-k
/// term gauss_pmf(k)·(ℰ(k)+ℰ(−k)) captures both ±k).
pub open spec fn gauss_pmf_partial(
    p: real, sigma2: real, t: real, e: spec_fn(int) -> real, n: nat,
) -> real
    decreases n,
{
    if n == 0 { 0real }
    else if n == 1 { gauss_pmf(p, sigma2, t, 0int) * e(0int) }
    else {
        gauss_pmf_partial(p, sigma2, t, e, (n - 1) as nat)
            + gauss_pmf(p, sigma2, t, (n - 1) as int)
                * (e((n - 1) as int) + e(-((n - 1) as int)))
    }
}

/// (c·K/a)·W = c·(K·W)/a   (a ≠ 0).
#[verifier::nonlinear]
proof fn lemma_pmf_term(c: real, k: real, a: real, w: real)
    requires a != 0real,
    ensures (c * k / a) * w == c * (k * w) / a,
{}

/// c·X/a + c·Y/a = c·(X+Y)/a   (a ≠ 0).
#[verifier::nonlinear]
proof fn lemma_div_add_regroup(c: real, x: real, y: real, a: real)
    requires a != 0real,
    ensures c * x / a + c * y / a == c * (x + y) / a,
{}

/// u ≤ w, a > 0  ⟹  u/a ≤ w/a.
#[verifier::nonlinear]
proof fn lemma_div_mono(u: real, w: real, a: real)
    requires u <= w, a > 0real,
    ensures u / a <= w / a,
{}

/// gauss_pmf_partial(n) = const·gauss_kernel_partial(σ²,ℰ,n) / a   (a > 0).
#[verifier::spinoff_prover]
pub proof fn lemma_gauss_pmf_partial_eq(
    p: real, sigma2: real, t: real, e: spec_fn(int) -> real, n: nat,
)
    requires sigma2 > 0real, t > 0real, 0real <= p < 1real, p == exp(-(1real / t)),
    ensures
        gauss_pmf_partial(p, sigma2, t, e, n)
            == gauss_const(p, sigma2, t) * gauss_kernel_partial(sigma2, e, n)
                / gauss_accept_prob(p, sigma2, t),
    decreases n,
{
    let cst = gauss_const(p, sigma2, t);
    let a = gauss_accept_prob(p, sigma2, t);
    lemma_gauss_const_pos(p, sigma2, t);
    lemma_gauss_accept_prob(p, sigma2, t);   // cst ≤ a
    assert(a > 0real) by(nonlinear_arith) requires cst > 0real, cst <= a;
    if n == 0 {
        assert(cst * gauss_kernel_partial(sigma2, e, 0nat) / a == 0real) by(nonlinear_arith)
            requires gauss_kernel_partial(sigma2, e, 0nat) == 0real, a != 0real;
    } else if n == 1 {
        let ker0 = gauss_kernel(sigma2, 0real);
        // pmf(0)·e0 = (cst·ker0/a)·e0 = cst·(ker0·e0)/a = cst·KP(1)/a.
        assert(gauss_pmf(p, sigma2, t, 0int) == cst * ker0 / a);
        lemma_pmf_term(cst, ker0, a, e(0int));
        assert(gauss_kernel_partial(sigma2, e, 1nat) == ker0 * e(0int));
    } else {
        let k = (n - 1) as nat;
        lemma_gauss_pmf_partial_eq(p, sigma2, t, e, k);   // IH
        let ker = gauss_kernel(sigma2, k as real);
        let w = e(k as int) + e(-(k as int));
        // pmf(k)·w = (cst·ker/a)·w = cst·(ker·w)/a = cst·KS(k)/a.
        assert(gauss_pmf(p, sigma2, t, k as int) == cst * ker / a) by {
            assert((k as int) as real == k as real);
        }
        lemma_pmf_term(cst, ker, a, w);
        assert(gauss_kernel_sym(sigma2, e, k) == ker * w);
        let ghost kp_k = gauss_kernel_partial(sigma2, e, k);
        let ghost ks_k = gauss_kernel_sym(sigma2, e, k);
        // pmf_partial(n) = cst·KP(k)/a + cst·KS(k)/a = cst·(KP(k)+KS(k))/a = cst·KP(n)/a.
        lemma_div_add_regroup(cst, kp_k, ks_k, a);
        assert(gauss_kernel_partial(sigma2, e, n) == kp_k + ks_k);
    }
}

/// The genuine expectation-preservation precondition (the public spec of the
/// sampler):  ε ≥ Σ_{x∈ℤ} gauss_pmf(x)·ℰ(x), stated as the bound on every
/// (nondecreasing, for ℰ ≥ 0) pmf partial sum — so ε bounds their supremum,
/// i.e. the series sum.
pub open spec fn gauss_expectation_bounded_by(
    p: real, sigma2: real, t: real, e: spec_fn(int) -> real, eps: real,
) -> bool {
    forall |n: nat| #[trigger] gauss_pmf_partial(p, sigma2, t, e, n) <= eps
}

/// The internal kernel-form precondition is exactly the genuine expectation bound:
///   dg_series_bounded_by(p,σ²,t,ℰ,ε)  ⟺  gauss_expectation_bounded_by(p,σ²,t,ℰ,ε)
///                                      (≡ ε ≥ Σ_x gauss_pmf(x)·ℰ(x)).
/// (For ℰ ≥ 0 the partials are nondecreasing — `lemma_gauss_pmf_partial_nondecreasing`
/// — so the RHS bounds the supremum = the series sum.)
#[verifier::spinoff_prover]
pub proof fn lemma_dg_series_iff(
    p: real, sigma2: real, t: real, e: spec_fn(int) -> real, eps: real,
)
    requires sigma2 > 0real, t > 0real, 0real <= p < 1real, p == exp(-(1real / t)),
    ensures
        dg_series_bounded_by(p, sigma2, t, e, eps)
            <==> gauss_expectation_bounded_by(p, sigma2, t, e, eps),
{
    let cst = gauss_const(p, sigma2, t);
    let a = gauss_accept_prob(p, sigma2, t);
    lemma_gauss_const_pos(p, sigma2, t);
    lemma_gauss_accept_prob(p, sigma2, t);
    assert(a > 0real) by(nonlinear_arith) requires cst > 0real, cst <= a;
    // Forward: dg_series_bounded_by ⟹ every pmf partial ≤ ε  (divide by a > 0).
    assert(dg_series_bounded_by(p, sigma2, t, e, eps)
        ==> (forall |n: nat| #[trigger] gauss_pmf_partial(p, sigma2, t, e, n) <= eps)) by {
        if dg_series_bounded_by(p, sigma2, t, e, eps) {
            assert forall |n: nat| #[trigger] gauss_pmf_partial(p, sigma2, t, e, n) <= eps by {
                lemma_gauss_pmf_partial_eq(p, sigma2, t, e, n);   // pmf(n) == cst·KP(n)/a
                let ghost v = cst * gauss_kernel_partial(sigma2, e, n);
                let ghost pf = gauss_pmf_partial(p, sigma2, t, e, n);
                assert(v <= a * eps);                             // instantiate the hypothesis
                assert(pf <= eps) by(nonlinear_arith) requires pf == v / a, v <= a * eps, a > 0real;
            }
        }
    }
    // Backward: every pmf partial ≤ ε ⟹ dg_series_bounded_by  (multiply by a > 0).
    assert((forall |n: nat| #[trigger] gauss_pmf_partial(p, sigma2, t, e, n) <= eps)
        ==> dg_series_bounded_by(p, sigma2, t, e, eps)) by {
        if (forall |n: nat| #[trigger] gauss_pmf_partial(p, sigma2, t, e, n) <= eps) {
            assert forall |n: nat|
                cst * #[trigger] gauss_kernel_partial(sigma2, e, n) <= a * eps by {
                lemma_gauss_pmf_partial_eq(p, sigma2, t, e, n);
                let ghost v = cst * gauss_kernel_partial(sigma2, e, n);
                let ghost pf = gauss_pmf_partial(p, sigma2, t, e, n);
                assert(pf <= eps);                                // instantiate the hypothesis
                assert(v <= a * eps) by(nonlinear_arith) requires pf == v / a, pf <= eps, a > 0real;
            }
        }
    }
}

/// For ℰ ≥ 0 the pmf partials are nondecreasing, so ∀n. partial(n) ≤ ε is exactly
/// ε ≥ Σ_x gauss_pmf(x)·ℰ(x)  (ε bounds the supremum of the partial sums).
#[verifier::spinoff_prover]
pub proof fn lemma_gauss_pmf_partial_nondecreasing(
    p: real, sigma2: real, t: real, e: spec_fn(int) -> real, n: nat,
)
    requires
        sigma2 > 0real, t > 0real, 0real <= p < 1real, p == exp(-(1real / t)),
        forall |x: int| (#[trigger] e(x)) >= 0real,
    ensures
        gauss_pmf_partial(p, sigma2, t, e, n) <= gauss_pmf_partial(p, sigma2, t, e, n + 1),
{
    let cst = gauss_const(p, sigma2, t);
    let a = gauss_accept_prob(p, sigma2, t);
    lemma_gauss_const_pos(p, sigma2, t);
    lemma_gauss_accept_prob(p, sigma2, t);
    assert(a > 0real) by(nonlinear_arith) requires cst > 0real, cst <= a;
    lemma_gauss_pmf_partial_eq(p, sigma2, t, e, n);
    lemma_gauss_pmf_partial_eq(p, sigma2, t, e, n + 1);
    lemma_gauss_kernel_partial_nondecreasing(sigma2, t, e, n);   // KP(n) ≤ KP(n+1)
    let ghost kn = gauss_kernel_partial(sigma2, e, n);
    let ghost kn1 = gauss_kernel_partial(sigma2, e, (n + 1) as nat);
    // partial(n) = (cst·kn)/a ≤ (cst·kn1)/a = partial(n+1).
    assert(cst * kn <= cst * kn1) by(nonlinear_arith) requires cst > 0real, kn <= kn1;
    lemma_div_mono(cst * kn, cst * kn1, a);
}

/// gauss_pmf is a genuine probability distribution:  Σ_x gauss_pmf(x) = 1
/// (the pmf-mass partials converge to 1).
#[verifier::spinoff_prover]
pub proof fn lemma_gauss_pmf_is_distribution(p: real, sigma2: real, t: real)
    requires sigma2 > 0real, t > 0real, 0real <= p < 1real, p == exp(-(1real / t)),
    ensures
        converges_to(|n: nat| gauss_pmf_partial(p, sigma2, t, dg_ones(), n), 1real),
{
    let cst = gauss_const(p, sigma2, t);
    let a = gauss_accept_prob(p, sigma2, t);
    let one = dg_ones();
    lemma_gauss_const_pos(p, sigma2, t);
    lemma_gauss_accept_prob(p, sigma2, t);   // accept_mass_seq → a, cst ≤ a
    assert(a > 0real) by(nonlinear_arith) requires cst > 0real, cst <= a;
    let am = accept_mass_seq(p, sigma2, t);   // am(n) = cst·KP_1(n) → a
    // (1/a)·am(n) → (1/a)·a = 1.
    lemma_limit_scale(am, a, 1real / a);
    let scaled = |n: nat| (1real / a) * seq_at(am, n);
    assert((1real / a) * a == 1real) by(nonlinear_arith) requires a > 0real;
    // pmf_partial(ones,n) == (1/a)·am(n).
    let pmf = |n: nat| gauss_pmf_partial(p, sigma2, t, one, n);
    assert forall |n: nat| seq_at(scaled, n) == seq_at(pmf, n) by {
        lemma_gauss_pmf_partial_eq(p, sigma2, t, one, n);   // pmf(n) == cst·KP_1(n)/a
        assert(seq_at(am, n) == cst * gauss_kernel_partial(sigma2, one, n));
        let ghost kn = gauss_kernel_partial(sigma2, one, n);
        assert((1real / a) * (cst * kn) == cst * kn / a) by(nonlinear_arith) requires a > 0real;
    }
    lemma_limit_pointwise_eq(scaled, pmf, 1real);
}

/// g_dl(y) ≥ 0  (C ∈ [0,1], ℰ ≥ 0, rc ≥ 0).
pub proof fn lemma_gdl_nonneg(p: real, sigma2: real, t: real, e: spec_fn(int) -> real, rc: real, y: int)
    requires sigma2 > 0real, t > 0real, e(y) >= 0real, rc >= 0real,
    ensures gauss_credit_alloc(sigma2, t, e, rc)(y) >= 0real,
{
    let c = gauss_accept(sigma2, t, y);
    assert(gauss_bias(sigma2, t, imag(y)) >= 0real) by(nonlinear_arith)
        requires sigma2 > 0real,
            gauss_bias(sigma2, t, imag(y))
                == (imag(y) - sigma2 / t) * (imag(y) - sigma2 / t) / (2real * sigma2);
    axiom_exp_neg_range(gauss_bias(sigma2, t, imag(y)));  // 0 < c ≤ 1
    assert(gauss_credit_alloc(sigma2, t, e, rc)(y) == c * e(y) + (1real - c) * rc);
    assert(gauss_credit_alloc(sigma2, t, e, rc)(y) >= 0real) by(nonlinear_arith)
        requires gauss_credit_alloc(sigma2, t, e, rc)(y) == c * e(y) + (1real - c) * rc,
            0real < c <= 1real, e(y) >= 0real, rc >= 0real;
}

/// The DL partial sums of g_dl are nondecreasing (g_dl ≥ 0, 0 < p < 1).
#[verifier::spinoff_prover]
pub proof fn lemma_gdl_partial_nondecreasing(
    p: real, sigma2: real, t: real, e: spec_fn(int) -> real, rc: real, n: nat,
)
    requires
        sigma2 > 0real, t > 0real, 0real < p < 1real,
        forall |x: int| (#[trigger] e(x)) >= 0real, rc >= 0real,
    ensures
        dl_partial_sum(p, gauss_credit_alloc(sigma2, t, e, rc), n)
            <= dl_partial_sum(p, gauss_credit_alloc(sigma2, t, e, rc), n + 1),
{
    let g = gauss_credit_alloc(sigma2, t, e, rc);
    if n == 0 {
        lemma_gdl_nonneg(p, sigma2, t, e, rc, 0int);
        assert(dl_partial_sum(p, g, 1nat) == dl_zero_summand(p, g));
        assert(dl_zero_summand(p, g) == (1real - p) / (1real + p) * g(0int));
        assert(dl_zero_summand(p, g) >= 0real) by(nonlinear_arith)
            requires dl_zero_summand(p, g) == (1real - p) / (1real + p) * g(0int),
                g(0int) >= 0real, 0real < p < 1real;
    } else {
        let k = n;
        lemma_gdl_nonneg(p, sigma2, t, e, rc, k as int);
        lemma_gdl_nonneg(p, sigma2, t, e, rc, -(k as int));
        lemma_pow_nonneg(p, k);
        assert(dl_partial_sum(p, g, n + 1) == dl_partial_sum(p, g, n) + dl_symmetric_summand(p, g, k));
        assert(dl_symmetric_summand(p, g, k) == pow(p, k) * (1real - p) / (1real + p) * (g(k as int) + g(-(k as int))));
        assert(dl_symmetric_summand(p, g, k) >= 0real) by(nonlinear_arith)
            requires
                dl_symmetric_summand(p, g, k) == pow(p, k) * (1real - p) / (1real + p) * (g(k as int) + g(-(k as int))),
                pow(p, k) >= 0real, 0real < p < 1real, g(k as int) >= 0real, g(-(k as int)) >= 0real;
    }
}

/// Bias arithmetic:  with σ² = sn²/sd², D = 2·sn²·sd²·t², base = a·sd²·t − sn²,
///   gauss_bias(σ², t, a) · D == base²,
/// so the computed rational  base²/D  equals the spec bias (D > 0).
#[verifier::spinoff_prover]
pub proof fn lemma_gauss_bias_eq(snr: real, sdr: real, tr: real, a: real, base_r: real)
    requires
        snr > 0real, sdr > 0real, tr > 0real, a >= 0real,
        base_r == a * (sdr * sdr) * tr - snr * snr,
    ensures
        gauss_bias((snr * snr) / (sdr * sdr), tr, a)
            * (2real * (snr * snr) * (sdr * sdr) * (tr * tr))
            == base_r * base_r,
{
    let sigma2 = (snr * snr) / (sdr * sdr);
    let big_d = 2real * (snr * snr) * (sdr * sdr) * (tr * tr);
    let q = a - sigma2 / tr;
    assert(sigma2 > 0real) by(nonlinear_arith)
        requires sigma2 == (snr * snr) / (sdr * sdr), snr > 0real, sdr > 0real;
    // sigma2·sd² = sn²
    assert(sigma2 * (sdr * sdr) == snr * snr) by(nonlinear_arith)
        requires sigma2 == (snr * snr) / (sdr * sdr), sdr > 0real;
    // q·(sd²·t) == base_r:  q·sd²t = a·sd²t − (sigma2/t)·sd²t = a·sd²t − sigma2·sd² = base_r.
    assert(q * (sdr * sdr * tr) == base_r) by(nonlinear_arith)
        requires q == a - sigma2 / tr, tr > 0real,
            sigma2 * (sdr * sdr) == snr * snr,
            base_r == a * (sdr * sdr) * tr - snr * snr;
    // D == 2·sigma2·sd⁴·t²  (since sigma2·sd² = sn²).
    assert(big_d == (2real * sigma2) * ((sdr * sdr) * (sdr * sdr) * (tr * tr))) by(nonlinear_arith)
        requires
            big_d == 2real * (snr * snr) * (sdr * sdr) * (tr * tr),
            sigma2 * (sdr * sdr) == snr * snr;
    // gauss_bias·D = (q²/(2σ²))·(2σ²·sd⁴t²) = q²·sd⁴t² = (q·sd²t)² = base².
    assert(gauss_bias(sigma2, tr, a) == q * q / (2real * sigma2)) by(nonlinear_arith)
        requires gauss_bias(sigma2, tr, a) == (a - sigma2 / tr) * (a - sigma2 / tr) / (2real * sigma2),
            q == a - sigma2 / tr;
    assert(gauss_bias(sigma2, tr, a) * big_d == base_r * base_r) by(nonlinear_arith)
        requires
            gauss_bias(sigma2, tr, a) == q * q / (2real * sigma2),
            big_d == (2real * sigma2) * ((sdr * sdr) * (sdr * sdr) * (tr * tr)),
            q * (sdr * sdr * tr) == base_r,
            sigma2 > 0real;
}

/// FINAL CREDIT BOUND.  Given the gaussian expectation precondition and retry
/// credit  rc = ε + slack/(1−const),  the proposal postcondition g_dl satisfies
/// the discrete-Laplace precondition  dl_series_bounded_by(p, g_dl, ε+slack).
///
/// Proof: the DL partial sums of g_dl are nondecreasing (g_dl ≥ 0), hence ≤ their
/// limit L; by the decomposition + the three limits (KP_e → LKP, DM → 1, AM → a),
/// L = const·LKP + rc·(1−a) ≤ a·ε + rc·(1−a) ≤ ε+slack.
#[verifier::spinoff_prover]
pub proof fn lemma_dg_dl_bound(
    p: real, sigma2: real, t: real, e: spec_fn(int) -> real, eps: real, slack: real, rc: real,
)
    requires
        sigma2 > 0real, t > 0real, 0real < p < 1real, p == exp(-(1real / t)),
        forall |x: int| (#[trigger] e(x)) >= 0real,
        eps > 0real, slack > 0real,
        rc == eps + slack / (1real - gauss_const(p, sigma2, t)),
        dg_series_bounded_by(p, sigma2, t, e, eps),
    ensures
        dl_series_bounded_by(p, gauss_credit_alloc(sigma2, t, e, rc), eps + slack),
{
    let cst = gauss_const(p, sigma2, t);
    let a = gauss_accept_prob(p, sigma2, t);
    let g = gauss_credit_alloc(sigma2, t, e, rc);
    lemma_gauss_const_pos(p, sigma2, t);
    lemma_gauss_const_lt_one(p, sigma2, t);
    lemma_gauss_accept_prob(p, sigma2, t);   // accept_mass_seq → a, const ≤ a ≤ 1
    lemma_dl_mass_limit(p);                   // dm → 1

    // d := slack/(1−const);  rc = ε + d;  (1−const)·d = slack.
    let ghost d = slack / (1real - cst);
    lemma_cancel(slack, 1real - cst);
    assert((1real - cst) * d == slack);
    assert(rc == eps + d);
    assert(d > 0real) by(nonlinear_arith)
        requires d == slack / (1real - cst), slack > 0real, 0real < cst < 1real;
    assert(rc >= 0real) by(nonlinear_arith) requires rc == eps + d, eps > 0real, d > 0real;

    let kpe = |n: nat| gauss_kernel_partial(sigma2, e, n);
    let dm = |n: nat| dl_partial_sum(p, dg_ones(), n);
    let am = accept_mass_seq(p, sigma2, t);

    // (1) KP_e converges to lkp;  const·lkp ≤ a·ε.
    assert(is_nondecreasing(kpe)) by {
        assert forall |n: nat| #[trigger] seq_at(kpe, n) <= seq_at(kpe, n + 1) by {
            lemma_gauss_kernel_partial_nondecreasing(sigma2, t, e, n);
        }
    }
    assert(is_bounded_above(kpe, a * eps / cst)) by {
        assert forall |n: nat| #[trigger] seq_at(kpe, n) <= a * eps / cst by {
            assert(cst * gauss_kernel_partial(sigma2, e, n) <= a * eps);  // precond
            assert(seq_at(kpe, n) <= a * eps / cst) by(nonlinear_arith)
                requires cst * gauss_kernel_partial(sigma2, e, n) <= a * eps, cst > 0real,
                    seq_at(kpe, n) == gauss_kernel_partial(sigma2, e, n);
        }
    }
    axiom_monotone_convergence(kpe, a * eps / cst);
    let ghost lkp = choose |l: real| converges_to(kpe, l);
    assert(converges_to(kpe, lkp));
    lemma_limit_scale(kpe, lkp, cst);          // |n| const·kpe(n) → const·lkp
    let ckpe = |n: nat| cst * seq_at(kpe, n);
    assert(is_bounded_above(ckpe, a * eps)) by {
        assert forall |n: nat| #[trigger] seq_at(ckpe, n) <= a * eps by {
            assert(seq_at(ckpe, n) == cst * seq_at(kpe, n));
            assert(cst * gauss_kernel_partial(sigma2, e, n) <= a * eps);
        }
    }
    lemma_limit_le_bound(ckpe, cst * lkp, a * eps);   // const·lkp ≤ a·ε

    // (2) build the combined limit  L = const·lkp + rc·1 − rc·a.
    lemma_limit_scale(dm, 1real, rc);          // rdm → rc
    let rdm = |n: nat| rc * seq_at(dm, n);
    lemma_limit_scale(am, a, rc);              // ram → rc·a
    let ram = |n: nat| rc * seq_at(am, n);
    lemma_limit_scale(ram, rc * a, -1real);    // nram → −rc·a
    let nram = |n: nat| (-1real) * seq_at(ram, n);
    lemma_limit_add(ckpe, rdm, cst * lkp, rc);
    let c12 = |n: nat| seq_at(ckpe, n) + seq_at(rdm, n);
    lemma_limit_add(c12, nram, cst * lkp + rc, -(rc * a));
    let comb = |n: nat| seq_at(c12, n) + seq_at(nram, n);
    let ghost ll = cst * lkp + rc + (-(rc * a));
    assert(converges_to(comb, ll));

    // gdl(n) == comb(n)  for all n  (the decomposition, with am = const·KM).
    let gdl = |n: nat| dl_partial_sum(p, g, n);
    assert forall |n: nat| seq_at(gdl, n) == seq_at(comb, n) by {
        lemma_dg_decomposition(p, sigma2, t, e, rc, n);
        assert(seq_at(am, n) == cst * gauss_kernel_partial(sigma2, dg_ones(), n));
        assert(seq_at(comb, n) == cst * seq_at(kpe, n) + rc * seq_at(dm, n) + (-1real) * (rc * seq_at(am, n)));
        assert(seq_at(gdl, n) == seq_at(comb, n)) by(nonlinear_arith)
            requires
                dl_partial_sum(p, g, n)
                    == cst * gauss_kernel_partial(sigma2, e, n)
                     + rc * (dl_partial_sum(p, dg_ones(), n) - cst * gauss_kernel_partial(sigma2, dg_ones(), n)),
                seq_at(gdl, n) == dl_partial_sum(p, g, n),
                seq_at(kpe, n) == gauss_kernel_partial(sigma2, e, n),
                seq_at(dm, n) == dl_partial_sum(p, dg_ones(), n),
                seq_at(am, n) == cst * gauss_kernel_partial(sigma2, dg_ones(), n),
                seq_at(comb, n) == cst * seq_at(kpe, n) + rc * seq_at(dm, n) + (-1real) * (rc * seq_at(am, n));
    }
    lemma_limit_pointwise_eq(comb, gdl, ll);   // gdl → ll

    // gdl is nondecreasing ⇒ each gdl(n) ≤ ll.
    assert(is_nondecreasing(gdl)) by {
        assert forall |n: nat| #[trigger] seq_at(gdl, n) <= seq_at(gdl, n + 1) by {
            lemma_gdl_partial_nondecreasing(p, sigma2, t, e, rc, n);
        }
    }
    lemma_monotone_limit_upper_bound(gdl, ll);

    // ll ≤ ε + slack:  ll = const·lkp + rc·(1−a) ≤ a·ε + rc·(1−a),
    //   rc·(1−a) = (ε+d)(1−a) = ε(1−a) + d(1−a) ≤ ε(1−a) + d(1−const) = ε(1−a) + slack.
    assert(ll <= eps + slack) by(nonlinear_arith)
        requires
            ll == cst * lkp + rc + (-(rc * a)),
            cst * lkp <= a * eps,
            rc == eps + d, (1real - cst) * d == slack,
            cst <= a, a <= 1real, 0real < cst < 1real, d > 0real;

    // Conclude the DL precondition.
    assert forall |n: nat| eps + slack >= #[trigger] dl_partial_sum(p, gauss_credit_alloc(sigma2, t, e, rc), n) by {
        assert(seq_at(gdl, n) == dl_partial_sum(p, g, n));
        assert(seq_at(gdl, n) <= ll);   // is_bounded_above(gdl, ll)
    }
}

/// Sample from the discrete Gaussian N_ℤ(0, σ²),  σ = scale  (an arbitrary-precision
/// rational `RBig`, matching opendp's `sample_discrete_gaussian(scale: RBig)`).
///
/// Expectation Preservation Rule:
///   ε ≥ Σ_{x∈ℤ} gauss_pmf(x)·ℰ(x)        (as gauss_expectation_bounded_by)
///   ─────────────────────────────────────────────────────
///   [{ ↯(ε) }] sample_discrete_gaussian(σ) [{ v. ↯(ℰ(v)) }]
#[verifier::spinoff_prover]
pub fn sample_discrete_gaussian(
    scale: &RBig,
    Ghost(e): Ghost<spec_fn(int) -> real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(eps): Ghost<real>,
) -> ((value, out_credit): (IBig, Tracked<ErrorCreditResource>))
    requires
        rbig_view(scale) > 0real,
        forall |x: int| (#[trigger] e(x)) >= 0real,
        eps > 0real,
        input_credit@ =~= (ErrorCreditCarrier::Value { car: eps }),
        gauss_expectation_bounded_by(
            exp(-(1real / ((rbig_view(scale).floor() + 1) as real))),
            rbig_view(scale) * rbig_view(scale),
            (rbig_view(scale).floor() + 1) as real, e, eps),
    ensures
        out_credit@@ =~= (ErrorCreditCarrier::Value { car: e(ibig_view(&value)) }),
{
    // scale = sn/sd  (sn ≥ 1 since scale > 0, sd ≥ 1).
    let parts = rbig_into_parts(scale);
    let sn_signed = parts.0;
    let sd = parts.1;
    let sn = ibig_abs(&sn_signed);
    // t = ⌊σ⌋ + 1  (a positive integer), as a UBig and as an RBig.
    let floor_i = rbig_floor(scale);
    let t_i = ibig_add(&floor_i, &ibig_from_i64(1i64));
    let t_ubig = ibig_abs(&t_i);
    let t_numer = ibig_from_ubig(&t_ubig);
    let one = ubig_from_u64(1u64);
    let t_rbig = rbig_from_parts(&t_numer, &one);

    let ghost snr = ubig_view(&sn) as real;
    let ghost sdr = ubig_view(&sd) as real;
    let ghost tr = ubig_view(&t_ubig) as real;
    let ghost p = exp(-(1real / tr));
    let ghost sigma2 = rbig_view(scale) * rbig_view(scale);
    let ghost cst = gauss_const(p, sigma2, tr);
    let ghost amp = 1real / (1real - cst);

    proof {
        // sn, sd > 0  (scale = sn/sd > 0).
        assert(rbig_view(scale) == ibig_view(&sn_signed) as real / sdr);
        assert(ubig_view(&sd) > 0);
        assert(ibig_view(&sn_signed) > 0) by(nonlinear_arith)
            requires rbig_view(scale) == ibig_view(&sn_signed) as real / sdr,
                rbig_view(scale) > 0real, sdr == ubig_view(&sd) as real, ubig_view(&sd) > 0;
        assert(ubig_view(&sn) as int == ibig_view(&sn_signed));   // ibig_abs, sn_signed ≥ 0
        assert(ubig_view(&sn) > 0);
        // σ = sn/sd ;  σ² = sn²/sd² = sigma2.
        assert(rbig_view(scale) == snr / sdr);
        assert(sigma2 == (snr * snr) / (sdr * sdr)) by(nonlinear_arith)
            requires sigma2 == rbig_view(scale) * rbig_view(scale),
                rbig_view(scale) == snr / sdr, sdr > 0real;
        assert(sigma2 > 0real) by(nonlinear_arith)
            requires sigma2 == (snr * snr) / (sdr * sdr), snr > 0real, sdr > 0real;
        // t = ⌊σ⌋ + 1 ≥ 1  (floor ≥ 0 since σ > 0).
        assert(ibig_view(&floor_i) == rbig_view(scale).floor());
        assert(rbig_view(scale).floor() >= 0) by(nonlinear_arith)
            requires rbig_view(scale) > 0real,
                rbig_view(scale) < (rbig_view(scale).floor() + 1) as real;
        assert(ibig_view(&t_i) == rbig_view(scale).floor() + 1);
        assert(ubig_view(&t_ubig) as int == ibig_view(&t_i));   // ibig_abs, t_i ≥ 1
        assert(tr == (rbig_view(scale).floor() + 1) as real);
        assert(tr >= 1real);
        assert(rbig_view(&t_rbig) == tr);   // t_rbig = t_ubig / 1
        // p, cst, amp.
        assert(1real / tr > 0real) by(nonlinear_arith) requires tr >= 1real;
        axiom_exp_neg_range(1real / tr);
        axiom_exp_neg_strict(1real / tr);
        lemma_gauss_const_pos(p, sigma2, tr);
        lemma_gauss_const_lt_one(p, sigma2, tr);
        assert(amp > 1real) by(nonlinear_arith) requires amp == 1real / (1real - cst), 0real < cst < 1real;
        // The public precondition is the genuine expectation bound under gauss_pmf
        // (with this exact p, σ², t);  convert it to the internal kernel-partial form.
        lemma_dg_series_iff(p, sigma2, tr, e, eps);
        assert(dg_series_bounded_by(p, sigma2, tr, e, eps));
    }

    // Bignum constants:  sn², sd², den = 2·sn²·sd²·t².
    let sn2 = ubig_mul(&sn, &sn);
    let sd2 = ubig_mul(&sd, &sd);
    let t2 = ubig_mul(&t_ubig, &t_ubig);
    let den = ubig_mul(&ubig_mul(&ubig_mul(&sn2, &sd2), &t2), &ubig_from_u64(2u64));

    // Thin-air slack + termination depth.
    let Tracked(slack_credit) = thin_air();
    let ghost init_slack: real;
    let ghost init_depth: nat;
    proof {
        init_slack = choose |v: real| v > 0real &&
            (ErrorCreditCarrier::Value { car: v } =~= slack_credit@);
        archimedean_exp_growth(init_slack, amp);
        init_depth = choose |k: nat| init_slack * pow(amp, k) >= 1real;
    }
    let tracked mut credit = ec_combine(input_credit, slack_credit, eps, init_slack);
    let ghost mut g_slack = init_slack;
    let ghost mut g_depth = init_depth;

    loop
        invariant
            ubig_view(&sn) > 0, ubig_view(&sd) > 0, ubig_view(&t_ubig) >= 1,
            snr == ubig_view(&sn) as real, sdr == ubig_view(&sd) as real,
            tr == ubig_view(&t_ubig) as real,
            rbig_view(&t_rbig) == tr,
            p == exp(-(1real / tr)),
            sigma2 == (snr * snr) / (sdr * sdr),
            cst == gauss_const(p, sigma2, tr), amp == 1real / (1real - cst),
            0real < p < 1real, sigma2 > 0real, tr >= 1real, 0real < cst < 1real, amp > 1real,
            forall |x: int| (#[trigger] e(x)) >= 0real,
            eps > 0real, g_slack > 0real,
            credit@ =~= (ErrorCreditCarrier::Value { car: eps + g_slack }),
            dg_series_bounded_by(p, sigma2, tr, e, eps),
            ubig_view(&sn2) == ubig_view(&sn) * ubig_view(&sn),
            ubig_view(&sd2) == ubig_view(&sd) * ubig_view(&sd),
            ubig_view(&den) == ubig_view(&sn2) * ubig_view(&sd2)
                * (ubig_view(&t_ubig) * ubig_view(&t_ubig)) * 2,
            g_slack * pow(amp, g_depth) >= 1real,
        decreases g_depth,
    {
        proof {
            if g_depth == 0nat {
                assert(pow(amp, 0nat) == 1real);
                ec_contradict(&credit);
            }
        }

        let ghost rc = eps + g_slack / (1real - cst);
        let ghost g_dl = gauss_credit_alloc(sigma2, tr, e, rc);
        proof {
            assert(rc >= 0real) by(nonlinear_arith)
                requires rc == eps + g_slack / (1real - cst), eps > 0real, g_slack > 0real, 0real < cst < 1real;
            assert forall |x: int| (#[trigger] g_dl(x)) >= 0real by {
                lemma_gdl_nonneg(p, sigma2, tr, e, rc, x);
            }
            lemma_dg_dl_bound(p, sigma2, tr, e, eps, g_slack, rc);
        }

        // Proposal draw  Y ~ L_ℤ(0, t)  via the fast (RBig) discrete-Laplace sampler.
        let (cand, Tracked(dl_credit)) = sample_discrete_laplace_fast(
            &t_rbig, Ghost(p), Ghost(g_dl), Tracked(credit), Ghost(eps + g_slack),
        );
        let ghost cand_i = ibig_view(&cand);

        // bias = (|cand|·sd²·t − sn²)² / (2·sn²·sd²·t²)
        let a_ubig = ibig_abs(&cand);
        let asdt = ubig_mul(&ubig_mul(&a_ubig, &sd2), &t_ubig);
        let base_i = ibig_sub(&ibig_from_ubig(&asdt), &ibig_from_ubig(&sn2));
        let num_i = ibig_mul(&base_i, &base_i);
        let num = ibig_abs(&num_i);

        let ghost a_int: int = if cand_i >= 0 { cand_i } else { -cand_i };
        let ghost a = a_int as real;
        let ghost base_int = ibig_view(&base_i);
        let ghost base_r = base_int as real;
        let ghost num_r = ubig_view(&num) as real;
        let ghost den_r = ubig_view(&den) as real;
        let ghost g_dl_cand = g_dl(cand_i);
        let ghost accept_e: spec_fn(bool) -> real = |b: bool| if b { e(cand_i) } else { rc };

        proof {
            // a = |cand| (int → real);  imag(cand) = a.
            assert(ubig_view(&a_ubig) as int == a_int);   // ibig_abs spec
            assert(imag(cand_i) == a);
            // base_int = |cand|·sd²·t − sn²  (integer).
            assert(ubig_view(&asdt) == ubig_view(&a_ubig) * ubig_view(&sd2) * ubig_view(&t_ubig));
            assert(base_int == ubig_view(&asdt) as int - ubig_view(&sn2) as int);
            assert(base_int == a_int * (ubig_view(&sd) as int * ubig_view(&sd) as int) * (ubig_view(&t_ubig) as int)
                - ubig_view(&sn) as int * ubig_view(&sn) as int) by(nonlinear_arith)
                requires
                    base_int == ubig_view(&asdt) as int - ubig_view(&sn2) as int,
                    ubig_view(&asdt) == ubig_view(&a_ubig) * ubig_view(&sd2) * ubig_view(&t_ubig),
                    ubig_view(&a_ubig) as int == a_int,
                    ubig_view(&sd2) == ubig_view(&sd) * ubig_view(&sd),
                    ubig_view(&sn2) == ubig_view(&sn) * ubig_view(&sn);
            // cast to real:  base_r = a·sd²·t − sn².
            assert(base_r == a * (sdr * sdr) * tr - snr * snr) by(nonlinear_arith)
                requires
                    base_r == base_int as real, a == a_int as real,
                    tr == ubig_view(&t_ubig) as real, snr == ubig_view(&sn) as real, sdr == ubig_view(&sd) as real,
                    base_int == a_int * (ubig_view(&sd) as int * ubig_view(&sd) as int) * (ubig_view(&t_ubig) as int)
                        - ubig_view(&sn) as int * ubig_view(&sn) as int;
            // num = base²  (as real).
            assert(ibig_view(&num_i) == base_int * base_int);
            assert(base_int * base_int >= 0) by(nonlinear_arith);
            assert(ubig_view(&num) as int == base_int * base_int);
            assert(num_r == base_r * base_r) by(nonlinear_arith)
                requires num_r == ubig_view(&num) as real,
                    ubig_view(&num) as int == base_int * base_int, base_r == base_int as real;
            // den = D  (as real).
            assert(den_r == 2real * (snr * snr) * (sdr * sdr) * (tr * tr)) by(nonlinear_arith)
                requires den_r == ubig_view(&den) as real,
                    ubig_view(&den) == ubig_view(&sn2) * ubig_view(&sd2)
                        * (ubig_view(&t_ubig) * ubig_view(&t_ubig)) * 2,
                    ubig_view(&sn2) == ubig_view(&sn) * ubig_view(&sn),
                    ubig_view(&sd2) == ubig_view(&sd) * ubig_view(&sd),
                    snr == ubig_view(&sn) as real, sdr == ubig_view(&sd) as real,
                    tr == ubig_view(&t_ubig) as real;
            assert(ubig_view(&den) > 0) by(nonlinear_arith)
                requires ubig_view(&den) == ubig_view(&sn2) * ubig_view(&sd2)
                        * (ubig_view(&t_ubig) * ubig_view(&t_ubig)) * 2,
                    ubig_view(&sn2) == ubig_view(&sn) * ubig_view(&sn),
                    ubig_view(&sd2) == ubig_view(&sd) * ubig_view(&sd),
                    ubig_view(&sn) > 0, ubig_view(&sd) > 0, ubig_view(&t_ubig) >= 1;
            assert(den_r > 0real) by(nonlinear_arith) requires den_r == ubig_view(&den) as real, ubig_view(&den) > 0;
            // gauss_bias·D == base² == num,  D == den > 0  ⇒  num/den == gauss_bias.
            //   (sigma2 == sn²/sd², so lemma_gauss_bias_eq's gauss_bias(sn²/sd², …) is gauss_bias(σ², …).)
            lemma_gauss_bias_eq(snr, sdr, tr, a, base_r);
            assert(gauss_bias(sigma2, tr, a) == num_r / den_r) by(nonlinear_arith)
                requires
                    gauss_bias(sigma2, tr, a) * den_r == base_r * base_r,
                    num_r == base_r * base_r, den_r > 0real;
            // exp(−(num/den)) == gauss_accept(σ²,t,cand).
            assert(gauss_accept(sigma2, tr, cand_i) == exp(-(num_r / den_r)));
            // accept arms and g_dl(cand) = bws(C, accept_e).
            assert(accept_e(true) == e(cand_i) && accept_e(false) == rc);
            assert(g_dl_cand == gauss_accept(sigma2, tr, cand_i) * e(cand_i)
                + (1real - gauss_accept(sigma2, tr, cand_i)) * rc);
        }

        // Bernoulli(exp(−num/den)) — build the rational num/den.
        let x_arg = rbig_from_parts(&ibig_from_ubig(&num), &den);
        proof {
            assert(rbig_view(&x_arg) == num_r / den_r);
            assert(rbig_view(&x_arg) >= 0real) by(nonlinear_arith)
                requires rbig_view(&x_arg) == num_r / den_r,
                    num_r == ubig_view(&num) as real, den_r == ubig_view(&den) as real,
                    ubig_view(&den) > 0;
            assert(exp(-rbig_view(&x_arg)) == exp(-(num_r / den_r)));
        }
        let (heads, Tracked(out_credit)) = sample_bernoulli_exp_rbig(
            x_arg, Ghost(accept_e), Tracked(dl_credit), Ghost(g_dl_cand),
        );

        if heads {
            return (cand, Tracked(out_credit));
        }

        // Reject: out has value accept_e(false) = rc = ε + g_slack/(1−const); amplify.
        proof {
            let old_slack = g_slack;
            let old_depth = g_depth;
            credit = out_credit;
            g_slack = old_slack / (1real - cst);
            g_depth = (old_depth - 1) as nat;
            lemma_mul_div_regroup(old_slack, 1real, 1real - cst);  // old_slack·1/(1−cst) = old_slack·(1/(1−cst))
            assert(g_slack == old_slack * amp) by(nonlinear_arith)
                requires g_slack == old_slack / (1real - cst), amp == 1real / (1real - cst),
                    old_slack * 1real / (1real - cst) == old_slack * (1real / (1real - cst));
            assert(g_slack > 0real) by(nonlinear_arith)
                requires g_slack == old_slack * amp, old_slack > 0real, amp > 1real;
            assert(eps + g_slack == rc) by(nonlinear_arith)
                requires rc == eps + old_slack / (1real - cst), g_slack == old_slack / (1real - cst);
            assert(pow(amp, old_depth) == amp * pow(amp, (old_depth - 1) as nat));
            real_assoc_mult(old_slack, amp, pow(amp, (old_depth - 1) as nat));
        }
    }
}

/// The Gaussian kernel partial sum of the zero postcondition is 0.
proof fn lemma_gauss_kernel_partial_zero(sigma2: real, e: spec_fn(int) -> real, n: nat)
    requires forall |x: int| #[trigger] e(x) == 0real,
    ensures gauss_kernel_partial(sigma2, e, n) == 0real,
    decreases n,
{
    if n == 0 {
    } else if n == 1 {
        assert(e(0int) == 0real);
        assert(gauss_kernel_partial(sigma2, e, 1nat) == gauss_kernel(sigma2, 0real) * e(0int));
    } else {
        let k = (n - 1) as nat;
        lemma_gauss_kernel_partial_zero(sigma2, e, k);
        assert(e(k as int) == 0real);
        assert(e(-(k as int)) == 0real);
        assert(gauss_kernel_sym(sigma2, e, k) == gauss_kernel(sigma2, k as real) * (e(k as int) + e(-(k as int))));
    }
}

/// Entry point: sample the discrete Gaussian with no caller preconditions
/// beyond a positive rational scale σ = scale_numer/scale_denom (uses the trivial
/// postcondition ℰ ≡ 0).  Builds the `RBig` scale and calls `sample_discrete_gaussian`.
pub fn sample_discrete_gaussian_entry(
    scale_numer: u64,
    scale_denom: u64,
) -> (ret: IBig)
    requires
        scale_numer > 0,
        scale_denom > 0,
{
    let scale = rbig_from_parts(
        &ibig_from_ubig(&ubig_from_u64(scale_numer)), &ubig_from_u64(scale_denom));
    let ghost e: spec_fn(int) -> real = |_x: int| 0real;
    let Tracked(cred) = thin_air();
    let ghost eps: real;
    proof {
        eps = choose |v: real| v > 0real &&
            (ErrorCreditCarrier::Value { car: v } =~= cred@);
        // rbig_view(scale) = scale_numer/scale_denom > 0.
        assert(rbig_view(&scale) == scale_numer as real / scale_denom as real);
        assert(rbig_view(&scale) > 0real) by(nonlinear_arith)
            requires rbig_view(&scale) == scale_numer as real / scale_denom as real,
                scale_numer > 0u64, scale_denom > 0u64;
        let tr = (rbig_view(&scale).floor() + 1) as real;
        let p = exp(-(1real / tr));
        let sigma2 = rbig_view(&scale) * rbig_view(&scale);
        // ⌊σ⌋ ≥ 0 (σ > 0), so tr ≥ 1.
        assert(rbig_view(&scale).floor() >= 0) by(nonlinear_arith)
            requires rbig_view(&scale) > 0real,
                rbig_view(&scale) < (rbig_view(&scale).floor() + 1) as real;
        assert(tr >= 1real);
        assert(1real / tr > 0real) by(nonlinear_arith) requires tr >= 1real;
        axiom_exp_neg_range(1real / tr);
        axiom_exp_neg_strict(1real / tr);
        assert(sigma2 > 0real) by(nonlinear_arith)
            requires sigma2 == rbig_view(&scale) * rbig_view(&scale), rbig_view(&scale) > 0real;
        lemma_gauss_const_pos(p, sigma2, tr);
        lemma_gauss_accept_prob(p, sigma2, tr);   // const ≤ a ≤ 1, so a·eps ≥ 0
        // ε ≥ Σ gauss_pmf·ℰ holds trivially since ℰ ≡ 0  (kernel partial sums are 0).
        assert forall |n: nat|
            gauss_const(p, sigma2, tr) * (#[trigger] gauss_kernel_partial(sigma2, e, n))
                <= gauss_accept_prob(p, sigma2, tr) * eps by {
            lemma_gauss_kernel_partial_zero(sigma2, e, n);
            assert(gauss_accept_prob(p, sigma2, tr) * eps >= 0real) by(nonlinear_arith)
                requires gauss_accept_prob(p, sigma2, tr) >= gauss_const(p, sigma2, tr),
                    gauss_const(p, sigma2, tr) > 0real, eps > 0real;
        }
        assert(dg_series_bounded_by(p, sigma2, tr, e, eps));
        lemma_dg_series_iff(p, sigma2, tr, e, eps);
        assert(gauss_expectation_bounded_by(p, sigma2, tr, e, eps));
    }
    let (v, _out) = sample_discrete_gaussian(&scale, Ghost(e), Tracked(cred), Ghost(eps));
    v
}

} // verus!
