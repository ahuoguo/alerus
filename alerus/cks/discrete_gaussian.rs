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


use vstd::prelude::*;

use random::{IBig, ubig_from_u64, ubig_mul, ibig_from_ubig, ibig_sub, ibig_mul, ibig_abs,
    RBig, rbig_into_parts, rbig_floor, rbig_from_parts, ibig_add, ibig_from_i64};
#[cfg(verus_keep_ghost)]
use random::{UBig};

verus! {

use crate::ec::*;
#[cfg(verus_keep_ghost)]
use crate::cks::discrete_gaussian_helper::*;
#[cfg(verus_keep_ghost)]
use crate::ec::ErrorCreditCarrier::Value;
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

// ─────────────────────────────────────────────────────────────────────────────
//  lim_n pⁿ = 0  for 0 ≤ p < 1.
// ─────────────────────────────────────────────────────────────────────────────

/// The geometric sequence  n ↦ pⁿ.
pub open spec fn pow_seq(p: real) -> spec_fn(nat) -> real {
    |n: nat| pow(p, n)
}

// ─────────────────────────────────────────────────────────────────────────────
//  DL proposal mass bound:  Σ_{|y|<n} P_L[y] ≤ 1   (the proposal is a sub-distribution
//  on every finite truncation).  Closed form (n ≥ 1):  (1+p)·DM(n) = (1+p) − 2pⁿ.
// ─────────────────────────────────────────────────────────────────────────────

// ─────────────────────────────────────────────────────────────────────────────
//  Acceptance mass ≤ proposal mass:  const·gauss_kernel_partial(σ², 1, n) ≤ DM(n).
//  Since C(k) ≤ 1 termwise, the accept mass never exceeds the proposal mass;
//  combined with DM(n) ≤ 1 this bounds the accept mass by 1 (⇒ a := lim exists).
// ─────────────────────────────────────────────────────────────────────────────

// ─────────────────────────────────────────────────────────────────────────────
//  Acceptance probability  a := lim_n const·gauss_kernel_partial(σ², 1, n)  (= const·Z).
//  The accept-mass sequence is nondecreasing and bounded above by 1, so it
//  converges; the limit `a` satisfies  const ≤ a ≤ 1  (so 1 − a ∈ [0, 1−const)).
// ─────────────────────────────────────────────────────────────────────────────

/// The accept-mass sequence  m ↦ const·gauss_kernel_partial(σ², 1, m).
pub open spec fn accept_mass_seq(p: real, sigma2: real, t: real) -> spec_fn(nat) -> real {
    |m: nat| gauss_const(p, sigma2, t) * gauss_kernel_partial(sigma2, dg_ones(), m)
}

/// Acceptance probability  a = lim of the accept-mass sequence.
pub open spec fn gauss_accept_prob(p: real, sigma2: real, t: real) -> real {
    choose |l: real| converges_to(accept_mass_seq(p, sigma2, t), l)
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

/// The genuine expectation-preservation precondition (the public spec of the
/// sampler):  ε ≥ Σ_{x∈ℤ} gauss_pmf(x)·ℰ(x), stated as the bound on every
/// (nondecreasing, for ℰ ≥ 0) pmf partial sum — so ε bounds their supremum,
/// i.e. the series sum.
pub open spec fn gauss_expectation_bounded_by(
    p: real, sigma2: real, t: real, e: spec_fn(int) -> real, eps: real,
) -> bool {
    forall |n: nat| #[trigger] gauss_pmf_partial(p, sigma2, t, e, n) <= eps
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
        input_credit@ =~= (Value { car: eps }),
        gauss_expectation_bounded_by(
            exp(-(1real / ((rbig_view(scale).floor() + 1) as real))),
            rbig_view(scale) * rbig_view(scale),
            (rbig_view(scale).floor() + 1) as real, e, eps),
    ensures
        out_credit@@ =~= (Value { car: e(ibig_view(&value)) }),
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
            (Value { car: v } =~= slack_credit@);
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
            credit@ =~= (Value { car: eps + g_slack }),
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
            (Value { car: v } =~= cred@);
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
