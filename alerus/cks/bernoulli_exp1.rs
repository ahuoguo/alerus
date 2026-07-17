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
#[cfg(verus_keep_ghost)]
use crate::cks::bernoulli_exp1_helper::*;
#[cfg(verus_keep_ghost)]
use crate::ec::ErrorCreditCarrier::Value;
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
        input_credit@ =~= (Value { car: eps }),
        eps >= bernoulli_weighted_sum(exp(-(numer_x as real / denom_x as real)), e),
    ensures
        out_credit@@ =~= (Value { car: e(value) }),
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
            (Value { car: v } =~= slack_credit@);
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
            dist_credit@ =~= (Value { car: g_dist_eps }),
            slack_credit@ =~= (Value { car: g_slack_val }),
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

        k = ubig_succ(&k);
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
        input_credit@ =~= (Value { car: eps }),
        eps >= bernoulli_weighted_sum(exp(-(ubig_view(numer) as real / ubig_view(denom) as real)), e),
    ensures
        out_credit@@ =~= (Value { car: e(value) }),
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
            (Value { car: v } =~= slack_credit@);
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
            dist_credit@ =~= (Value { car: g_dist_eps }),
            slack_credit@ =~= (Value { car: g_slack_val }),
            g_dist_eps >= bernoulli_weighted_sum(g_pk, e),
            g_slack_val * slack_product(x, ubig_view(&k), g_depth) >= 1real,
        decreases g_depth,
    {
        let ghost kn = ubig_view(&k);

        proof {
            if g_depth == 0nat { ec_contradict(&slack_credit); }
        }

        let k_denom = ubig_mul(&k, &denom);
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

        k = ubig_succ(&k);
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
