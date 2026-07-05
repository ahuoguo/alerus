//! Sample from Bernoulli(exp(-x)) for x ≥ 0.
//!
//! Decomposes x = floor(x) + frac(x), then:
//!   1. Sample floor(x) independent Bernoulli(exp(-1)).
//!   2. If all are true, sample Bernoulli(exp(-frac(x))).
//!   3. Return false if any Bernoulli(exp(-1)) is false.
//!
//! Since exp(-x) = exp(-1)^floor(x) · exp(-frac(x)), the output
//! is Bernoulli(exp(-x)).
//!
//! We prove the following Expectation Preservation Rule
//!
//! ```text
//!   ε ≥ exp(-x) · ℰ(true) + (1 - exp(-x)) · ℰ(false)
//!   ---------------------------------------------------
//!   [{ ↯(ε) }] sample_bernoulli_exp(x) [{ v. ↯(ℰ(v)) }]
//! ```

use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::calc_macro::*;

use random::{UBig, ubig_sub, ubig_is_zero};

verus! {

use crate::ec::*;
#[cfg(verus_keep_ghost)]
use crate::cks::bernoulli_rational::{bernoulli_weighted_sum, lemma_bws_nonneg};
use crate::cks::bernoulli_exp1::{sample_bernoulli_exp1, sample_bernoulli_exp1_ubig};
#[cfg(verus_keep_ghost)]
use crate::math::exp::{exp, axiom_exp_neg_range, axiom_exp_add, lemma_exp_decompose, axiom_exp_zero};
#[cfg(verus_keep_ghost)]
use crate::extern_spec::ubig_view;
use crate::extern_spec::ubig_lt;

/// Credit allocation for the Bernoulli(exp(-1)) flip at each iteration.
/// heads: continue with bws(prob_remaining, e)
/// tails: e(false)
pub open spec fn exp_flip_e(
    prob_remaining: real,
    e: spec_fn(bool) -> real,
) -> spec_fn(bool) -> real {
    |b: bool| if b { bernoulli_weighted_sum(prob_remaining, e) } else { e(false) }
}

/// The Bernoulli(exp(-1)) flip average exactly consumes eps.
/// exp(-1) · bws(prob_rem, e) + (1-exp(-1)) · e(false) == bws(exp(-1)·prob_rem, e)
#[verifier::spinoff_prover]
proof fn lemma_exp_flip_average(
    prob_remaining: real,
    e: spec_fn(bool) -> real,
)
    ensures ({
        let p1 = exp(-1real);
        let flip_e = exp_flip_e(prob_remaining, e);
        bernoulli_weighted_sum(p1, flip_e) == bernoulli_weighted_sum(p1 * prob_remaining, e)
    }),
{
    let p1 = exp(-1real);
    let flip_e = exp_flip_e(prob_remaining, e);
    let et = e(true);
    let ef = e(false);
    let pr = prob_remaining;

    // Unfold spec fns
    assert(flip_e(true) == pr * et + (1real - pr) * ef);
    assert(flip_e(false) == ef);

    // Unfold bws on both sides
    assert(bernoulli_weighted_sum(p1, flip_e)
        == p1 * flip_e(true) + (1real - p1) * flip_e(false));
    assert(bernoulli_weighted_sum(p1 * pr, e)
        == (p1 * pr) * et + (1real - p1 * pr) * ef);

    // Walk through the algebra step by step
    calc! {
        (==)
        bernoulli_weighted_sum(p1, flip_e); {}
        p1 * flip_e(true) + (1real - p1) * flip_e(false); {}
        p1 * (pr * et + (1real - pr) * ef) + (1real - p1) * ef; {
            // distribute p1 into the sum
            assert(p1 * (pr * et + (1real - pr) * ef)
                == p1 * pr * et + p1 * (1real - pr) * ef)
                by(nonlinear_arith);
        }
        p1 * pr * et + p1 * (1real - pr) * ef + (1real - p1) * ef; {
            // combine the ef terms: p1·(1-pr)·ef + (1-p1)·ef = (1 - p1·pr)·ef
            assert(p1 * (1real - pr) * ef + (1real - p1) * ef
                == (1real - p1 * pr) * ef)
                by(nonlinear_arith);
        }
        p1 * pr * et + (1real - p1 * pr) * ef; {
            // associativity: p1*pr*et == (p1*pr)*et
            assert(p1 * pr * et == (p1 * pr) * et)
                by(nonlinear_arith);
        }
        (p1 * pr) * et + (1real - p1 * pr) * ef; {}
        bernoulli_weighted_sum(p1 * pr, e);
    }
}

// ============================================================================
// Sampler
// ============================================================================

/// Sample from Bernoulli(exp(-x)) where x = numer_x/denom_x ≥ 0.
///
/// While x > 1: flip Bernoulli(exp(-1)). If false, return false. Else x -= 1.
/// Then flip Bernoulli(exp(-frac(x))) via sample_bernoulli_exp1.
pub fn sample_bernoulli_exp(
    numer_x: u64,
    denom_x: u64,
    Ghost(e): Ghost<spec_fn(bool) -> real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(eps): Ghost<real>,
) -> ((value, out_credit): (bool, Tracked<ErrorCreditResource>))
    requires
        denom_x > 0,
        0real <= exp(-(numer_x as real / denom_x as real)) <= 1real,
        e(true) >= 0real,
        e(false) >= 0real,
        eps >= 0real,
        input_credit@ =~= (ErrorCreditCarrier::Value { car: eps }),
        eps >= bernoulli_weighted_sum(exp(-(numer_x as real / denom_x as real)), e),
    ensures
        out_credit@@ =~= (ErrorCreditCarrier::Value { car: e(value) }),
{
    let mut remaining_numer = numer_x;
    let ghost mut g_prob = exp(-(numer_x as real / denom_x as real));
    let ghost mut g_eps = eps;
    let tracked mut credit = input_credit;

    // While x > 1: flip Bernoulli(exp(-1)). If false, return false.
    while remaining_numer > denom_x
        invariant
            denom_x > 0,
            e(true) >= 0real,
            e(false) >= 0real,
            remaining_numer <= numer_x,
            g_prob == exp(-(remaining_numer as real / denom_x as real)),
            0real <= g_prob <= 1real,
            credit@ =~= (ErrorCreditCarrier::Value { car: g_eps }),
            g_eps >= bernoulli_weighted_sum(g_prob, e),
        decreases remaining_numer as int,
    {
        let ghost p1 = exp(-1real);
        let ghost prob_remaining = exp(-((remaining_numer - denom_x) as real / denom_x as real));

        let ghost flip_e = exp_flip_e(prob_remaining, e);

        proof {
            // exp(-x) = exp(-1) · exp(-(x-1))
            lemma_exp_decompose(remaining_numer, denom_x);
            // So g_prob == p1 · prob_remaining

            // exp(-1) ∈ (0, 1]
            axiom_exp_neg_range(1real);
            // prob_remaining ∈ (0, 1]
            assert((remaining_numer - denom_x) as real / denom_x as real >= 0real)
                by(nonlinear_arith)
                requires remaining_numer > denom_x, denom_x > 0u64;
            axiom_exp_neg_range((remaining_numer - denom_x) as real / denom_x as real);

            // The flip average identity
            lemma_exp_flip_average(prob_remaining, e);
            // bws(p1, flip_e) == bws(g_prob, e) <= g_eps

            // g_eps >= bws(g_prob, e) >= 0
            lemma_bws_nonneg(g_prob, e);
            // bws(prob_remaining, e) >= 0  (needed for flip_e(true) >= 0)
            lemma_bws_nonneg(prob_remaining, e);

            // denom_x / denom_x == 1
            assert(denom_x as real / denom_x as real == 1real) by(nonlinear_arith)
                requires denom_x > 0u64;
            // So exp(-(denom_x/denom_x)) == exp(-1) == p1
            // boosted_eps >= g_eps >= bws(p1, flip_e)
            assert(g_eps >= bernoulli_weighted_sum(p1, flip_e));
        }

        // Flip Bernoulli(exp(-1)) using sample_bernoulli_exp1(denom_x, denom_x)
        let (heads, Tracked(out_credit)) = sample_bernoulli_exp1(
            denom_x,
            denom_x,
            Ghost(flip_e),
            Tracked(credit),
            Ghost(g_eps),
        );

        if !heads {
            // Tails: return false. out_credit has value flip_e(false) = e(false).
            return (false, Tracked(out_credit));
        }

        // Heads: out_credit has value flip_e(true) = bws(prob_remaining, e).
        remaining_numer = remaining_numer - denom_x;
        proof {
            g_prob = prob_remaining;
            g_eps = bernoulli_weighted_sum(prob_remaining, e);
            credit = out_credit;
        }
    }

    // Now remaining_numer <= denom_x, so frac ∈ [0, 1].
    // Flip Bernoulli(exp(-frac)) to get final result.

    // TODO: i think you can also pass this to sample_bernoulli_exp1 
    // after fixing the precondition of sample_bernoulli_exp1, but that will complicated
    // the amplifcation factor reasoning...
    if remaining_numer == 0 {
        // exp(0) = 1, so Bernoulli(1) = always true.
        // g_eps >= bws(exp(0), e) = bws(1, e) = e(true).
        // Need to return credit with value e(true).
        // credit has value g_eps >= e(true), so split off e(true).
        proof {
            axiom_exp_zero(); // exp(0) = 1
            assert(remaining_numer as real / denom_x as real == 0real) by(nonlinear_arith)
                requires remaining_numer == 0u64, denom_x > 0u64;
            // g_prob == exp(0) == 1, bws(1, e) = 1·e(T) + 0·e(F) = e(T)
            // So g_eps >= bws(1, e) = e(true), hence leftover >= 0
            assert(bernoulli_weighted_sum(1real, e) == e(true)) by(nonlinear_arith)
                requires bernoulli_weighted_sum(1real, e) == 1real * e(true) + (1real - 1real) * e(false);
        }
        let ghost leftover = g_eps - e(true);
        let tracked (ret_credit, _discard) = ec_split(credit, e(true), leftover);
        return (true, Tracked(ret_credit));
    }

    // 0 < remaining_numer <= denom_x, so frac ∈ (0, 1].
    proof { lemma_bws_nonneg(g_prob, e); } // g_eps >= bws(g_prob, e) >= 0

    sample_bernoulli_exp1(
        remaining_numer,
        denom_x,
        Ghost(e),
        Tracked(credit),
        Ghost(g_eps),
    )
}

/// exp(−(num/den)) = exp(−1) · exp(−((num−den)/den))  for num > den > 0.
/// (Bignum analogue of `lemma_exp_decompose`, proved inline via `axiom_exp_add`.)
proof fn lemma_exp_decompose_ubig(num: nat, den: nat)
    requires den > 0, num > den,
    ensures
        exp(-(num as real / den as real))
            == exp(-1real) * exp(-((num - den) as real / den as real)),
{
    let frac = (num - den) as real / den as real;
    assert(frac >= 0real) by(nonlinear_arith)
        requires frac == (num - den) as real / den as real, den > 0, num > den;
    axiom_exp_add(1real, frac);
    // 1 + (num−den)/den == num/den
    assert(1real + frac == num as real / den as real) by(nonlinear_arith)
        requires frac == (num - den) as real / den as real, den > 0, num > den;
}

/// Bignum variant of [`sample_bernoulli_exp`]: Bernoulli(exp(−x)) for x ≥ 0 with
/// x = numer/denom given as arbitrary-precision `UBig`s.  Same expectation
/// preservation rule.  The exp(−1) flips reuse the u64 `sample_bernoulli_exp1(1,1)`;
/// the final fractional flip uses `sample_bernoulli_exp1_ubig`.
pub fn sample_bernoulli_exp_ubig(
    numer: &UBig,
    denom: &UBig,
    Ghost(e): Ghost<spec_fn(bool) -> real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(eps): Ghost<real>,
) -> ((value, out_credit): (bool, Tracked<ErrorCreditResource>))
    requires
        ubig_view(denom) > 0,
        e(true) >= 0real,
        e(false) >= 0real,
        eps >= 0real,
        input_credit@ =~= (ErrorCreditCarrier::Value { car: eps }),
        eps >= bernoulli_weighted_sum(exp(-(ubig_view(numer) as real / ubig_view(denom) as real)), e),
    ensures
        out_credit@@ =~= (ErrorCreditCarrier::Value { car: e(value) }),
{
    let ghost dv = ubig_view(denom);
    let mut remaining = numer.clone();
    let ghost mut g_prob = exp(-(ubig_view(numer) as real / dv as real));
    let ghost mut g_eps = eps;
    let tracked mut credit = input_credit;

    proof {
        assert(ubig_view(numer) as real / dv as real >= 0real) by(nonlinear_arith)
            requires dv > 0;
        axiom_exp_neg_range(ubig_view(numer) as real / dv as real);
    }

    // While x > 1 (remaining > denom): flip Bernoulli(exp(−1)); tails ⇒ false.
    while ubig_lt(denom, &remaining)
        invariant
            dv == ubig_view(denom), dv > 0,
            e(true) >= 0real,
            e(false) >= 0real,
            g_prob == exp(-(ubig_view(&remaining) as real / dv as real)),
            0real <= g_prob <= 1real,
            credit@ =~= (ErrorCreditCarrier::Value { car: g_eps }),
            g_eps >= bernoulli_weighted_sum(g_prob, e),
        decreases ubig_view(&remaining),
    {
        let ghost rv = ubig_view(&remaining);
        let ghost p1 = exp(-1real);
        let ghost prob_remaining = exp(-((rv - dv) as real / dv as real));
        let ghost flip_e = exp_flip_e(prob_remaining, e);

        proof {
            // g_prob == exp(−1) · prob_remaining
            lemma_exp_decompose_ubig(rv, dv);
            axiom_exp_neg_range(1real);
            assert((rv - dv) as real / dv as real >= 0real) by(nonlinear_arith)
                requires rv > dv, dv > 0;
            axiom_exp_neg_range((rv - dv) as real / dv as real);
            lemma_exp_flip_average(prob_remaining, e);
            lemma_bws_nonneg(g_prob, e);
            lemma_bws_nonneg(prob_remaining, e);
            // bws(exp(−1), flip_e) == bws(g_prob, e) <= g_eps
            assert(g_eps >= bernoulli_weighted_sum(p1, flip_e));
        }

        // Bernoulli(exp(−1)) via the u64 sampler at (1, 1).
        let (heads, Tracked(out_credit)) = sample_bernoulli_exp1(
            1u64, 1u64, Ghost(flip_e), Tracked(credit), Ghost(g_eps),
        );

        if !heads {
            return (false, Tracked(out_credit));
        }

        let new_remaining = ubig_sub(&remaining, denom);
        proof {
            assert(ubig_view(&new_remaining) == rv - dv);
            g_prob = prob_remaining;
            g_eps = bernoulli_weighted_sum(prob_remaining, e);
            credit = out_credit;
        }
        remaining = new_remaining;
    }

    // Now remaining ≤ denom, so frac = remaining/denom ∈ [0, 1].
    let is_zero = ubig_is_zero(&remaining);
    if is_zero {
        // exp(0) = 1, so Bernoulli(1) is deterministically true; split off e(true).
        proof {
            axiom_exp_zero();
            assert(ubig_view(&remaining) as real / dv as real == 0real) by(nonlinear_arith)
                requires ubig_view(&remaining) == 0, dv > 0;
            assert(bernoulli_weighted_sum(1real, e) == e(true)) by(nonlinear_arith)
                requires bernoulli_weighted_sum(1real, e) == 1real * e(true) + (1real - 1real) * e(false);
        }
        let ghost leftover = g_eps - e(true);
        let tracked (ret_credit, _discard) = ec_split(credit, e(true), leftover);
        return (true, Tracked(ret_credit));
    }

    // 0 < remaining ≤ denom.
    proof { lemma_bws_nonneg(g_prob, e); }

    sample_bernoulli_exp1_ubig(
        &remaining,
        denom,
        Ghost(e),
        Tracked(credit),
        Ghost(g_eps),
    )
}

} // verus!
