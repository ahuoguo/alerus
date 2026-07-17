use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use vstd::calc_macro::*;

verus! {

#[cfg(verus_keep_ghost)]
use crate::cks::bernoulli_exp::*;
#[cfg(verus_keep_ghost)]
use crate::ec::*;
#[cfg(verus_keep_ghost)]
use crate::cks::bernoulli_rational::bernoulli_weighted_sum;
#[cfg(verus_keep_ghost)]
use crate::math::exp::{exp, axiom_exp_add, lemma_exp_decompose};

/// The Bernoulli(exp(-1)) flip average exactly consumes eps.
/// exp(-1) · bws(prob_rem, e) + (1-exp(-1)) · e(false) == bws(exp(-1)·prob_rem, e)
#[verifier::spinoff_prover]
pub proof fn lemma_exp_flip_average(
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

/// exp(−(num/den)) = exp(−1) · exp(−((num−den)/den))  for num > den > 0.
/// (Bignum analogue of `lemma_exp_decompose`, proved inline via `axiom_exp_add`.)
pub proof fn lemma_exp_decompose_ubig(num: nat, den: nat)
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

} // verus!
