//! Sample from Bernoulli(p) for rational p = numer/denom.
//!
//! Implemented via: sample u ~ Uniform([0, denom)), return (numer > u).
//! This gives P[true] = numer/denom = p exactly.
//!
//! We prove the following Expectation Preservation Rule
//!
//! ```text
//!   ε ≥ p · ℰ(true) + (1 - p) · ℰ(false)
//!   ----------------------------------------
//!   [{ ↯(ε) }] sample_bernoulli_rational(numer, denom) [{ v. ↯(ℰ(v)) }]
//! ```
//!
//! See opendp correspondence in `sample_bernoulli_rational` in opendp/rust/src/traits/samplers/bernoulli/mod.rs.

use vstd::prelude::*;

use random::UBig;

verus! {

use crate::ec::*;
use crate::rand_primitives::rand_ubig;
#[cfg(verus_keep_ghost)]
use crate::rand_primitives::{average_nat, sum_credit};
use crate::extern_spec::ubig_lt;
#[cfg(verus_keep_ghost)]
use crate::extern_spec::ExUBig;
#[cfg(verus_keep_ghost)]
use crate::extern_spec::ubig_view;

/// Weighted sum for Bernoulli(p): p · ℰ(true) + (1 - p) · ℰ(false).
pub open spec fn bernoulli_weighted_sum(
    prob: real,
    e: spec_fn(bool) -> real,
) -> real {
    prob * e(true) + (1real - prob) * e(false)
}

/// bws(prob, e) >= 0 when prob ∈ [0, 1] and e >= 0.
pub proof fn lemma_bws_nonneg(prob: real, e: spec_fn(bool) -> real)
    requires 0real <= prob <= 1real, e(true) >= 0real, e(false) >= 0real,
    ensures bernoulli_weighted_sum(prob, e) >= 0real,
{
    assert(bernoulli_weighted_sum(prob, e) >= 0real) by(nonlinear_arith)
        requires 0real <= prob <= 1real, e(true) >= 0real, e(false) >= 0real,
            bernoulli_weighted_sum(prob, e) == prob * e(true) + (1real - prob) * e(false);
}

/// Credit allocation for the uniform sampler underlying Bernoulli(numer/denom):
///   outcome i < numer  → e(true)   (accepted: return true)
///   outcome i ≥ numer  → e(false)  (rejected: return false)
pub open spec fn bernoulli_credit_alloc(
    numer: nat,
    e: spec_fn(bool) -> real,
) -> spec_fn(real) -> real {
    |i: real| if i < numer as real { e(true) } else { e(false) }
}

/// Σ_{i<n} alloc(i) = numer·ℰ(true) + (n-numer)·ℰ(false)  when n ≥ numer,
///                   = n·ℰ(true)                            when n ≤ numer.
proof fn lemma_sum_bernoulli(numer: nat, e: spec_fn(bool) -> real, n: nat)
    ensures
        n <= numer ==>
            sum_credit(bernoulli_credit_alloc(numer, e), n) == n as real * e(true),
        n >= numer ==>
            sum_credit(bernoulli_credit_alloc(numer, e), n)
                == numer as real * e(true) + (n - numer) as real * e(false),
    decreases n,
{
    let alloc = bernoulli_credit_alloc(numer, e);
    if n == 0 {
        assert(0real == 0nat as real * e(true)) by(nonlinear_arith);
        assert(0real == 0nat as real * e(true) + 0nat as real * e(false)) by(nonlinear_arith);
    } else {
        lemma_sum_bernoulli(numer, e, (n - 1) as nat);
        let k = (n - 1) as nat;
        assert(sum_credit(alloc, n) == sum_credit(alloc, k) + alloc(k as real));
        if n <= numer {
            assert(sum_credit(alloc, n) == n as real * e(true))
                by(nonlinear_arith)
                requires
                    sum_credit(alloc, n) == sum_credit(alloc, k) + alloc(k as real),
                    sum_credit(alloc, k) == k as real * e(true),
                    alloc(k as real) == e(true),
                    n == k + 1;
        } else if k >= numer {
            assert(sum_credit(alloc, n) ==
                numer as real * e(true) + (n - numer) as real * e(false))
                by(nonlinear_arith)
                requires
                    sum_credit(alloc, n) == sum_credit(alloc, k) + alloc(k as real),
                    sum_credit(alloc, k) == numer as real * e(true)
                        + (k - numer) as real * e(false),
                    alloc(k as real) == e(false),
                    n == k + 1,
                    k >= numer;
        }
    }
}

proof fn lemma_bernoulli_average(numer: nat, denom: nat, e: spec_fn(bool) -> real)
    requires
        denom > 0,
        numer <= denom,
        e(true) >= 0real,
        e(false) >= 0real,
    ensures
        average_nat(denom, bernoulli_credit_alloc(numer, e))
            == bernoulli_weighted_sum(numer as real / denom as real, e),
{
    lemma_sum_bernoulli(numer, e, denom);
    let sum = sum_credit(bernoulli_credit_alloc(numer, e), denom);
    assert(average_nat(denom, bernoulli_credit_alloc(numer, e))
        == bernoulli_weighted_sum(numer as real / denom as real, e))
        by(nonlinear_arith)
        requires
            sum == numer as real * e(true)
                + (denom - numer) as real * e(false),
            average_nat(denom, bernoulli_credit_alloc(numer, e)) == sum / denom as real,
            denom > 0nat,
            numer <= denom;
}

/// Sample from Bernoulli(numer/denom) with distribution credit.
/// numer and denom are UBig for overflow-free arithmetic.
pub fn sample_bernoulli_rational(
    numer: &UBig,
    denom: &UBig,
    Ghost(e): Ghost<spec_fn(bool) -> real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(eps): Ghost<real>,
) -> ((value, out_credit): (bool, Tracked<ErrorCreditResource>))
    requires
        ubig_view(denom) > 0,
        ubig_view(numer) <= ubig_view(denom),
        e(true) >= 0real,
        e(false) >= 0real,
        eps > 0real,
        input_credit@ =~= (ErrorCreditCarrier::Value { car: eps }),
        eps >= bernoulli_weighted_sum(ubig_view(numer) as real / ubig_view(denom) as real, e),
    ensures
        out_credit@@ =~= (ErrorCreditCarrier::Value { car: e(value) }),
{
    let ghost nn = ubig_view(numer);
    let ghost dn = ubig_view(denom);
    let ghost alloc = bernoulli_credit_alloc(nn, e);

    proof {
        lemma_bernoulli_average(nn, dn, e);
        assert forall |i: nat| (#[trigger] alloc(i as real)) >= 0real by {
            if (i as real) < nn as real {} else {}
        };
    }

    let (val, Tracked(outcome_credit)) = rand_ubig(denom, Tracked(input_credit), Ghost(alloc));
    let ghost vn = ubig_view(&val);

    let result = ubig_lt(&val, numer);
    (result, Tracked(outcome_credit))
}

} // verus!
