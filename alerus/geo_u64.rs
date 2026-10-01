//! Geometric distribution with a concrete u64 counter and an approximate
//! distributional spec.
//!
//! ```text
//!   ε ≥ Σ_{i=0}^∞ (1/2)^(i+1) * ℰ(i)        ∀ i. 0 ≤ ℰ(i)
//!   ----------------------------------------------------
//!   [{ ↯(ε + εs) }] geo_u64() [{ v. ↯(ℰ(v)) }]
//!   where εs = (1/2)^(2^64)
//! ```
//!

use vstd::prelude::*;

verus! {

use crate::ec::*;
#[cfg(verus_keep_ghost)]
use crate::ec::ErrorCreditCarrier::Value;
use crate::rand_primitives::rand_2_u64;
#[cfg(verus_keep_ghost)]
use crate::math::pow::pow;
#[cfg(verus_keep_ghost)]
use crate::math::series::*;
#[cfg(verus_keep_ghost)]
use crate::geo_dist::{credit_nonzero, lemma_must_zero_bound};

/// εs: the probability that Geo(1/2) lands at or above 2^64, i.e. that the
/// counter would wrap.
pub open spec fn geo_u64_slack() -> real {
    pow(0.5real, u64::MAX as nat + 1)
}

/// ℰ shifted by k: i ↦ ℰ(i + k), the credit function after k tails.
pub open spec fn shift_by(e: spec_fn(nat) -> real, k: nat) -> spec_fn(nat) -> real {
    |i: nat| e(i + k)
}

/// Slack still held after k tails: εs · 2^k = (1/2)^(2^64 - k).
pub open spec fn slack_at(k: u64) -> real {
    pow(0.5real, (u64::MAX - k + 1) as nat)
}

/// Coin-flip allocation: heads (0) → ℰ(0), tails (1) → 2ε - ℰ(0).
spec fn geo_u64_credit_alloc(e: spec_fn(nat) -> real, eps: real) -> spec_fn(nat) -> real {
    |outcome: nat| if outcome == 0 { e(0nat) } else { 2real * eps - e(0nat) }
}

/// Geo(1/2) over u64, with a wrapping counter.
pub fn geo_u64(
    Ghost(e): Ghost<spec_fn(nat) -> real>,
    Ghost(dist_bound): Ghost<real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
) -> ((value, out_credit): (u64, Tracked<ErrorCreditResource>))
    requires
        forall |i: nat| (#[trigger] e(i)) >= 0real,
        geo_series_bounded_by(e, dist_bound),
        input_credit@ =~= (Value { car: dist_bound + geo_u64_slack() }),
    ensures
        out_credit@@ =~= (Value { car: e(value as nat) }),
{
    let mut k: u64 = 0;
    let tracked mut credit = input_credit;
    let ghost mut cur = dist_bound + geo_u64_slack();

    assert(shift_by(e, 0nat) =~= e);

    loop
        invariant
            forall |i: nat| (#[trigger] e(i)) >= 0real,
            credit@ =~= (Value { car: cur }),
            geo_series_bounded_by(shift_by(e, k as nat), cur - slack_at(k)),
        decreases u64::MAX - k,
    {
        let ghost ek = shift_by(e, k as nat);
        proof {
            lemma_pow_nonneg(0.5real, (u64::MAX - k + 1) as nat);
            // partial_sum(1) = 0.5·ℰ_k(0) ≤ cur - slack, so cur ≥ 0.5·ℰ_k(0) ≥ 0.
            assert(pow(0.5real, 0nat) == 1real);
            assert(pow(0.5real, 1nat) == 0.5real);
            assert(partial_sum(geo_summands(ek), 1nat) ==
                partial_sum(geo_summands(ek), 0nat) + geo_summands(ek)(0nat));
        }

        let ghost alloc = geo_u64_credit_alloc(ek, cur);
        let (b, Tracked(next)) = rand_2_u64(Tracked(credit), Ghost(alloc));

        if b == 0 {
            return (k, Tracked(next));
        }

        proof {
            lemma_shift_bound(ek, cur, slack_at(k));
            credit = next;
            cur = 2real * cur - ek(0nat);
            if k == u64::MAX {
                ec_contradict(&credit);
            }
            assert(shift_e(ek) =~= shift_by(e, (k + 1) as nat));
        }
        k = k.wrapping_add(1);
    }
}

/// Client example: with ↯(1/2 + εs), the sample must be 0.
/// Same as `geo_dist::example_geo_must_be_zero`, plus the u64 slack.
pub fn example_geo_u64_must_be_zero(
    Tracked(credit): Tracked<ErrorCreditResource>,
) -> (ret: u64)
    requires
        credit@ =~= (Value { car: 0.5real + geo_u64_slack() }),
    ensures
        ret == 0,
{
    let ghost e = credit_nonzero();
    proof {
        assert forall |n: nat| 0.5real >= #[trigger] partial_sum(geo_summands(e), n) by {
            lemma_must_zero_bound(n);
        };
    }

    let (v, Tracked(out_credit)) = geo_u64(Ghost(e), Ghost(0.5real), Tracked(credit));
    proof {
        if v != 0 {
            ec_contradict(&out_credit);
        }
    }
    v
}

} // verus!
