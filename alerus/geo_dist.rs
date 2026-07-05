//! Geometric Distribution with BigNums and Distributional Spec.
//!
//! This extends geo.rs with:
//! 1. dashu UBig for unbounded output (geo.rs uses u64 with wrapping_add)
//! 2. A distribution credit via the expectation rule:
//! https://github.com/logsem/clutch/blob/cpp26-distributions/theories/eris/lib/sampling/geometric/implementation.v#L109-L116
//!
//! ```text
//!   ε ≥ Σ_{i=0}^∞ (1/2)^(i+1) * ℰ(i)
//!   ------------------------------------
//!   [{ ↯(ε) }] geo() [{ v. ↯(ℰ(v)) }]
//! ```
//!
//! The weight (1/2)^(i+1) is the probability of outcome i (i tails then heads).
//! After geo() returns v, we own error credit ℰ(v).
//!
//! The input credit ε is split into two parts:
//! - Distribution credit (ε - slack): covers the geometric series Σ (1/2)^(i+1) * ℰ(i)
//! - Slack credit: reserved for termination, doubles at each recursive step
//!
//! Representing infinite sums in Verus:
//! We express "ε ≥ Σ_{i=0}^∞ (1/2)^(i+1) * ℰ(i)" as a universal bound over all
//! finite partial sums: ∀ n. ε ≥ Σ_{i=0}^{n-1} (1/2)^(i+1) * ℰ(i).

use vstd::prelude::*;
use random::{UBig, ubig_zero, ubig_succ};
#[cfg(verus_keep_ghost)]
use random::ubig_add;

verus! {

use crate::ec::*;
use crate::rand_primitives::{rand_2_u64, thin_air};
#[cfg(verus_keep_ghost)]
use crate::math::pow::{pow, archimedean_exp_growth};
#[cfg(verus_keep_ghost)]
use crate::math::real::real_assoc_mult;
#[cfg(verus_keep_ghost)]
use crate::math::series::*;
#[cfg(verus_keep_ghost)]
use crate::extern_spec::ExUBig;
#[cfg(verus_keep_ghost)]
use crate::extern_spec::ubig_view;

/// Credit allocation: outcome 0 → ℰ(0), outcome 1 → 2ε - ℰ(0).
spec fn geo_dist_credit_alloc(e: spec_fn(nat) -> real, eps: real) -> spec_fn(real) -> real {
    |outcome: real|
        if outcome == 0real {
            e(0nat)
        } else {
            2real * eps - e(0nat)
        }
}

/// Bounded geometric distribution sampler.
/// ε = (ε - slack) + slack: series bound + termination credit.
/// On recursion: new_ε = 2ε - ℰ(0), new_slack = 2·slack.
pub fn bounded_geo_dist(
    Ghost(e): Ghost<spec_fn(nat) -> real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(depth): Ghost<nat>,
    Ghost(eps): Ghost<real>,
    Ghost(slack): Ghost<real>,
) -> ((value, out_credit): (UBig, Tracked<ErrorCreditResource>))
    requires
        forall |i: nat| (#[trigger] e(i)) >= 0real,
        eps > 0real,
        slack > 0real,
        input_credit.view() =~= (ErrorCreditCarrier::Value { car: eps }),
        geo_series_bounded_by(e, eps - slack),
        slack * pow(2real, depth) >= 1real,
    ensures
        out_credit@.view() =~= (ErrorCreditCarrier::Value { car: e(ubig_view(&value)) }),
    decreases depth,
{
    proof {
        if depth == 0nat {
            assert(pow(2real, 0nat) == 1real);
            assert(partial_sum(geo_summands(e), 0nat) == 0real);
            ec_contradict(&input_credit);
        }

        // Unfold partial_sum(1) = 0.5·e(0) to establish eps ≥ 0.5·e(0)
        assert(pow(0.5real, 0nat) == 1real);
        assert(pow(0.5real, 1nat) == 0.5real) by(nonlinear_arith)
            requires pow(0.5real, 1nat) == 0.5real * pow(0.5real, 0nat),
                pow(0.5real, 0nat) == 1real;
        assert(geo_summands(e)(0nat) == pow(0.5real, 1nat) * e(0nat));
        assert(partial_sum(geo_summands(e), 1nat) ==
            partial_sum(geo_summands(e), 0nat) + geo_summands(e)(0nat));
    }

    let ghost credit_alloc = geo_dist_credit_alloc(e, eps);

    let (val, Tracked(outcome_credit)) = rand_2_u64(
        Tracked(input_credit),
        Ghost(credit_alloc),
    );

    if val == 0 {
        let ret = ubig_zero();
        (ret, Tracked(outcome_credit))
    } else {
        let ghost new_eps = 2real * eps - e(0nat);
        let ghost new_slack = 2real * slack;

        proof {
            lemma_shift_bound(e, eps, slack);
            real_assoc_mult(slack, 2real, pow(2real, (depth - 1) as nat));
        }
        
        let (rest, output_credit) = bounded_geo_dist(
            Ghost(shift_e(e)),
            Tracked(outcome_credit),
            Ghost((depth - 1) as nat),
            Ghost(new_eps),
            Ghost(new_slack),
        );

        let result = ubig_succ(&rest);
        (result, output_credit)
    }
}

pub fn unbounded_geo_dist(
    Ghost(e): Ghost<spec_fn(nat) -> real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(dist_bound): Ghost<real>,
) -> ((value, out_credit): (UBig, Tracked<ErrorCreditResource>))
    requires
        forall |i: nat| (#[trigger] e(i)) >= 0real,
        dist_bound >= 0real,
        input_credit.view() =~= (ErrorCreditCarrier::Value { car: dist_bound }),
        geo_series_bounded_by(e, dist_bound),
    ensures
        out_credit@.view() =~= (ErrorCreditCarrier::Value { car: e(ubig_view(&value)) }),
{
    let Tracked(slack_credit) = thin_air();

    let ghost slack: real;
    let ghost depth: nat;

    proof {
        slack = choose |v: real| v > 0real &&
            (ErrorCreditCarrier::Value { car: v } =~= slack_credit.view());
        archimedean_exp_growth(slack, 2real);
        depth = choose |k: nat| slack * pow(2real, k) >= 1real;
    }

    let ghost eps = dist_bound + slack;
    let tracked combined: ErrorCreditResource;
    proof {
        combined = ec_combine(input_credit, slack_credit, dist_bound, slack);
    }
    bounded_geo_dist(
        Ghost(e),
        Tracked(combined),
        Ghost(depth),
        Ghost(eps),
        Ghost(slack),
    )
}

proof fn lemma_geo_dist_average(e: spec_fn(nat) -> real, eps: real)
    requires
        eps > 0real,
        2real * eps >= e(0nat),
    ensures
        eps >= (geo_dist_credit_alloc(e, eps)(0real)
              + geo_dist_credit_alloc(e, eps)(1real)) / 2real,
{}

/// ℰ(v) = 0 if v == 0, else 1. Series = 0.5.
pub open spec fn credit_nonzero() -> spec_fn(nat) -> real {
    |v: nat| if v == 0 { 0real } else { 1real }
}

/// 0.5 credits -> v == 0.
pub fn example_geo_must_be_zero(
    Tracked(credit): Tracked<ErrorCreditResource>,
) -> (ret: UBig)
    requires
        credit.view() =~= (ErrorCreditCarrier::Value { car: 0.5real }),
    ensures
        ubig_view(&ret) == 0,
{
    let ghost e = credit_nonzero();

    proof {
        assert forall |n: nat| 0.5real >= #[trigger] partial_sum(geo_summands(e), n) by {
            lemma_must_zero_bound(n);
        };
    }

    let (v, Tracked(out_credit)) = unbounded_geo_dist(
        Ghost(e),
        Tracked(credit),
        Ghost(0.5real),
    );

    proof {
        if ubig_view(&v) != 0 {
            ec_contradict(&out_credit);
        }
    }

    v
}

proof fn lemma_pow_half_small()
    ensures
        pow(0.5real, 0nat) == 1real,
        pow(0.5real, 1nat) == 0.5real,
        pow(0.5real, 2nat) == 0.25real,
        pow(0.5real, 3nat) == 0.125real,
{
    assert(pow(0.5real, 1nat) == 0.5real) by(nonlinear_arith)
        requires pow(0.5real, 1nat) == 0.5real * pow(0.5real, 0nat),
            pow(0.5real, 0nat) == 1real;
    assert(pow(0.5real, 2nat) == 0.25real) by(nonlinear_arith)
        requires pow(0.5real, 2nat) == 0.5real * pow(0.5real, 1nat),
            pow(0.5real, 1nat) == 0.5real;
    assert(pow(0.5real, 3nat) == 0.125real) by(nonlinear_arith)
        requires pow(0.5real, 3nat) == 0.5real * pow(0.5real, 2nat),
            pow(0.5real, 2nat) == 0.25real;
}

proof fn lemma_zero_term(s: spec_fn(nat) -> real, k: nat)
    requires s(k) == 0real,
    ensures geo_summands(s)(k) == 0real,
{
    lemma_pow_nonneg(0.5real, k + 1);
    assert(geo_summands(s)(k) == 0real) by(nonlinear_arith)
        requires geo_summands(s)(k) == pow(0.5real, k + 1) * 0real;
}

/// 0 + 1/4 + 1/8 + ... ≤ 0.5 (term 0 is zero, rest are (1/2)^(i+1)).
proof fn lemma_must_zero_bound(n: nat)
    ensures
        0.5real >= partial_sum(geo_summands(credit_nonzero()), n),
{
    let e = credit_nonzero();
    let s = geo_summands(e);
    if n == 0 {
    } else if n == 1 {
        lemma_zero_term(e, 0nat);
        assert(partial_sum(s, 1nat) == partial_sum(s, 0nat) + s(0nat));
    } else {
        lemma_must_zero_tight(n);
        lemma_pow_nonneg(0.5real, n);
    }
}

proof fn lemma_must_zero_tight(n: nat)
    requires n >= 1,
    ensures
        partial_sum(geo_summands(credit_nonzero()), n) + pow(0.5real, n) <= 0.5real,
    decreases n,
{
    let e = credit_nonzero();
    let s = geo_summands(e);
    if n == 1 {
        lemma_zero_term(e, 0nat);
        assert(partial_sum(s, 1nat) == partial_sum(s, 0nat) + s(0nat));
        lemma_pow_half_small();
    } else {
        lemma_must_zero_tight((n - 1) as nat);
        let k = (n - 1) as nat;
        assert(partial_sum(s, n) + pow(0.5real, n) == partial_sum(s, k) + pow(0.5real, k))
            by(nonlinear_arith)
            requires
                partial_sum(s, n) == partial_sum(s, k) + s(k),
                s(k) == pow(0.5real, k + 1) * 1real,
                pow(0.5real, k + 1) == 0.5real * pow(0.5real, k),
                pow(0.5real, n) == 0.5real * pow(0.5real, k);
    }
}

/// ℰ(v) = 0 if v ≤ 1, else 1. Series = 0.25.
pub open spec fn credit_above_one() -> spec_fn(nat) -> real {
    |v: nat| if v <= 1 { 0real } else { 1real }
}

/// 0.25 credits -> v ≤ 1.
pub fn example_geo_tail_bound(
    Tracked(credit): Tracked<ErrorCreditResource>,
) -> (ret: UBig)
    requires
        credit.view() =~= (ErrorCreditCarrier::Value { car: 0.25real }),
    ensures
        ubig_view(&ret) <= 1,
{
    let ghost e = credit_above_one();

    proof {
        assert forall |n: nat| 0.25real >= #[trigger] partial_sum(geo_summands(e), n) by {
            lemma_tail_bound(n);
        };
    }

    let (v, Tracked(out_credit)) = unbounded_geo_dist(
        Ghost(e),
        Tracked(credit),
        Ghost(0.25real),
    );

    proof {
        if ubig_view(&v) > 1 {
            ec_contradict(&out_credit);
        }
    }

    v
}

/// 0 + 0 + 1/8 + 1/16 + ... ≤ 0.25 (terms 0,1 are zero, rest are (1/2)^(i+1)).
proof fn lemma_tail_bound(n: nat)
    ensures
        0.25real >= partial_sum(geo_summands(credit_above_one()), n),
{
    let e = credit_above_one();
    let s = geo_summands(e);
    if n == 0 {
    } else if n == 1 {
        lemma_zero_term(e, 0nat);
        assert(partial_sum(s, 1nat) == partial_sum(s, 0nat) + s(0nat));
    } else if n == 2 {
        lemma_zero_term(e, 0nat);
        lemma_zero_term(e, 1nat);
        assert(partial_sum(s, 1nat) == partial_sum(s, 0nat) + s(0nat));
        assert(partial_sum(s, 2nat) == partial_sum(s, 1nat) + s(1nat));
    } else {
        lemma_tail_bound_tight(n);
        lemma_pow_nonneg(0.5real, n);
    }
}

proof fn lemma_tail_bound_tight(n: nat)
    requires n >= 2,
    ensures
        partial_sum(geo_summands(credit_above_one()), n) + pow(0.5real, n) <= 0.25real,
    decreases n,
{
    let e = credit_above_one();
    let s = geo_summands(e);
    if n == 2 {
        lemma_zero_term(e, 0nat);
        lemma_zero_term(e, 1nat);
        assert(partial_sum(s, 1nat) == partial_sum(s, 0nat) + s(0nat));
        assert(partial_sum(s, 2nat) == partial_sum(s, 1nat) + s(1nat));
        lemma_pow_half_small();
    } else {
        lemma_tail_bound_tight((n - 1) as nat);
        let k = (n - 1) as nat;
        assert(partial_sum(s, n) + pow(0.5real, n) == partial_sum(s, k) + pow(0.5real, k))
            by(nonlinear_arith)
            requires
                partial_sum(s, n) == partial_sum(s, k) + s(k),
                s(k) == pow(0.5real, k + 1) * 1real,
                pow(0.5real, k + 1) == 0.5real * pow(0.5real, k),
                pow(0.5real, n) == 0.5real * pow(0.5real, k);
    }
}

/// Sample from the geometric distribution (entry point, no preconditions).
pub fn geo_dist_sample() -> (ret: UBig)
{
    let ghost e: spec_fn(nat) -> real = |_v: nat| 0real;
    let Tracked(credit) = thin_air();

    proof {
        assert forall |n: nat| 0real >= #[trigger] partial_sum(geo_summands(e), n) by {
            lemma_zero_series_bound(e, n);
        };
    }

    let ghost dist_bound: real;
    proof {
        if credit.view().value() =~= None {} // OBSERVE
        dist_bound = choose |v: real| credit.view().value() == Some(v);
    }

    let (v, _out) = unbounded_geo_dist(
        Ghost(e),
        Tracked(credit),
        Ghost(dist_bound),
    );
    v
}

proof fn lemma_zero_series_bound(e: spec_fn(nat) -> real, n: nat)
    requires forall |i: nat| (#[trigger] e(i)) == 0real,
    ensures 0real >= partial_sum(geo_summands(e), n),
    decreases n,
{
    if n > 0 {
        lemma_zero_series_bound(e, (n - 1) as nat);
        lemma_zero_term(e, (n - 1) as nat);
    }
}

} // verus!
