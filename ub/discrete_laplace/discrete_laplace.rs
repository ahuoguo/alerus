// Sample from the Discrete Laplace distribution DL(0, scale).
//
// From CKS20: sample sign ∈ {+, -} uniformly, then sample magnitude
// from Geometric(1 - exp(-1/scale)). Reject (-, 0) to avoid double-counting zero.
//
// Let p = exp(-1/scale). and:
//   P[0]  = (1 - p) / (1 + p)
//   P[+k] = P[-k] = p^k · (1 - p) / (1 + p)   for k ≥ 1
//
// We prove the following Expectation Preservation Rule
//
//   ε ≥ Σ_{x=-∞}^{∞} P[x] · ℰ(x)
//   --------------------------------
//   [{ ↯(ε) }] sample_discrete_laplace(scale) [{ v. ↯(ℰ(v)) }]

use vstd::prelude::*;

use random::{IBig, ubig_from_u64, ibig_from_ubig, ibig_neg, ibig_is_zero, RBig, rbig_into_parts, ibig_abs};
#[cfg(verus_keep_ghost)]
use random::UBig;

verus! {

use crate::ub::*;
#[cfg(verus_keep_ghost)]
use crate::math::pow::{pow, archimedean_exp_growth};
#[cfg(verus_keep_ghost)]
use crate::math::real::real_assoc_mult;
#[cfg(verus_keep_ghost)]
use crate::math::series::*;
#[cfg(verus_keep_ghost)]
use crate::math::exp::{exp, axiom_exp_neg_range, axiom_exp_neg_strict};
use crate::rand_primitives::thin_air;
#[cfg(verus_keep_ghost)]
use crate::discrete_laplace::bernoulli_rational::bernoulli_weighted_sum;
use crate::discrete_laplace::bernoulli_rational::sample_bernoulli_rational;
use crate::discrete_laplace::geometric_exp::sample_geometric_exp;
use crate::discrete_laplace::geometric_exp_fast::sample_geometric_exp_fast;
#[cfg(verus_keep_ghost)]
use crate::discrete_laplace::geometric_exp::{geo_exp_series_bounded_by, geo_exp_partial_sum, geo_exp_summand};
#[cfg(verus_keep_ghost)]
use crate::extern_spec::{ExUBig, ExIBig, ExRBig, ubig_view, ibig_view, rbig_view};

/// Summand for |x| = k ≥ 1: P[+k]·ℰ(+k) + P[-k]·ℰ(-k).
pub open spec fn dl_symmetric_summand(p: real, e: spec_fn(int) -> real, k: nat) -> real {
    pow(p, k) * (1real - p) / (1real + p) * (e(k as int) + e(-(k as int)))
}

/// Summand for x = 0: P[0] · ℰ(0) = (1 - p)/(1 + p) · ℰ(0).
pub open spec fn dl_zero_summand(p: real, e: spec_fn(int) -> real) -> real {
    (1real - p) / (1real + p) * e(0int)
}

/// Partial sum over |x| < n.
pub open spec fn dl_partial_sum(p: real, e: spec_fn(int) -> real, n: nat) -> real
    decreases n,
{
    if n == 0 { 0real }
    else if n == 1 { dl_zero_summand(p, e) }
    else { dl_partial_sum(p, e, (n - 1) as nat) + dl_symmetric_summand(p, e, (n - 1) as nat) }
}

/// The series is bounded: ∀n. bound ≥ partial_sum(n).
pub open spec fn dl_series_bounded_by(p: real, e: spec_fn(int) -> real, bound: real) -> bool {
    forall |n: nat| bound >= #[trigger] dl_partial_sum(p, e, n)
}

/// Positive-branch postcondition: e_pos(k) = ℰ(+k).
pub open spec fn dl_e_pos(e: spec_fn(int) -> real) -> spec_fn(nat) -> real {
    |k: nat| e(k as int)
}

/// Negative-branch postcondition: e_neg(0) = retry_credit, e_neg(k) = ℰ(-k) for k ≥ 1.
pub open spec fn dl_e_neg(e: spec_fn(int) -> real, retry_credit: real) -> spec_fn(nat) -> real {
    |k: nat| if k == 0 { retry_credit } else { e(-(k as int)) }
}

/// Pure negative postcondition: e_neg_pure(k) = ℰ(-k).
pub open spec fn dl_e_neg_pure(e: spec_fn(int) -> real) -> spec_fn(nat) -> real {
    |k: nat| e(-(k as int))
}

/// DL decomposition identity (n ≥ 1):
///   (1+p) · dl_partial_sum(n) + (1-p) · e(0)
///     = geo_partial_sum(e_pos, n) + geo_partial_sum(e_neg_pure, n)
proof fn lemma_dl_decomposition(p: real, e: spec_fn(int) -> real, n: nat)
    requires n >= 1, 0real < p,
    ensures
        (1real + p) * dl_partial_sum(p, e, n) + (1real - p) * e(0int)
            == geo_exp_partial_sum(p, dl_e_pos(e), n)
             + geo_exp_partial_sum(p, dl_e_neg_pure(e), n),
    decreases n,
{
    let e_pos = dl_e_pos(e);
    let e_neg = dl_e_neg_pure(e);
    if n == 1 {
        assert(pow(p, 0nat) == 1real);
        assert(e_pos(0nat) == e(0int));
        assert(e_neg(0nat) == e(0int));
        assert((1real + p) * dl_partial_sum(p, e, 1nat) + (1real - p) * e(0int)
            == geo_exp_partial_sum(p, e_pos, 1nat) + geo_exp_partial_sum(p, e_neg, 1nat))
            by(nonlinear_arith)
            requires
                dl_partial_sum(p, e, 1nat) == (1real - p) / (1real + p) * e(0int),
                geo_exp_partial_sum(p, e_pos, 1nat)
                    == geo_exp_partial_sum(p, e_pos, 0nat) + geo_exp_summand(p, e_pos, 0nat),
                geo_exp_partial_sum(p, e_neg, 1nat)
                    == geo_exp_partial_sum(p, e_neg, 0nat) + geo_exp_summand(p, e_neg, 0nat),
                geo_exp_summand(p, e_pos, 0nat) == pow(p, 0nat) * (1real - p) * e(0int),
                geo_exp_summand(p, e_neg, 0nat) == pow(p, 0nat) * (1real - p) * e(0int),
                pow(p, 0nat) == 1real,
                p > 0real;
    } else {
        lemma_dl_decomposition(p, e, (n - 1) as nat);
        let k = (n - 1) as nat;
        assert(e_pos(k) == e(k as int));
        assert(e_neg(k) == e(-(k as int)));
        assert((1real + p) * dl_symmetric_summand(p, e, k)
            == geo_exp_summand(p, e_pos, k) + geo_exp_summand(p, e_neg, k))
            by(nonlinear_arith)
            requires
                dl_symmetric_summand(p, e, k) == pow(p, k) * (1real - p) / (1real + p) * (e(k as int) + e(-(k as int))),
                geo_exp_summand(p, e_pos, k) == pow(p, k) * (1real - p) * e(k as int),
                geo_exp_summand(p, e_neg, k) == pow(p, k) * (1real - p) * e(-(k as int)),
                p > 0real;
        assert((1real + p) * dl_partial_sum(p, e, n) + (1real - p) * e(0int)
            == geo_exp_partial_sum(p, e_pos, n) + geo_exp_partial_sum(p, e_neg, n))
            by(nonlinear_arith)
            requires
                (1real + p) * dl_partial_sum(p, e, k) + (1real - p) * e(0int)
                    == geo_exp_partial_sum(p, e_pos, k) + geo_exp_partial_sum(p, e_neg, k),
                dl_partial_sum(p, e, n) == dl_partial_sum(p, e, k) + dl_symmetric_summand(p, e, k),
                geo_exp_partial_sum(p, e_pos, n) == geo_exp_partial_sum(p, e_pos, k) + geo_exp_summand(p, e_pos, k),
                geo_exp_partial_sum(p, e_neg, n) == geo_exp_partial_sum(p, e_neg, k) + geo_exp_summand(p, e_neg, k),
                (1real + p) * dl_symmetric_summand(p, e, k) == geo_exp_summand(p, e_pos, k) + geo_exp_summand(p, e_neg, k);
    }
}

/// Relate geo(e_neg(retry), n) to geo(e_neg_pure, n):
///   geo(e_neg(rc), n) = geo(e_neg_pure, n) + (1-p)·rc - (1-p)·e(0)  for n ≥ 1
proof fn lemma_geo_neg_relate(p: real, e: spec_fn(int) -> real, rc: real, n: nat)
    requires n >= 1,
    ensures
        geo_exp_partial_sum(p, dl_e_neg(e, rc), n)
            == geo_exp_partial_sum(p, dl_e_neg_pure(e), n)
             + (1real - p) * rc - (1real - p) * e(0int),
    decreases n,
{
    let e_neg = dl_e_neg(e, rc);
    let e_neg_pure = dl_e_neg_pure(e);
    if n == 1 {
        assert(pow(p, 0nat) == 1real);
        assert(e_neg(0nat) == rc);
        assert(e_neg_pure(0nat) == e(0int));
        // Unfold: geo(f, 1) = geo(f, 0) + summand(f, 0) = 0 + summand(f, 0)
        let gn = geo_exp_partial_sum(p, e_neg, 1nat);
        let gnp = geo_exp_partial_sum(p, e_neg_pure, 1nat);
        assert(gn == geo_exp_partial_sum(p, e_neg, 0nat) + geo_exp_summand(p, e_neg, 0nat));
        assert(gnp == geo_exp_partial_sum(p, e_neg_pure, 0nat) + geo_exp_summand(p, e_neg_pure, 0nat));
        assert(gn == geo_exp_summand(p, e_neg, 0nat));
        assert(gnp == geo_exp_summand(p, e_neg_pure, 0nat));
        assert(gn == gnp + (1real - p) * rc - (1real - p) * e(0int))
            by(nonlinear_arith)
            requires
                gn == pow(p, 0nat) * (1real - p) * rc,
                gnp == pow(p, 0nat) * (1real - p) * e(0int),
                pow(p, 0nat) == 1real;
    } else {
        lemma_geo_neg_relate(p, e, rc, (n - 1) as nat);
        let k = (n - 1) as nat;
        assert(e_neg(k) == e_neg_pure(k));
        assert(geo_exp_summand(p, e_neg, k) == geo_exp_summand(p, e_neg_pure, k));
    }
}

/// Joint bound: A_n + geo(e_neg(rc), n) ≤ (1+p)·dl_bound + (1-p)·rc  for all n.
proof fn lemma_dl_joint_bound(p: real, e: spec_fn(int) -> real, dl_bound: real, rc: real, n: nat)
    requires
        0real < p < 1real,
        forall |x: int| (#[trigger] e(x)) >= 0real,
        dl_series_bounded_by(p, e, dl_bound),
        rc >= 0real,
    ensures
        geo_exp_partial_sum(p, dl_e_pos(e), n)
        + geo_exp_partial_sum(p, dl_e_neg(e, rc), n)
        <= (1real + p) * dl_bound + (1real - p) * rc,
{
    if n == 0 {
        assert((1real + p) * dl_bound + (1real - p) * rc >= 0real) by(nonlinear_arith)
            requires 0real < p < 1real, dl_bound >= dl_partial_sum(p, e, 0nat),
                dl_partial_sum(p, e, 0nat) == 0real, rc >= 0real;
    } else {
        lemma_dl_decomposition(p, e, n);
        lemma_geo_neg_relate(p, e, rc, n);
        assert(geo_exp_partial_sum(p, dl_e_pos(e), n)
            + geo_exp_partial_sum(p, dl_e_neg(e, rc), n)
            <= (1real + p) * dl_bound + (1real - p) * rc)
            by(nonlinear_arith)
            requires
                (1real + p) * dl_partial_sum(p, e, n) + (1real - p) * e(0int)
                    == geo_exp_partial_sum(p, dl_e_pos(e), n)
                     + geo_exp_partial_sum(p, dl_e_neg_pure(e), n),
                dl_bound >= dl_partial_sum(p, e, n),
                geo_exp_partial_sum(p, dl_e_neg(e, rc), n)
                    == geo_exp_partial_sum(p, dl_e_neg_pure(e), n)
                     + (1real - p) * rc - (1real - p) * e(0int),
                e(0int) >= 0real,
                0real < p < 1real,
                rc >= 0real;
    }
}

/// geo_exp_partial_sum(p, f, n) ≥ 0 when f(k) ≥ 0 and 0 < p < 1.
proof fn lemma_geo_partial_nonneg(p: real, f: spec_fn(nat) -> real, n: nat)
    requires
        0real < p < 1real,
        forall |k: nat| (#[trigger] f(k)) >= 0real,
    ensures
        geo_exp_partial_sum(p, f, n) >= 0real,
    decreases n,
{
    if n > 0 {
        lemma_geo_partial_nonneg(p, f, (n - 1) as nat);
        let k = (n - 1) as nat;
        lemma_pow_nonneg(p, k);
        assert(geo_exp_summand(p, f, k) >= 0real) by(nonlinear_arith)
            requires pow(p, k) >= 0real, f(k) >= 0real,
                geo_exp_summand(p, f, k) == pow(p, k) * (1real - p) * f(k),
                0real < p < 1real;
    }
}

/// partial_sum of geo_exp_summands equals geo_exp_partial_sum.
proof fn lemma_partial_sum_eq_geo(p: real, f: spec_fn(nat) -> real, n: nat)
    ensures partial_sum(|k: nat| geo_exp_summand(p, f, k), n) == geo_exp_partial_sum(p, f, n),
    decreases n,
{
    if n > 0 {
        lemma_partial_sum_eq_geo(p, f, (n - 1) as nat);
    }
}

/// Credit split for the discrete Laplace sampler.
///
/// The DL sampler draws a sign and then a magnitude from Geometric(1-p).
/// The positive branch needs geo_exp_series_bounded_by(p, e_pos, pos_bound)
/// and the negative branch needs geo_exp_series_bounded_by(p, e_neg(rc), neg_bound),
/// where e_pos(k) = ℰ(+k), e_neg(0) = retry_credit rc, e_neg(k) = ℰ(-k) for k ≥ 1.
///
/// This lemma derives those two bounds from the single DL series bound.
///
/// Proof Sketch:
///   -  Rewrite each geo partial sum in terms of the DL partial sum via
///      lemma_dl_decomposition and lemma_geo_neg_relate:
///        A_n(pos) + A_n(neg) ≤ (1+p)·dl_bound + (1-p)·rc ≤ 2·total
///      Since both are non-negative, each is individually ≤ 2·total.
///
///   -  Both series have non-negative terms, so their partial sums are
///      non-decreasing and bounded → summable (lemma_bounded_series_summable).
///
///   -  Take the limits pos_limit and neg_limit. Since partial sums are
///      non-decreasing and converge, each limit is an upper bound on all
///      partial sums (lemma_monotone_limit_upper_bound).
///
///   -  Show pos_limit + neg_limit ≤ 2·total by taking the limit of the
///      averaged sequence (A_n(pos) + A_n(neg))/2 ≤ total, then applying
///      lemma_limit_le_bound.
///
///   -  Witness pos_bound = pos_limit, neg_bound = neg_limit.
proof fn lemma_dl_credit_split(
    p: real,
    e: spec_fn(int) -> real,
    dl_bound: real,
    rc: real,
    total: real,
)
    requires
        0real < p < 1real,
        forall |x: int| (#[trigger] e(x)) >= 0real,
        dl_series_bounded_by(p, e, dl_bound),
        rc >= 0real,
        total > 0real,
        (1real + p) * dl_bound + (1real - p) * rc <= 2real * total,
    ensures
        exists |pos_bound: real, neg_bound: real| {
            &&& pos_bound >= 0real
            &&& neg_bound >= 0real
            &&& pos_bound + neg_bound <= 2real * total
            &&& geo_exp_series_bounded_by(p, dl_e_pos(e), pos_bound)
            &&& geo_exp_series_bounded_by(p, dl_e_neg(e, rc), neg_bound)
        },
{
    let e_pos = dl_e_pos(e);
    let e_neg = dl_e_neg(e, rc);
    let s_pos = |k: nat| geo_exp_summand(p, e_pos, k);
    let s_neg = |k: nat| geo_exp_summand(p, e_neg, k);

    // Non-negative terms
    assert forall |n: nat| #[trigger] seq_at(s_pos, n) >= 0real by {
        lemma_pow_nonneg(p, n);
        assert(e_pos(n) == e(n as int));
        assert(e(n as int) >= 0real);
        assert(s_pos(n) >= 0real) by(nonlinear_arith)
            requires pow(p, n) >= 0real, e_pos(n) >= 0real,
                s_pos(n) == pow(p, n) * (1real - p) * e_pos(n), 0real < p < 1real;
    };
    assert forall |n: nat| #[trigger] seq_at(s_neg, n) >= 0real by {
        lemma_pow_nonneg(p, n);
        if n == 0 { assert(e_neg(0nat) == rc); }
        else { assert(e_neg(n) == e(-(n as int))); assert(e(-(n as int)) >= 0real); }
        assert(s_neg(n) >= 0real) by(nonlinear_arith)
            requires pow(p, n) >= 0real, e_neg(n) >= 0real,
                s_neg(n) == pow(p, n) * (1real - p) * e_neg(n), 0real < p < 1real;
    };

    // Both bounded by 2·total (from joint bound + non-negativity of the other)
    assert(partial_sums_bounded_by(s_pos, 2real * total)) by {
        assert forall |n: nat| 2real * total >= #[trigger] partial_sum(s_pos, n) by {
            lemma_partial_sum_eq_geo(p, e_pos, n);
            lemma_dl_joint_bound(p, e, dl_bound, rc, n);
            assert forall |k: nat| (#[trigger] e_neg(k)) >= 0real by {
                if k == 0 {} else { assert(e(-(k as int)) >= 0real); }
            };
            lemma_geo_partial_nonneg(p, e_neg, n);
        };
    };
    assert(partial_sums_bounded_by(s_neg, 2real * total)) by {
        assert forall |n: nat| 2real * total >= #[trigger] partial_sum(s_neg, n) by {
            lemma_partial_sum_eq_geo(p, e_neg, n);
            lemma_dl_joint_bound(p, e, dl_bound, rc, n);
            assert forall |k: nat| (#[trigger] e_pos(k)) >= 0real by {
                assert(e(k as int) >= 0real);
            };
            lemma_geo_partial_nonneg(p, e_pos, n);
        };
    };

    // Both converge
    lemma_bounded_series_summable(s_pos, 2real * total);
    lemma_bounded_series_summable(s_neg, 2real * total);
    let pos_limit: real = choose |l: real| sums_to(s_pos, l);
    let neg_limit: real = choose |l: real| sums_to(s_neg, l);

    // Limits are upper bounds on partial sums
    lemma_partial_sums_nondecreasing(s_pos);
    lemma_partial_sums_nondecreasing(s_neg);
    lemma_monotone_limit_upper_bound(partial_sum_seq(s_pos), pos_limit);
    lemma_monotone_limit_upper_bound(partial_sum_seq(s_neg), neg_limit);

    // pos_limit + neg_limit ≤ 2·total (via average)
    lemma_limit_average(partial_sum_seq(s_pos), partial_sum_seq(s_neg), pos_limit, neg_limit);
    let avg = |n: nat| (seq_at(partial_sum_seq(s_pos), n) + seq_at(partial_sum_seq(s_neg), n)) / 2real;
    assert(is_bounded_above(avg, total)) by {
        assert forall |n: nat| #[trigger] seq_at(avg, n) <= total by {
            lemma_partial_sum_eq_geo(p, e_pos, n);
            lemma_partial_sum_eq_geo(p, e_neg, n);
            lemma_dl_joint_bound(p, e, dl_bound, rc, n);
            assert(seq_at(avg, n) <= total) by(nonlinear_arith)
                requires
                    seq_at(avg, n) == (partial_sum(s_pos, n) + partial_sum(s_neg, n)) / 2real,
                    partial_sum(s_pos, n) == geo_exp_partial_sum(p, e_pos, n),
                    partial_sum(s_neg, n) == geo_exp_partial_sum(p, e_neg, n),
                    geo_exp_partial_sum(p, e_pos, n) + geo_exp_partial_sum(p, e_neg, n)
                        <= (1real + p) * dl_bound + (1real - p) * rc,
                    (1real + p) * dl_bound + (1real - p) * rc <= 2real * total;
        };
    };
    lemma_limit_le_bound(avg, (pos_limit + neg_limit) / 2real, total);

    // Limits ≥ 0
    assert(pos_limit >= 0real) by {
        assert(seq_at(partial_sum_seq(s_pos), 0nat) <= pos_limit);
    };
    assert(neg_limit >= 0real) by {
        assert(seq_at(partial_sum_seq(s_neg), 0nat) <= neg_limit);
    };

    // Limits bound the series
    assert(geo_exp_series_bounded_by(p, e_pos, pos_limit)) by {
        assert forall |n: nat| pos_limit >= #[trigger] geo_exp_partial_sum(p, e_pos, n) by {
            lemma_partial_sum_eq_geo(p, e_pos, n);
            assert(seq_at(partial_sum_seq(s_pos), n) <= pos_limit);
        };
    };
    assert(geo_exp_series_bounded_by(p, e_neg, neg_limit)) by {
        assert forall |n: nat| neg_limit >= #[trigger] geo_exp_partial_sum(p, e_neg, n) by {
            lemma_partial_sum_eq_geo(p, e_neg, n);
            assert(seq_at(partial_sum_seq(s_neg), n) <= neg_limit);
        };
    };

    assert(pos_limit + neg_limit <= 2real * total) by(nonlinear_arith)
        requires (pos_limit + neg_limit) / 2real <= total;
}

/// Associativity: a * (b * c) == (a * b) * c.
/// Sample from Discrete Laplace DL(0, scale) where 1/scale = inv_numer/inv_denom.
pub fn sample_discrete_laplace(
    inv_numer: u64,
    inv_denom: u64,
    Ghost(p): Ghost<real>,
    Ghost(e): Ghost<spec_fn(int) -> real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(eps): Ghost<real>,
) -> (ret: (IBig, Tracked<ErrorCreditResource>))
    requires
        inv_numer > 0,
        inv_denom > 0,
        0real < p < 1real,
        p == exp(-(inv_numer as real / inv_denom as real)),
        forall |x: int| (#[trigger] e(x)) >= 0real,
        eps > 0real,
        input_credit.view() =~= (ErrorCreditCarrier::Value { car: eps }),
        dl_series_bounded_by(p, e, eps),
    ensures
        ret.1@.view() =~= (ErrorCreditCarrier::Value { car: e(ibig_view(&ret.0)) }),
{
    // Get slack for termination
    let Tracked(slack_credit) = thin_air();
    let ghost slack: real;
    let ghost depth: nat;
    proof {
        slack = choose |v: real| v > 0real &&
            (ErrorCreditCarrier::Value { car: v } =~= slack_credit.view());
        archimedean_exp_growth(slack, 2real);
        depth = choose |k: nat| slack * #[trigger] pow(2real, k) >= 1real;
    }

    let ghost g_total = eps + slack;
    let tracked combined = ec_combine(input_credit, slack_credit, eps, slack);

    let tracked mut credit = combined;
    let ghost mut g_eps = eps;
    let ghost mut g_slack = slack;
    let ghost mut g_depth = depth;

    loop
        invariant
            inv_numer > 0,
            inv_denom > 0,
            0real < p < 1real,
            p == exp(-(inv_numer as real / inv_denom as real)),
            forall |x: int| (#[trigger] e(x)) >= 0real,
            g_eps > 0real,
            g_slack > 0real,
            credit.view() =~= (ErrorCreditCarrier::Value { car: g_eps + g_slack }),
            dl_series_bounded_by(p, e, g_eps),
            g_slack * pow(2real, g_depth) >= 1real,
        decreases g_depth,
    {
        proof {
            if g_depth == 0nat {
                assert(pow(2real, 0nat) == 1real);
                // g_slack >= 1, so g_eps + g_slack >= 1
                ec_contradict(&credit);
            }
        }

        let ghost sign_total = g_eps + g_slack;

        // Retry credit on rejection: g_eps + 2·g_slack (slack doubles)
        let ghost rc = g_eps + 2real * g_slack;

        // Credit split
        proof {
            // Joint bound: (1+p)·g_eps + (1-p)·rc ≤ 2·sign_total
            // = (1+p)·g_eps + (1-p)·(g_eps + 2·g_slack)
            // = 2·g_eps + 2(1-p)·g_slack ≤ 2·g_eps + 2·g_slack = 2·sign_total
            assert((1real + p) * g_eps + (1real - p) * rc <= 2real * sign_total)
                by(nonlinear_arith)
                requires
                    rc == g_eps + 2real * g_slack,
                    sign_total == g_eps + g_slack,
                    0real < p < 1real,
                    g_slack > 0real;
            assert(sign_total > 0real) by(nonlinear_arith)
                requires g_eps > 0real, g_slack > 0real, sign_total == g_eps + g_slack;
            lemma_dl_credit_split(p, e, g_eps, rc, sign_total);
        }

        let ghost pos_bound: real;
        let ghost neg_bound: real;
        proof {
            let pair: (real, real) = choose |pb: real, nb: real| {
                &&& pb >= 0real
                &&& nb >= 0real
                &&& pb + nb <= 2real * sign_total
                &&& geo_exp_series_bounded_by(p, dl_e_pos(e), pb)
                &&& geo_exp_series_bounded_by(p, dl_e_neg(e, rc), nb)
            };
            pos_bound = pair.0;
            neg_bound = pair.1;
        }

        let ghost sign_e: spec_fn(bool) -> real = |b: bool| if b { pos_bound } else { neg_bound };

        proof {
            assert(bernoulli_weighted_sum(0.5real, sign_e)
                == 0.5real * pos_bound + 0.5real * neg_bound);
            assert(sign_total >= bernoulli_weighted_sum(0.5real, sign_e))
                by(nonlinear_arith)
                requires
                    bernoulli_weighted_sum(0.5real, sign_e) == 0.5real * pos_bound + 0.5real * neg_bound,
                    pos_bound + neg_bound <= 2real * sign_total;
        }

        // Step 1: Flip sign
        let one = ubig_from_u64(1u64);
        let two = ubig_from_u64(2u64);
        let (positive, Tracked(branch_credit)) = sample_bernoulli_rational(
            &one,
            &two,
            Ghost(sign_e),
            Tracked(credit),
            Ghost(sign_total),
        );

        if positive {
            // Step 2a: Geometric with positive postcondition
            let ghost e_pos = dl_e_pos(e);

            let (magnitude, Tracked(out_credit)) = sample_geometric_exp(
                inv_numer,
                inv_denom,
                Ghost(p),
                Ghost(e_pos),
                Tracked(branch_credit),
                Ghost(pos_bound),
            );

            // +magnitude as IBig
            let result = ibig_from_ubig(magnitude);
            return (result, Tracked(out_credit));
        } else {
            // Step 2b: Geometric with negative postcondition
            let ghost e_neg = dl_e_neg(e, rc);

            let (magnitude, Tracked(out_credit)) = sample_geometric_exp(
                inv_numer,
                inv_denom,
                Ghost(p),
                Ghost(e_neg),
                Tracked(branch_credit),
                Ghost(neg_bound),
            );

            let mag_ibig = ibig_from_ubig(magnitude);
            let is_zero = ibig_is_zero(&mag_ibig);

            if !is_zero {
                // Accept: return -magnitude
                let result = ibig_neg(mag_ibig);
                proof {
                    // ibig_view(&result) == -ibig_view(&mag_ibig) == -(ubig_view(&magnitude) as int)
                    // e_neg(ubig_view(&magnitude)) == e(-(ubig_view(&magnitude) as int)) since ubig_view != 0
                    // and e(-(ubig_view(&magnitude) as int)) == e(ibig_view(&result))
                    assert(ibig_view(&mag_ibig) == ubig_view(&magnitude) as int);
                    assert(ibig_view(&mag_ibig) != 0int);
                    assert(ubig_view(&magnitude) != 0nat);
                }
                return (result, Tracked(out_credit));
            }

            // Rejected (-, 0): out_credit has value e_neg(0) = rc = g_eps + 2·g_slack
            proof {
                let old_slack = g_slack;
                let old_depth = g_depth;

                // is_zero == true implies ubig_view(&magnitude) == 0
                assert(ibig_view(&mag_ibig) == ubig_view(&magnitude) as int);
                assert(ibig_view(&mag_ibig) == 0int);
                assert(ubig_view(&magnitude) == 0nat);
                // out_credit.value = e_neg(0) = rc = g_eps + 2·old_slack
                assert(dl_e_neg(e, rc)(0nat) == rc);
                assert(rc == g_eps + 2real * old_slack);

                credit = out_credit;
                g_slack = 2real * old_slack;
                g_depth = (old_depth - 1) as nat;

                // credit.value = rc = g_eps + 2·old_slack = g_eps + g_slack
                assert(g_eps + g_slack == rc);

                // Termination: g_slack * pow(2, g_depth) >= 1
                assert(pow(2real, old_depth) == 2real * pow(2real, (old_depth - 1) as nat));
                real_assoc_mult(old_slack, 2real, pow(2real, (old_depth - 1) as nat));
            }
        }
    }
}

/// Fast variant of [`sample_discrete_laplace`] taking an arbitrary-precision
/// rational `scale` (matching opendp's `sample_discrete_laplace(scale: RBig)`):
/// identical Hoare rule and proof, but draws each magnitude with
/// `sample_geometric_exp_fast` instead of the slow `sample_geometric_exp`.
/// The credit-split machinery (`lemma_dl_credit_split` etc.) is reused verbatim.
///
///   p = e^{−1/scale};  scale = sn/sd, so 1/scale = sd/sn and the fast geometric
///   sampler is fed numerator `sd`, denominator `sn`.
pub fn sample_discrete_laplace_fast(
    scale: &RBig,
    Ghost(p): Ghost<real>,
    Ghost(e): Ghost<spec_fn(int) -> real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(eps): Ghost<real>,
) -> (ret: (IBig, Tracked<ErrorCreditResource>))
    requires
        rbig_view(scale) > 0real,
        0real < p < 1real,
        p == exp(-(1real / rbig_view(scale))),
        forall |x: int| (#[trigger] e(x)) >= 0real,
        eps > 0real,
        input_credit.view() =~= (ErrorCreditCarrier::Value { car: eps }),
        dl_series_bounded_by(p, e, eps),
    ensures
        ret.1@.view() =~= (ErrorCreditCarrier::Value { car: e(ibig_view(&ret.0)) }),
{
    // scale = sn/sd (sn ≥ 1 since scale > 0, sd ≥ 1); 1/scale = sd/sn.
    let parts = rbig_into_parts(scale);
    let sn_signed = parts.0;
    let sd = parts.1;
    let sn = ibig_abs(&sn_signed);
    proof {
        // rbig_view(scale) = sn_signed / sd, denom sd > 0  (from rbig_into_parts).
        assert(rbig_view(scale) == ibig_view(&sn_signed) as real / ubig_view(&sd) as real);
        assert(ubig_view(&sd) > 0);
        assert(ibig_view(&sn_signed) > 0) by(nonlinear_arith)
            requires rbig_view(scale) == ibig_view(&sn_signed) as real / ubig_view(&sd) as real,
                rbig_view(scale) > 0real, ubig_view(&sd) > 0;
        // sn = |sn_signed| = sn_signed (≥ 0), so sn > 0.
        assert(ubig_view(&sn) as int == ibig_view(&sn_signed));   // ibig_abs, sn_signed ≥ 0
        assert(ubig_view(&sn) > 0);
        assert(rbig_view(scale) == ubig_view(&sn) as real / ubig_view(&sd) as real);
        // 1/scale = sd/sn, so p = e^{−1/scale} = e^{−sd/sn}.
        assert(1real / rbig_view(scale) == ubig_view(&sd) as real / ubig_view(&sn) as real)
            by(nonlinear_arith)
            requires rbig_view(scale) == ubig_view(&sn) as real / ubig_view(&sd) as real,
                ubig_view(&sn) > 0, ubig_view(&sd) > 0;
        assert(p == exp(-(ubig_view(&sd) as real / ubig_view(&sn) as real)));
    }

    // Get slack for termination
    let Tracked(slack_credit) = thin_air();
    let ghost slack: real;
    let ghost depth: nat;
    proof {
        slack = choose |v: real| v > 0real &&
            (ErrorCreditCarrier::Value { car: v } =~= slack_credit.view());
        archimedean_exp_growth(slack, 2real);
        depth = choose |k: nat| slack * #[trigger] pow(2real, k) >= 1real;
    }

    let tracked combined = ec_combine(input_credit, slack_credit, eps, slack);

    let tracked mut credit = combined;
    let ghost mut g_eps = eps;
    let ghost mut g_slack = slack;
    let ghost mut g_depth = depth;

    loop
        invariant
            ubig_view(&sn) > 0,
            ubig_view(&sd) > 0,
            0real < p < 1real,
            p == exp(-(ubig_view(&sd) as real / ubig_view(&sn) as real)),
            forall |x: int| (#[trigger] e(x)) >= 0real,
            g_eps > 0real,
            g_slack > 0real,
            credit.view() =~= (ErrorCreditCarrier::Value { car: g_eps + g_slack }),
            dl_series_bounded_by(p, e, g_eps),
            g_slack * pow(2real, g_depth) >= 1real,
        decreases g_depth,
    {
        proof {
            if g_depth == 0nat {
                assert(pow(2real, 0nat) == 1real);
                ec_contradict(&credit);
            }
        }

        let ghost sign_total = g_eps + g_slack;
        let ghost rc = g_eps + 2real * g_slack;

        // Credit split (shared with the slow variant).
        proof {
            assert((1real + p) * g_eps + (1real - p) * rc <= 2real * sign_total)
                by(nonlinear_arith)
                requires
                    rc == g_eps + 2real * g_slack,
                    sign_total == g_eps + g_slack,
                    0real < p < 1real,
                    g_slack > 0real;
            assert(sign_total > 0real) by(nonlinear_arith)
                requires g_eps > 0real, g_slack > 0real, sign_total == g_eps + g_slack;
            lemma_dl_credit_split(p, e, g_eps, rc, sign_total);
        }

        let ghost pos_bound: real;
        let ghost neg_bound: real;
        proof {
            let pair: (real, real) = choose |pb: real, nb: real| {
                &&& pb >= 0real
                &&& nb >= 0real
                &&& pb + nb <= 2real * sign_total
                &&& geo_exp_series_bounded_by(p, dl_e_pos(e), pb)
                &&& geo_exp_series_bounded_by(p, dl_e_neg(e, rc), nb)
            };
            pos_bound = pair.0;
            neg_bound = pair.1;
        }

        let ghost sign_e: spec_fn(bool) -> real = |b: bool| if b { pos_bound } else { neg_bound };

        proof {
            assert(bernoulli_weighted_sum(0.5real, sign_e)
                == 0.5real * pos_bound + 0.5real * neg_bound);
            assert(sign_total >= bernoulli_weighted_sum(0.5real, sign_e))
                by(nonlinear_arith)
                requires
                    bernoulli_weighted_sum(0.5real, sign_e) == 0.5real * pos_bound + 0.5real * neg_bound,
                    pos_bound + neg_bound <= 2real * sign_total;
        }

        // Step 1: Flip sign
        let one = ubig_from_u64(1u64);
        let two = ubig_from_u64(2u64);
        let (positive, Tracked(branch_credit)) = sample_bernoulli_rational(
            &one,
            &two,
            Ghost(sign_e),
            Tracked(credit),
            Ghost(sign_total),
        );

        if positive {
            // Step 2a: fast Geometric with positive postcondition
            let ghost e_pos = dl_e_pos(e);

            let (magnitude, Tracked(out_credit)) = sample_geometric_exp_fast(
                &sd,
                &sn,
                Ghost(p),
                Ghost(e_pos),
                Tracked(branch_credit),
                Ghost(pos_bound),
            );

            let result = ibig_from_ubig(magnitude);
            return (result, Tracked(out_credit));
        } else {
            // Step 2b: fast Geometric with negative postcondition
            let ghost e_neg = dl_e_neg(e, rc);

            let (magnitude, Tracked(out_credit)) = sample_geometric_exp_fast(
                &sd,
                &sn,
                Ghost(p),
                Ghost(e_neg),
                Tracked(branch_credit),
                Ghost(neg_bound),
            );

            let mag_ibig = ibig_from_ubig(magnitude);
            let is_zero = ibig_is_zero(&mag_ibig);

            if !is_zero {
                // Accept: return -magnitude
                let result = ibig_neg(mag_ibig);
                proof {
                    assert(ibig_view(&mag_ibig) == ubig_view(&magnitude) as int);
                    assert(ibig_view(&mag_ibig) != 0int);
                    assert(ubig_view(&magnitude) != 0nat);
                }
                return (result, Tracked(out_credit));
            }

            // Rejected (-, 0): amplify slack and retry.
            proof {
                let old_slack = g_slack;
                let old_depth = g_depth;

                assert(ibig_view(&mag_ibig) == ubig_view(&magnitude) as int);
                assert(ibig_view(&mag_ibig) == 0int);
                assert(ubig_view(&magnitude) == 0nat);
                assert(dl_e_neg(e, rc)(0nat) == rc);
                assert(rc == g_eps + 2real * old_slack);

                credit = out_credit;
                g_slack = 2real * old_slack;
                g_depth = (old_depth - 1) as nat;

                assert(g_eps + g_slack == rc);
                assert(pow(2real, old_depth) == 2real * pow(2real, (old_depth - 1) as nat));
                real_assoc_mult(old_slack, 2real, pow(2real, (old_depth - 1) as nat));
            }
        }
    }
}

/// Entry point: sample from Discrete Laplace with no preconditions.
pub fn sample_discrete_laplace_entry(
    scale_numer: u64,
    scale_denom: u64,
) -> (ret: IBig)
    requires
        scale_numer > 0,
        scale_denom > 0,
{
    let ghost p = exp(-(scale_denom as real / scale_numer as real));
    let ghost e: spec_fn(int) -> real = |_x: int| 0real;
    let Tracked(cred) = thin_air();

    let ghost eps: real;
    proof {
        eps = choose |v: real| v > 0real &&
            (ErrorCreditCarrier::Value { car: v } =~= cred.view());
        assert(scale_denom as real / scale_numer as real > 0real) by(nonlinear_arith)
            requires scale_denom > 0u64, scale_numer > 0u64;
        axiom_exp_neg_range(scale_denom as real / scale_numer as real);
        axiom_exp_neg_strict(scale_denom as real / scale_numer as real);
        assert forall |n: nat| eps >= #[trigger] dl_partial_sum(p, e, n) by {
            lemma_zero_dl_bound(p, e, n);
        };
    }

    let (v, _out) = sample_discrete_laplace(
        scale_denom,
        scale_numer,
        Ghost(p),
        Ghost(e),
        Tracked(cred),
        Ghost(eps),
    );
    v
}

proof fn lemma_zero_dl_bound(p: real, e: spec_fn(int) -> real, n: nat)
    requires forall |x: int| (#[trigger] e(x)) == 0real,
    ensures dl_partial_sum(p, e, n) == 0real,
    decreases n,
{
    if n == 0 {
    } else if n == 1 {
        assert(e(0int) == 0real);
        assert(dl_zero_summand(p, e) == 0real) by(nonlinear_arith)
            requires dl_zero_summand(p, e) == (1real - p) / (1real + p) * 0real;
    } else {
        lemma_zero_dl_bound(p, e, (n - 1) as nat);
        let k = (n - 1) as nat;
        assert(e(k as int) == 0real);
        assert(e(-(k as int)) == 0real);
        assert(dl_symmetric_summand(p, e, k) == 0real) by(nonlinear_arith)
            requires dl_symmetric_summand(p, e, k)
                == pow(p, k) * (1real - p) / (1real + p) * (0real + 0real);
    }
}

} // verus!
