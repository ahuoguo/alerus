use vstd::prelude::*;

verus! {

#[cfg(verus_keep_ghost)]
use crate::cks::discrete_laplace::*;
#[cfg(verus_keep_ghost)]
use crate::ec::*;
#[cfg(verus_keep_ghost)]
use crate::math::pow::pow;
#[cfg(verus_keep_ghost)]
use crate::math::series::*;
#[cfg(verus_keep_ghost)]
use crate::cks::geometric_exp::{geo_exp_series_bounded_by, geo_exp_partial_sum, geo_exp_summand};

/// DL decomposition identity (n ≥ 1):
///   (1+p) · dl_partial_sum(n) + (1-p) · e(0)
///     = geo_partial_sum(e_pos, n) + geo_partial_sum(e_neg_pure, n)
pub proof fn lemma_dl_decomposition(p: real, e: spec_fn(int) -> real, n: nat)
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
pub proof fn lemma_geo_neg_relate(p: real, e: spec_fn(int) -> real, rc: real, n: nat)
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
pub proof fn lemma_dl_joint_bound(p: real, e: spec_fn(int) -> real, dl_bound: real, rc: real, n: nat)
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
pub proof fn lemma_geo_partial_nonneg(p: real, f: spec_fn(nat) -> real, n: nat)
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
pub proof fn lemma_partial_sum_eq_geo(p: real, f: spec_fn(nat) -> real, n: nat)
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
pub proof fn lemma_dl_credit_split(
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

pub proof fn lemma_zero_dl_bound(p: real, e: spec_fn(int) -> real, n: nat)
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
