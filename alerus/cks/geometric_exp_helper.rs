use vstd::prelude::*;

verus! {

#[cfg(verus_keep_ghost)]
use crate::cks::geometric_exp::*;
#[cfg(verus_keep_ghost)]
use crate::ec::*;
#[cfg(verus_keep_ghost)]
use crate::math::pow::pow;
#[cfg(verus_keep_ghost)]
use crate::math::series::shift_e;
#[cfg(verus_keep_ghost)]
use crate::cks::bernoulli_rational::bernoulli_weighted_sum;

/// The Bernoulli(p) flip weighted sum exactly equals eps.
pub proof fn lemma_geo_exp_flip_average(p: real, e: spec_fn(nat) -> real, eps: real)
    requires 0real < p,
    ensures
        bernoulli_weighted_sum(p, geo_exp_flip_e(p, e, eps)) == eps,
{
    let flip_e = geo_exp_flip_e(p, e, eps);
    assert(flip_e(true) == (eps - (1real - p) * e(0)) / p);
    assert(flip_e(false) == e(0));
    assert(bernoulli_weighted_sum(p, flip_e)
        == p * flip_e(true) + (1real - p) * flip_e(false));
    assert(p * flip_e(true) + (1real - p) * flip_e(false) == eps)
        by(nonlinear_arith)
        requires
            flip_e(true) == (eps - (1real - p) * e(0)) / p,
            flip_e(false) == e(0),
            p > 0real;
}

/// First-step decomposition:
///   geo_exp_partial_sum(p, e, n+1) = (1-p)·e(0) + p · geo_exp_partial_sum(p, shift_e(e), n)
pub proof fn lemma_geo_exp_first_step(p: real, e: spec_fn(nat) -> real, n: nat)
    ensures
        geo_exp_partial_sum(p, e, n + 1)
            == (1real - p) * e(0) + p * geo_exp_partial_sum(p, shift_e(e), n),
    decreases n,
{
    if n == 0 {
        assert(pow(p, 0nat) == 1real);
        assert(geo_exp_partial_sum(p, e, 1nat)
            == geo_exp_partial_sum(p, e, 0nat) + geo_exp_summand(p, e, 0nat));
        assert(geo_exp_summand(p, e, 0nat) == (1real - p) * e(0)) by(nonlinear_arith)
            requires geo_exp_summand(p, e, 0nat) == pow(p, 0nat) * (1real - p) * e(0),
                pow(p, 0nat) == 1real;
    } else {
        lemma_geo_exp_first_step(p, e, (n - 1) as nat);
        let k = (n - 1) as nat;
        assert(geo_exp_partial_sum(p, shift_e(e), n)
            == geo_exp_partial_sum(p, shift_e(e), k) + geo_exp_summand(p, shift_e(e), k));
        assert(shift_e(e)(k) == e(n));
        assert(pow(p, n) == p * pow(p, k));
        assert(geo_exp_summand(p, e, n) == p * geo_exp_summand(p, shift_e(e), k))
            by(nonlinear_arith)
            requires
                geo_exp_summand(p, e, n) == pow(p, n) * (1real - p) * e(n),
                geo_exp_summand(p, shift_e(e), k) == pow(p, k) * (1real - p) * shift_e(e)(k),
                shift_e(e)(k) == e(n),
                pow(p, n) == p * pow(p, k);
        assert(geo_exp_partial_sum(p, e, n + 1)
            == (1real - p) * e(0) + p * geo_exp_partial_sum(p, shift_e(e), n))
            by(nonlinear_arith)
            requires
                geo_exp_partial_sum(p, e, n + 1)
                    == geo_exp_partial_sum(p, e, n) + geo_exp_summand(p, e, n),
                geo_exp_partial_sum(p, e, n)
                    == (1real - p) * e(0) + p * geo_exp_partial_sum(p, shift_e(e), k),
                geo_exp_partial_sum(p, shift_e(e), n)
                    == geo_exp_partial_sum(p, shift_e(e), k) + geo_exp_summand(p, shift_e(e), k),
                geo_exp_summand(p, e, n) == p * geo_exp_summand(p, shift_e(e), k);
    }
}

/// Distribution bound transfers through one shift step.
pub proof fn lemma_geo_exp_shift_bound(
    p: real,
    e: spec_fn(nat) -> real,
    dist_bound: real,
)
    requires
        0real < p,
        forall |i: nat| (#[trigger] e(i)) >= 0real,
        geo_exp_series_bounded_by(p, e, dist_bound),
    ensures
        geo_exp_series_bounded_by(p, shift_e(e), (dist_bound - (1real - p) * e(0)) / p),
{
    assert forall |n: nat| ((dist_bound - (1real - p) * e(0)) / p)
        >= #[trigger] geo_exp_partial_sum(p, shift_e(e), n) by {
        lemma_geo_exp_first_step(p, e, n);
        assert(dist_bound >= geo_exp_partial_sum(p, e, n + 1));
        assert(((dist_bound - (1real - p) * e(0)) / p) >= geo_exp_partial_sum(p, shift_e(e), n))
            by(nonlinear_arith)
            requires
                geo_exp_partial_sum(p, e, n + 1)
                    == (1real - p) * e(0) + p * geo_exp_partial_sum(p, shift_e(e), n),
                dist_bound >= geo_exp_partial_sum(p, e, n + 1),
                e(0nat) >= 0real,
                p > 0real;
    };
}

/// flip_e(true) >= 0 when eps > (1-p)·e(0) and p > 0.
pub proof fn lemma_flip_true_nonneg(p: real, e: spec_fn(nat) -> real, eps: real)
    requires
        0real < p,
        eps > (1real - p) * e(0),
    ensures
        geo_exp_flip_e(p, e, eps)(true) >= 0real,
{
    assert(geo_exp_flip_e(p, e, eps)(true) >= 0real) by(nonlinear_arith)
        requires
            geo_exp_flip_e(p, e, eps)(true) == (eps - (1real - p) * e(0)) / p,
            eps > (1real - p) * e(0),
            p > 0real;
}

} // verus!
