//! Sample from Geometric(1 - exp(-x)) for x > 0.
//!
//! Loop: flip Bernoulli(exp(-x)). If true, increment k. If false, return k.
//! Output k has P[k] = p^k · (1 - p) where p = exp(-x).
//!
//! We prove the following Expectation Preservation Rule
//!
//! ```text
//!   ε ≥ Σ_{k=0}^∞ p^k · (1 - p) · ℰ(k)
//!   -------------------------------------------------
//!   [{ ↯(ε) }] sample_geometric_exp(x) [{ v. ↯(ℰ(v)) }]
//! ```

use vstd::prelude::*;

use random::{UBig, ubig_zero, ubig_succ};

verus! {

use crate::ec::*;
#[cfg(verus_keep_ghost)]
use crate::extern_spec::{ExUBig, ubig_view};
#[cfg(verus_keep_ghost)]
use crate::math::pow::{pow, archimedean_exp_growth};
#[cfg(verus_keep_ghost)]
use crate::math::real::real_assoc_mult;
#[cfg(verus_keep_ghost)]
use crate::math::series::shift_e;
#[cfg(verus_keep_ghost)]
use crate::math::exp::exp;
use crate::rand_primitives::thin_air;
use crate::cks::bernoulli_exp::sample_bernoulli_exp;
#[cfg(verus_keep_ghost)]
use crate::cks::bernoulli_rational::bernoulli_weighted_sum;

/// k-th summand of the geometric series: p^k · (1 - p) · ℰ(k).
pub open spec fn geo_exp_summand(p: real, e: spec_fn(nat) -> real, k: nat) -> real {
    pow(p, k) * (1real - p) * e(k)
}

/// Partial sum: Σ_{i<n} p^i · (1 - p) · ℰ(i).
pub open spec fn geo_exp_partial_sum(p: real, e: spec_fn(nat) -> real, n: nat) -> real
    decreases n,
{
    if n == 0 { 0real }
    else { geo_exp_partial_sum(p, e, (n - 1) as nat) + geo_exp_summand(p, e, (n - 1) as nat) }
}

/// The series is bounded: ∀n. bound ≥ Σ_{k<n} p^k · (1-p) · ℰ(k).
pub open spec fn geo_exp_series_bounded_by(p: real, e: spec_fn(nat) -> real, bound: real) -> bool {
    forall |n: nat| bound >= #[trigger] geo_exp_partial_sum(p, e, n)
}

/// Credit allocation for the Bernoulli(p) flip.
/// heads (true):  credit for next iteration = (eps - (1-p)·e(0)) / p
/// tails (false): return with credit e(0)
pub open spec fn geo_exp_flip_e(
    p: real,
    e: spec_fn(nat) -> real,
    eps: real,
) -> spec_fn(bool) -> real {
    |b: bool| if b { (eps - (1real - p) * e(0)) / p } else { e(0) }
}

// ============================================================================
// Lemmas
// ============================================================================

/// The Bernoulli(p) flip weighted sum exactly equals eps.
proof fn lemma_geo_exp_flip_average(p: real, e: spec_fn(nat) -> real, eps: real)
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
proof fn lemma_geo_exp_first_step(p: real, e: spec_fn(nat) -> real, n: nat)
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
proof fn lemma_geo_exp_shift_bound(
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
proof fn lemma_flip_true_nonneg(p: real, e: spec_fn(nat) -> real, eps: real)
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

/// Associativity: a * (b * c) == (a * b) * c.
// ============================================================================
// Sampler
// ============================================================================

/// Sample from Geometric(1 - exp(-x)) where x = numer_x/denom_x > 0.
///
/// Loop flipping Bernoulli(p) where p = exp(-x). On each flip:
///   tails → return k
///   heads → k++, shift postcondition, amplify slack by 1/p
/// Terminates when depth reaches 0 (credit >= 1 → contradiction).
pub fn sample_geometric_exp(
    numer_x: u64,
    denom_x: u64,
    Ghost(p): Ghost<real>,
    Ghost(e): Ghost<spec_fn(nat) -> real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(dist_bound): Ghost<real>,
) -> ((value, out_credit): (UBig, Tracked<ErrorCreditResource>))
    requires
        denom_x > 0,
        0real < p < 1real,
        p == exp(-(numer_x as real / denom_x as real)),
        forall |k: nat| (#[trigger] e(k)) >= 0real,
        dist_bound >= 0real,
        input_credit.view() =~= (ErrorCreditCarrier::Value { car: dist_bound }),
        geo_exp_series_bounded_by(p, e, dist_bound),
    ensures
        out_credit@.view() =~= (ErrorCreditCarrier::Value { car: e(ubig_view(&value)) }),
{
    // Obtain slack credit and depth bound for termination
    let Tracked(slack_credit) = thin_air();

    let ghost slack: real;
    let ghost g_depth: nat;
    let ghost inv_p = 1real / p;

    proof {
        slack = choose |v: real| v > 0real &&
            (ErrorCreditCarrier::Value { car: v } =~= slack_credit.view());
        assert(inv_p > 1real) by(nonlinear_arith)
            requires 0real < p < 1real, inv_p == 1real / p;
        archimedean_exp_growth(slack, inv_p);
        g_depth = choose |k: nat| slack * #[trigger] pow(inv_p, k) >= 1real;
    }

    let ghost g_eps = dist_bound + slack;
    let tracked mut credit: ErrorCreditResource;
    proof {
        credit = ec_combine(input_credit, slack_credit, dist_bound, slack);
    }

    // Main loop
    let mut k = ubig_zero();
    let ghost mut g_kn: nat = 0;
    let ghost mut g_e: spec_fn(nat) -> real = e;
    let ghost mut g_eps = g_eps;
    let ghost mut g_slack = slack;
    let ghost mut g_depth = g_depth;

    loop
        invariant
            denom_x > 0,
            0real < p < 1real,
            p == exp(-(numer_x as real / denom_x as real)),
            forall |i: nat| (#[trigger] e(i)) >= 0real,
            g_kn == ubig_view(&k),
            forall |i: nat| #[trigger] g_e(i) == e(i + g_kn),
            g_eps > 0real,
            g_slack > 0real,
            credit.view() =~= (ErrorCreditCarrier::Value { car: g_eps }),
            geo_exp_series_bounded_by(p, g_e, g_eps - g_slack),
            g_slack * pow(1real / p, g_depth) >= 1real,
        decreases g_depth,
    {
        proof {
            // dist_bound = g_eps - g_slack >= partial_sum(0) = 0
            assert(geo_exp_partial_sum(p, g_e, 0nat) == 0real);
            assert(g_eps - g_slack >= 0real);

            if g_depth == 0nat {
                assert(pow(1real / p, 0nat) == 1real);
                ec_contradict(&credit);
            }

            // g_eps > (1-p)·g_e(0) from series bound + slack > 0
            assert(pow(p, 0nat) == 1real);
            assert(geo_exp_partial_sum(p, g_e, 1nat)
                == geo_exp_partial_sum(p, g_e, 0nat) + geo_exp_summand(p, g_e, 0nat));
            assert(geo_exp_summand(p, g_e, 0nat) == (1real - p) * g_e(0)) by(nonlinear_arith)
                requires geo_exp_summand(p, g_e, 0nat) == pow(p, 0nat) * (1real - p) * g_e(0),
                    pow(p, 0nat) == 1real;

            lemma_geo_exp_flip_average(p, g_e, g_eps);
            lemma_flip_true_nonneg(p, g_e, g_eps);
        }

        let ghost flip_e = geo_exp_flip_e(p, g_e, g_eps);

        let (heads, Tracked(outcome_credit)) = sample_bernoulli_exp(
            numer_x,
            denom_x,
            Ghost(flip_e),
            Tracked(credit),
            Ghost(g_eps),
        );

        if !heads {
            // Tails: flip_e(false) = g_e(0) = e(g_kn) = e(ubig_view(&k))
            return (k, Tracked(outcome_credit));
        }

        // Heads: shift postcondition, amplify slack, decrement depth
        k = ubig_succ(&k);
        proof {
            let old_e = g_e;
            let old_eps = g_eps;
            let old_slack = g_slack;
            let old_kn = g_kn;
            let old_depth = g_depth;

            // old_e(i) >= 0 (needed for shift_bound)
            assert forall |i: nat| (#[trigger] old_e(i)) >= 0real by {
                assert(e(i + old_kn) >= 0real);
            };

            // Shift bound: produces bound on shift_e(old_e)
            lemma_geo_exp_shift_bound(p, old_e, old_eps - old_slack);

            // Update ghost state
            g_e = shift_e(old_e);
            g_kn = old_kn + 1;
            g_eps = geo_exp_flip_e(p, old_e, old_eps)(true);
            g_slack = old_slack / p;
            g_depth = (old_depth - 1) as nat;
            credit = outcome_credit;

            assert(g_eps > 0real) by(nonlinear_arith)
                requires
                    g_eps == (old_eps - (1real - p) * old_e(0)) / p,
                    old_eps - old_slack >= (1real - p) * old_e(0),
                    old_slack > 0real,
                    p > 0real;

            assert(g_slack > 0real) by(nonlinear_arith)
                requires g_slack == old_slack / p, old_slack > 0real, p > 0real;

            // g_eps - g_slack matches what shift_bound produced
            assert(g_eps - g_slack == (old_eps - old_slack - (1real - p) * old_e(0)) / p)
                by(nonlinear_arith)
                requires
                    g_eps == (old_eps - (1real - p) * old_e(0)) / p,
                    g_slack == old_slack / p,
                    p > 0real;

            // Termination: g_slack * pow(1/p, g_depth) >= 1
            assert(pow(1real / p, old_depth)
                == (1real / p) * pow(1real / p, (old_depth - 1) as nat));
            real_assoc_mult(old_slack, 1real / p, pow(1real / p, (old_depth - 1) as nat));
            assert(g_slack == old_slack * (1real / p)) by(nonlinear_arith)
                requires g_slack == old_slack / p, p > 0real;
        }
    }
}

} // verus!
