//! Sample from the Discrete Laplace distribution DL(0, scale).
//!
//! From CKS20: sample sign ∈ {+, -} uniformly, then sample magnitude
//! from Geometric(1 - exp(-1/scale)). Reject (-, 0) to avoid double-counting zero.
//!
//! Let p = exp(-1/scale). and:
//! ```text
//!   P[0]  = (1 - p) / (1 + p)
//!   P[+k] = P[-k] = p^k · (1 - p) / (1 + p)   for k ≥ 1
//! ```
//!
//! We prove the following Expectation Preservation Rule
//!
//! ```text
//!   ε ≥ Σ_{x=-∞}^{∞} P[x] · ℰ(x)
//!   --------------------------------
//!   [{ ↯(ε) }] sample_discrete_laplace(scale) [{ v. ↯(ℰ(v)) }]
//! ```

use vstd::prelude::*;

use random::{IBig, ubig_from_u64, ibig_from_ubig, ibig_neg, ibig_is_zero, RBig, rbig_into_parts, ibig_abs};
#[cfg(verus_keep_ghost)]
use random::UBig;

verus! {

use crate::ec::*;
#[cfg(verus_keep_ghost)]
use crate::cks::discrete_laplace_helper::*;
#[cfg(verus_keep_ghost)]
use crate::ec::ErrorCreditCarrier::Value;
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
use crate::cks::bernoulli_rational::bernoulli_weighted_sum;
use crate::cks::bernoulli_rational::sample_bernoulli_rational;
use crate::cks::geometric_exp::sample_geometric_exp;
use crate::cks::geometric_exp_fast::sample_geometric_exp_fast;
#[cfg(verus_keep_ghost)]
use crate::cks::geometric_exp::{geo_exp_series_bounded_by, geo_exp_partial_sum, geo_exp_summand};
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

/// Sample from Discrete Laplace DL(0, scale) where 1/scale = inv_numer/inv_denom.
pub fn sample_discrete_laplace(
    inv_numer: u64,
    inv_denom: u64,
    Ghost(p): Ghost<real>,
    Ghost(e): Ghost<spec_fn(int) -> real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(eps): Ghost<real>,
) -> ((value, out_credit): (IBig, Tracked<ErrorCreditResource>))
    requires
        inv_numer > 0,
        inv_denom > 0,
        0real < p < 1real,
        p == exp(-(inv_numer as real / inv_denom as real)),
        forall |x: int| (#[trigger] e(x)) >= 0real,
        eps > 0real,
        input_credit@ =~= (Value { car: eps }),
        dl_series_bounded_by(p, e, eps),
    ensures
        out_credit@@ =~= (Value { car: e(ibig_view(&value)) }),
{
    // Get slack for termination
    let Tracked(slack_credit) = thin_air();
    let ghost slack: real;
    let ghost depth: nat;
    proof {
        slack = choose |v: real| v > 0real &&
            (Value { car: v } =~= slack_credit@);
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
            credit@ =~= (Value { car: g_eps + g_slack }),
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
            let result = ibig_from_ubig(&magnitude);
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

            let mag_ibig = ibig_from_ubig(&magnitude);
            let is_zero = ibig_is_zero(&mag_ibig);

            if !is_zero {
                // Accept: return -magnitude
                let result = ibig_neg(&mag_ibig);
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
) -> ((value, out_credit): (IBig, Tracked<ErrorCreditResource>))
    requires
        rbig_view(scale) > 0real,
        0real < p < 1real,
        p == exp(-(1real / rbig_view(scale))),
        forall |x: int| (#[trigger] e(x)) >= 0real,
        eps > 0real,
        input_credit@ =~= (Value { car: eps }),
        dl_series_bounded_by(p, e, eps),
    ensures
        out_credit@@ =~= (Value { car: e(ibig_view(&value)) }),
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
            (Value { car: v } =~= slack_credit@);
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
            credit@ =~= (Value { car: g_eps + g_slack }),
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

            let result = ibig_from_ubig(&magnitude);
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

            let mag_ibig = ibig_from_ubig(&magnitude);
            let is_zero = ibig_is_zero(&mag_ibig);

            if !is_zero {
                // Accept: return -magnitude
                let result = ibig_neg(&mag_ibig);
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
            (Value { car: v } =~= cred@);
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

} // verus!
