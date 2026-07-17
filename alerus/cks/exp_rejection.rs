//! Exponential-rejection sampler producing rejection_dist(u) = e^{−u/d} / N
//! on {0, …, d−1}, where N = Σ_{u<d} e^{−u/d}.
//!
//! Algorithm:
//! ```text
//!   loop:
//!     u ← Uniform({0, …, d−1})
//!     b ← Bernoulli(e^{−u/d})
//!     if b: return u
//! ```
//!
//! Expectation Preservation Rule:
//!
//! ```text
//!   eps_avg ≥ E_{u ~ rejection_dist}[ℰ(u)] = (1/N) · Σ_{u<d} e^{−u/d} · ℰ(u)
//!   ─────────────────────────────────────────────────────────────────────────
//!   [{ ↯(eps_avg) }] sample_exp_rejection(d) [{ u. ↯(ℰ(u)) }]
//! ```
//!
//! Credit derivation:
//!
//! ```text
//!   alloc(w)        = e^{−w/d} · flip_accept(w) + (1 − e^{−w/d}) · flip_reject
//!   flip_accept(w)  = ℰ(w)                                    // accept arm
//!   flip_reject     = E_{l ~ rejection_dist}[ℰ(l)]            // recursive expected value
//! ```
//!
//! the average over the uniform step exactly equals the target expectation:
//!
//!   E_{u ~ rejection_dist}[ℰ(u)]  =  (1/d) · Σ_w alloc(w).
//!
//! To close the while-loop in Hoare logic we add thin-air slack ε and amplify:
//!   rej_credit  = amp·ε + eps_avg     (amp = 1/R, R = 1 − N/d)
//!   alloc(w)    = e^{−w/d}·ℰ(w) + (1 − e^{−w/d})·rej_credit
//!   average(d, alloc) ≤ ε + eps_avg                         (`lemma_rej_average`)
//! On rejection the carried credit is `rej_credit`; the next iteration uses
//! ε ↦ amp·ε.  Since amp > 1 the slack grows geometrically and the
//! Archimedean property bounds the number of iterations.

use vstd::prelude::*;

verus! {

use crate::ec::*;
#[cfg(verus_keep_ghost)]
use crate::cks::exp_rejection_helper::*;
#[cfg(verus_keep_ghost)]
use crate::ec::ErrorCreditCarrier::Value;
#[cfg(verus_keep_ghost)]
use crate::math::pow::{pow, archimedean_exp_growth};
#[cfg(verus_keep_ghost)]
use crate::math::real::real_assoc_mult;
#[cfg(verus_keep_ghost)]
use crate::math::exp::{exp, axiom_exp_zero, axiom_exp_neg_range, axiom_exp_neg_strict, axiom_exp_add};
use crate::rand_primitives::{thin_air, rand_ubig};
#[cfg(verus_keep_ghost)]
use crate::rand_primitives::{average_nat, sum_credit};
use crate::cks::bernoulli_exp::sample_bernoulli_exp_rbig;
use random::{UBig, ubig_from_u64, rbig_from_parts, ibig_from_ubig};
use crate::extern_spec::ubig_lt;
#[cfg(verus_keep_ghost)]
use crate::extern_spec::{ubig_view, ibig_view, rbig_view};
#[cfg(verus_keep_ghost)]
use crate::cks::bernoulli_rational::bernoulli_weighted_sum;

/// e^{−u/d}.
pub open spec fn rej_weight(d: nat, u: nat) -> real {
    exp(-(u as real / d as real))
}

/// Σ_{i<n} e^{−i/d}.
pub open spec fn rej_weight_sum(d: nat, n: nat) -> real
    decreases n,
{
    if n == 0 { 0real }
    else { rej_weight_sum(d, (n - 1) as nat) + rej_weight(d, (n - 1) as nat) }
}

/// N := Σ_{i<d} e^{−i/d}.
pub open spec fn rej_norm_const(d: nat) -> real {
    rej_weight_sum(d, d)
}

/// Σ_{i<n} e^{−i/d} · ℰ(i).
pub open spec fn rej_weighted_sum(d: nat, e: spec_fn(nat) -> real, n: nat) -> real
    decreases n,
{
    if n == 0 { 0real }
    else {
        rej_weighted_sum(d, e, (n - 1) as nat)
            + rej_weight(d, (n - 1) as nat) * e((n - 1) as nat)
    }
}

/// E_{u ~ rejection_dist}[ℰ(u)] = (1/N) · Σ_{u<d} e^{−u/d} · ℰ(u).
pub open spec fn rej_weighted_avg(d: nat, e: spec_fn(nat) -> real) -> real {
    rej_weighted_sum(d, e, d) / rej_norm_const(d)
}

/// Average rejection rate:  R = 1 − N/d.
/// (P(accept) = Σ_u (1/d)·e^{−u/d} = N/d.)
pub open spec fn rej_rate(d: nat) -> real {
    1real - rej_norm_const(d) / d as real
}

/// Slack amplification factor:  amp = 1/R.
pub open spec fn rej_amp(d: nat) -> real {
    1real / rej_rate(d)
}

/// Per-outcome credit for the uniform rand_u64 step:
///   h(u) = e^{−u/d} · ℰ(u) + (1 − e^{−u/d}) · rej_credit.
pub open spec fn rej_credit_alloc(
    d: nat, e: spec_fn(nat) -> real, rej_credit: real,
) -> spec_fn(nat) -> real {
    |u: nat| {
        let w = exp(-(u as real / d as real));
        w * e(u) + (1real - w) * rej_credit
    }
}

/// Bernoulli flip postcondition:
///   true  arm: ℰ(u)
///   false arm: rej_credit
pub open spec fn rej_flip_e(
    e: spec_fn(nat) -> real, u: nat, rej_credit: real,
) -> spec_fn(bool) -> real {
    |b: bool| if b { e(u) } else { rej_credit }
}

pub fn sample_exp_rejection(
    denom: &UBig,
    Ghost(e): Ghost<spec_fn(nat) -> real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(eps_avg): Ghost<real>,
) -> ((value, out_credit): (UBig, Tracked<ErrorCreditResource>))
    requires
        ubig_view(denom) > 0,
        forall |u: nat| (#[trigger] e(u)) >= 0real,
        eps_avg >= 0real,
        input_credit@ =~= (Value { car: eps_avg }),
        eps_avg >= rej_weighted_avg(ubig_view(denom), e),
    ensures
        ubig_view(&value) < ubig_view(denom),
        out_credit@@ =~= (Value { car: e(ubig_view(&value)) }),
{
    let ghost d = ubig_view(denom);

    // d == 1: the only outcome is u = 0, accepted with certainty (e^{−0/1} = 1).
    // No rejection occurs, so the amplification machinery (which needs d > 1) is
    // bypassed — we draw u = 0 directly with the plain credit allocation ℰ.
    let one_ub = ubig_from_u64(1u64);
    if !ubig_lt(&one_ub, denom) {
        proof { assert(d == 1); }
        let ghost alloc = rej_credit_alloc(d, e, 0real);
        proof {
            lemma_rej_avg_one(e);                 // rej_weighted_avg(1,e) == e(0)
            lemma_rej_avg_one_alloc(e, 0real);    // average_nat(1, alloc) == e(0)
            lemma_rej_alloc_nonneg(d, e, 0real);  // forall i. alloc(i) >= 0
        }
        let (u_val, Tracked(u_credit)) = rand_ubig(denom, Tracked(input_credit), Ghost(alloc));
        proof {
            assert(ubig_view(&u_val) == 0);                 // < d == 1
            assert(ubig_view(&u_val) as real == 0real);
            lemma_rej_alloc_at_zero(d, e, 0real);           // alloc(0) == e(0)
        }
        return (u_val, Tracked(u_credit));
    }
    proof { assert(d > 1); }

    let ghost amp = rej_amp(d);

    let Tracked(eps_credit) = thin_air();
    let ghost init_eps: real;
    proof {
        init_eps = choose |v: real| v > 0real &&
            (Value { car: v } =~= eps_credit@);
    }
    let tracked mut credit = ec_combine(input_credit, eps_credit, eps_avg, init_eps);

    let ghost mut g_eps: real = init_eps;
    let ghost mut g_depth: nat;

    proof {
        lemma_rej_rate_range(d);
        archimedean_exp_growth(init_eps, amp);
        g_depth = choose |k: nat| init_eps * pow(amp, k) >= 1real;
    }

    let mut u: UBig = ubig_from_u64(0u64);
    let mut accepted: bool = false;

    while !accepted
        invariant
            ubig_view(denom) > 1,
            d == ubig_view(denom),
            forall |u: nat| (#[trigger] e(u)) >= 0real,
            eps_avg >= 0real,
            eps_avg >= rej_weighted_avg(d, e),
            amp > 1real,
            amp == rej_amp(d),
            // Credit invariant (still rejecting).
            !accepted ==> g_eps > 0real,
            !accepted ==> credit@ =~= (Value { car: g_eps + eps_avg }),
            !accepted ==> g_eps * pow(amp, g_depth) >= 1real,
            // Accept postcondition.
            accepted ==> ubig_view(&u) < ubig_view(denom),
            accepted ==> credit@ =~= (Value { car: e(ubig_view(&u)) }),
        decreases g_depth,
    {
        proof {
            if g_depth == 0nat {
                assert(pow(amp, 0nat) == 1real);
                assert(g_eps + eps_avg >= 1real) by(nonlinear_arith)
                    requires g_eps >= 1real, eps_avg >= 0real;
                ec_contradict(&credit);
            }
        }

        let ghost rej_credit = amp * g_eps + eps_avg;
        let ghost alloc = rej_credit_alloc(d, e, rej_credit);

        proof {
            assert(rej_credit >= 0real) by(nonlinear_arith)
                requires rej_credit == amp * g_eps + eps_avg,
                    amp > 1real, g_eps > 0real, eps_avg >= 0real;
            lemma_rej_average(d, e, g_eps, eps_avg);
            lemma_rej_alloc_nonneg(d, e, rej_credit);
        }

        let (u_val, Tracked(u_credit)) = rand_ubig(
            denom, Tracked(credit), Ghost(alloc),
        );

        let ghost uvn = ubig_view(&u_val);
        let ghost g_flip_e = rej_flip_e(e, uvn, rej_credit);
        let ghost g_h_val = alloc(uvn);

        proof {
            assert(uvn as real / d as real >= 0real) by(nonlinear_arith)
                requires d > 0;
            axiom_exp_neg_range(uvn as real / d as real);
            lemma_rej_bws(d, uvn, e, rej_credit);
        }

        // Bernoulli(exp(−u_val/denom)) — build the rational u_val/denom.
        let x_arg = rbig_from_parts(&ibig_from_ubig(&u_val), denom);
        proof {
            // rbig_view(&x_arg) == uvn/d, so the exp preconditions carry over.
            assert(rbig_view(&x_arg) == uvn as real / d as real);
            assert(rbig_view(&x_arg) >= 0real) by(nonlinear_arith)
                requires rbig_view(&x_arg) == uvn as real / d as real, d > 0;
        }
        let (heads, Tracked(flip_out)) = sample_bernoulli_exp_rbig(
            x_arg, Ghost(g_flip_e), Tracked(u_credit), Ghost(g_h_val),
        );

        if heads {
            u = u_val;
            accepted = true;
            proof {
                credit = flip_out;
                g_depth = (g_depth - 1) as nat;
            }
        } else {
            proof {
                let old_eps = g_eps;
                let old_depth = g_depth;
                credit = flip_out;
                g_eps = amp * old_eps;
                g_depth = (old_depth - 1) as nat;

                assert(g_eps > 0real) by(nonlinear_arith)
                    requires g_eps == amp * old_eps, amp > 1real, old_eps > 0real;
                assert(pow(amp, old_depth) == amp * pow(amp, (old_depth - 1) as nat));
                real_assoc_mult(old_eps, amp, pow(amp, (old_depth - 1) as nat));
                assert(g_eps * pow(amp, g_depth) >= 1real) by(nonlinear_arith)
                    requires
                        g_eps == amp * old_eps,
                        old_eps * pow(amp, old_depth) >= 1real,
                        pow(amp, old_depth) == amp * pow(amp, (old_depth - 1) as nat),
                        (old_eps * amp) * pow(amp, (old_depth - 1) as nat)
                            == old_eps * (amp * pow(amp, (old_depth - 1) as nat)),
                        g_depth == (old_depth - 1) as nat,
                        amp > 1real, old_eps > 0real;
            }
        }
    }

    (u, Tracked(credit))
}

} // verus!
