// 1D Symmetric Random Walk - Almost Sure Termination
// Solves by having the credit allocation as the failure probability, 
// namely: fail_prob(steps, pos) = 1 - Pr[walk from pos reaches 0 in ≤ steps]
//
// fail_prob(0, p) = 1
// fail_prob(s, 0) = 0
// fail_prob(s, p) = (fail_prob(s-1, p-1) fail_prob(s-1, p+1)) / 2
//
// Then the credit allocation is just the last case of the recurrence relation.
//
// The rest of the heavy lifting is proving the Archimedean property: 
// ∀ δ > 0, ∀ p, ∃ s, fail_prob(s, p) < δ
//
// Proof of rw_ast (fail_limit(p) := lim_{s→∞} fail_prob(s, p)):
//   1. fail_prob(s, p) is non-increasing in s and bounded below by 0,
//      so by monotone convergence it converges to fail_limit(p).
//   2. Taking limits in the recurrence gives the discrete harmonic equation:
//        fail_limit(p) = (fail_limit(p-1) + fail_limit(p+1))/2,  fail_limit(0) = 0
//      The general solution is fail_limit(p) = A + B·p. Since fail_limit(0) = 0,
//      A = 0, so fail_limit(p) = p · fail_limit(1).
//   3. Since fail_prob(s, p) <= 1 for all s, we have fail_limit(p) <= 1 for all p.
//      If fail_limit(1) > 0, by the archimedean property pick p >= 1/fail_limit(1)
//      to get fail_limit(p) = p · fail_limit(1) > 1, a contradiction.
//      Therefore fail_limit(1) = 0, and fail_limit(p) = 0 for all p.
//   4. Since fail_prob(s, p) converges to 0, for any delta > 0 there exists s
//      with fail_prob(s, p) < delta.

use vstd::prelude::*;

use random::{UBig, ubig_zero, ubig_succ, ubig_pred, ubig_is_zero, ubig_from_u64};

verus! {

use crate::ec::*;
use crate::rand_primitives::{rand_1_u64, thin_air};
#[cfg(verus_keep_ghost)]
use crate::rand_primitives::sum_credit;
#[cfg(verus_keep_ghost)]
use crate::math::pow::{nat_to_real, archimedean_nat};
#[cfg(verus_keep_ghost)]
use crate::math::series::{
    seq_at, dist,
    converges_to, converges, exists_close_suffix, suffix_is_close,
    is_nonincreasing, is_bounded_below, is_bounded_above,
    lemma_monotone_convergence_decreasing,
    lemma_limit_shift, lemma_limit_average,
    lemma_limit_le_bound, lemma_limit_ge_bound,
    lemma_limit_unique, lemma_limit_pointwise_eq,
    lemma_convergent_witness,
};
#[cfg(verus_keep_ghost)]
use crate::extern_spec::ExUBig;
#[cfg(verus_keep_ghost)]
use crate::extern_spec::ubig_view;

/// fail_prob(steps, pos) = 1 - Pr[walk from pos reaches 0 in ≤ steps].
pub open spec fn fail_prob(steps: nat, pos: nat) -> real
    decreases steps,
{
    if pos == 0 { 0real }
    else if steps == 0 { 1real }
    else { (fail_prob((steps - 1) as nat, (pos - 1) as nat)
          + fail_prob((steps - 1) as nat, pos + 1)) / 2real }
}

/// The sequence s ↦ fail_prob(s, p).
pub open spec fn fail_prob_seq(p: nat) -> spec_fn(nat) -> real {
    |s: nat| fail_prob(s, p)
}

/// fail_limit(p) := lim_{s→∞} fail_prob(s, p).
pub open spec fn fail_limit(p: nat) -> real {
    choose |l: real| converges_to(fail_prob_seq(p), l)
}

proof fn lemma_fail_prob_nonneg(steps: nat, pos: nat)
    ensures fail_prob(steps, pos) >= 0real,
    decreases steps,
{
    if pos == 0 || steps == 0 { }
    else {
        lemma_fail_prob_nonneg((steps - 1) as nat, (pos - 1) as nat);
        lemma_fail_prob_nonneg((steps - 1) as nat, pos + 1);
    }
}

proof fn lemma_fail_prob_le_one(steps: nat, pos: nat)
    ensures fail_prob(steps, pos) <= 1real,
    decreases steps,
{
    if pos == 0 || steps == 0 { }
    else {
        lemma_fail_prob_le_one((steps - 1) as nat, (pos - 1) as nat);
        lemma_fail_prob_le_one((steps - 1) as nat, pos + 1);
        assert(fail_prob(steps, pos) <= 1real) by(nonlinear_arith)
            requires
                fail_prob((steps-1) as nat, (pos-1) as nat) <= 1real,
                fail_prob((steps-1) as nat, pos + 1) <= 1real,
                fail_prob(steps, pos) == (fail_prob((steps-1) as nat, (pos-1) as nat)
                    + fail_prob((steps-1) as nat, pos + 1)) / 2real;
    }
}

proof fn lemma_fail_prob_mono(steps: nat, pos: nat)
    ensures fail_prob(steps + 1, pos) <= fail_prob(steps, pos),
    decreases steps,
{
    if pos == 0 {
    } else if steps == 0 {
        lemma_fail_prob_le_one(0, (pos - 1) as nat);
        lemma_fail_prob_le_one(0, pos + 1);
    } else {
        lemma_fail_prob_mono((steps - 1) as nat, (pos - 1) as nat);
        lemma_fail_prob_mono((steps - 1) as nat, pos + 1);
        assert(fail_prob(steps + 1, pos) <= fail_prob(steps, pos)) by(nonlinear_arith)
            requires
                fail_prob(steps, (pos-1) as nat) <= fail_prob((steps-1) as nat, (pos-1) as nat),
                fail_prob(steps, pos + 1) <= fail_prob((steps-1) as nat, pos + 1),
                fail_prob(steps + 1, pos) == (fail_prob(steps, (pos-1) as nat) + fail_prob(steps, pos + 1)) / 2real,
                fail_prob(steps, pos) == (fail_prob((steps-1) as nat, (pos-1) as nat) + fail_prob((steps-1) as nat, pos + 1)) / 2real;
    }
}

proof fn lemma_fail_limit_converges(p: nat)
    ensures converges_to(fail_prob_seq(p), fail_limit(p)),
{
    assert(is_nonincreasing(fail_prob_seq(p))) by {
        assert forall |n: nat|
            #[trigger] seq_at(fail_prob_seq(p), n) >= seq_at(fail_prob_seq(p), n + 1)
        by { lemma_fail_prob_mono(n, p); };
    };
    assert(is_bounded_below(fail_prob_seq(p), 0real)) by {
        assert forall |n: nat|
            #[trigger] seq_at(fail_prob_seq(p), n) >= 0real
        by { lemma_fail_prob_nonneg(n, p); };
    };
    lemma_monotone_convergence_decreasing(fail_prob_seq(p), 0real);
}

/// fail_limit(0) = 0  (constant-zero sequence converges to 0).
proof fn lemma_fail_limit_zero_base()
    ensures fail_limit(0) == 0real,
{
    lemma_fail_limit_converges(0nat);
    assert(converges_to(fail_prob_seq(0nat), 0real)) by {
        assert forall |epsilon: real| epsilon > 0real
            implies #[trigger] exists_close_suffix(fail_prob_seq(0nat), 0real, epsilon)
        by {
            assert(suffix_is_close(fail_prob_seq(0nat), 0real, epsilon, 0nat)) by {
                assert forall |n: nat| n >= 0nat implies
                    dist(#[trigger] seq_at(fail_prob_seq(0nat), n), 0real) < epsilon
                by { assert(dist(0real, 0real) == 0real) by(nonlinear_arith); };
            };
        };
    };
    lemma_limit_unique(fail_prob_seq(0nat), fail_limit(0nat), 0real);
}

/// fail_limit(p) = (fail_limit(p-1) + fail_limit(p+1)) / 2  for p > 0.
proof fn lemma_fail_limit_recurrence(p: nat)
    requires p > 0,
    ensures fail_limit(p) == (fail_limit((p - 1) as nat) + fail_limit(p + 1)) / 2real,
{
    let p1 = (p - 1) as nat;
    let seq_shifted = |d: nat| seq_at(fail_prob_seq(p), d + 1);
    let seq_avg = |d: nat| (seq_at(fail_prob_seq(p1), d) + seq_at(fail_prob_seq(p + 1), d)) / 2real;

    assert(forall |d: nat| seq_at(seq_shifted, d) == seq_at(seq_avg, d));

    lemma_fail_limit_converges(p);
    lemma_limit_shift(fail_prob_seq(p), fail_limit(p));

    lemma_fail_limit_converges(p1);
    lemma_fail_limit_converges(p + 1);
    lemma_limit_average(fail_prob_seq(p1), fail_prob_seq(p + 1), fail_limit(p1), fail_limit(p + 1));

    lemma_limit_pointwise_eq(seq_avg, seq_shifted, (fail_limit(p1) + fail_limit(p + 1)) / 2real);
    lemma_limit_unique(seq_shifted, fail_limit(p), (fail_limit(p1) + fail_limit(p + 1)) / 2real);
}

/// fail_limit(p) = p · fail_limit(1).
/// Proof by induction and:
///  `fail_limit(p) = 2(p-1)·fail_limit(1) - (p-2)·fail_limit(1) = p·fail_limit(1).`
proof fn lemma_fail_limit_linear(p: nat)
    ensures fail_limit(p) == nat_to_real(p) * fail_limit(1),
    decreases p,
{
    if p == 0 {
        lemma_fail_limit_zero_base();
        assert(nat_to_real(0nat) == 0real);
    } else if p == 1 {
        assert(nat_to_real(1nat) == 1real);
    } else {
        lemma_fail_limit_recurrence((p - 1) as nat);
        lemma_fail_limit_linear((p - 1) as nat);
        lemma_fail_limit_linear((p - 2) as nat);
        assert(fail_limit(p) == nat_to_real(p) * fail_limit(1)) by(nonlinear_arith)
            requires
                fail_limit((p-1) as nat) == (fail_limit((p-2) as nat) + fail_limit(p)) / 2real,
                fail_limit((p-1) as nat) == nat_to_real((p-1) as nat) * fail_limit(1),
                fail_limit((p-2) as nat) == nat_to_real((p-2) as nat) * fail_limit(1),
                nat_to_real(p) == nat_to_real((p-1) as nat) + 1real,
                nat_to_real((p-1) as nat) == nat_to_real((p-2) as nat) + 1real;
    }
}

/// fail_limit(p) = 0 for all p.
proof fn lemma_fail_limit_zero(p: nat)
    ensures fail_limit(p) == 0real,
{
    lemma_fail_limit_linear(p);
    // fail_limit(1) ≥ 0
    lemma_fail_limit_converges(1);
    assert(is_bounded_below(fail_prob_seq(1), 0real)) by {
        assert forall |n: nat| #[trigger] seq_at(fail_prob_seq(1), n) >= 0real
        by { lemma_fail_prob_nonneg(n, 1); };
    };
    lemma_limit_ge_bound(fail_prob_seq(1), fail_limit(1), 0real);
    // If fail_limit(1) > 0, pick k ≥ 1/fail_limit(1) (archimedean).
    // Then fail_limit(k+1) = (k+1)·fail_limit(1) > 1, contradicting fail_limit(k+1) ≤ 1.
    if fail_limit(1) > 0real {
        assert(1real / fail_limit(1) >= 0real) by(nonlinear_arith)
            requires fail_limit(1) > 0real;
        archimedean_nat(1real / fail_limit(1));
        let k = choose |k: nat| nat_to_real(k) >= 1real / fail_limit(1);
        lemma_fail_limit_linear(k + 1);
        assert(fail_limit(k + 1) > 1real) by(nonlinear_arith)
            requires
                fail_limit(k + 1) == nat_to_real(k + 1) * fail_limit(1),
                nat_to_real(k + 1) == nat_to_real(k) + 1real,
                nat_to_real(k) >= 1real / fail_limit(1),
                fail_limit(1) > 0real;
        lemma_fail_limit_converges(k + 1);
        assert(is_bounded_above(fail_prob_seq(k + 1), 1real)) by {
            assert forall |n: nat| #[trigger] seq_at(fail_prob_seq(k + 1), n) <= 1real
            by { lemma_fail_prob_le_one(n, k + 1); };
        };
        lemma_limit_le_bound(fail_prob_seq(k + 1), fail_limit(k + 1), 1real);
        assert(false);
    }
}

/// For any starting position pos and δ > 0, ∃ s. fail_prob(s, pos) < δ.
pub proof fn rw_ast(pos: nat, delta: real)
    requires delta > 0real,
    ensures exists |s: nat| fail_prob(s, pos) < delta,
{
    lemma_fail_limit_zero(pos);
    lemma_fail_limit_converges(pos);
    lemma_convergent_witness(fail_prob_seq(pos), 0real, delta);
}

/// Credit allocation: fail_prob(steps-1, pos(-/+)1) for each coin outcome.
spec fn rw_credit_alloc(outcome: real, steps: nat, pos: nat) -> real {
    if outcome == 0real {
        fail_prob((steps - 1) as nat, (pos - 1) as nat)
    } else {
        fail_prob((steps - 1) as nat, pos + 1)
    }
}

/// 1D random walk from position n to 0.
///
/// Credit invariant: eps ≥ fail_prob(depth, n).
/// At depth = 0, n > 0: fail_prob = 1, so eps ≥ 1, ec_contradict (dead code below).
/// Both branches use depth - 1. decreases depth.
pub fn bounded_random_walk_1d(
    n: &UBig,
    Tracked(credit): Tracked<ErrorCreditResource>,
    Ghost(depth): Ghost<nat>,
) -> (ret: UBig)
    requires
        exists |eps: real| {
            &&& credit.view() =~= (ErrorCreditCarrier::Value { car: eps })
            &&& eps >= fail_prob(depth, ubig_view(n))
        },
    decreases depth,
{
    if ubig_is_zero(n) {
        return ubig_zero();
    }

    let ghost eps: real;
    let ghost pos: nat;

    proof {
        pos = ubig_view(n);
        eps = choose |v: real| {
            &&& credit.view() =~= (ErrorCreditCarrier::Value { car: v })
            &&& v >= fail_prob(depth, pos)
        };
        if depth == 0nat { ec_contradict(&credit); }
    }

    let ghost alloc = |x: real| rw_credit_alloc(x, depth, pos);

    proof {
        assert forall |i: nat| (#[trigger] alloc(i as real)) >= 0real by {
            if i == 0 { lemma_fail_prob_nonneg((depth - 1) as nat, (pos - 1) as nat); }
            else { lemma_fail_prob_nonneg((depth - 1) as nat, pos + 1); }
        };
        assert(sum_credit(alloc, 1) == sum_credit(alloc, 0) + alloc(0real)); // OBSERVE
    }

    let (val, Tracked(outcome_credit)) = rand_1_u64(Tracked(credit), Ghost(alloc));

    if val == 0 {
        let n_pred = ubig_pred(n.clone());
        if ubig_is_zero(&n_pred) { n_pred }
        else { bounded_random_walk_1d(&n_pred, Tracked(outcome_credit), Ghost((depth - 1) as nat)) }
    } else {
        let n_succ = ubig_succ(n.clone());
        bounded_random_walk_1d(&n_succ, Tracked(outcome_credit), Ghost((depth - 1) as nat))
    }
}

/// Entry point: 1D random walk from position n to 0.
/// Uses thin_air for initial credit and rw_ast to find sufficient depth.
pub fn random_walk_1d(n: u64) -> (ret: UBig)
{
    let Tracked(credit) = thin_air();
    let ghost eps: real;
    let ghost depth: nat;
    let n_big = ubig_from_u64(n);

    proof {
        let pos = ubig_view(&n_big);
        if credit.view().value() =~= None { } // OBSERVE
        eps = choose |v: real| credit.view().value() == Some(v);
        rw_ast(pos, eps);
        depth = choose |d: nat| fail_prob(d, pos) < eps;
    }

    bounded_random_walk_1d(&n_big, Tracked(credit), Ghost(depth))
}

}
