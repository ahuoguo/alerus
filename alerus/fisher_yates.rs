//! Fisher–Yates shuffle — Eris error-credit case study.
//!
//! References:
//!   - partial Eris version
//!     https://github.com/logsem/clutch/blob/main/theories/eris/examples/fisher_yates.v
//!   - "Verifying the Fisher-Yates Shuffle Algorithm in Dafny"
//!      - https://arxiv.org/abs/2501.06084
//!      - https://github.com/dafny-lang/Dafny-VMC/tree/main/src/Util/FisherYates
//!
//! ## The specification
//!
//! For a duplicate-free vector `v` of length n and ANY fixed target permutation
//! `lav` of it (ghost), the Eris triple is
//!
//! ```text
//!   { ↯(1/n!) }  fisher_yates(v)  { v'.  v' ≡ₚ v  ∧  v' ≠ lav }
//! ```
//!
//! i.e. each specific permutation of `v` is produced with probability ≤ 1/n!.
//! A duplicate-free list of length n has exactly n! permutations, so these n!
//! upper bounds force the output distribution to be exactly uniform.

use vstd::prelude::*;

verus! {

use crate::ec::*;
#[cfg(verus_keep_ghost)]
use crate::ec::ErrorCreditCarrier::Value;
use crate::rand_primitives::rand_u64;
#[cfg(verus_keep_ghost)]
use crate::rand_primitives::{sum_credit, average};
#[cfg(verus_keep_ghost)]
use crate::math::exp::factorial;
#[cfg(verus_keep_ghost)]
use vstd::seq_lib::lemma_multiset_commutative;
#[cfg(verus_keep_ghost)]
use vstd::multiset::group_multiset_axioms;

/// Positions ≥ `m` of `s1` and `s2` agree (the already-fixed suffix).
pub open spec fn eq_from(s1: Seq<u64>, s2: Seq<u64>, m: int) -> bool {
    forall |p: int| m <= p < s1.len() ==> s1[p] == s2[p]
}

/// n! ≥ 1.
pub proof fn lemma_factorial_pos(n: nat)
    ensures factorial(n) >= 1real,
    decreases n,
{
    if n > 0 {
        lemma_factorial_pos((n - 1) as nat);
        assert(factorial(n) >= 1real) by(nonlinear_arith)
            requires
                factorial(n) == n as real * factorial((n - 1) as nat),
                factorial((n - 1) as nat) >= 1real,
                n >= 1;
    }
}

/// Sum of an allocation that is zero everywhere.
proof fn lemma_sum_zero(alloc: spec_fn(nat) -> real, m: nat)
    requires forall |x: nat| #[trigger] alloc(x) == 0real,
    ensures sum_credit(alloc, m) == 0real,
    decreases m,
{
    if m > 0 { lemma_sum_zero(alloc, (m - 1) as nat); }
}

/// Sum of a point-mass allocation: all of `val` sits on outcome `k`.
proof fn lemma_sum_point(alloc: spec_fn(nat) -> real, k: nat, val: real, m: nat)
    requires forall |x: nat| #[trigger] alloc(x) == (if x == k { val } else { 0real }),
    ensures sum_credit(alloc, m) == (if k < m { val } else { 0real }),
    decreases m,
{
    if m > 0 { lemma_sum_point(alloc, k, val, (m - 1) as nat); }
}

/// A swap leaves the multiset of a sequence unchanged.
proof fn lemma_swap_multiset(s: Seq<u64>, i: int, j: int)
    requires
        0 <= i < s.len(),
        0 <= j < s.len(),
    ensures
        s.update(i, s[j]).update(j, s[i]).to_multiset() == s.to_multiset(),
{
    broadcast use group_multiset_axioms;
    broadcast use vstd::seq_lib::group_to_multiset_ensures;

    let ms = s.to_multiset();
    let half_swapped = s.update(i, s[j]);
    let swapped = half_swapped.update(j, s[i]);

    // update = insert + remove on the multiset (to_multiset_update)
    assert(half_swapped.to_multiset() == ms.insert(s[j]).remove(s[i]));
    assert(half_swapped[j] == s[j]);
    assert(swapped.to_multiset() == half_swapped.to_multiset().insert(s[i]).remove(s[j]));

    assert forall |x: u64| #[trigger] swapped.to_multiset().count(x) == ms.count(x) by {
        assert(ms.count(s[i]) > 0);
        assert(ms.count(s[j]) > 0);
    };
    assert(swapped.to_multiset() =~= ms);
}

/// If two equal-multiset sequences agree from position `m` on, their prefixes
/// below `m` also carry equal multisets (subtract the common suffix).
proof fn lemma_prefix_multiset(s1: Seq<u64>, s2: Seq<u64>, m: int)
    requires
        s1.len() == s2.len(),
        0 <= m <= s1.len(),
        s1.to_multiset() == s2.to_multiset(),
        eq_from(s1, s2, m),
    ensures
        s1.take(m).to_multiset() == s2.take(m).to_multiset(),
{
    broadcast use group_multiset_axioms;

    assert(s1 =~= s1.take(m) + s1.skip(m));
    assert(s2 =~= s2.take(m) + s2.skip(m));
    lemma_multiset_commutative(s1.take(m), s1.skip(m));
    lemma_multiset_commutative(s2.take(m), s2.skip(m));
    assert(s1.skip(m) =~= s2.skip(m));
    assert forall |x: u64|
        #[trigger] s1.take(m).to_multiset().count(x) == s2.take(m).to_multiset().count(x)
    by {
        assert(s1.to_multiset().count(x)
            == s1.take(m).to_multiset().count(x) + s1.skip(m).to_multiset().count(x));
        assert(s2.to_multiset().count(x)
            == s2.take(m).to_multiset().count(x) + s2.skip(m).to_multiset().count(x));
    };
    assert(s1.take(m).to_multiset() =~= s2.take(m).to_multiset());
}

/// No-duplicates transfers across multiset equality.
proof fn lemma_nodup_transfer(s1: Seq<u64>, s2: Seq<u64>)
    requires
        s1.no_duplicates(),
        s1.to_multiset() == s2.to_multiset(),
    ensures
        s2.no_duplicates(),
{
    s1.lemma_multiset_has_no_duplicates();
    s2.lemma_multiset_has_no_duplicates_conv();
}

/// The target value lav[i] sits somewhere in the unfixed prefix s[0..=i]:
/// s ≡ₚ lav and the suffixes beyond i agree, so the prefix multisets agree
/// and lav[i] ∈ lav[0..=i] must appear in s[0..=i].
proof fn lemma_find_target(s: Seq<u64>, lav: Seq<u64>, i: int) -> (k: int)
    requires
        s.len() == lav.len(),
        0 <= i < s.len(),
        s.to_multiset() == lav.to_multiset(),
        eq_from(s, lav, i + 1),
    ensures
        0 <= k <= i,
        s[k] == lav[i],
{
    broadcast use group_multiset_axioms;
    broadcast use vstd::seq_lib::group_to_multiset_ensures;

    lemma_prefix_multiset(s, lav, i + 1);
    let s_prefix = s.take(i + 1);
    let lav_prefix = lav.take(i + 1);
    assert(lav_prefix[i] == lav[i]);
    assert(lav_prefix.contains(lav[i]));
    assert(s_prefix.to_multiset().count(lav[i]) > 0);
    let k = choose |q: int| 0 <= q < s_prefix.len() && s_prefix[q] == lav[i];
    k
}

/// Fisher–Yates shuffle, Eris spec:
///
/// ```text
///   { ↯(1/n!) }  fisher_yates(v, lav)  { v ≡ₚ old(v)  ∧  v ≠ lav }
/// ```
///
/// `lav` is any permutation of the input, so every specific
/// permutation is hit with probability at most 1/n! — uniformity, since a
/// duplicate-free length-n vector has exactly n! permutations.
pub fn fisher_yates(
    v: &mut Vec<u64>,
    Ghost(lav): Ghost<Seq<u64>>,
    Tracked(credit_in): Tracked<ErrorCreditResource>,
)
    requires
        old(v)@.no_duplicates(),
        lav.to_multiset() == old(v)@.to_multiset(),
        credit_in@ =~= (Value { car: 1real / factorial(old(v)@.len()) }),
    ensures
        final(v)@.len() == old(v)@.len(),
        final(v)@.to_multiset() == old(v)@.to_multiset(),
        final(v)@ != lav,
{
    let ghost n = old(v)@.len();
    let tracked mut credit = credit_in;
    let ghost mut eps: real = 1real / factorial(n);

    proof {
        vstd::seq_lib::to_multiset_len(lav);
        vstd::seq_lib::to_multiset_len(old(v)@);
        lemma_factorial_pos(n);
        assert(eps >= 0real) by(nonlinear_arith)
            requires factorial(n) >= 1real, eps == 1real / factorial(n);
    }

    if v.len() <= 1 {
        proof {
            // 1/0! = 1/1! = 1: owning ↯(1) is contradictory.  (For n = 1 the
            // postcondition v ≠ lav is indeed only true with probability 0.)
            assert(factorial(0nat) == 1real);
            assert(factorial(1nat) == 1nat as real * factorial(0nat));
            ec_contradict(&credit);
        }
        return;
    }

    let mut i: usize = v.len() - 1;

    while i >= 1
        invariant
            v@.len() == n,
            lav.len() == n,
            n <= usize::MAX,
            i < n,
            old(v)@.no_duplicates(),
            v@.to_multiset() == old(v)@.to_multiset(),
            lav.to_multiset() == old(v)@.to_multiset(),
            credit@ =~= (Value { car: eps }),
            eps >= 0real,
            eq_from(v@, lav, i as int + 1) ==> eps >= 1real / factorial((i + 1) as nat),
        decreases i,
    {
        // Snapshots of the vector and credit before this iteration's draw + swap.
        let ghost v_pre = v@;
        let ghost eps_pre = eps;
        // The draw below has i+1 equally likely outcomes.
        let ghost n_outcomes: nat = (i + 1) as nat;
        // Does the already-fixed suffix v[i+1..] still agree with lav[i+1..]?
        let ghost suffix_matches = eq_from(v_pre, lav, i as int + 1);

        // k: the unique position of lav[i] within v[0..=i].
        let ghost mut k: nat = 0;
        proof {
            if suffix_matches {
                let k0 = lemma_find_target(v_pre, lav, i as int);
                k = k0 as nat;
                assert(k <= i && v_pre[k as int] == lav[i as int]);
            }
        }

        // While the suffix still matches, the whole budget rides on outcome k;
        // once it differs, nothing is needed.
        let ghost alloc = |x: nat|
            if suffix_matches && x == k { (n_outcomes as real) * eps_pre } else { 0real };

        proof {
            assert forall |x: nat| (#[trigger] alloc(x)) >= 0real by {
                if suffix_matches && x == k {
                    assert((n_outcomes as real) * eps_pre >= 0real) by(nonlinear_arith)
                        requires eps_pre >= 0real, n_outcomes >= 1;
                }
            };
            // ε ≥ average(i+1, alloc)
            if suffix_matches {
                lemma_sum_point(alloc, k, (n_outcomes as real) * eps_pre, n_outcomes);
                assert(((n_outcomes as real) * eps_pre) / (n_outcomes as real) == eps_pre)
                    by(nonlinear_arith)
                    requires n_outcomes >= 1;
            } else {
                lemma_sum_zero(alloc, n_outcomes);
                assert((0real) / (n_outcomes as real) == 0real) by(nonlinear_arith)
                    requires n_outcomes >= 1;
            }
        }

        let bound: u64 = (i as u64) + 1;
        let (j64, Tracked(credit_out)) = rand_u64(bound, Tracked(credit), Ghost(alloc));
        proof {
            credit = credit_out;
            eps = alloc(j64 as nat);
        }

        // swap v[i] <-> v[j]
        let j: usize = j64 as usize;
        let val_i: u64 = v[i];
        let val_j: u64 = v[j];
        v.set(i, val_j);
        v.set(j, val_i);

        proof {
            lemma_swap_multiset(v_pre, i as int, j as int);

            if suffix_matches {
                if j as nat == k {
                    // Kept matching: received (i+1)·ε ≥ (i+1)/(i+1)! = 1/i!.
                    lemma_factorial_pos(i as nat);
                    assert(factorial(n_outcomes) == (n_outcomes as real) * factorial(i as nat));
                    assert(eps >= 1real / factorial(i as nat)) by(nonlinear_arith)
                        requires
                            eps == (n_outcomes as real) * eps_pre,
                            eps_pre >= 1real / factorial(n_outcomes),
                            factorial(n_outcomes) == (n_outcomes as real) * factorial(i as nat),
                            factorial(i as nat) >= 1real,
                            n_outcomes >= 1;
                } else {
                    // j ≠ k: the new v[i] = v_pre[j] ≠ v_pre[k] = lav[i] (no
                    // duplicates), so the suffix from i on now disagrees — forever.
                    lemma_nodup_transfer(old(v)@, v_pre);
                    assert(v@[i as int] != lav[i as int]);
                    assert(!eq_from(v@, lav, i as int));
                }
            } else {
                // Already disagreeing beyond i; the swap can't fix positions > i.
                let p = choose |p: int| i as int + 1 <= p < v_pre.len() && v_pre[p] != lav[p];
                assert(!eq_from(v@, lav, i as int));
            }
        }

        i = i - 1;
    }

    proof {
        // i = 0: a still-matching suffix v[1..] = lav[1..] would mean we own
        // ↯(1/1!) = ↯(1) — contradiction.
        if eq_from(v@, lav, 1) {
            assert(factorial(0nat) == 1real);
            assert(factorial(1nat) == 1nat as real * factorial(0nat));
            ec_contradict(&credit);
        }
        // So some position ≥ 1 differs; in particular v ≠ lav.
        assert(v@ != lav) by {
            if v@ == lav {
                assert(eq_from(v@, lav, 1));
            }
        };
    }
}

} // verus!
