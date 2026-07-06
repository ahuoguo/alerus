//! FDR — Lumbroso's Fast Dice Roller: sample uniformly from {0, …, n−1} using only
//! fair coin flips.
//!
//! References (verification via distributional invariants):
//!   - [FM 26]   https://arxiv.org/abs/2509.06410
//!   - [LAFI 26] https://popl26.sigplan.org/details/lafi-2026-papers/19/
//!
//! ── Algorithm (Lumbroso) ──────────────────────────────────────────────────────
//! ```text
//!   v ← 1; c ← 0
//!   loop {
//!       v ← 2·v;  c ← 2·c + flip();          // flip() ∈ {0,1}, fair
//!       if v ≥ n {
//!           if c < n { return c }            // accept
//!           else { v ← v − n;  c ← c − n }   // reject, restart the residual range
//!       }
//!   }
//! ```
//!
//! We prove the Expectation-Preservation Rule for the uniform distribution:
//!
//! ```text
//!            ε ≥ (1/n)·Σ_{i<n} ℰ(i)
//!   ───────────────────────────────────────────────
//!   [{ ↯(ε) }] sample_fdr(n) [{ v. ↯(ℰ(v)) }]
//! ```
//!
//! ── Idea: two credits at one budget (cf. random_walk.rs) ──────────────────────
//! Per execution path, the error-credit framework tracks two non-negative reals.
//!
//!  (1) VALUE — the conditional expectation  fdr_f(v,c,k) = E[ℰ(out) | state (v,c)]
//!      using ≤ k coin flips:
//! ```text
//!        fdr_f(v,c,0) = 0                                  (ran out of k)
//!        fdr_f(v,c,k) = ½·( fdr_h(2v,2c,k−1) + fdr_h(2v,2c+1,k−1) )
//!        fdr_h(v,c,k) = ℰ(c)             if v ≥ n, c < n   (accept)
//!                     = fdr_f(v−n,c−n,k) if v ≥ n, c ≥ n   (reject, restart)
//!                     = fdr_f(v,c,k)     if v < n          (continue doubling)
//! ```
//!      On accept the value credit is exactly ℰ(c) (correctness), and the truncated
//!      mean never exceeds the uniform mean:  fdr_f(1,0,k) ≤ average_nat(n,ℰ)
//!      (`lemma_fdr_f_le_average`), so the uniform precondition ε ≥ average_nat starts it.
//!
//!  (2) TERMINATION — the failure probability  fdr_fail_f(v,c,k) = 1 − P(accept within k flips)
//! ```text
//!        fdr_fail_f(v,c,0) = 1                                       (ran out of k)
//!        fdr_fail_f(v,c,k) = ½·( fdr_fail_h(2v,2c,k−1) + fdr_fail_h(2v,2c+1,k−1) )
//!        fdr_fail_h(v,c,k) = 0                     if v ≥ n, c < n   (accept)
//!                          = fdr_fail_f(v−n,c−n,k) if v ≥ n, c ≥ n   (reject, restart)
//!                          = fdr_fail_f(v,c,k)     if v < n          (continue doubling)
//! ```
//!
//! The loop carries  credit = ↯(ce)  with  ce ≥ fdr_f(v,c,k) + fdr_fail_f(v,c,k),
//! `k` the structural `decreases`.  Each coin flip is credit-exact (the allocation
//! b ↦ fdr_h(…) + fdr_fail_h(…) averages to the invariant's RHS); on ACCEPT the fail
//! term is 0, so the held credit is exactly ↯(ℰ(c)); at k = 0 the fail term is 1,
//! forcing ce ≥ 1 — impossible for a held credit (< 1), so `ec_contradict`.  No
//! amplification: termination is funded directly by the failure-probability credit.
//!
//! Almost-sure termination (that some `k` suffices) is FDR's analogue of the random
//! walk's harmonic argument, via the SAME sum-trick as the value bound:  summing the
//! failure probability over c,  FS(v,k) := Σ_{c<v} fdr_fail_f(v,c,k),  collapses by
//! reindex + threshold-split to  FS(v,k) = ½·FS(next(v), k−1),  where next(v) = 2v if
//! 2v < n else 2v−n (the loop's own v-update — so next(v) ∈ [0,n) because v < n).  With
//! FS(v,0) = v, unrolling gives  FS(v,k) ≤ n / 2^k → 0  (`lemma_fdr_fail_fs_bound`).  Since
//! fdr_fail_f(1,0,k) = FS(1,k) ≤ n/2^k, Archimedes yields a sufficient `k`
//! (`lemma_fdr_fail_witness`).

use vstd::prelude::*;

verus! {

use crate::ec::*;
#[cfg(verus_keep_ghost)]
use crate::ec::ErrorCreditCarrier::Value;
use crate::rand_primitives::{thin_air, rand_2_u64};
#[cfg(verus_keep_ghost)]
use crate::rand_primitives::{sum_credit, average_nat};
#[cfg(verus_keep_ghost)]
use crate::math::pow::{pow, archimedean_exp_growth};

/// Fuel-bounded conditional expectation  E[ℰ(out) | loop-head state (v, c)]  using
/// ≤ `k` coin flips — the value the credit carries.  A run that exhausts its
/// budget before accepting contributes 0.  One flip turns (v,c) into (2v, 2c+b),
/// b ∈ {0,1} each w.p. ½, so fdr_f averages the two post-double `fdr_h` cases.
pub open spec fn fdr_f(n: nat, e: spec_fn(real) -> real, v: nat, c: nat, k: nat) -> real
    decreases k, 0nat,
{
    if k == 0 {
        0real
    } else {
        (fdr_h(n, e, 2 * v, 2 * c, (k - 1) as nat)
            + fdr_h(n, e, 2 * v, 2 * c + 1, (k - 1) as nat)) / 2real
    }
}

/// Evaluates an already-doubled state (v, c) — `fdr_f` feeds it (2·v, 2·c+b):
/// accept if v ≥ n and c < n (output c), reject if v ≥ n and c ≥ n (restart the
/// residual range (v−n, c−n)), otherwise keep doubling.
pub open spec fn fdr_h(n: nat, e: spec_fn(real) -> real, v: nat, c: nat, k: nat) -> real
    decreases k, 1nat,
{
    if v >= n {
        if c < n {
            e(c as real)                          // accept
        } else {
            fdr_f(n, e, (v - n) as nat, (c - n) as nat, k)   // reject, restart
        }
    } else {
        fdr_f(n, e, v, c, k)                   // continue doubling
    }
}

// The uniform expectation FDR must dominate is the framework's average of ℰ over
// {0, …, n−1}:  average_nat(n, ℰ) = sum_credit(ℰ, n) / n = (1/n)·Σ_{i<n} ℰ(i)
// (see `rand_primitives`; this is exactly what `ho_rej_samp` uses).  fdr_f(1,0,·)
// converges up to it, and we prove the ≤ half below.

// Both approximations are non-negative when ℰ ≥ 0.  The f/h split with matching
// (k, tag) measures mirrors the spec fns' mutual recursion (f tag 0, h tag 1).

pub proof fn lemma_fdr_f_nonneg(n: nat, e: spec_fn(real) -> real, v: nat, c: nat, k: nat)
    requires forall |x: real| (#[trigger] e(x)) >= 0real,
    ensures fdr_f(n, e, v, c, k) >= 0real,
    decreases k, 0nat,
{
    if k > 0 {
        lemma_fdr_h_nonneg(n, e, 2 * v, 2 * c, (k - 1) as nat);
        lemma_fdr_h_nonneg(n, e, 2 * v, 2 * c + 1, (k - 1) as nat);
    }
}

pub proof fn lemma_fdr_h_nonneg(n: nat, e: spec_fn(real) -> real, v: nat, c: nat, k: nat)
    requires forall |x: real| (#[trigger] e(x)) >= 0real,
    ensures fdr_h(n, e, v, c, k) >= 0real,
    decreases k, 1nat,
{
    if v >= n {
        if c < n {
            assert(e(c as real) >= 0real);
        } else {
            lemma_fdr_f_nonneg(n, e, (v - n) as nat, (c - n) as nat, k);
        }
    } else {
        lemma_fdr_f_nonneg(n, e, v, c, k);
    }
}

// ─────────────────────────────────────────────────────────────────────────────
//  The uniform bound  fdr_f(1,0,k) ≤ average_nat(n,ℰ)  (so ε ≥ average_nat starts the loop).
//  Only ≤ is needed — every sampler here uses an inequality precondition
//  `ε ≥ expectation`.  Proof: the c-summed approximation
//  S(v,k) := Σ_{c<v} fdr_f(v,c,k) satisfies S(v,k) ≤ v·average_nat by induction on the
//  flip budget k (well-founded), via a reindexing identity and the threshold split.
// ─────────────────────────────────────────────────────────────────────────────

/// Σ_{c<j} fdr_f(n,e,v,c,k)  — sum of the k-flip approximation over the first j
/// values c at range v.  (S(v,k) := fdr_fsum_upto(n,e,v,v,k).)
pub open spec fn fdr_fsum_upto(n: nat, e: spec_fn(real) -> real, v: nat, j: nat, k: nat) -> real
    decreases j,
{
    if j == 0 { 0real }
    else { fdr_fsum_upto(n, e, v, (j - 1) as nat, k) + fdr_f(n, e, v, (j - 1) as nat, k) }
}

/// Σ_{c<j} fdr_h(n,e,v,c,k).
pub open spec fn fdr_hsum_upto(n: nat, e: spec_fn(real) -> real, v: nat, j: nat, k: nat) -> real
    decreases j,
{
    if j == 0 { 0real }
    else { fdr_hsum_upto(n, e, v, (j - 1) as nat, k) + fdr_h(n, e, v, (j - 1) as nat, k) }
}

/// Σ_{c<j} ( fdr_h(n,e,v,2c,k) + fdr_h(n,e,v,2c+1,k) ).
pub open spec fn fdr_pairsum(n: nat, e: spec_fn(real) -> real, v: nat, j: nat, k: nat) -> real
    decreases j,
{
    if j == 0 { 0real }
    else {
        fdr_pairsum(n, e, v, (j - 1) as nat, k)
            + fdr_h(n, e, v, (2 * ((j - 1) as nat)) as nat, k) + fdr_h(n, e, v, (2 * ((j - 1) as nat) + 1) as nat, k)
    }
}

/// n·average = Σ_{i<n} ℰ(i)  (n > 0):  just unfolds `average_nat`.
pub proof fn lemma_fdr_average_sum(n: nat, e: spec_fn(real) -> real)
    requires n > 0,
    ensures sum_credit(e, n) == (n as real) * average_nat(n, e),
{
    assert(sum_credit(e, n) == (n as real) * (sum_credit(e, n) / n as real)) by(nonlinear_arith)
        requires n > 0;
}

/// sum_credit(ℰ, mm) = Σ_{i<mm} ℰ(i) ≥ 0 for ℰ ≥ 0.
pub proof fn lemma_fdr_sum_nonneg(e: spec_fn(real) -> real, mm: nat)
    requires forall |x: real| (#[trigger] e(x)) >= 0real,
    ensures sum_credit(e, mm) >= 0real,
    decreases mm,
{
    if mm > 0 {
        lemma_fdr_sum_nonneg(e, (mm - 1) as nat);
        assert(e((mm - 1) as real) >= 0real);   // sum_credit's term, ℰ ≥ 0
    }
}

/// average_nat(n, ℰ) ≥ 0 for ℰ ≥ 0  (n > 0).
pub proof fn lemma_fdr_average_nonneg(n: nat, e: spec_fn(real) -> real)
    requires forall |x: real| (#[trigger] e(x)) >= 0real, n > 0,
    ensures average_nat(n, e) >= 0real,
{
    lemma_fdr_sum_nonneg(e, n);
    assert(average_nat(n, e) >= 0real) by(nonlinear_arith)
        requires average_nat(n, e) == sum_credit(e, n) / n as real, sum_credit(e, n) >= 0real, n > 0;
}

/// Reindex:  Σ_{c<j}(fdr_h(v,2c)+fdr_h(v,2c+1)) = Σ_{c<2j} fdr_h(v,c).
pub proof fn lemma_fdr_pairsum_eq_hsum(n: nat, e: spec_fn(real) -> real, v: nat, j: nat, k: nat)
    ensures fdr_pairsum(n, e, v, j, k) == fdr_hsum_upto(n, e, v, 2 * j, k),
    decreases j,
{
    if j > 0 {
        lemma_fdr_pairsum_eq_hsum(n, e, v, (j - 1) as nat, k);
        // hsum(2j) = hsum(2j-1) + h(2j-1) = hsum(2j-2) + h(2j-2) + h(2j-1)
        assert(fdr_hsum_upto(n, e, v, 2 * j, k)
            == fdr_hsum_upto(n, e, v, (2 * j - 1) as nat, k) + fdr_h(n, e, v, (2 * j - 1) as nat, k));
        assert(fdr_hsum_upto(n, e, v, (2 * j - 1) as nat, k)
            == fdr_hsum_upto(n, e, v, (2 * j - 2) as nat, k) + fdr_h(n, e, v, (2 * j - 2) as nat, k));
        assert(fdr_hsum_upto(n, e, v, 2 * j, k)
            == fdr_hsum_upto(n, e, v, (2 * j - 2) as nat, k)
                + fdr_h(n, e, v, (2 * j - 2) as nat, k) + fdr_h(n, e, v, (2 * j - 1) as nat, k));
        assert((2 * j - 2) as nat == 2 * ((j - 1) as nat));
        assert((2 * j - 1) as nat == 2 * ((j - 1) as nat) + 1);
    }
}

/// fdr_fsum_upto(v,j,k+1) = ½ · fdr_pairsum(2v,j,k)  (term-by-term from fdr_f's recursion).
pub proof fn lemma_fdr_fsum_half_pairsum(n: nat, e: spec_fn(real) -> real, v: nat, j: nat, k: nat)
    ensures fdr_fsum_upto(n, e, v, j, (k + 1) as nat) == (1real / 2real) * fdr_pairsum(n, e, 2 * v, j, k),
    decreases j,
{
    if j > 0 {
        lemma_fdr_fsum_half_pairsum(n, e, v, (j - 1) as nat, k);
        // fdr_f(v,j-1,k+1) = (fdr_h(2v,2(j-1),k) + fdr_h(2v,2(j-1)+1,k))/2
        let ghost prev_f = fdr_fsum_upto(n, e, v, (j - 1) as nat, (k + 1) as nat);
        let ghost prev_p = fdr_pairsum(n, e, 2 * v, (j - 1) as nat, k);
        let ghost ha = fdr_h(n, e, 2 * v, (2 * ((j - 1) as nat)) as nat, k);
        let ghost hb = fdr_h(n, e, 2 * v, (2 * ((j - 1) as nat) + 1) as nat, k);
        assert(fdr_f(n, e, v, (j - 1) as nat, (k + 1) as nat) == (ha + hb) / 2real);
        assert(prev_f == (1real / 2real) * prev_p);
        assert(fdr_fsum_upto(n, e, v, j, (k + 1) as nat) == prev_f + (ha + hb) / 2real);
        assert(fdr_pairsum(n, e, 2 * v, j, k) == prev_p + ha + hb);
        assert(prev_f + (ha + hb) / 2real == (1real / 2real) * (prev_p + ha + hb)) by(nonlinear_arith)
            requires prev_f == (1real / 2real) * prev_p;
    }
}

/// Below threshold (v < n): every h-term continues, so the h-sum equals the f-sum.
pub proof fn lemma_fdr_hsum_eq_fsum_lt_n(n: nat, e: spec_fn(real) -> real, v: nat, j: nat, k: nat)
    requires v < n,
    ensures fdr_hsum_upto(n, e, v, j, k) == fdr_fsum_upto(n, e, v, j, k),
    decreases j,
{
    if j > 0 {
        lemma_fdr_hsum_eq_fsum_lt_n(n, e, v, (j - 1) as nat, k);
        assert(fdr_h(n, e, v, (j - 1) as nat, k) == fdr_f(n, e, v, (j - 1) as nat, k));  // v < n
    }
}

/// At/above threshold, the low part (c < n) sums the accept values ℰ — exactly the
/// framework's sum_credit(ℰ, j) = Σ_{c<j} ℰ(c).
pub proof fn lemma_fdr_hsum_low(n: nat, e: spec_fn(real) -> real, v: nat, j: nat, k: nat)
    requires v >= n, j <= n,
    ensures fdr_hsum_upto(n, e, v, j, k) == sum_credit(e, j),
    decreases j,
{
    if j > 0 {
        lemma_fdr_hsum_low(n, e, v, (j - 1) as nat, k);
        assert(((j - 1) as nat) < n);
        assert(fdr_h(n, e, v, (j - 1) as nat, k) == e(((j - 1) as nat) as real));  // accept
        assert(((j - 1) as nat) as real == (j - 1) as real);    // = sum_credit's term
    }
}

/// Threshold split:  for v ≥ n and i ≤ v−n,
///   Σ_{c<n+i} fdr_h(v,c) = Σ_{c<n} ℰ(c)  +  Σ_{c'<i} fdr_f(v−n, c', k).
pub proof fn lemma_fdr_hsum_split(n: nat, e: spec_fn(real) -> real, v: nat, i: nat, k: nat)
    requires v >= n, i <= (v - n) as nat,
    ensures
        fdr_hsum_upto(n, e, v, (n + i) as nat, k)
            == sum_credit(e, n) + fdr_fsum_upto(n, e, (v - n) as nat, i, k),
    decreases i,
{
    if i == 0 {
        lemma_fdr_hsum_low(n, e, v, n, k);   // Σ_{c<n} h = sum_credit(e,n)
    } else {
        lemma_fdr_hsum_split(n, e, v, (i - 1) as nat, k);
        // h(v, n+i-1, k): v >= n and c = n+i-1 >= n  ⟹ reject ⟹ fdr_f(v-n, (n+i-1)-n, k) = fdr_f(v-n, i-1, k)
        assert((n + i) as nat - 1 == n + (i - 1) as nat);
        assert(n + (i - 1) as nat >= n);
        assert(fdr_h(n, e, v, (n + (i - 1) as nat) as nat, k)
            == fdr_f(n, e, (v - n) as nat, (i - 1) as nat, k)) by {
            assert((n + (i - 1) as nat - n) as nat == (i - 1) as nat);
        }
    }
}

/// S(v,k) := Σ_{c<v} fdr_f(v,c,k) ≤ v·average_nat(n,ℰ),  by induction on k k.
pub proof fn lemma_fdr_sum_le(n: nat, e: spec_fn(real) -> real, v: nat, k: nat)
    requires forall |x: real| (#[trigger] e(x)) >= 0real, n > 0,
    ensures fdr_fsum_upto(n, e, v, v, k) <= (v as real) * average_nat(n, e),
    decreases k,
{
    lemma_fdr_average_nonneg(n, e);
    let ghost tgt = average_nat(n, e);
    if k == 0 {
        // fdr_f(·,0) = 0, so the whole sum is 0.
        assert(fdr_fsum_upto(n, e, v, v, 0nat) == 0real) by {
            lemma_fdr_fsum_zero(n, e, v, v);
        }
        assert(0real <= (v as real) * tgt) by(nonlinear_arith) requires tgt >= 0real;
    } else {
        let ghost kk = (k - 1) as nat;
        // S(v,k) = ½ · pairsum(2v, v, kk) = ½ · hsum(2v, 2v, kk).
        lemma_fdr_fsum_half_pairsum(n, e, v, v, kk);
        lemma_fdr_pairsum_eq_hsum(n, e, 2 * v, v, kk);
        let ghost hh = fdr_hsum_upto(n, e, 2 * v, 2 * v, kk);
        assert(fdr_fsum_upto(n, e, v, v, k) == (1real / 2real) * hh);
        if 2 * v < n {
            lemma_fdr_hsum_eq_fsum_lt_n(n, e, 2 * v, 2 * v, kk);   // hh = S(2v, kk)
            lemma_fdr_sum_le(n, e, 2 * v, kk);                        // S(2v,kk) ≤ 2v·tgt
            let ghost s2 = fdr_fsum_upto(n, e, 2 * v, 2 * v, kk);
            assert(hh == s2);
            assert((1real / 2real) * hh <= (v as real) * tgt) by(nonlinear_arith)
                requires hh == s2, s2 <= (2 * v) as real * tgt;
        } else {
            // hh = sum_credit(e,n) + S(2v−n, kk) = n·tgt + S(2v−n, kk).
            lemma_fdr_hsum_split(n, e, 2 * v, (2 * v - n) as nat, kk);
            assert((n + (2 * v - n) as nat) as nat == 2 * v);
            lemma_fdr_average_sum(n, e);
            lemma_fdr_sum_le(n, e, (2 * v - n) as nat, kk);
            let ghost sr = fdr_fsum_upto(n, e, (2 * v - n) as nat, (2 * v - n) as nat, kk);
            assert(hh == sum_credit(e, n) + sr);
            assert((1real / 2real) * hh <= (v as real) * tgt) by(nonlinear_arith)
                requires hh == sum_credit(e, n) + sr,
                    sum_credit(e, n) == (n as real) * tgt,
                    sr <= ((2 * v - n) as nat) as real * tgt,
                    2 * v >= n;
        }
    }
}

/// fdr_fsum_upto at k 0 is 0.
pub proof fn lemma_fdr_fsum_zero(n: nat, e: spec_fn(real) -> real, v: nat, j: nat)
    ensures fdr_fsum_upto(n, e, v, j, 0nat) == 0real,
    decreases j,
{
    if j > 0 {
        lemma_fdr_fsum_zero(n, e, v, (j - 1) as nat);
    }
}

/// Translation lemma:  fdr_f(n, ℰ, 1, 0, k) ≤ average_nat(n, ℰ).  A finite-budget
/// run's conditional expectation never exceeds the genuine uniform average
/// average_nat(n, ℰ) = (1/n)·Σ_{i<n} ℰ(i)  (from `lemma_fdr_sum_le` at v = 1, where
/// S(1, k) = fdr_f(1, 0, k)).  This is what lets `sample_fdr` take the real
/// uniform-distribution precondition ε ≥ average_nat(n, ℰ).
pub proof fn lemma_fdr_f_le_average(n: nat, e: spec_fn(real) -> real, k: nat)
    requires forall |x: real| (#[trigger] e(x)) >= 0real, n > 0,
    ensures fdr_f(n, e, 1, 0, k) <= average_nat(n, e),
{
    reveal_with_fuel(fdr_fsum_upto, 2);
    lemma_fdr_sum_le(n, e, 1, k);   // S(1, k) ≤ 1·average
    assert(fdr_fsum_upto(n, e, 1, 1, k) == fdr_f(n, e, 1, 0, k));
    assert((1 as real) * average_nat(n, e) == average_nat(n, e));
}

// ═════════════════════════════════════════════════════════════════════════════
//  FUEL-FREE (always-returns) FDR.
//
//  Almost-sure termination is carried — following `random_walk.rs` — as a
//  *failure-probability* credit  fdr_fail_f(v,c,steps) = 1 − P(accept within
//  `steps` flips).  Note it does NOT depend on ℰ (it is purely structural).
//  Combined with the (k-bounded) value credit fdr_f at the SAME budget, the
//  loop carries  ε ≥ fdr_f(v,c,depth) + fdr_fail_f(v,c,depth):  on accept fail = 0
//  (exact ↯(ℰ(c))), at depth = 0 fail = 1 ⇒ ε ≥ 1 ⇒ ec_contradict.  `depth` is the
//  structural decreases — no amplification.
//
//  The a.s.-termination bound comes from the same sum-trick as the value bound above:
//  FS(v,steps) := Σ_{c<v} fdr_fail_f(v,c,steps) satisfies FS(v,steps) = ½·FS(next,steps−1)
//  (next(v) ∈ [0,n)), and FS(v,0) = v, so FS(v,steps) ≤ n / 2^steps → 0.  Since
//  fdr_fail_f(1,0,steps) = FS(1,steps), the start state accepts a.s.
// ═════════════════════════════════════════════════════════════════════════════

/// Failure probability at a loop-head state (v,c) within `steps` coin flips:
/// 1 − P(accept within `steps`).  (Independent of ℰ.)
pub open spec fn fdr_fail_f(n: nat, v: nat, c: nat, steps: nat) -> real
    decreases steps, 0nat,
{
    if steps == 0 {
        1real
    } else {
        (fdr_fail_h(n, 2 * v, 2 * c, (steps - 1) as nat)
            + fdr_fail_h(n, 2 * v, 2 * c + 1, (steps - 1) as nat)) / 2real
    }
}

/// Post-double failure prob:  accept (v ≥ n, c < n) ⇒ 0; reject ⇒ recurse at (v−n,c−n);
/// continue (v < n) ⇒ recurse at (v,c).
pub open spec fn fdr_fail_h(n: nat, v: nat, c: nat, steps: nat) -> real
    decreases steps, 1nat,
{
    if v >= n {
        if c < n { 0real } else { fdr_fail_f(n, (v - n) as nat, (c - n) as nat, steps) }
    } else {
        fdr_fail_f(n, v, c, steps)
    }
}

// 0 ≤ fdr_fail ≤ 1  (mutual induction on (steps, tag), mirroring fdr_f/fdr_h).

pub proof fn lemma_fdr_fail_f_nonneg(n: nat, v: nat, c: nat, steps: nat)
    ensures fdr_fail_f(n, v, c, steps) >= 0real,
    decreases steps, 0nat,
{
    if steps > 0 {
        lemma_fdr_fail_h_nonneg(n, 2 * v, 2 * c, (steps - 1) as nat);
        lemma_fdr_fail_h_nonneg(n, 2 * v, 2 * c + 1, (steps - 1) as nat);
    }
}

pub proof fn lemma_fdr_fail_h_nonneg(n: nat, v: nat, c: nat, steps: nat)
    ensures fdr_fail_h(n, v, c, steps) >= 0real,
    decreases steps, 1nat,
{
    if v >= n {
        if c < n { } else { lemma_fdr_fail_f_nonneg(n, (v - n) as nat, (c - n) as nat, steps); }
    } else {
        lemma_fdr_fail_f_nonneg(n, v, c, steps);
    }
}

pub proof fn lemma_fdr_fail_f_le_one(n: nat, v: nat, c: nat, steps: nat)
    ensures fdr_fail_f(n, v, c, steps) <= 1real,
    decreases steps, 0nat,
{
    if steps > 0 {
        lemma_fdr_fail_h_le_one(n, 2 * v, 2 * c, (steps - 1) as nat);
        lemma_fdr_fail_h_le_one(n, 2 * v, 2 * c + 1, (steps - 1) as nat);
    }
}

pub proof fn lemma_fdr_fail_h_le_one(n: nat, v: nat, c: nat, steps: nat)
    ensures fdr_fail_h(n, v, c, steps) <= 1real,
    decreases steps, 1nat,
{
    if v >= n {
        if c < n { } else { lemma_fdr_fail_f_le_one(n, (v - n) as nat, (c - n) as nat, steps); }
    } else {
        lemma_fdr_fail_f_le_one(n, v, c, steps);
    }
}

// ── Sum machinery for the a.s.-termination bound  FS(v,steps) ≤ n / 2^steps ────
// FS(v,steps) := Σ_{c<v} fdr_fail_f(v,c,steps).  Same reindex/split as step 2,
// except the accept terms contribute 0 (not ℰ).

pub open spec fn fdr_fail_fsum(n: nat, v: nat, j: nat, steps: nat) -> real
    decreases j,
{
    if j == 0 { 0real }
    else { fdr_fail_fsum(n, v, (j - 1) as nat, steps) + fdr_fail_f(n, v, (j - 1) as nat, steps) }
}

pub open spec fn fdr_fail_hsum(n: nat, v: nat, j: nat, steps: nat) -> real
    decreases j,
{
    if j == 0 { 0real }
    else { fdr_fail_hsum(n, v, (j - 1) as nat, steps) + fdr_fail_h(n, v, (j - 1) as nat, steps) }
}

pub open spec fn fdr_fail_pairsum(n: nat, v: nat, j: nat, steps: nat) -> real
    decreases j,
{
    if j == 0 { 0real }
    else {
        fdr_fail_pairsum(n, v, (j - 1) as nat, steps)
            + fdr_fail_h(n, v, 2 * ((j - 1) as nat), steps)
            + fdr_fail_h(n, v, 2 * ((j - 1) as nat) + 1, steps)
    }
}

/// pow(2, ·) > 0.
pub proof fn lemma_pow2_pos(k: nat)
    ensures pow(2real, k) > 0real,
    decreases k,
{
    if k > 0 {
        lemma_pow2_pos((k - 1) as nat);
        assert(pow(2real, k) == 2real * pow(2real, (k - 1) as nat));
    }
}

/// Reindex:  Σ_{c<j}(fail_h(v,2c)+fail_h(v,2c+1)) = Σ_{c<2j} fail_h(v,c).
pub proof fn lemma_fdr_fail_pairsum_eq_hsum(n: nat, v: nat, j: nat, steps: nat)
    ensures fdr_fail_pairsum(n, v, j, steps) == fdr_fail_hsum(n, v, 2 * j, steps),
    decreases j,
{
    if j > 0 {
        reveal_with_fuel(fdr_fail_hsum, 2);
        lemma_fdr_fail_pairsum_eq_hsum(n, v, (j - 1) as nat, steps);
        assert(fdr_fail_hsum(n, v, 2 * j, steps)
            == fdr_fail_hsum(n, v, (2 * j - 2) as nat, steps)
                + fdr_fail_h(n, v, (2 * j - 2) as nat, steps)
                + fdr_fail_h(n, v, (2 * j - 1) as nat, steps));
        assert((2 * j - 2) as nat == 2 * ((j - 1) as nat));
        assert((2 * j - 1) as nat == 2 * ((j - 1) as nat) + 1);
    }
}

/// fsum(v,j,steps+1) = ½ · pairsum(2v,j,steps).
pub proof fn lemma_fdr_fail_fsum_half_pairsum(n: nat, v: nat, j: nat, steps: nat)
    ensures fdr_fail_fsum(n, v, j, (steps + 1) as nat)
        == (1real / 2real) * fdr_fail_pairsum(n, 2 * v, j, steps),
    decreases j,
{
    if j > 0 {
        lemma_fdr_fail_fsum_half_pairsum(n, v, (j - 1) as nat, steps);
        let ghost prev_f = fdr_fail_fsum(n, v, (j - 1) as nat, (steps + 1) as nat);
        let ghost prev_p = fdr_fail_pairsum(n, 2 * v, (j - 1) as nat, steps);
        let ghost ha = fdr_fail_h(n, 2 * v, 2 * ((j - 1) as nat), steps);
        let ghost hb = fdr_fail_h(n, 2 * v, 2 * ((j - 1) as nat) + 1, steps);
        assert(fdr_fail_f(n, v, (j - 1) as nat, (steps + 1) as nat) == (ha + hb) / 2real);
        assert(prev_f == (1real / 2real) * prev_p);
        assert(prev_f + (ha + hb) / 2real == (1real / 2real) * (prev_p + ha + hb)) by(nonlinear_arith)
            requires prev_f == (1real / 2real) * prev_p;
    }
}

/// Below threshold (v < n): every term continues, so hsum = fsum.
pub proof fn lemma_fdr_fail_hsum_eq_fsum_lt_n(n: nat, v: nat, j: nat, steps: nat)
    requires v < n,
    ensures fdr_fail_hsum(n, v, j, steps) == fdr_fail_fsum(n, v, j, steps),
    decreases j,
{
    if j > 0 {
        lemma_fdr_fail_hsum_eq_fsum_lt_n(n, v, (j - 1) as nat, steps);
        assert(fdr_fail_h(n, v, (j - 1) as nat, steps) == fdr_fail_f(n, v, (j - 1) as nat, steps));
    }
}

/// Accept region (v ≥ n, c < n) contributes 0.
pub proof fn lemma_fdr_fail_hsum_low_zero(n: nat, v: nat, j: nat, steps: nat)
    requires v >= n, j <= n,
    ensures fdr_fail_hsum(n, v, j, steps) == 0real,
    decreases j,
{
    if j > 0 {
        lemma_fdr_fail_hsum_low_zero(n, v, (j - 1) as nat, steps);
        assert(((j - 1) as nat) < n);
        assert(fdr_fail_h(n, v, (j - 1) as nat, steps) == 0real);   // accept ⇒ 0
    }
}

/// Threshold split:  for v ≥ n, i ≤ v−n,  Σ_{c<n+i} fail_h(v,c) = Σ_{c'<i} fail_f(v−n,c').
pub proof fn lemma_fdr_fail_hsum_split(n: nat, v: nat, i: nat, steps: nat)
    requires v >= n, i <= (v - n) as nat,
    ensures fdr_fail_hsum(n, v, (n + i) as nat, steps) == fdr_fail_fsum(n, (v - n) as nat, i, steps),
    decreases i,
{
    if i == 0 {
        lemma_fdr_fail_hsum_low_zero(n, v, n, steps);
    } else {
        lemma_fdr_fail_hsum_split(n, v, (i - 1) as nat, steps);
        assert((n + i) as nat - 1 == n + (i - 1) as nat);
        assert(n + (i - 1) as nat >= n);
        assert(fdr_fail_h(n, v, (n + (i - 1) as nat) as nat, steps)
            == fdr_fail_f(n, (v - n) as nat, (i - 1) as nat, steps)) by {
            assert((n + (i - 1) as nat - n) as nat == (i - 1) as nat);
        }
    }
}

/// fsum(v,j,0) = j  (fail_f(·,0) = 1).
pub proof fn lemma_fdr_fail_fsum_zero_steps(n: nat, v: nat, j: nat)
    ensures fdr_fail_fsum(n, v, j, 0nat) == (j as real),
    decreases j,
{
    if j > 0 {
        lemma_fdr_fail_fsum_zero_steps(n, v, (j - 1) as nat);
    }
}

/// The decay bound:  FS(v,steps) := Σ_{c<v} fail_f(v,c,steps) ≤ n / 2^steps,  for v < n.
pub proof fn lemma_fdr_fail_fs_bound(n: nat, v: nat, steps: nat)
    requires v < n,
    ensures fdr_fail_fsum(n, v, v, steps) <= (n as real) / pow(2real, steps),
    decreases steps,
{
    lemma_pow2_pos(steps);
    if steps == 0 {
        lemma_fdr_fail_fsum_zero_steps(n, v, v);   // FS(v,v,0) = v
        assert(pow(2real, 0nat) == 1real);
        assert((v as real) <= (n as real) / pow(2real, 0nat)) by(nonlinear_arith)
            requires v < n, pow(2real, 0nat) == 1real;
    } else {
        let ghost kk = (steps - 1) as nat;
        lemma_fdr_fail_fsum_half_pairsum(n, v, v, kk);
        lemma_fdr_fail_pairsum_eq_hsum(n, 2 * v, v, kk);
        let ghost hh = fdr_fail_hsum(n, 2 * v, 2 * v, kk);
        assert(fdr_fail_fsum(n, v, v, steps) == (1real / 2real) * hh);
        let ghost pk = pow(2real, kk);
        lemma_pow2_pos(kk);
        assert(pow(2real, steps) == 2real * pk);
        let ghost fsnext: real;
        if 2 * v < n {
            lemma_fdr_fail_hsum_eq_fsum_lt_n(n, 2 * v, 2 * v, kk);
            lemma_fdr_fail_fs_bound(n, 2 * v, kk);
            fsnext = fdr_fail_fsum(n, 2 * v, 2 * v, kk);
            assert(hh == fsnext);
        } else {
            lemma_fdr_fail_hsum_split(n, 2 * v, (2 * v - n) as nat, kk);
            assert((n + (2 * v - n) as nat) as nat == 2 * v);
            lemma_fdr_fail_fs_bound(n, (2 * v - n) as nat, kk);
            fsnext = fdr_fail_fsum(n, (2 * v - n) as nat, (2 * v - n) as nat, kk);
            assert(hh == fsnext);
        }
        // ½·hh ≤ ½·(n/pk) = n/(2pk) = n/pow(2,steps).
        assert(fdr_fail_fsum(n, v, v, steps) <= (n as real) / pow(2real, steps)) by(nonlinear_arith)
            requires fdr_fail_fsum(n, v, v, steps) == (1real / 2real) * hh,
                hh == fsnext, fsnext <= (n as real) / pk, pk > 0real,
                pow(2real, steps) == 2real * pk;
    }
}

/// Start-state failure bound:  fdr_fail_f(1,0,steps) ≤ n / 2^steps.
pub proof fn lemma_fdr_fail_at_start(n: nat, steps: nat)
    requires n > 1,
    ensures fdr_fail_f(n, 1, 0, steps) <= (n as real) / pow(2real, steps),
{
    reveal_with_fuel(fdr_fail_fsum, 2);
    lemma_fdr_fail_fs_bound(n, 1, steps);   // FS(1,steps) ≤ n/2^steps  (needs 1 < n)
    assert(fdr_fail_fsum(n, 1, 1, steps) == fdr_fail_f(n, 1, 0, steps));
}

/// Almost-sure termination at the start:  ∀δ>0, ∃steps. fdr_fail_f(1,0,steps) < δ.
pub proof fn lemma_fdr_fail_witness(n: nat, delta: real)
    requires n > 1, delta > 0real,
    ensures exists |steps: nat| fdr_fail_f(n, 1, 0, steps) < delta,
{
    assert((n as real) > 0real);
    assert(delta / (n as real) > 0real) by(nonlinear_arith) requires delta > 0real, (n as real) > 0real;
    archimedean_exp_growth(delta / (n as real), 2real);
    let k = choose |k: nat| (delta / (n as real)) * pow(2real, k) >= 1real;
    let ghost pk = pow(2real, k);
    lemma_pow2_pos(k);
    lemma_fdr_fail_at_start(n, (k + 1) as nat);
    assert(pow(2real, (k + 1) as nat) == 2real * pk);
    // (δ/n)·pk ≥ 1 ⇒ δ·pk ≥ n ⇒ n/(2pk) < δ.
    assert(delta * pk >= (n as real)) by(nonlinear_arith)
        requires (delta / (n as real)) * pk >= 1real, (n as real) > 0real;
    assert(fdr_fail_f(n, 1, 0, (k + 1) as nat) < delta) by(nonlinear_arith)
        requires fdr_fail_f(n, 1, 0, (k + 1) as nat) <= (n as real) / pow(2real, (k + 1) as nat),
            pow(2real, (k + 1) as nat) == 2real * pk,
            delta * pk >= (n as real), pk > 0real, (n as real) > 0real;
    assert(fdr_fail_f(n, 1, 0, (k + 1) as nat) < delta);   // witness steps = k+1
}

/// Lumbroso's Fast Dice Roller — samples uniformly from {0, …, n−1} using fair coin
/// flips; always returns.  Almost-sure termination is funded by the failure-probability
/// credit (no `k`, no amplification), and the precondition is the genuine
/// uniform-distribution expectation bound:
///
///   ε ≥ average_nat(n, ℰ)       ( = (1/n)·Σ_{i<n} ℰ(i),  the Uniform{0..n−1} mean )
///   ─────────────────────────────────────────────────
///   [{ ↯(ε) }] sample_fdr(n) [{ v. ↯(ℰ(v)) }]
#[verifier::spinoff_prover]
pub fn sample_fdr(
    n: u64,
    Ghost(e): Ghost<spec_fn(real) -> real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(eps): Ghost<real>,
) -> ((value, out_credit): (u64, Tracked<ErrorCreditResource>))
    requires
        n > 1,
        n <= u64::MAX / 2,
        forall |x: real| (#[trigger] e(x)) >= 0real,
        eps >= average_nat(n as nat, e),
        input_credit@ =~= (Value { car: eps }),
    ensures
        value < n,
        out_credit@@ =~= (Value { car: e(value as real) }),
{
    // Thin-air room for the termination credit, and a depth with fail(1,0,depth) < s0.
    proof { lemma_fdr_average_nonneg(n as nat, e); }   // average_nat ≥ 0, hence eps ≥ 0
    let Tracked(slack) = thin_air();
    let ghost s0 = choose |sv: real| sv > 0real && (slack@ =~= (Value { car: sv }));
    let tracked mut credit = ec_combine(input_credit, slack, eps, s0);   // ↯(eps + s0)
    let ghost mut k: nat;
    proof {
        lemma_fdr_fail_witness(n as nat, s0);
        k = choose |st: nat| fdr_fail_f(n as nat, 1, 0, st) < s0;
        lemma_fdr_f_le_average(n as nat, e, k);   // fdr_f(1,0,k) ≤ average_nat ≤ eps
        // eps + s0 ≥ fdr_f(1,0,k) + fdr_fail_f(1,0,k):
        assert(eps + s0 >= fdr_f(n as nat, e, 1, 0, k) + fdr_fail_f(n as nat, 1, 0, k))
            by(nonlinear_arith)
            requires fdr_f(n as nat, e, 1, 0, k) <= average_nat(n as nat, e),
                eps >= average_nat(n as nat, e),
                fdr_fail_f(n as nat, 1, 0, k) < s0;
    }
    let ghost mut g_ce = eps + s0;

    let mut v: u64 = 1;
    let mut c: u64 = 0;

    loop
        invariant
            n > 1, n <= u64::MAX / 2,
            1 <= v, v < n, c < v,
            forall |x: real| (#[trigger] e(x)) >= 0real,
            credit@ =~= (Value { car: g_ce }),
            g_ce >= fdr_f(n as nat, e, v as nat, c as nat, k) + fdr_fail_f(n as nat, v as nat, c as nat, k),
        decreases k,
    {
        proof {
            if k == 0 {
                // fdr_f(v,c,0) = 0, fdr_fail_f(v,c,0) = 1, so g_ce ≥ 1, but held g_ce < 1.
                ec_contradict(&credit);
            }
        }
        let ghost kk = k;
        // coin alloc: b ↦ fdr_h(2v,2c+b,k−1) + fdr_fail_h(2v,2c+b,k−1).
        let ghost alloc = |x: real| {
            let cc: nat = if x == 1real { 2 * (c as nat) + 1 } else { 2 * (c as nat) };
            fdr_h(n as nat, e, 2 * (v as nat), cc, (kk - 1) as nat)
                + fdr_fail_h(n as nat, 2 * (v as nat), cc, (kk - 1) as nat)
        };
        proof {
            assert forall |i: nat| (#[trigger] alloc(i as real)) >= 0real by {
                lemma_fdr_h_nonneg(n as nat, e, 2 * (v as nat), 2 * (c as nat), (kk - 1) as nat);
                lemma_fdr_h_nonneg(n as nat, e, 2 * (v as nat), 2 * (c as nat) + 1, (kk - 1) as nat);
                lemma_fdr_fail_h_nonneg(n as nat, 2 * (v as nat), 2 * (c as nat), (kk - 1) as nat);
                lemma_fdr_fail_h_nonneg(n as nat, 2 * (v as nat), 2 * (c as nat) + 1, (kk - 1) as nat);
            }
            // (alloc(0)+alloc(1))/2 == fdr_f(v,c,k) + fdr_fail_f(v,c,k).
            let ghost fdh0 = fdr_h(n as nat, e, 2 * (v as nat), 2 * (c as nat), (kk - 1) as nat);
            let ghost fdh1 = fdr_h(n as nat, e, 2 * (v as nat), 2 * (c as nat) + 1, (kk - 1) as nat);
            let ghost flh0 = fdr_fail_h(n as nat, 2 * (v as nat), 2 * (c as nat), (kk - 1) as nat);
            let ghost flh1 = fdr_fail_h(n as nat, 2 * (v as nat), 2 * (c as nat) + 1, (kk - 1) as nat);
            assert((alloc(0real) + alloc(1real)) / 2real
                == fdr_f(n as nat, e, v as nat, c as nat, kk)
                 + fdr_fail_f(n as nat, v as nat, c as nat, kk)) by(nonlinear_arith)
                requires
                    alloc(0real) == fdh0 + flh0, alloc(1real) == fdh1 + flh1,
                    fdr_f(n as nat, e, v as nat, c as nat, kk) == (fdh0 + fdh1) / 2real,
                    fdr_fail_f(n as nat, v as nat, c as nat, kk) == (flh0 + flh1) / 2real;
        }

        let (b, Tracked(out)) = rand_2_u64(Tracked(credit), Ghost(alloc));
        proof {
            credit = out;
            g_ce = alloc(b as real);   // held credit is now alloc(b)
            k = (kk - 1) as nat;
        }

        v = 2 * v;
        c = 2 * c + b;

        if v >= n {
            if c < n {
                // accept:  alloc(b) = fdr_h(v,c,k) + fdr_fail_h(v,c,k) = ℰ(c) + 0.
                proof {
                    assert((c as nat) as real == c as real);
                    assert(g_ce == e(c as real));
                }
                return (c, Tracked(credit));
            } else {
                // reject:  alloc(b) = fdr_f(v−n,c−n,k) + fdr_fail_f(v−n,c−n,k) = G(v',c',k).
                v = v - n;
                c = c - n;
            }
        }
    }
}

} // verus!
