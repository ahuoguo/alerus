// Alias Method — sample outcome i ∈ {0,…,n−1} with probability aᵢ/m (m = Σ aᵢ),
// in O(1) per sample, using two uniform draws.  Exact / integer version (no floats),
// verified in the same error-credit (Eris/Verus) framework as fldr.rs.
//
// References:
//   - Walker 1977, Vose 1991
//   - https://www.keithschwarz.com/darts-dice-coins/
//   - rust-random/rand alias method: https://github.com/rust-random/rand/pull/692
//   - FLDR paper reference implementation:
//     https://github.com/probsys/fast-loaded-dice-roller-experiments
//
// ## Algorithm
// Preprocess weights a₀,…,a_{n−1} (total m) into two length-n tables, `prob` and
// `alias`, so that the n equal-probability "bins" (one per index) each hold total
// mass m, split between two labels:  bin i holds prob[i] units of label i and
// (m − prob[i]) units of label alias[i].  Multiplying weights by n, the tables are
// built so that each label k's total units across all bins is n·aₖ
//
// Sampling is two uniform draws and a comparison:
//
//   i ← Uniform{0,…,n−1}                        // pick a bin
//   r ← Uniform{0,…,m−1}                        // pick within the bin
//   return  if r < prob[i] { i } else { alias[i] }
//
// Then  P(k) = (1/n)·Σ_i ( [i=k]·prob[i] + [alias[i]=k]·(m−prob[i]) ) / m
//            = (1/(n·m))·(total units of k across all bins).
// For this to equal aₖ/m we need (total units of k) = n·aₖ — which is exactly the
// `valid_alias` condition `label_units(t, n, k) == n·weights(k)`
//
// ## Expectation-Preservation Rule
//            ε ≥ Σ_{i<n} (aᵢ/m)·ℰ(i)
//   ────────────────────────────────────────────────
//   [{ ↯(ε) }] sample_alias(tab) [{ i. ↯(ℰ(i)) }]
//
// The two uniform draws nest.  The OUTER bin draw is funded with `inner_eps(i)` = bin_credit(i)/m
// =  1/m · (prob[i]·ℰ(i) + (m−prob[i])·ℰ(alias[i])) — which is the average the INNER threshold draw
// needs to then yield ↯(ℰ(result)):  average_{r<m} ℰ(r<prob[i] ? i : alias[i]) = inner_eps(i)
// (`lemma_inner_average`, a step sum split at prob[i] via `lemma_ialloc_stepsum`).
//
// It then remains to fund the outer draw from ε, i.e. to show its average is the target:
//   average_{i<n} inner_eps(i)  =  Σ_{k<n} (aₖ/m)·ℰ(k)           (`lemma_average_outer`)
// Clearing the /m and /n, this is  Σ_i bin_credit(i) = n·Σ_k aₖ·ℰ(k)  (`lemma_bin_sum_eq`)
//
// `bin_contrib(i,k)`: the count of label-k units sitting in bin i: prob[i] of them when k = i 
// (m−prob[i]) when k = alias[i], 0 otherwise.
//
//   Σ_i bin_credit(i)  =  Σ_i Σ_k ℰ(k)·bin_contrib(i,k)    -- per bin (≤2 labels): lemma_bin_contrib_sum_sel
//                      =  Σ_k ℰ(k)·Σ_i bin_contrib(i,k)    -- lemma_fubini
//                      =  Σ_k ℰ(k)·label_units(k)          -- label_units(k) := Σ_i bin_contrib(i,k)
//                      =  Σ_k ℰ(k)·(n·aₖ) = n·Σ_k aₖ·ℰ(k)   -- lemma_label_credit_sum_validity

// ## Preprocessing: `build_alias`
// Scale weights by n: scaled_weights[i] = n·aᵢ. A bin is _small_ if scaled_weights[i] < m, 
// _large_ if ≥ m, and active until finalized. Each step pops a small bin s
// and a large bin l, then finalizes s: prob[s] ← scaled_weights[s], alias[s] ← l (s keeps
// its own units and borrows the (m − scaled_weights[s]) shortfall from l), and re-pushes 
// l by its new count.
//
// Three major invariants:
//  - Mass:  placed(k) + scaled_weights[k] = n·aₖ for every label k, where placed(k) sums the
//    finalized bins' contributions.  Each finalize moves the donated units scaled→placed
//    (`lemma_placed_update`); holds at entry as placed = 0 (`lemma_placed_zero`).
//  - Balance:  Σ_{active} scaled_weights = (#active)·m.  Forces a large partner to exist when
//    small is nonempty — else the active sum would be < (#active)·m (`lemma_sum_active_le`).
//  - Worklists hold exactly the active small / large bins, duplicate-free
//    (`lemma_reestablish_worklists`).


use vstd::prelude::*;

verus! {

use crate::ub::*;
use crate::rand_primitives::{rand_u64, thin_air};
#[cfg(verus_keep_ghost)]
use crate::rand_primitives::{sum_credit, average, average_nat};
#[cfg(verus_keep_ghost)]
use crate::alias_helper::*;

/// A preprocessed alias distribution over outcomes 0..n−1.  `m = Σ weights`.
/// Bin i holds `prob(i)` units of label i and `m − prob(i)` units of label `alias(i)`.
pub struct Alias {
    pub n: nat,
    pub m: nat,
    pub weights: spec_fn(nat) -> nat,
    pub prob: spec_fn(nat) -> nat,
    pub alias: spec_fn(nat) -> nat,
}

/// Σ_{i<j} weights(i)  (nat) — pins down m = total weight.
pub open spec fn sum_of_weights(t: Alias, j: nat) -> nat
    decreases j,
{
    if j == 0 { 0nat } else { sum_of_weights(t, (j - 1) as nat) + (t.weights)((j - 1) as nat) }
}

/// Σ_{i<j} weights(i)·ℰ(i)  (real).
pub open spec fn wsum(t: Alias, e: spec_fn(real) -> real, j: nat) -> real
    decreases j,
{
    if j == 0 {
        0real
    } else {
        wsum(t, e, (j - 1) as nat) + (t.weights)((j - 1) as nat) as real * e((j - 1) as real)
    }
}

/// (1/m)·Σ aᵢ·ℰ(i).
pub open spec fn alias_exp(t: Alias, e: spec_fn(real) -> real) -> real {
    wsum(t, e, t.n) / (t.m as real)
}

/// Bin i's total credit (ℰ summed over its m slots):  prob(i)·ℰ(i) + (m−prob(i))·ℰ(alias(i)).
/// The inner draw averages this over the m thresholds, so inner_eps(i) = bin_credit(i)/m.
pub open spec fn bin_credit(t: Alias, e: spec_fn(real) -> real, i: nat) -> real {
    (t.prob)(i) as real * e(i as real)
        + ((t.m - (t.prob)(i)) as nat) as real * e((t.alias)(i) as real)
}

/// Σ_{i<j} bin_credit(i).
pub open spec fn bin_sum(t: Alias, e: spec_fn(real) -> real, j: nat) -> real
    decreases j,
{
    if j == 0 { 0real } else { bin_sum(t, e, (j - 1) as nat) + bin_credit(t, e, (j - 1) as nat) }
}

/// Credit the inner draw needs at bin i:  bin_credit(i)/m.  (= the outer draw's ℰ at i.)
pub open spec fn inner_eps(t: Alias, e: spec_fn(real) -> real, i: nat) -> real {
    bin_credit(t, e, i) / (t.m as real)
}

/// Units of label k contributed by bin i.
pub open spec fn bin_contrib(t: Alias, i: nat, k: nat) -> nat {
    (if i == k { (t.prob)(i) } else { 0nat })
        + (if (t.alias)(i) == k { (t.m - (t.prob)(i)) as nat } else { 0nat })
}

/// Σ_{i<j} bin_contrib(i, k) — units of label k across the first j bins.
pub open spec fn label_units(t: Alias, j: nat, k: nat) -> nat
    decreases j,
{
    if j == 0 { 0nat } else { label_units(t, (j - 1) as nat, k) + bin_contrib(t, (j - 1) as nat, k) }
}

/// Σ_{k<n} ℰ(k)·label_units(j,k)
pub open spec fn label_credit_sum(t: Alias, e: spec_fn(real) -> real, j: nat, n: nat) -> real
    decreases n,
{
    if n == 0 {
        0real
    } else {
        label_credit_sum(t, e, j, (n - 1) as nat) + e((n - 1) as real) * (label_units(t, j, (n - 1) as nat) as real)
    }
}

/// Σ_{k<n} ℰ(k)·bin_contrib(i,k) — bin i's contribution, label-grouped.
pub open spec fn bin_contrib_sum(t: Alias, e: spec_fn(real) -> real, i: nat, n: nat) -> real
    decreases n,
{
    if n == 0 {
        0real
    } else {
        bin_contrib_sum(t, e, i, (n - 1) as nat) + e((n - 1) as real) * (bin_contrib(t, i, (n - 1) as nat) as real)
    }
}

/// `t` is a well-formed integer alias table:
///  - n,m ≥ 1 and m = Σ weights;
///  - each bin's probabilities are in range (prob(i) ≤ m, alias(i) < n);
///  - every label k's total units equal n·aₖ  (Vose's redistribution invariant).
pub open spec fn valid_alias(t: Alias) -> bool {
    &&& t.n >= 1
    &&& t.m >= 1
    &&& t.m == sum_of_weights(t, t.n)
    &&& (forall |i: nat| i < t.n ==> #[trigger] (t.prob)(i) <= t.m)
    &&& (forall |i: nat| i < t.n ==> #[trigger] (t.alias)(i) < t.n)
    &&& (forall |k: nat| k < t.n ==> #[trigger] label_units(t, t.n, k) == t.n * (t.weights)(k))
}

/// Units bin i contributes to label k, from raw arrays (i finalized).
pub open spec fn binc(prob: Seq<u64>, alias: Seq<u64>, m: nat, i: int, k: nat) -> nat {
    (if i == k as int { prob[i] as nat } else { 0nat })
        + (if alias[i] as nat == k { (m - prob[i] as nat) as nat } else { 0nat })
}

/// Σ_{i<j, !active[i]} binc(i,k) — units of label k from the finalized (!active) bins below j.
pub open spec fn placed(prob: Seq<u64>, alias: Seq<u64>, active: Seq<bool>, m: nat, j: nat, k: nat) -> nat
    decreases j,
{
    if j == 0 {
        0nat
    } else {
        placed(prob, alias, active, m, (j - 1) as nat, k)
            + (if !active[(j - 1) as int] { binc(prob, alias, m, (j - 1) as int, k) } else { 0nat })
    }
}

/// Σ_{i<j, active[i]} scaled_weights[i].
pub open spec fn sum_active(scaled_weights: Seq<u64>, active: Seq<bool>, j: nat) -> nat
    decreases j,
{
    if j == 0 { 0nat }
    else { sum_active(scaled_weights, active, (j - 1) as nat) + (if active[(j - 1) as int] { scaled_weights[(j - 1) as int] as nat } else { 0nat }) }
}

/// #{ i < j : active[i] }.
pub open spec fn count_active(active: Seq<bool>, j: nat) -> nat
    decreases j,
{
    if j == 0 { 0nat } else { count_active(active, (j - 1) as nat) + (if active[(j - 1) as int] { 1nat } else { 0nat }) }
}

/// Σ_{i<j} s[i]  — sum of the first j entries of a Seq<u64> (used for the weights total).
pub open spec fn seq_sum(s: Seq<u64>, j: nat) -> nat
    decreases j,
{
    if j == 0 { 0nat } else { seq_sum(s, (j - 1) as nat) + s[(j - 1) as int] as nat }
}

/// Outer-draw allocation:  bin x ↦ the credit the inner draw needs there.
pub open spec fn oalloc(t: Alias, e: spec_fn(real) -> real) -> spec_fn(real) -> real {
    |x: real| inner_eps(t, e, x.floor() as nat)
}

/// Inner-draw allocation at bin i:  threshold y ↦ ℰ(y<prob(i) ? i : alias(i)).
pub open spec fn ialloc(t: Alias, e: spec_fn(real) -> real, i: nat) -> spec_fn(real) -> real {
    |y: real| if y < (t.prob)(i) as real { e(i as real) } else { e((t.alias)(i) as real) }
}

/// Runtime alias table.  `prob[i]`/`alias[i]` are the two-label split of  bin i
pub struct AliasTable {
    pub n: u64,
    pub m: u64,
    pub weights: Vec<u64>,
    pub prob: Vec<u64>,
    pub alias: Vec<u64>,
}

impl AliasTable {
    pub open spec fn view(self) -> Alias {
        Alias {
            n: self.n as nat,
            m: self.m as nat,
            weights: |i: nat| if i < self.weights@.len() { self.weights@[i as int] as nat } else { 0nat },
            prob: |i: nat| if i < self.prob@.len() { self.prob@[i as int] as nat } else { 0nat },
            alias: |i: nat| if i < self.alias@.len() { self.alias@[i as int] as nat } else { 0nat },
        }
    }

    pub open spec fn wf(self) -> bool {
        &&& valid_alias(self.view())
        &&& self.prob@.len() == self.n
        &&& self.alias@.len() == self.n
        &&& self.n as nat <= usize::MAX as nat
    }
}

#[verifier::spinoff_prover]
pub fn sample_alias(
    tab: &AliasTable,
    Ghost(e): Ghost<spec_fn(real) -> real>,
    Tracked(credit): Tracked<ErrorCreditResource>,
    Ghost(eps): Ghost<real>,
) -> (ret: (u64, Tracked<ErrorCreditResource>))
    requires
        tab.wf(),
        forall |x: real| (#[trigger] e(x)) >= 0real,
        eps >= alias_exp(tab.view(), e),
        credit.view() =~= (ErrorCreditCarrier::Value { car: eps }),
    ensures
        ret.0 < tab.n,
        ret.1@.view() =~= (ErrorCreditCarrier::Value { car: e(ret.0 as real) }),
{
    let ghost t = tab.view();
    let ghost oa = oalloc(t, e);

    proof {
        assert forall |k: nat| (#[trigger] oa(k as real)) >= 0real by {
            lemma_inner_eps_nonneg(t, e, (k as real).floor() as nat);
        }
        lemma_average_outer(t, e);
    }
    let (i, Tracked(c1)) = rand_u64(tab.n, Tracked(credit), Ghost(oa));

    let ghost ia = ialloc(t, e, i as nat);
    proof {
        lemma_inner_average(t, e, i as nat);
    }
    let (r, Tracked(c2)) = rand_u64(tab.m, Tracked(c1), Ghost(ia));

    let pi: u64 = tab.prob[i as usize];
    let result: u64 = if r < pi { i } else { tab.alias[i as usize] };
    (result, Tracked(c2))
}

/// build a validated alias table from integer weights
#[verifier::spinoff_prover]
pub fn build_alias(weights: Vec<u64>, m: u64) -> (ret: AliasTable)
    requires
        weights@.len() >= 1,
        m >= 1,
        (weights@.len() as nat) * (m as nat) <= u64::MAX as nat,
        m as nat == seq_sum(weights@, weights@.len() as nat),
    ensures
        ret.wf(), ret.n as nat == weights@.len(), ret.m == m, ret.weights@ == weights@,
{
    let n: u64 = weights.len() as u64;
    let ghost wseq = weights@;

    // init:  scaled_weights[i] = n·aᵢ;  prob/alias = 0;  all bins active.
    let mut scaled_weights: Vec<u64> = Vec::new();
    let mut prob: Vec<u64> = Vec::new();
    let mut alias: Vec<u64> = Vec::new();
    let mut i: u64 = 0;
    while i < n
        invariant
            n as nat == wseq.len(), 
            n as nat <= usize::MAX as nat, 
            i <= n,
            (n as nat) * (m as nat) <= u64::MAX as nat,
            weights@ == wseq, 
            m as nat == seq_sum(wseq, n as nat),
            scaled_weights@.len() == i == prob@.len() == alias@.len(),
            forall |x: int| 0 <= x < i ==> #[trigger]scaled_weights@[x] as nat == (n as nat) * (wseq[x] as nat),
            forall |x: int| 0 <= x < i ==> prob@[x] == 0 && alias@[x] == 0,
        decreases n - i,
    {
        proof {
            lemma_seq_sum_term(wseq, n as nat, i as nat);
            assert(wseq[i as int] as nat <= m as nat);     // wseq[i] ≤ wsum = m (loop invariant)
            assert((n as nat) * (wseq[i as int] as nat) <= (n as nat) * (m as nat)) by(nonlinear_arith)
                requires (wseq[i as int] as nat) <= m as nat;
        }
        scaled_weights.push(n * weights[i as usize]);
        prob.push(0);
        alias.push(0);
        i = i + 1;
    }

    let ghost mut active: Seq<bool> = Seq::new(n as nat, |x: int| true);
    proof {
        lemma_sum_scaled_init(scaled_weights@, active, wseq, n as nat, n as nat);   // Σ scaled_weights = n·m
        lemma_count_all_active(active, n as nat);                                   // count = n
        assert forall |k: nat| #![trigger wseq[k as int]] k < n implies
            placed(prob@, alias@, active, m as nat, n as nat, k) + scaled_weights@[k as int] as nat
                == (n as nat) * (wseq[k as int] as nat) by {
            lemma_placed_zero(prob@, alias@, active, m as nat, n as nat, k);
        }
    }

    // classify each bin into the small (scaled_weights < m) / large (scaled_weights ≥ m) worklists
    let mut small: Vec<u64> = Vec::new();
    let mut large: Vec<u64> = Vec::new();
    let mut j: u64 = 0;
    while j < n
        invariant
            scaled_weights@.len() == n, 
            j <= n, 
            n as nat <= usize::MAX as nat,
            small@.no_duplicates(),
            large@.no_duplicates(),
            forall |idx: int| #![trigger small@[idx]] 0 <= idx < small@.len() ==>
                (small@[idx] as nat) < j as nat && (scaled_weights@[small@[idx] as int] as nat) < m as nat,
            forall |idx: int| #![trigger large@[idx]] 0 <= idx < large@.len() ==>
                (large@[idx] as nat) < j as nat && (scaled_weights@[large@[idx] as int] as nat) >= m as nat,
            forall |x: int| #![trigger scaled_weights@[x]] 0 <= x < j ==>
                ((scaled_weights@[x] as nat) < m as nat ==> small@.contains(x as u64))
                && ((scaled_weights@[x] as nat) >= m as nat ==> large@.contains(x as u64)),
        decreases n - j,
    {
        let ghost small_old = small@;
        let ghost large_old = large@;
        if scaled_weights[j as usize] < m {
            small.push(j);
            proof {
                assert(!small_old.contains(j)) by {
                    assert forall |q: int| 0 <= q < small_old.len() implies small_old[q] != j by {
                        assert((small_old[q] as nat) < j as nat);
                    }
                }
                lemma_push_no_dup(small_old, j);
                assert(small@.contains(j)) by { assert(small@[small_old.len() as int] == j); }
                assert forall |x: int| #![trigger scaled_weights@[x]] 0 <= x < j as int implies
                    ((scaled_weights@[x] as nat) < m as nat ==> small@.contains(x as u64))
                    && ((scaled_weights@[x] as nat) >= m as nat ==> large@.contains(x as u64)) by {
                    if (scaled_weights@[x] as nat) < m as nat { vstd::seq_lib::lemma_seq_contains_after_push(small_old, j, x as u64); }
                }
            }
        } else {
            large.push(j);
            proof {
                assert(!large_old.contains(j)) by {
                    assert forall |q: int| 0 <= q < large_old.len() implies large_old[q] != j by {
                        assert((large_old[q] as nat) < j as nat);
                    }
                }
                lemma_push_no_dup(large_old, j);
                assert(large@.contains(j)) by { assert(large@[large_old.len() as int] == j); }
                assert forall |x: int| #![trigger scaled_weights@[x]] 0 <= x < j as int implies
                    ((scaled_weights@[x] as nat) < m as nat ==> small@.contains(x as u64))
                    && ((scaled_weights@[x] as nat) >= m as nat ==> large@.contains(x as u64)) by {
                    if (scaled_weights@[x] as nat) >= m as nat { vstd::seq_lib::lemma_seq_contains_after_push(large_old, j, x as u64);
                     }
                }
            }
        }
        j = j + 1;
    }

    // each pass pairs one small bin with one large bin
    loop
        invariant
            n as nat == wseq.len(),
            n >= 1,
            m >= 1,
            n as nat <= usize::MAX as nat,
            (n as nat) * (m as nat) <= u64::MAX as nat,
            weights@ == wseq, 
            m as nat == seq_sum(wseq, n as nat),
            scaled_weights@.len() == n, prob@.len() == n, alias@.len() == n,
            active.len() == n,
            forall |x: int| #![trigger active[x]] 0 <= x < n && !active[x] ==> prob@[x] as nat <= m as nat && (alias@[x] as nat) < n as nat,
            forall |x: int| #![trigger active[x]] 0 <= x < n && !active[x] ==> scaled_weights@[x] == 0,
            forall |k: nat| #![trigger wseq[k as int]] k < n ==>
                placed(prob@, alias@, active, m as nat, n as nat, k) + scaled_weights@[k as int] as nat
                    == (n as nat) * (wseq[k as int] as nat),
            sum_active(scaled_weights@, active, n as nat) == count_active(active, n as nat) * (m as nat),
            // worklists hold exactly the active small / large bins, duplicate-free
            small@.no_duplicates(), large@.no_duplicates(),
            forall |idx: int| #![trigger small@[idx]] 0 <= idx < small@.len() ==>
                (small@[idx] as nat) < n as nat && active[small@[idx] as int]
                && (scaled_weights@[small@[idx] as int] as nat) < m as nat,
            forall |idx: int| #![trigger large@[idx]] 0 <= idx < large@.len() ==>
                (large@[idx] as nat) < n as nat && active[large@[idx] as int]
                && (scaled_weights@[large@[idx] as int] as nat) >= m as nat,
            forall |x: int| #![trigger active[x]] 0 <= x < n && active[x] ==>
                ((scaled_weights@[x] as nat) < m as nat ==> small@.contains(x as u64))
                && ((scaled_weights@[x] as nat) >= m as nat ==> large@.contains(x as u64)),
        decreases small@.len() + large@.len(),
    {
        if small.len() == 0 {
            if large.len() == 0 {
                let tab = AliasTable { n, m, weights, prob, alias };
                proof {
                    let ghost t = tab.view();
                    assert forall |k: nat| k < t.n implies #[trigger] label_units(t, t.n, k) == t.n * (t.weights)(k) by {
                        lemma_placed_eq_label_units(t, prob@, alias@, active, m as nat, n as nat, k);
                        assert(!active[k as int]);
                        assert(scaled_weights@[k as int] == 0);
                    }
                    lemma_sum_of_weights_eq_seq_sum(t, wseq, n as nat);
                    assert forall |i: nat| i < t.n implies #[trigger] (t.prob)(i) <= t.m by { assert(!active[i as int]); }
                    assert forall |i: nat| i < t.n implies #[trigger] (t.alias)(i) < t.n by { assert(!active[i as int]); }
                    assert(valid_alias(t));
                }
                return tab;
            }
            // small empty (but large isn't), so every active bin is at exactly m; finalize one of them.
            proof {
                assert forall |i2: int| #![trigger active[i2]] 0 <= i2 < n && active[i2]
                    implies scaled_weights@[i2] as nat >= m as nat by {
                    if (scaled_weights@[i2] as nat) < m as nat {
                        assert(small@.contains(i2 as u64));               // coverage
                        let widx = choose |q: int| 0 <= q < small@.len() && small@[q] == i2 as u64;
                        assert(0 <= widx < small@.len());                 // contradicts small empty
                    }
                }
                lemma_all_eq_m(scaled_weights@, active, m as nat, n as nat);   // all active scaled == m
            }
            let ghost large_old = large@;
            assert((large@[large@.len() - 1] as nat) < n as nat
                && active[large@[large@.len() - 1] as int]
                && (scaled_weights@[large@[large@.len() - 1] as int] as nat) == m as nat);
            let l = large.remove(large.len() - 1);
            let ghost prob_old = prob@;
            let ghost alias_old = alias@;
            let ghost scaled_old = scaled_weights@;
            let ghost active_old = active;
            prob.set(l as usize, m);
            alias.set(l as usize, l);
            scaled_weights.set(l as usize, 0);
            proof {
                active = active.update(l as int, false);
                assert(large@ =~= large_old.drop_last());
                // per-label mass
                assert forall |k: nat| #![trigger wseq[k as int]] k < n implies
                    placed(prob@, alias@, active, m as nat, n as nat, k) + scaled_weights@[k as int] as nat
                        == (n as nat) * (wseq[k as int] as nat) by {
                    lemma_placed_update(prob_old, alias_old, active_old, m as nat, n as nat, k, l as int, m, l);
                }
                // aggregate balance: removing l (active, scaled == m) keeps Σ == count·m
                lemma_sum_update(scaled_old, active_old, n as nat, l as int, 0);
                lemma_sum_deactivate(scaled_weights@, active_old, n as nat, l as int);
                lemma_count_deactivate(active_old, n as nat, l as int);
                assert((count_active(active_old, n as nat) - 1) * (m as nat)
                    == count_active(active_old, n as nat) * (m as nat) - (m as nat)) by(nonlinear_arith)
                    requires count_active(active_old, n as nat) >= 1;
                assert forall |idx: int| #![trigger large@[idx]] 0 <= idx < large@.len() implies
                    (large@[idx] as nat) < n as nat && active[large@[idx] as int]
                    && (scaled_weights@[large@[idx] as int] as nat) >= m as nat by {
                    assert(large@[idx] == large_old[idx]);
                }
                assert forall |x: int| #![trigger active[x]] 0 <= x < n && active[x] implies
                    ((scaled_weights@[x] as nat) < m as nat ==> small@.contains(x as u64))
                    && ((scaled_weights@[x] as nat) >= m as nat ==> large@.contains(x as u64)) by {
                    assert(scaled_weights@[x] as nat == m as nat);   // x ≠ l, still active ⇒ == m
                    lemma_drop_last_contains(large_old, x as u64);   // x ≠ l = large_old.last()
                }
            }
            continue;
        }
        // pop an under-full bin s  (small nonempty here, so the index is valid)
        let ghost small_old = small@;
        let s = small.remove(small.len() - 1);
        assert(small@ =~= small_old.drop_last());

        // an under-full bin forces an over-full partner (else Σ scaled_weights < count·m)
        if large.len() == 0 {
            proof {
                assert forall |i2: int| #![trigger active[i2]] 0 <= i2 < n && active[i2]
                    implies scaled_weights@[i2] as nat <= (m - 1) as nat by {
                    if (scaled_weights@[i2] as nat) >= m as nat {
                        assert(large@.contains(i2 as u64));           // coverage
                        let q = choose |q2: int| 0 <= q2 < large@.len() && large@[q2] == i2 as u64;
                        assert(0 <= q < large@.len());                // contradicts large empty
                    }
                }
                lemma_count_active_pos(active, n as nat, s as int);   // s active ⇒ count ≥ 1
                lemma_sum_active_le(scaled_weights@, active, (m - 1) as nat, n as nat);
                assert(count_active(active, n as nat) * ((m - 1) as nat) + count_active(active, n as nat)
                    == count_active(active, n as nat) * (m as nat)) by(nonlinear_arith)
                    requires m >= 1;
                assert(false);
            }
        }
        // pop the over-full bin l
        let ghost large_old = large@;
        proof {
            assert(large@.len() >= 1);
            assert((large@[large@.len() - 1] as nat) < n as nat);
            assert(active[large@[large@.len() - 1] as int]);
            assert((scaled_weights@[large@[large@.len() - 1] as int] as nat) >= m as nat);
        }
        let l = large.remove(large.len() - 1);
        proof {
            assert(large@ =~= large_old.drop_last());
            assert((l as nat) < n as nat && active[l as int] && (scaled_weights@[l as int] as nat) >= m as nat);
        }

        let ghost prob_old = prob@;
        let ghost alias_old = alias@;
        let ghost scaled_old = scaled_weights@;
        let ghost active_old = active;
        let ghost small_mid = small@;     // == small_old.drop_last()
        let ghost large_mid = large@;     // == large_old.drop_last()
        let ss: u64 = scaled_weights[s as usize];
        let sl: u64 = scaled_weights[l as usize];
        let donate: u64 = m - ss;
        assert(s != l);                                       // ss < m ≤ sl
        assert(sl >= donate);                                 // sl ≥ m ≥ donate
        let nl: u64 = sl - donate;
        prob.set(s as usize, ss);
        alias.set(s as usize, l);
        scaled_weights.set(s as usize, 0);
        scaled_weights.set(l as usize, nl);
        proof {
            active = active.update(s as int, false);
            // per-label mass
            assert forall |k: nat| #![trigger wseq[k as int]] k < n implies
                placed(prob@, alias@, active, m as nat, n as nat, k) + scaled_weights@[k as int] as nat
                    == (n as nat) * (wseq[k as int] as nat) by {
                lemma_placed_update(prob_old, alias_old, active_old, m as nat, n as nat, k, s as int, ss, l);
            }
            // aggregate Σ scaled_weights = count·m.  scaled_weights@ == scaled_old.update(s,0).update(l,nl)
            // (set order: s then l), so update s first, then l.
            lemma_sum_update(scaled_old, active_old, n as nat, s as int, 0);
            lemma_sum_update(scaled_old.update(s as int, 0), active_old, n as nat, l as int, nl);
            lemma_sum_deactivate(scaled_weights@, active_old, n as nat, s as int);
            lemma_count_deactivate(active_old, n as nat, s as int);
            assert((count_active(active_old, n as nat) - 1) * (m as nat)
                == count_active(active_old, n as nat) * (m as nat) - (m as nat)) by(nonlinear_arith)
                requires count_active(active_old, n as nat) >= 1;
            // worklist prep: kept prefixes are duplicate-free and miss the popped tops
            // l ∉ small_mid:  small entries had scaled_old < m, but scaled_old[l] ≥ m
            assert(!small_mid.contains(l)) by {
                assert forall |q: int| 0 <= q < small_mid.len() implies small_mid[q] != l by {
                    assert(small_mid[q] == small_old[q]);
                    assert((scaled_old[small_old[q] as int] as nat) < m as nat);
                }
            }
        }
        // re-classify the reduced over-full bin l into its worklist, then re-prove invariants
        if nl < m {
            small.push(l);
            
        } else {
            large.push(l);
            
        }
        proof {
            lemma_reestablish_worklists(small@, large@, small_mid, large_mid, small_old, large_old,
                active_old, active, scaled_old, scaled_weights@, s, l, nl, m, n);
        }
    }
}

pub fn sample_748_alias(
    Ghost(e): Ghost<spec_fn(real) -> real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(eps): Ghost<real>,
) -> (ret: (u64, Tracked<ErrorCreditResource>))
    requires
        forall |x: real| (#[trigger] e(x)) >= 0real,
        eps >= (7real * e(0real) + 4real * e(1real) + 8real * e(2real)) / 19real,
        input_credit.view() =~= (ErrorCreditCarrier::Value { car: eps }),
    ensures
        ret.0 < 3,
        ret.1@.view() =~= (ErrorCreditCarrier::Value { car: e(ret.0 as real) }),
{
    let mut w: Vec<u64> = Vec::new();
    w.push(7); w.push(4); w.push(8);
    proof { reveal_with_fuel(seq_sum, 4); }
    let tab = build_alias(w, 19); // tab.wf(), n==3, m==19, weights==[7,4,8]
    proof { reveal_with_fuel(wsum, 4); }
    sample_alias(&tab, Ghost(e), Tracked(input_credit), Ghost(eps))
}

pub fn run_alias_zero() -> (ret: u64)
    ensures ret < 3,
{
    let ghost e = |x: real| 0real;
    let Tracked(credit) = thin_air();
    let ghost eps = choose |sv: real|
        sv > 0real && (credit.view() =~= (ErrorCreditCarrier::Value { car: sv }));
    proof {
        assert((7real * e(0real) + 4real * e(1real) + 8real * e(2real)) / 19real == 0real)
            by(nonlinear_arith)
            requires e(0real) == 0real, e(1real) == 0real, e(2real) == 0real;
        assert(eps >= (7real * e(0real) + 4real * e(1real) + 8real * e(2real)) / 19real);  // eps > 0 ≥ 0
    }
    let (r, _) = sample_748_alias(Ghost(e), Tracked(credit), Ghost(eps));
    r
}

pub fn example_alias() -> (ret: u64)
    ensures ret < 3,
{
    run_alias_zero()
}

} // verus!
