use vstd::prelude::*;

verus! {
#[cfg(verus_keep_ghost)]
use crate::alias::*;
#[cfg(verus_keep_ghost)]
use crate::rand_primitives::{sum_credit, average, average_nat};

/// Pushing a fresh element preserves `no_duplicates`.
pub proof fn lemma_push_no_dup(s: Seq<u64>, x: u64)
    requires s.no_duplicates(), !s.contains(x),
    ensures s.push(x).no_duplicates(),
{
    let p = s.push(x);
    assert forall |i: int, j: int| 0 <= i < p.len() && 0 <= j < p.len() && i != j
        implies p[i] != p[j] by {
        if i < s.len() && j < s.len() {
            // both inside the prefix → s's no_duplicates
        } else if i == s.len() {
            assert(p[i] == x && p[j] == s[j]);   // s[j] != x since !s.contains(x)
        } else {
            assert(p[j] == x && p[i] == s[i]);
        }
    }
}

/// An element other than the last survives `drop_last`.
pub proof fn lemma_drop_last_contains(s: Seq<u64>, x: u64)
    requires s.len() > 0, s.contains(x), x != s.last(),
    ensures s.drop_last().contains(x),
{
    let w = choose |q: int| 0 <= q < s.len() && s[q] == x;
    assert(s[w] == x);
    assert(w != s.len() - 1);                    // else x == s.last()
    assert(s.drop_last()[w] == x);               // witness lands in the prefix
}

/// Re-establish the three worklist invariants (entries-valid for small / large, and
/// coverage) after one redistribution step finalizes `s`, donates to `l`, and re-pushes
/// `l` into whichever stack matches its reduced count `nl`.  `*_old` are the stacks at
/// loop top, `*_mid` their `drop_last` after the two pops, `*_new` after the re-push.
pub proof fn lemma_reestablish_worklists(
    small_new: Seq<u64>, large_new: Seq<u64>,
    small_mid: Seq<u64>, large_mid: Seq<u64>,
    small_old: Seq<u64>, large_old: Seq<u64>,
    active_old: Seq<bool>, active_new: Seq<bool>,
    scaled_old: Seq<u64>, scaled_new: Seq<u64>,
    s: u64, l: u64, nl: u64, m: u64, n: u64,
)
    requires
        n >= 1, active_old.len() == n, scaled_old.len() == n,
        // shapes of the kept prefixes and the re-pushed stacks
        small_mid == small_old.drop_last(), large_mid == large_old.drop_last(),
        small_old.len() >= 1, large_old.len() >= 1,
        small_old.last() == s, large_old.last() == l,
        nl < m ==> (small_new == small_mid.push(l) && large_new == large_mid),
        nl >= m ==> (small_new == small_mid && large_new == large_mid.push(l)),
        small_old.no_duplicates(), large_old.no_duplicates(),
        // how `active` and `scaled_weights` changed this step
        active_new == active_old.update(s as int, false),
        scaled_new == scaled_old.update(s as int, 0).update(l as int, nl),
        // facts about the paired bins
        (s as nat) < n as nat, (l as nat) < n as nat, s != l,
        active_old[l as int],
        (scaled_old[s as int] as nat) < m as nat, (scaled_old[l as int] as nat) >= m as nat,
        // old worklist invariants (loop top: stacks over scaled_old / active_old)
        forall |idx: int| 0 <= idx < small_old.len() ==>
            (#[trigger] small_old[idx] as nat) < n as nat && active_old[small_old[idx] as int]
            && (scaled_old[small_old[idx] as int] as nat) < m as nat,
        forall |idx: int| 0 <= idx < large_old.len() ==>
            (#[trigger] large_old[idx] as nat) < n as nat && active_old[large_old[idx] as int]
            && (scaled_old[large_old[idx] as int] as nat) >= m as nat,
        forall |x: int| 0 <= x < n && (#[trigger] active_old[x]) ==>
            ((scaled_old[x] as nat) < m as nat ==> small_old.contains(x as u64))
            && ((scaled_old[x] as nat) >= m as nat ==> large_old.contains(x as u64)),
    ensures
        forall |idx: int| 0 <= idx < small_new.len() ==>
            (#[trigger] small_new[idx] as nat) < n as nat && active_new[small_new[idx] as int]
            && (scaled_new[small_new[idx] as int] as nat) < m as nat,
        forall |idx: int| 0 <= idx < large_new.len() ==>
            (#[trigger] large_new[idx] as nat) < n as nat && active_new[large_new[idx] as int]
            && (scaled_new[large_new[idx] as int] as nat) >= m as nat,
        forall |x: int| 0 <= x < n && (#[trigger] active_new[x]) ==>
            ((scaled_new[x] as nat) < m as nat ==> small_new.contains(x as u64))
            && ((scaled_new[x] as nat) >= m as nat ==> large_new.contains(x as u64)),
{
    // s, l are the popped tops; the kept prefixes equal the old lists' prefixes.
    assert(s == small_old[small_old.len() - 1]);
    assert(l == large_old[large_old.len() - 1]);
    assert forall |idx: int| 0 <= idx < small_mid.len() implies small_mid[idx] == small_old[idx] by {}
    assert forall |idx: int| 0 <= idx < large_mid.len() implies large_mid[idx] == large_old[idx] by {}

    // Each kept small entry e satisfies e != s (no_duplicates) and e != l (scaled_old[e] < m ≤
    // scaled_old[l]); symmetrically for large.  That's all the SMT needs: the active/scaled
    // updates at s, l then don't touch e, and `push` only appends.  The two branches differ
    // solely in which list `l` is re-pushed onto.
    assert forall |idx: int| 0 <= idx < small_mid.len() implies
        small_old[idx] != s && small_old[idx] != l by {}
    assert forall |idx: int| 0 <= idx < large_mid.len() implies
        large_old[idx] != s && large_old[idx] != l by {}

    if nl < m {
        // small_new == small_mid.push(l);  large_new == large_mid
        assert forall |idx: int| #![auto] 0 <= idx < small_new.len() implies
            (small_new[idx] as nat) < n as nat && active_new[small_new[idx] as int]
            && (scaled_new[small_new[idx] as int] as nat) < m as nat by {}
        assert forall |idx: int| #![auto] 0 <= idx < large_new.len() implies
            (large_new[idx] as nat) < n as nat && active_new[large_new[idx] as int]
            && (scaled_new[large_new[idx] as int] as nat) >= m as nat by {}
        assert forall |x: int| #![auto] 0 <= x < n && active_new[x] implies
            ((scaled_new[x] as nat) < m as nat ==> small_new.contains(x as u64))
            && ((scaled_new[x] as nat) >= m as nat ==> large_new.contains(x as u64)) by {
            if x == l as int {
                assert(small_new[small_mid.len() as int] == l);   // pushed ⇒ contains
            } else if x != s as int {
                if (scaled_old[x] as nat) < m as nat {
                    lemma_drop_last_contains(small_old, x as u64);
                    vstd::seq_lib::lemma_seq_contains_after_push(small_mid, l, x as u64);
                } else {
                    lemma_drop_last_contains(large_old, x as u64);
                }
            }
        }
    } else {
        // small_new == small_mid;  large_new == large_mid.push(l)
        assert forall |idx: int| #![auto] 0 <= idx < small_new.len() implies
            (small_new[idx] as nat) < n as nat && active_new[small_new[idx] as int]
            && (scaled_new[small_new[idx] as int] as nat) < m as nat by {}
        assert forall |idx: int| #![auto] 0 <= idx < large_new.len() implies
            (large_new[idx] as nat) < n as nat && active_new[large_new[idx] as int]
            && (scaled_new[large_new[idx] as int] as nat) >= m as nat by {}
        assert forall |x: int| #![auto] 0 <= x < n && active_new[x] implies
            ((scaled_new[x] as nat) < m as nat ==> small_new.contains(x as u64))
            && ((scaled_new[x] as nat) >= m as nat ==> large_new.contains(x as u64)) by {
            if x == l as int {
                assert(large_new[large_mid.len() as int] == l);   // pushed ⇒ contains
            } else if x != s as int {
                if (scaled_old[x] as nat) < m as nat {
                    lemma_drop_last_contains(small_old, x as u64);
                } else {
                    lemma_drop_last_contains(large_old, x as u64);
                    vstd::seq_lib::lemma_seq_contains_after_push(large_mid, l, x as u64);
                }
            }
        }
    }
}

/// Updating bin s ≥ j leaves `placed` over [0,j) unchanged.
pub proof fn lemma_placed_unaffected(
    prob: Seq<u64>, alias: Seq<u64>, active: Seq<bool>, m: nat, j: nat, k: nat, s: int, ps: u64, ls: u64,
)
    requires
        s >= j, j <= prob.len(), alias.len() == prob.len(), active.len() == prob.len(), s < prob.len(),
    ensures
        placed(prob.update(s, ps), alias.update(s, ls), active.update(s, false), m, j, k)
            == placed(prob, alias, active, m, j, k),
    decreases j,
{
    if j > 0 {
        lemma_placed_unaffected(prob, alias, active, m, (j - 1) as nat, k, s, ps, ls);
        assert(prob.update(s, ps)[(j - 1) as int] == prob[(j - 1) as int]);   // s != j−1
        assert(alias.update(s, ls)[(j - 1) as int] == alias[(j - 1) as int]);
        assert(active.update(s, false)[(j - 1) as int] == active[(j - 1) as int]);
    }
}

/// Finalizing bin s (active true→false, prob[s]=ps, alias[s]=ls) increases `placed` by
/// bin s's contribution.
pub proof fn lemma_placed_update(
    prob: Seq<u64>, alias: Seq<u64>, active: Seq<bool>, m: nat, j: nat, k: nat, s: int, ps: u64, ls: u64,
)
    requires
        s < j, 0 <= s, active[s], j <= prob.len(),
        alias.len() == prob.len(), active.len() == prob.len(),
    ensures
        placed(prob.update(s, ps), alias.update(s, ls), active.update(s, false), m, j, k)
            == placed(prob, alias, active, m, j, k)
             + binc(prob.update(s, ps), alias.update(s, ls), m, s, k),
    decreases j,
{
    if (j - 1) as int == s {
        lemma_placed_unaffected(prob, alias, active, m, (j - 1) as nat, k, s, ps, ls);
        assert(!active.update(s, false)[(j - 1) as int]);
    } else {
        lemma_placed_update(prob, alias, active, m, (j - 1) as nat, k, s, ps, ls);
        assert(prob.update(s, ps)[(j - 1) as int] == prob[(j - 1) as int]);
        assert(alias.update(s, ls)[(j - 1) as int] == alias[(j - 1) as int]);
        assert(active.update(s, false)[(j - 1) as int] == active[(j - 1) as int]);
    }
}

/// When every bin below j is finalized (!active), `placed` is exactly the view's `label_units`.
pub proof fn lemma_placed_eq_label_units(
    t: Alias, prob: Seq<u64>, alias: Seq<u64>, active: Seq<bool>, m: nat, j: nat, k: nat,
)
    requires
        t.m == m,
        forall |i: int| 0 <= i < j ==> !active[i],
        forall |i: int| 0 <= i < j ==> (t.prob)(i as nat) == prob[i] as nat,
        forall |i: int| 0 <= i < j ==> (t.alias)(i as nat) == alias[i] as nat,
    ensures label_units(t, j, k) == placed(prob, alias, active, m, j, k),
    decreases j,
{
    if j > 0 {
        lemma_placed_eq_label_units(t, prob, alias, active, m, (j - 1) as nat, k);
        assert(!active[(j - 1) as int]);
        assert(bin_contrib(t, (j - 1) as nat, k) == binc(prob, alias, m, (j - 1) as int, k));
    }
}

/// Active values each ≥ m sum to at least count·m.
pub proof fn lemma_sum_active_ge(scaled_weights: Seq<u64>, active: Seq<bool>, m: nat, j: nat)
    requires forall |i: int| #![trigger active[i]] 0 <= i < j && active[i] ==> scaled_weights[i] as nat >= m,
    ensures sum_active(scaled_weights, active, j) >= count_active(active, j) * m,
    decreases j,
{
    if j > 0 {
        let ghost cm = count_active(active, (j - 1) as nat);
        lemma_sum_active_ge(scaled_weights, active, m, (j - 1) as nat);
        assert(sum_active(scaled_weights, active, j)
            == sum_active(scaled_weights, active, (j - 1) as nat)
             + (if active[(j - 1) as int] { scaled_weights[(j - 1) as int] as nat } else { 0nat }));
        if active[(j - 1) as int] {
            assert(scaled_weights[(j - 1) as int] as nat >= m);
            assert(count_active(active, j) == cm + 1);
            assert(count_active(active, j) * m == cm * m + m) by(nonlinear_arith)
                requires count_active(active, j) == cm + 1;
        } else {
            assert(count_active(active, j) == cm);
            assert(count_active(active, j) * m == cm * m) by(nonlinear_arith)
                requires count_active(active, j) == cm;
        }
    } else {
        assert(count_active(active, 0) * m == 0) by(nonlinear_arith);
    }
}

/// If active values each ≥ m sum to exactly count·m, every one equals m.
pub proof fn lemma_all_eq_m(scaled_weights: Seq<u64>, active: Seq<bool>, m: nat, j: nat)
    requires
        forall |i: int| #![trigger active[i]] 0 <= i < j && active[i] ==> scaled_weights[i] as nat >= m,
        sum_active(scaled_weights, active, j) == count_active(active, j) * m,
    ensures forall |i: int| 0 <= i < j && active[i] ==> scaled_weights[i] as nat == m,
    decreases j,
{
    if j > 0 {
        let ghost cm = count_active(active, (j - 1) as nat);
        lemma_sum_active_ge(scaled_weights, active, m, (j - 1) as nat);
        if active[(j - 1) as int] {
            assert(count_active(active, j) == cm + 1);
            assert(count_active(active, j) * m == cm * m + m) by(nonlinear_arith)
                requires count_active(active, j) == cm + 1;
        } else {
            assert(count_active(active, j) == cm);
        }
        lemma_all_eq_m(scaled_weights, active, m, (j - 1) as nat);
    }
}

/// An active index witnesses count ≥ 1.
pub proof fn lemma_count_active_pos(active: Seq<bool>, j: nat, s: int)
    requires 0 <= s < j, active[s],
    ensures count_active(active, j) >= 1,
    decreases j,
{
    if (j - 1) as int != s { lemma_count_active_pos(active, (j - 1) as nat, s); }
}

/// Active values each ≤ M sum to at most count·M.
pub proof fn lemma_sum_active_le(scaled_weights: Seq<u64>, active: Seq<bool>, mm: nat, j: nat)
    requires forall |i: int| #![trigger active[i]] 0 <= i < j && active[i] ==> scaled_weights[i] as nat <= mm,
    ensures sum_active(scaled_weights, active, j) <= count_active(active, j) * mm,
    decreases j,
{
    if j > 0 {
        let ghost cm = count_active(active, (j - 1) as nat);
        lemma_sum_active_le(scaled_weights, active, mm, (j - 1) as nat);
        assert(sum_active(scaled_weights, active, j)
            == sum_active(scaled_weights, active, (j - 1) as nat)
             + (if active[(j - 1) as int] { scaled_weights[(j - 1) as int] as nat } else { 0nat }));
        if active[(j - 1) as int] {
            assert(count_active(active, j) == cm + 1);
            assert(count_active(active, j) * mm == cm * mm + mm) by(nonlinear_arith)
                requires count_active(active, j) == cm + 1;
        } else {
            assert(count_active(active, j) == cm);
            assert(count_active(active, j) * mm == cm * mm) by(nonlinear_arith)
                requires count_active(active, j) == cm;
        }
    } else {
        assert(count_active(active, 0) * mm == 0) by(nonlinear_arith);
    }
}

/// Each weight ≤ the total (for the n·aᵢ ≤ n·m overflow bound).
pub proof fn lemma_seq_sum_term(s: Seq<u64>, j: nat, k: nat)
    requires k < j,
    ensures s[k as int] as nat <= seq_sum(s, j),
    decreases j,
{
    if k < (j - 1) as nat { lemma_seq_sum_term(s, (j - 1) as nat, k); }
}

/// The spec `sum_of_weights` over a view equals the array sum `seq_sum`.
pub proof fn lemma_sum_of_weights_eq_seq_sum(t: Alias, s: Seq<u64>, j: nat)
    requires forall |i: nat| i < j ==> #[trigger] (t.weights)(i) == s[i as int] as nat,
    ensures sum_of_weights(t, j) == seq_sum(s, j),
    decreases j,
{
    if j > 0 { lemma_sum_of_weights_eq_seq_sum(t, s, (j - 1) as nat); }
}

/// With every bin still active, `placed` is 0.
pub proof fn lemma_placed_zero(prob: Seq<u64>, alias: Seq<u64>, active: Seq<bool>, m: nat, j: nat, k: nat)
    requires forall |i: int| 0 <= i < j ==> active[i],
    ensures placed(prob, alias, active, m, j, k) == 0,
    decreases j,
{
    if j > 0 { lemma_placed_zero(prob, alias, active, m, (j - 1) as nat, k); }
}

/// Σ active scaled_weights = nn·Σweights, when all active and scaled_weights[i] = nn·weights[i].
pub proof fn lemma_sum_scaled_init(scaled_weights: Seq<u64>, active: Seq<bool>, weights: Seq<u64>, nn: nat, j: nat)
    requires forall |i: int| #![trigger active[i]] #![trigger scaled_weights[i]] 0 <= i < j ==> active[i] && scaled_weights[i] as nat == nn * (weights[i] as nat),
    ensures sum_active(scaled_weights, active, j) == nn * seq_sum(weights, j),
    decreases j,
{
    if j > 0 {
        lemma_sum_scaled_init(scaled_weights, active, weights, nn, (j - 1) as nat);
        assert(active[(j - 1) as int] && scaled_weights[(j - 1) as int] as nat == nn * (weights[(j - 1) as int] as nat));
        assert(sum_active(scaled_weights, active, j) == sum_active(scaled_weights, active, (j - 1) as nat) + scaled_weights[(j - 1) as int] as nat);
        assert(nn * seq_sum(weights, (j - 1) as nat) + nn * (weights[(j - 1) as int] as nat)
            == nn * seq_sum(weights, j)) by(nonlinear_arith)
            requires seq_sum(weights, j) == seq_sum(weights, (j - 1) as nat) + weights[(j - 1) as int] as nat;
    } else {
        assert(nn * seq_sum(weights, 0) == 0) by(nonlinear_arith);
    }
}

/// All-active count is j.
pub proof fn lemma_count_all_active(active: Seq<bool>, j: nat)
    requires forall |i: int| 0 <= i < j ==> active[i],
    ensures count_active(active, j) == j,
    decreases j,
{
    if j > 0 { lemma_count_all_active(active, (j - 1) as nat); }
}

/// Updating scaled_weights at s shifts `sum_active` by the delta there (if s active).
pub proof fn lemma_sum_update(scaled_weights: Seq<u64>, active: Seq<bool>, j: nat, s: int, v: u64)
    requires 0 <= s, s < scaled_weights.len(), j <= scaled_weights.len(),
    ensures
        s >= j ==> sum_active(scaled_weights.update(s, v), active, j) == sum_active(scaled_weights, active, j),
        s < j ==> sum_active(scaled_weights.update(s, v), active, j) + (if active[s] { scaled_weights[s] as nat } else { 0nat })
            == sum_active(scaled_weights, active, j) + (if active[s] { v as nat } else { 0nat }),
    decreases j,
{
    if j > 0 {
        lemma_sum_update(scaled_weights, active, (j - 1) as nat, s, v);
        assert(scaled_weights.update(s, v)[(j - 1) as int]
            == (if (j - 1) as int == s { v } else { scaled_weights[(j - 1) as int] }));
    }
}

/// Deactivating bin s removes its scaled_weights from `sum_active` (if it was active).
pub proof fn lemma_sum_deactivate(scaled_weights: Seq<u64>, active: Seq<bool>, j: nat, s: int)
    requires 0 <= s, s < active.len(), j <= active.len(),
    ensures
        s >= j ==> sum_active(scaled_weights, active.update(s, false), j) == sum_active(scaled_weights, active, j),
        s < j && active[s] ==> sum_active(scaled_weights, active.update(s, false), j) + (scaled_weights[s] as nat)
            == sum_active(scaled_weights, active, j),
        s < j && !active[s] ==> sum_active(scaled_weights, active.update(s, false), j) == sum_active(scaled_weights, active, j),
    decreases j,
{
    if j > 0 {
        lemma_sum_deactivate(scaled_weights, active, (j - 1) as nat, s);
        assert(active.update(s, false)[(j - 1) as int]
            == (if (j - 1) as int == s { false } else { active[(j - 1) as int] }));
    }
}

/// Deactivating an active bin s drops the active count by 1.
pub proof fn lemma_count_deactivate(active: Seq<bool>, j: nat, s: int)
    requires 0 <= s, s < active.len(), j <= active.len(),
    ensures
        s >= j ==> count_active(active.update(s, false), j) == count_active(active, j),
        s < j && active[s] ==> count_active(active.update(s, false), j) + 1 == count_active(active, j),
        s < j && !active[s] ==> count_active(active.update(s, false), j) == count_active(active, j),
    decreases j,
{
    if j > 0 {
        lemma_count_deactivate(active, (j - 1) as nat, s);
        assert(active.update(s, false)[(j - 1) as int]
            == (if (j - 1) as int == s { false } else { active[(j - 1) as int] }));
    }
}

/// Selection:  bin_contrib_sum(i, n) picks out the (≤2) labels bin i touches.
pub proof fn lemma_bin_contrib_sum_sel(t: Alias, e: spec_fn(real) -> real, i: nat, n: nat)
    ensures
        bin_contrib_sum(t, e, i, n)
            == (if i < n { (t.prob)(i) as real * e(i as real) } else { 0real })
             + (if (t.alias)(i) < n { ((t.m - (t.prob)(i)) as nat) as real * e((t.alias)(i) as real) } else { 0real }),
    decreases n,
{
    if n > 0 {
        let ghost km = (n - 1) as nat;
        lemma_bin_contrib_sum_sel(t, e, i, km);
        let ghost vp = (t.prob)(i) as real * e(i as real);
        let ghost va = ((t.m - (t.prob)(i)) as nat) as real * e((t.alias)(i) as real);
        // bound km→n increments each "< n" conditional by its "== km" case
        assert((if i < n { vp } else { 0real })
            == (if i < km { vp } else { 0real }) + (if i == km { vp } else { 0real }));
        assert((if (t.alias)(i) < n { va } else { 0real })
            == (if (t.alias)(i) < km { va } else { 0real }) + (if (t.alias)(i) == km { va } else { 0real }));
        // the bin (km) term equals those two increments (cast + ℰ congruence at i==km / alias==km)
        assert(e(km as real) * (bin_contrib(t, i, km) as real)
            == (if i == km { vp } else { 0real }) + (if (t.alias)(i) == km { va } else { 0real })) by(nonlinear_arith)
            requires
                bin_contrib(t, i, km) == (if i == km { (t.prob)(i) } else { 0nat })
                    + (if (t.alias)(i) == km { (t.m - (t.prob)(i)) as nat } else { 0nat }),
                i == km ==> e(km as real) == e(i as real),
                (t.alias)(i) == km ==> e(km as real) == e((t.alias)(i) as real),
                vp == (t.prob)(i) as real * e(i as real),
                va == ((t.m - (t.prob)(i)) as nat) as real * e((t.alias)(i) as real);
    }
}

/// Adding bin j−1 to the label-grouped view adds its bin_contrib_sum.
pub proof fn lemma_label_credit_sum_step(t: Alias, e: spec_fn(real) -> real, j: nat, n: nat)
    requires j >= 1,
    ensures label_credit_sum(t, e, j, n) == label_credit_sum(t, e, (j - 1) as nat, n) + bin_contrib_sum(t, e, (j - 1) as nat, n),
    decreases n,
{
    if n > 0 {
        let ghost km = (n - 1) as nat;
        lemma_label_credit_sum_step(t, e, j, km);
        // distribute  e(km)·LU(j,km) = e(km)·LU(j−1,km) + e(km)·BC(j−1,km)  (cast + distributivity)
        assert(e((n - 1) as real) * (label_units(t, j, km) as real)
            == e((n - 1) as real) * (label_units(t, (j - 1) as nat, km) as real)
             + e((n - 1) as real) * (bin_contrib(t, (j - 1) as nat, km) as real))
            by(nonlinear_arith)
            requires label_units(t, j, km)
                == label_units(t, (j - 1) as nat, km) + bin_contrib(t, (j - 1) as nat, km);
    }
}

/// With no bins, every label has 0 units, so the label-grouped sum is 0.
pub proof fn lemma_label_credit_sum_zero(t: Alias, e: spec_fn(real) -> real, n: nat)
    ensures label_credit_sum(t, e, 0, n) == 0real,
    decreases n,
{
    if n > 0 {
        lemma_label_credit_sum_zero(t, e, (n - 1) as nat);
        assert(label_units(t, 0, (n - 1) as nat) == 0);
        assert(e((n - 1) as real) * (label_units(t, 0, (n - 1) as nat) as real) == 0real) by(nonlinear_arith)
            requires label_units(t, 0, (n - 1) as nat) == 0;
    }
}

/// Finite Fubini:  the bin-grouped sum equals the label-grouped sum.
pub proof fn lemma_fubini(t: Alias, e: spec_fn(real) -> real, j: nat)
    requires valid_alias(t), j <= t.n,
    ensures bin_sum(t, e, j) == label_credit_sum(t, e, j, t.n),
    decreases j,
{
    if j > 0 {
        let ghost jm = (j - 1) as nat;
        assert(jm < t.n);
        assert((t.alias)(jm) < t.n);                           // valid_alias
        lemma_fubini(t, e, jm);                                // bin_sum(jm) == label_credit_sum(jm,n)
        lemma_label_credit_sum_step(t, e, j, t.n);                          // label_credit_sum(j,n) == label_credit_sum(jm,n) + bin_contrib_sum(jm,n)
        lemma_bin_contrib_sum_sel(t, e, jm, t.n);                        // bin_contrib_sum(jm,n) == bin_credit(jm)  (jm, alias(jm) < n)
    } else {
        lemma_label_credit_sum_zero(t, e, t.n);                             // label_credit_sum(0,n) == 0 == bin_sum(0)
    }
}

/// Under validity, the label-grouped sum is n·wsum.
pub proof fn lemma_label_credit_sum_validity(t: Alias, e: spec_fn(real) -> real, n: nat)
    requires valid_alias(t), n <= t.n,
    ensures label_credit_sum(t, e, t.n, n) == (t.n as real) * wsum(t, e, n),
    decreases n,
{
    if n > 0 {
        let ghost km = (n - 1) as nat;
        let ghost w = (t.weights)(km) as real;
        let ghost ek = e((n - 1) as real);
        lemma_label_credit_sum_validity(t, e, km);                          // label_credit_sum(n,km) == n·wsum(km)
        assert(label_units(t, t.n, km) == t.n * (t.weights)(km));   // validity
        assert((t.n * (t.weights)(km)) as real == (t.n as real) * ((t.weights)(km) as real)) by(nonlinear_arith);
        assert((label_units(t, t.n, km) as real) == (t.n as real) * w);
        // the added label_credit_sum term:  ek·(label_units as real) == n·(w·ek)
        assert(ek * (label_units(t, t.n, km) as real) == (t.n as real) * (w * ek)) by(nonlinear_arith)
            requires (label_units(t, t.n, km) as real) == (t.n as real) * w;
        // n·wsum(n) == n·wsum(km) + n·(w·ek)
        assert((t.n as real) * wsum(t, e, n) == (t.n as real) * wsum(t, e, km) + (t.n as real) * (w * ek))
            by(nonlinear_arith)
            requires wsum(t, e, n) == wsum(t, e, km) + w * ek;
    }
}


/// **Main correctness:**  Σ bin_credit over bins = n · Σ aᵢℰ(i).
pub proof fn lemma_bin_sum_eq(t: Alias, e: spec_fn(real) -> real)
    requires valid_alias(t),
    ensures bin_sum(t, e, t.n) == (t.n as real) * wsum(t, e, t.n),
{
    lemma_fubini(t, e, t.n);
    lemma_label_credit_sum_validity(t, e, t.n);
}

/// inner_eps ≥ 0 when ℰ ≥ 0 (so the allocs are non-negative).
pub proof fn lemma_inner_eps_nonneg(t: Alias, e: spec_fn(real) -> real, i: nat)
    requires forall |x: real| (#[trigger] e(x)) >= 0real, t.m >= 1,
    ensures inner_eps(t, e, i) >= 0real,
{
    assert(bin_credit(t, e, i) >= 0real) by(nonlinear_arith)
        requires e(i as real) >= 0real, e((t.alias)(i) as real) >= 0real;
    assert(inner_eps(t, e, i) >= 0real) by(nonlinear_arith)
        requires bin_credit(t, e, i) >= 0real, (t.m as real) >= 1real;
}

/// sum_credit of the outer alloc is bin_sum / m.
pub proof fn lemma_oalloc_sum(t: Alias, e: spec_fn(real) -> real, j: nat)
    requires t.m >= 1,
    ensures sum_credit(oalloc(t, e), j) == bin_sum(t, e, j) / (t.m as real),
    decreases j,
{
    if j > 0 {
        lemma_oalloc_sum(t, e, (j - 1) as nat);
        assert(((j - 1) as real).floor() as nat == (j - 1) as nat);          // round-trip
        assert((oalloc(t, e))((j - 1) as real) == inner_eps(t, e, (j - 1) as nat));   // closure β + round-trip
        // (oalloc)(j−1) == inner_eps(j−1) == bin_credit(j−1)/m, and (a/m)+(b/m)=(a+b)/m
        assert(sum_credit(oalloc(t, e), j) == bin_sum(t, e, j) / (t.m as real)) by(nonlinear_arith)
            requires
                sum_credit(oalloc(t, e), (j - 1) as nat) == bin_sum(t, e, (j - 1) as nat) / (t.m as real),
                (oalloc(t, e))((j - 1) as real) == bin_credit(t, e, (j - 1) as nat) / (t.m as real),
                sum_credit(oalloc(t, e), j)
                    == sum_credit(oalloc(t, e), (j - 1) as nat) + (oalloc(t, e))((j - 1) as real),
                bin_sum(t, e, j) == bin_sum(t, e, (j - 1) as nat) + bin_credit(t, e, (j - 1) as nat),
                (t.m as real) >= 1real;
    } else {
        assert(0real / (t.m as real) == 0real) by(nonlinear_arith) requires (t.m as real) >= 1real;
    }
}

/// The outer draw's average equals the target expectation.
pub proof fn lemma_average_outer(t: Alias, e: spec_fn(real) -> real)
    requires valid_alias(t),
    ensures average_nat(t.n, oalloc(t, e)) == alias_exp(t, e),
{
    lemma_oalloc_sum(t, e, t.n);                              // sum_credit = bin_sum(n)/m
    lemma_bin_sum_eq(t, e);                                   // bin_sum(n) = n·wsum(n)
    assert(average_nat(t.n, oalloc(t, e)) == alias_exp(t, e)) by(nonlinear_arith)
        requires
            sum_credit(oalloc(t, e), t.n) == bin_sum(t, e, t.n) / (t.m as real),
            bin_sum(t, e, t.n) == (t.n as real) * wsum(t, e, t.n),
            average_nat(t.n, oalloc(t, e)) == sum_credit(oalloc(t, e), t.n) / (t.n as real),
            alias_exp(t, e) == wsum(t, e, t.n) / (t.m as real),
            (t.n as real) >= 1real, (t.m as real) >= 1real;
}

/// The inner step sum:  Σ_{y<m} ℰ(y < prob(i) ? i : alias(i))  — credit over bin i's m thresholds.
pub proof fn lemma_ialloc_stepsum(t: Alias, e: spec_fn(real) -> real, i: nat, m: nat)
    ensures
        sum_credit(ialloc(t, e, i), m)
            == (if m <= (t.prob)(i) { m as real * e(i as real) }
                else { (t.prob)(i) as real * e(i as real)
                       + (m - (t.prob)(i)) as real * e((t.alias)(i) as real) }),
    decreases m,
{
    if m > 0 {
        let ghost km = (m - 1) as nat;
        let ghost p = (t.prob)(i);
        let ghost ei = e(i as real);
        let ghost ea = e((t.alias)(i) as real);
        lemma_ialloc_stepsum(t, e, i, km);                   // IH at km
        if km < p {
            assert((ialloc(t, e, i))(km as real) == ei) by { assert((km as real) < p as real); }
            // m ≤ p:  sum(km) = km·ei  ⇒  sum(m) = (km+1)·ei = m·ei
            assert(sum_credit(ialloc(t, e, i), m) == m as real * ei) by(nonlinear_arith)
                requires
                    sum_credit(ialloc(t, e, i), m) == sum_credit(ialloc(t, e, i), km) + ei,
                    sum_credit(ialloc(t, e, i), km) == km as real * ei,
                    m == km + 1;
        } else {
            assert((ialloc(t, e, i))(km as real) == ea) by { assert((km as real) >= p as real); }
            // km ≥ p:  resolve the IH if-then-else to the else form  (km==p ⇒ (km−p)=0)
            assert(sum_credit(ialloc(t, e, i), km) == p as real * ei + (km - p) as real * ea) by(nonlinear_arith)
                requires
                    km >= p,
                    sum_credit(ialloc(t, e, i), km)
                        == (if km <= p { km as real * ei } else { p as real * ei + (km - p) as real * ea });
            // m > p:  sum(m) = sum(km) + ea = p·ei + (m−p)·ea
            assert(sum_credit(ialloc(t, e, i), m) == p as real * ei + (m - p) as real * ea) by(nonlinear_arith)
                requires
                    sum_credit(ialloc(t, e, i), m) == sum_credit(ialloc(t, e, i), km) + ea,
                    sum_credit(ialloc(t, e, i), km) == p as real * ei + (km - p) as real * ea,
                    km >= p, m == km + 1;
        }
    } else {
        assert(m as real * e(i as real) == 0real) by(nonlinear_arith) requires m == 0;
    }
}

/// The inner draw's average at bin i equals inner_eps(i).
pub proof fn lemma_inner_average(t: Alias, e: spec_fn(real) -> real, i: nat)
    requires t.m >= 1, (t.prob)(i) <= t.m,
    ensures average_nat(t.m, ialloc(t, e, i)) == inner_eps(t, e, i),
{
    let ghost p = (t.prob)(i);
    let ghost ei = e(i as real);
    let ghost ea = e((t.alias)(i) as real);
    lemma_ialloc_stepsum(t, e, i, t.m as nat);               // sum = if m<=p {m·ei} else {p·ei+(m-p)·ea}
    if t.m as nat <= p {
        assert(t.m as nat == p);                             // p <= m and m <= p
        assert(sum_credit(ialloc(t, e, i), t.m as nat) == bin_credit(t, e, i)) by(nonlinear_arith)
            requires
                t.m == p,
                sum_credit(ialloc(t, e, i), t.m as nat) == t.m as real * ei,
                bin_credit(t, e, i) == p as real * ei + ((t.m - p) as nat) as real * ea;
    } else {
        assert(sum_credit(ialloc(t, e, i), t.m as nat) == bin_credit(t, e, i)) by(nonlinear_arith)
            requires
                t.m > p,
                sum_credit(ialloc(t, e, i), t.m as nat) == p as real * ei + (t.m - p) as real * ea,
                bin_credit(t, e, i) == p as real * ei + ((t.m - p) as nat) as real * ea;
    }
    assert(average_nat(t.m, ialloc(t, e, i)) == inner_eps(t, e, i)) by(nonlinear_arith)
        requires
            sum_credit(ialloc(t, e, i), t.m as nat) == bin_credit(t, e, i),
            average_nat(t.m, ialloc(t, e, i)) == sum_credit(ialloc(t, e, i), t.m as nat) / (t.m as real),
            inner_eps(t, e, i) == bin_credit(t, e, i) / (t.m as real),
            (t.m as real) >= 1real;
}

} // verus!
