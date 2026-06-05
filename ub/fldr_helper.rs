// Helper lemmas for `fldr.rs`.  All `proof fn`s of the FLDR development live here;
// `fldr.rs` keeps the structs, spec fns, and executable code.  Everything below is
// ghost-only (erased in a normal build), so the crate imports are gated on
// `verus_keep_ghost`.
use vstd::prelude::*;

verus! {
#[cfg(verus_keep_ghost)]
use crate::ub::*;
#[cfg(verus_keep_ghost)]
use crate::fldr::*;
#[cfg(verus_keep_ghost)]
use crate::rand_primitives::{thin_air, rand_1_u64};
#[cfg(verus_keep_ghost)]
use crate::math::pow::{pow, archimedean_pow};
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse};
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::{pow2, lemma_pow2_pos, lemma_pow2_unfold, lemma_pow2_strictly_increases, lemma_pow2_adds, lemma2_to64};

broadcast use {lemma_pow2_pos, lemma_pow2_unfold, lemma_pow2_strictly_increases};


// Both approximations are non-negative when ℰ ≥ 0.  The f/g split with matching
// (k, tag) measures mirrors the spec fns' mutual recursion (f tag 0, g tag 1).

pub proof fn lemma_fldr_f_nonneg(t: Ddg, e: spec_fn(real) -> real, c: nat, d: nat, k: nat)
    requires forall |x: real| (#[trigger] e(x)) >= 0real,
    ensures fldr_f(t, e, c, d, k) >= 0real,
    decreases k, 0nat,
{
    if k > 0 {
        lemma_fldr_g_nonneg(t, e, c + 1, 2 * d, (k - 1) as nat);
        lemma_fldr_g_nonneg(t, e, c + 1, 2 * d + 1, (k - 1) as nat);
    }
}

pub proof fn lemma_fldr_g_nonneg(t: Ddg, e: spec_fn(real) -> real, c: nat, d: nat, k: nat)
    requires forall |x: real| (#[trigger] e(x)) >= 0real,
    ensures fldr_g(t, e, c, d, k) >= 0real,
    decreases k, 1nat,
{
    if d < (t.h)(c) {
        if (t.lab)(c, d) < t.n {
            assert(e((t.lab)(c, d) as real) >= 0real);
        } else {
            lemma_fldr_f_nonneg(t, e, 0, 0, k);
        }
    } else {
        lemma_fldr_f_nonneg(t, e, c, (d - (t.h)(c)) as nat, k);
    }
}

pub proof fn lemma_fldr_v_pairsum_eq_vs(t: Ddg, e: spec_fn(real) -> real, c: nat, j: nat, k: nat)
    ensures fldr_vpairsum(t, e, c, j, k) == fldr_vs(t, e, c, 2 * j, k),
    decreases j,
{
    if j > 0 {
        lemma_fldr_v_pairsum_eq_vs(t, e, c, (j - 1) as nat, k);
        assert(fldr_vs(t, e, c, 2 * j, k)
            == fldr_vs(t, e, c, (2 * j - 1) as nat, k) + fldr_g(t, e, c, (2 * j - 1) as nat, k));
        assert(fldr_vs(t, e, c, (2 * j - 1) as nat, k)
            == fldr_vs(t, e, c, (2 * j - 2) as nat, k) + fldr_g(t, e, c, (2 * j - 2) as nat, k));
        assert((2 * j - 2) as nat == 2 * ((j - 1) as nat));
        assert((2 * j - 1) as nat == 2 * ((j - 1) as nat) + 1);
    }
}

pub proof fn lemma_fldr_v_vfsum_half_vpairsum(t: Ddg, e: spec_fn(real) -> real, c: nat, j: nat, k: nat)
    ensures fldr_vfsum(t, e, c, j, (k + 1) as nat) == (1real / 2real) * fldr_vpairsum(t, e, c + 1, j, k),
    decreases j,
{
    if j > 0 {
        lemma_fldr_v_vfsum_half_vpairsum(t, e, c, (j - 1) as nat, k);
        let ghost ga = fldr_g(t, e, c + 1, (2 * ((j - 1) as nat)) as nat, k);
        let ghost gb = fldr_g(t, e, c + 1, (2 * ((j - 1) as nat) + 1) as nat, k);
        let ghost pf = fldr_vfsum(t, e, c, (j - 1) as nat, (k + 1) as nat);
        let ghost p = fldr_vpairsum(t, e, c + 1, (j - 1) as nat, k);
        assert(fldr_f(t, e, c, (j - 1) as nat, (k + 1) as nat) == (ga + gb) / 2real);
        assert(pf == (1real / 2real) * p);
        assert(fldr_vpairsum(t, e, c + 1, j, k) == p + ga + gb);
        assert(pf + (ga + gb) / 2real == (1real / 2real) * (p + ga + gb)) by(nonlinear_arith)
            requires pf == (1real / 2real) * p;
    }
}

/// Leaf part:  for j ≤ h(c) (all leaves), with labels ≤ n on level c,
///   VS(c,j,F) = AC(c,j) + (#reject leaves among first j)·Val_F.
pub proof fn lemma_fldr_vs_leaf(t: Ddg, e: spec_fn(real) -> real, c: nat, j: nat, k: nat)
    requires
        j <= (t.h)(c),
        forall |d: nat| d < (t.h)(c) ==> #[trigger] (t.lab)(c, d) <= t.n,
    ensures
        fldr_vs(t, e, c, j, k)
            == fldr_ac(t, e, c, j) + (l_lbl_cnt_upto(t, c, t.n, j) as real) * fldr_f(t, e, 0, 0, k),
    decreases j,
{
    if j > 0 {
        lemma_fldr_vs_leaf(t, e, c, (j - 1) as nat, k);
        assert(((j - 1) as nat) < (t.h)(c));
        let ghost cprev = l_lbl_cnt_upto(t, c, t.n, (j - 1) as nat) as real;
        let ghost vk = fldr_f(t, e, 0, 0, k);
        if (t.lab)(c, (j - 1) as nat) == t.n {
            assert(l_lbl_cnt_upto(t, c, t.n, j) as real == cprev + 1real);
            assert((cprev + 1real) * vk == cprev * vk + vk) by(nonlinear_arith);
        } else {
            assert(l_lbl_cnt_upto(t, c, t.n, j) as real == cprev);
        }
    }
}

pub proof fn lemma_fldr_vs_internal(t: Ddg, e: spec_fn(real) -> real, c: nat, m: nat, k: nat)
    ensures
        fldr_vs(t, e, c, ((t.h)(c) + m) as nat, k)
            == fldr_vs(t, e, c, (t.h)(c), k) + fldr_vfsum(t, e, c, m, k),
    decreases m,
{
    if m > 0 {
        lemma_fldr_vs_internal(t, e, c, (m - 1) as nat, k);
        assert((((t.h)(c) + (m - 1) as nat) - (t.h)(c)) as nat == (m - 1) as nat);
    }
}

/// Adding leaf d=j−1 (label L = lab(c,j−1)) bumps count(c,L,·) by 1, so the
/// grouped sum gains ℰ(L) iff L < n.
pub proof fn lemma_fldr_sumlab_step(t: Ddg, e: spec_fn(real) -> real, c: nat, j: nat, n: nat)
    requires j >= 1,
    ensures
        fldr_sumlab(t, e, c, j, n)
            == fldr_sumlab(t, e, c, (j - 1) as nat, n)
               + (if (t.lab)(c, (j - 1) as nat) < n { e((t.lab)(c, (j - 1) as nat) as real) } else { 0real }),
    decreases n,
{
    if n > 0 {
        lemma_fldr_sumlab_step(t, e, c, j, (n - 1) as nat);
        let ghost lbl = (n - 1) as nat;
        // count(c,lbl,j) = count(c,lbl,j-1) + [lab(c,j-1) == lbl]
        assert(l_lbl_cnt_upto(t, c, lbl, j)
            == l_lbl_cnt_upto(t, c, lbl, (j - 1) as nat)
               + (if (t.lab)(c, (j - 1) as nat) == lbl { 1nat } else { 0nat }));
        if (t.lab)(c, (j - 1) as nat) == lbl {
            assert((l_lbl_cnt_upto(t, c, lbl, j) as real) * e(lbl as real)
                == (l_lbl_cnt_upto(t, c, lbl, (j - 1) as nat) as real) * e(lbl as real) + e(lbl as real))
                by(nonlinear_arith)
                requires l_lbl_cnt_upto(t, c, lbl, j) as real == (l_lbl_cnt_upto(t, c, lbl, (j - 1) as nat) as real) + 1real;
        }
    }
}

/// At j = 0 every count is 0, so the grouped sum is 0.
pub proof fn lemma_fldr_sumlab_zero(t: Ddg, e: spec_fn(real) -> real, c: nat, n: nat)
    ensures fldr_sumlab(t, e, c, 0, n) == 0real,
    decreases n,
{
    if n > 0 {
        lemma_fldr_sumlab_zero(t, e, c, (n - 1) as nat);
        assert(l_lbl_cnt_upto(t, c, (n - 1) as nat, 0) == 0);
        assert((l_lbl_cnt_upto(t, c, (n - 1) as nat, 0) as real) * e((n - 1) as real) == 0real)
            by(nonlinear_arith)
            requires l_lbl_cnt_upto(t, c, (n - 1) as nat, 0) == 0;
    }
}

/// Single-level grouping:  AC(c,j) = Σ_{ℓ<n} count(c,ℓ,j)·ℰ(ℓ),  given labels ≤ n.
pub proof fn lemma_fldr_ac_eq_sumlab(t: Ddg, e: spec_fn(real) -> real, c: nat, j: nat)
    requires forall |d: nat| d < j ==> #[trigger] (t.lab)(c, d) <= t.n,
    ensures fldr_ac(t, e, c, j) == fldr_sumlab(t, e, c, j, t.n),
    decreases j,
{
    if j == 0 {
        lemma_fldr_sumlab_zero(t, e, c, t.n);
    } else {
        assert(forall |d: nat| d < (j - 1) as nat ==> #[trigger] (t.lab)(c, d) <= t.n);
        lemma_fldr_ac_eq_sumlab(t, e, c, (j - 1) as nat);
        lemma_fldr_sumlab_step(t, e, c, j, t.n);
        let ghost gain = if (t.lab)(c, (j - 1) as nat) < t.n {
            e((t.lab)(c, (j - 1) as nat) as real)
        } else { 0real };
        assert(fldr_ac(t, e, c, j) == fldr_ac(t, e, c, (j - 1) as nat) + gain);
        assert(fldr_sumlab(t, e, c, j, t.n) == fldr_sumlab(t, e, c, (j - 1) as nat, t.n) + gain);
    }
}

/// One DDG level (value):  VS(c,N(c),F) = AC(c,h(c)) + RJ(c)·Val_F + ½·VS(c+1,N(c+1),F−1).
pub proof fn lemma_fldr_v_level(t: Ddg, e: spec_fn(real) -> real, c: nat, k: nat)
    requires
        (t.h)(c) <= ddg_nodes(t, c),
        forall |d: nat| d < (t.h)(c) ==> #[trigger] (t.lab)(c, d) <= t.n,
        k >= 1,
    ensures
        fldr_vs(t, e, c, ddg_nodes(t, c), k)
            == fldr_ac(t, e, c, (t.h)(c))
               + (l_lbl_cnt_upto(t, c, t.n, (t.h)(c)) as real) * fldr_f(t, e, 0, 0, k)
               + (1real / 2real) * fldr_vs(t, e, c + 1, ddg_nodes(t, c + 1), (k - 1) as nat),
{
    let ghost hh = (t.h)(c);
    let ghost m = (ddg_nodes(t, c) - hh) as nat;
    assert(ddg_nodes(t, c) == (hh + m) as nat);
    lemma_fldr_vs_internal(t, e, c, m, k);
    lemma_fldr_vs_leaf(t, e, c, hh, k);
    lemma_fldr_v_vfsum_half_vpairsum(t, e, c, m, (k - 1) as nat);
    assert(((k - 1) as nat + 1) as nat == k);
    lemma_fldr_v_pairsum_eq_vs(t, e, c + 1, m, (k - 1) as nat);
    assert(ddg_nodes(t, c + 1) == 2 * m);
}

/// rhs_acc(c,n) = rhs_acc(c−1,n) + 2^{K−c}·sumlab(c,h(c),n)   (induction on n).
pub proof fn lemma_fldr_rhs_acc_step(t: Ddg, e: spec_fn(real) -> real, c: nat, n: nat)
    requires c >= 1,
    ensures
        fldr_rhs_acc(t, e, c, n)
            == fldr_rhs_acc(t, e, (c - 1) as nat, n)
               + (pow2((t.levels - c) as nat) as real) * fldr_sumlab(t, e, c, (t.h)(c), n),
    decreases n,
{
    if n > 0 {
        lemma_fldr_rhs_acc_step(t, e, c, (n - 1) as nat);
        let ghost lbl = (n - 1) as nat;
        let ghost p = pow2((t.levels - c) as nat) as real;
        let ghost cnt = l_lbl_cnt_upto(t, c, lbl, (t.h)(c));
        // wenc(lbl,c) = wenc(lbl,c-1) + count(c,lbl,h(c))·2^{K-c}   (def + cast)
        assert(w_of_lbl_to_l(t, lbl, c)
            == w_of_lbl_to_l(t, lbl, (c - 1) as nat) + cnt * pow2((t.levels - c) as nat));
        lemma_nat_mul_real_cast(cnt, pow2((t.levels - c) as nat));
        assert((w_of_lbl_to_l(t, lbl, c) as real)
            == (w_of_lbl_to_l(t, lbl, (c - 1) as nat) as real) + (cnt as real) * p);
        assert(fldr_rhs_acc(t, e, c, n)
                == fldr_rhs_acc(t, e, (c - 1) as nat, n)
                   + p * fldr_sumlab(t, e, c, (t.h)(c), n))
            by(nonlinear_arith)
            requires
                fldr_rhs_acc(t, e, c, n)
                    == fldr_rhs_acc(t, e, c, lbl) + (w_of_lbl_to_l(t, lbl, c) as real) * e(lbl as real),
                fldr_rhs_acc(t, e, c, lbl)
                    == fldr_rhs_acc(t, e, (c - 1) as nat, lbl) + p * fldr_sumlab(t, e, c, (t.h)(c), lbl),
                (w_of_lbl_to_l(t, lbl, c) as real)
                    == (w_of_lbl_to_l(t, lbl, (c - 1) as nat) as real) + (cnt as real) * p,
                fldr_rhs_acc(t, e, (c - 1) as nat, n)
                    == fldr_rhs_acc(t, e, (c - 1) as nat, lbl) + (w_of_lbl_to_l(t, lbl, (c - 1) as nat) as real) * e(lbl as real),
                fldr_sumlab(t, e, c, (t.h)(c), n)
                    == fldr_sumlab(t, e, c, (t.h)(c), lbl) + (cnt as real) * e(lbl as real);
    }
}

/// At c = K, the per-label encoding is the weight (validity), so rhs_acc(K,n) = wsum(n).
pub proof fn lemma_fldr_rhs_acc_eq_wsum(t: Ddg, e: spec_fn(real) -> real, n: nat)
    requires valid_ddg(t), n <= t.n,
    ensures fldr_rhs_acc(t, e, t.levels, n) == fldr_wsum(t, e, n),
    decreases n,
{
    if n > 0 {
        lemma_fldr_rhs_acc_eq_wsum(t, e, (n - 1) as nat);
        assert(w_of_lbl_to_l(t, (n - 1) as nat, t.levels) == (t.weights)((n - 1) as nat));  // validity
    }
}

/// At c = 0 every encoding is 0, so rhs_acc(0,n) = 0.
pub proof fn lemma_fldr_rhs_acc_zero(t: Ddg, e: spec_fn(real) -> real, n: nat)
    ensures fldr_rhs_acc(t, e, 0, n) == 0real,
    decreases n,
{
    if n > 0 {
        lemma_fldr_rhs_acc_zero(t, e, (n - 1) as nat);
        assert(w_of_lbl_to_l(t, (n - 1) as nat, 0) == 0);
        assert((w_of_lbl_to_l(t, (n - 1) as nat, 0) as real) * e((n - 1) as real) == 0real)
            by(nonlinear_arith)
            requires w_of_lbl_to_l(t, (n - 1) as nat, 0) == 0;
    }
}

/// ewenc(c) = rhs_acc(c,n)   (induction on c, using AC = sumlab per level).
pub proof fn lemma_fldr_ewenc_eq_rhs(t: Ddg, e: spec_fn(real) -> real, c: nat)
    requires valid_ddg(t), c <= t.levels,
    ensures fldr_ewenc(t, e, c) == fldr_rhs_acc(t, e, c, t.n),
    decreases c,
{
    if c == 0 {
        lemma_fldr_rhs_acc_zero(t, e, t.n);
    } else {
        lemma_fldr_ewenc_eq_rhs(t, e, (c - 1) as nat);
        lemma_fldr_rhs_acc_step(t, e, c, t.n);
        assert(forall |d: nat| d < (t.h)(c) ==> #[trigger] (t.lab)(c, d) <= t.n);  // validity
        lemma_fldr_ac_eq_sumlab(t, e, c, (t.h)(c));
        let ghost p = pow2((t.levels - c) as nat) as real;
        assert(fldr_ewenc(t, e, c) == fldr_ewenc(t, e, (c - 1) as nat) + fldr_ac(t, e, c, (t.h)(c)) * p);
        assert(fldr_ac(t, e, c, (t.h)(c)) * p == p * fldr_sumlab(t, e, c, (t.h)(c), t.n))
            by(nonlinear_arith)
            requires fldr_ac(t, e, c, (t.h)(c)) == fldr_sumlab(t, e, c, (t.h)(c), t.n);
    }
}

/// The leaf-sum identity:  Σ_{c=1}^K AC(c,h(c))·2^{K−c} = Σ_{ℓ<n} weights(ℓ)·ℰ(ℓ).
pub proof fn lemma_fldr_leafsum(t: Ddg, e: spec_fn(real) -> real)
    requires valid_ddg(t),
    ensures fldr_ewenc(t, e, t.levels) == fldr_wsum(t, e, t.n),
{
    lemma_fldr_ewenc_eq_rhs(t, e, t.levels);
    lemma_fldr_rhs_acc_eq_wsum(t, e, t.n);
}

// 0 ≤ fail ≤ 1  (mutual induction on (k, tag), mirroring fldr_f/fldr_g).
pub proof fn lemma_fldr_fail_f_bounds(t: Ddg, c: nat, d: nat, k: nat)
    ensures 0real <= fldr_fail_f(t, c, d, k) <= 1real,
    decreases k, 0nat,
{
    if k > 0 {
        lemma_fldr_fail_g_bounds(t, c + 1, 2 * d, (k - 1) as nat);
        lemma_fldr_fail_g_bounds(t, c + 1, 2 * d + 1, (k - 1) as nat);
    }
}

pub proof fn lemma_fldr_fail_g_bounds(t: Ddg, c: nat, d: nat, k: nat)
    ensures 0real <= fldr_fail_g(t, c, d, k) <= 1real,
    decreases k, 1nat,
{
    if d < (t.h)(c) {
        if (t.lab)(c, d) < t.n {
        } else {
            lemma_fldr_fail_f_bounds(t, 0, 0, k);
        }
    } else {
        lemma_fldr_fail_f_bounds(t, c, (d - (t.h)(c)) as nat, k);
    }
}

// Monotone non-increasing in the flip budget: more fuel never increases failure.
// One step (fail(k+1) ≤ fail(k)); the general statement chains it.
pub proof fn lemma_fldr_fail_f_step(t: Ddg, c: nat, d: nat, k: nat)
    ensures fldr_fail_f(t, c, d, (k + 1) as nat) <= fldr_fail_f(t, c, d, k),
    decreases k, 0nat,
{
    if k == 0 {
        lemma_fldr_fail_f_bounds(t, c, d, 1);
    } else {
        lemma_fldr_fail_g_step(t, c + 1, 2 * d, (k - 1) as nat);
        lemma_fldr_fail_g_step(t, c + 1, 2 * d + 1, (k - 1) as nat);
    }
}

pub proof fn lemma_fldr_fail_g_step(t: Ddg, c: nat, d: nat, k: nat)
    ensures fldr_fail_g(t, c, d, (k + 1) as nat) <= fldr_fail_g(t, c, d, k),
    decreases k, 1nat,
{
    if d < (t.h)(c) {
        if (t.lab)(c, d) < t.n {
        } else {
            lemma_fldr_fail_f_step(t, 0, 0, k);
        }
    } else {
        lemma_fldr_fail_f_step(t, c, (d - (t.h)(c)) as nat, k);
    }
}

/// Reindex pairs:  Σ_{d<j}(g(c,2d)+g(c,2d+1)) = Σ_{e<2j} g(c,e).
pub proof fn lemma_fldr_fail_pairsum_eq_ffs(t: Ddg, c: nat, j: nat, k: nat)
    ensures fldr_fail_pairsum(t, c, j, k) == fldr_fail_ffs(t, c, 2 * j, k),
    decreases j,
{
    if j > 0 {
        lemma_fldr_fail_pairsum_eq_ffs(t, c, (j - 1) as nat, k);
        assert(fldr_fail_ffs(t, c, 2 * j, k)
            == fldr_fail_ffs(t, c, (2 * j - 1) as nat, k) + fldr_fail_g(t, c, (2 * j - 1) as nat, k));
        assert(fldr_fail_ffs(t, c, (2 * j - 1) as nat, k)
            == fldr_fail_ffs(t, c, (2 * j - 2) as nat, k) + fldr_fail_g(t, c, (2 * j - 2) as nat, k));
        assert((2 * j - 2) as nat == 2 * ((j - 1) as nat));
        assert((2 * j - 1) as nat == 2 * ((j - 1) as nat) + 1);
    }
}

/// fsum(c,j,k+1) = ½·pairsum(c+1,j,k)  (term-by-term from fail_f's recurrence).
pub proof fn lemma_fldr_fail_fsum_half_pairsum(t: Ddg, c: nat, j: nat, k: nat)
    ensures fldr_fail_fsum(t, c, j, (k + 1) as nat) == (1real / 2real) * fldr_fail_pairsum(t, c + 1, j, k),
    decreases j,
{
    if j > 0 {
        lemma_fldr_fail_fsum_half_pairsum(t, c, (j - 1) as nat, k);
        let ghost ga = fldr_fail_g(t, c + 1, (2 * ((j - 1) as nat)) as nat, k);
        let ghost gb = fldr_fail_g(t, c + 1, (2 * ((j - 1) as nat) + 1) as nat, k);
        let ghost pf = fldr_fail_fsum(t, c, (j - 1) as nat, (k + 1) as nat);
        let ghost p = fldr_fail_pairsum(t, c + 1, (j - 1) as nat, k);
        assert(fldr_fail_f(t, c, (j - 1) as nat, (k + 1) as nat) == (ga + gb) / 2real);
        assert(pf == (1real / 2real) * p);
        assert(fldr_fail_pairsum(t, c + 1, j, k) == p + ga + gb);
        assert(pf + (ga + gb) / 2real == (1real / 2real) * (p + ga + gb)) by(nonlinear_arith)
            requires pf == (1real / 2real) * p;
    }
}

/// Leaf part:  for j ≤ h(c) (all leaves), with labels ≤ n on level c, the fail-sum is
/// (#reject leaves among the first j)·Fail_k  (accept leaves contribute 0).
pub proof fn lemma_fldr_fail_ffs_leaf(t: Ddg, c: nat, j: nat, k: nat)
    requires
        j <= (t.h)(c),
        forall |d: nat| d < (t.h)(c) ==> #[trigger] (t.lab)(c, d) <= t.n,
    ensures
        fldr_fail_ffs(t, c, j, k)
            == (l_lbl_cnt_upto(t, c, t.n, j) as real) * fldr_fail_f(t, 0, 0, k),
    decreases j,
{
    if j > 0 {
        lemma_fldr_fail_ffs_leaf(t, c, (j - 1) as nat, k);
        assert(((j - 1) as nat) < (t.h)(c));
        let ghost cprev = l_lbl_cnt_upto(t, c, t.n, (j - 1) as nat) as real;
        let ghost fk = fldr_fail_f(t, 0, 0, k);
        // fail_g(c, j-1, k) = (lab == n) ? Fail_k : 0,  count(c,n,j) = count(c,n,j-1) + [lab==n].
        if (t.lab)(c, (j - 1) as nat) == t.n {
            assert(l_lbl_cnt_upto(t, c, t.n, j) as real == cprev + 1real);
            assert((cprev + 1real) * fk == cprev * fk + fk) by(nonlinear_arith);
        } else {
            assert(l_lbl_cnt_upto(t, c, t.n, j) as real == cprev);
        }
    }
}

/// Internal part:  positions [h(c), h(c)+m) are internal, so summing fail_g there
/// equals summing fail_f over [0, m).
pub proof fn lemma_fldr_fail_ffs_internal(t: Ddg, c: nat, m: nat, k: nat)
    ensures
        fldr_fail_ffs(t, c, ((t.h)(c) + m) as nat, k)
            == fldr_fail_ffs(t, c, (t.h)(c), k) + fldr_fail_fsum(t, c, m, k),
    decreases m,
{
    if m > 0 {
        lemma_fldr_fail_ffs_internal(t, c, (m - 1) as nat, k);
        assert((((t.h)(c) + (m - 1) as nat) - (t.h)(c)) as nat == (m - 1) as nat);
    }
}

/// One DDG level:  FFS(c, N(c), k) = RJ(c)·Fail_k + ½·FFS(c+1, N(c+1), k−1),
/// where RJ(c) = #reject leaves at level c and Fail_k = fldr_fail_f(0,0,k).
pub proof fn lemma_fldr_fail_level(t: Ddg, c: nat, k: nat)
    requires
        (t.h)(c) <= ddg_nodes(t, c),
        forall |d: nat| d < (t.h)(c) ==> #[trigger] (t.lab)(c, d) <= t.n,
        k >= 1,
    ensures
        fldr_fail_ffs(t, c, ddg_nodes(t, c), k)
            == (l_lbl_cnt_upto(t, c, t.n, (t.h)(c)) as real) * fldr_fail_f(t, 0, 0, k)
               + (1real / 2real) * fldr_fail_ffs(t, c + 1, ddg_nodes(t, c + 1), (k - 1) as nat),
{
    let ghost hh = (t.h)(c);
    let ghost m = (ddg_nodes(t, c) - hh) as nat;
    assert(ddg_nodes(t, c) == (hh + m) as nat);
    lemma_fldr_fail_ffs_internal(t, c, m, k);          // ffs(c,N(c)) = ffs(c,hh) + fsum(c,m)
    lemma_fldr_fail_ffs_leaf(t, c, hh, k);              // ffs(c,hh) = RJ(c)·Fail_k
    lemma_fldr_fail_fsum_half_pairsum(t, c, m, (k - 1) as nat);  // fsum(c,m,k) = ½ pairsum(c+1,m,k-1)
    assert(((k - 1) as nat + 1) as nat == k);
    lemma_fldr_fail_pairsum_eq_ffs(t, c + 1, m, (k - 1) as nat); // pairsum(c+1,m,k-1) = ffs(c+1,2mm,k-1)
    assert(ddg_nodes(t, c + 1) == 2 * m);
}

// ── Epoch decay:  Fail_{(j+1)K} ≤ ρ·Fail_{jK} with ρ < 1 ──────────────────────

/// More fuel never increases the failure probability.
pub proof fn lemma_fldr_fail_f_mono(t: Ddg, c: nat, d: nat, a: nat, b: nat)
    requires a >= b,
    ensures fldr_fail_f(t, c, d, a) <= fldr_fail_f(t, c, d, b),
    decreases a - b,
{
    if a > b {
        lemma_fldr_fail_f_step(t, c, d, (a - 1) as nat);     // fail_f(a) ≤ fail_f(a-1)
        lemma_fldr_fail_f_mono(t, c, d, (a - 1) as nat, b);  // fail_f(a-1) ≤ fail_f(b)
    }
}

pub proof fn lemma_fldr_tr_nonneg(t: Ddg, c: nat)
    ensures fldr_tr(t, c) >= 0real,
    decreases t.levels + 1 - c,
{
    if c <= t.levels {
        lemma_fldr_tr_nonneg(t, c + 1);
    }
}

/// The decay bound:  FFS(c, N(c), g) ≤ TR(c)·Fail_{g−(K−c)}  (downward induction on c),
/// chaining the per-level recurrence and bounding each Fail by its smallest-fuel value.
pub proof fn lemma_fldr_ffs_bound(t: Ddg, c: nat, g: nat)
    requires
        valid_ddg(t),
        1 <= c <= t.levels,
        g >= (t.levels - c + 1) as nat,
    ensures
        fldr_fail_ffs(t, c, ddg_nodes(t, c), g)
            <= fldr_tr(t, c) * fldr_fail_f(t, 0, 0, (g - (t.levels - c)) as nat),
    decreases t.levels + 1 - c,
{
    assert((t.h)(c) <= ddg_nodes(t, c));                       // from valid_ddg
    lemma_fldr_fail_level(t, c, g);
    let ghost rj = l_lbl_cnt_upto(t, c, t.n, (t.h)(c)) as real;
    let ghost lo = (g - (t.levels - c)) as nat;
    let ghost fg = fldr_fail_f(t, 0, 0, g);
    let ghost flo = fldr_fail_f(t, 0, 0, lo);
    lemma_fldr_fail_f_bounds(t, 0, 0, lo);
    if c == t.levels {
        assert(ddg_nodes(t, c + 1) == 0);                      // N(K+1) = 0 from valid_ddg
        assert(fldr_fail_ffs(t, c + 1, 0, (g - 1) as nat) == 0real);
        assert(fldr_tr(t, c + 1) == 0real);                    // c+1 > levels
        assert(lo == g);
    } else {
        lemma_fldr_ffs_bound(t, c + 1, (g - 1) as nat);
        let ghost tr1 = fldr_tr(t, c + 1);
        let ghost ffs1 = fldr_fail_ffs(t, c + 1, ddg_nodes(t, c + 1), (g - 1) as nat);
        assert((g - 1) as nat - (t.levels - (c + 1)) == lo);   // fuel offsets line up
        lemma_fldr_fail_f_mono(t, 0, 0, g, lo);                // fg ≤ flo
        lemma_fldr_tr_nonneg(t, c + 1);                        // tr1 ≥ 0
        assert(rj * fg + (1real / 2real) * ffs1 <= (rj + (1real / 2real) * tr1) * flo)
            by(nonlinear_arith)
            requires fg <= flo, ffs1 <= tr1 * flo, rj >= 0real, tr1 >= 0real, flo >= 0real;
    }
}

/// (n·m) as real == (n as real)·(m as real)  — cast distributes over ·  (mult is
/// repeated addition, and the addition cast is automatic).
pub proof fn lemma_nat_mul_real_cast(a: nat, b: nat)
    ensures (a * b) as real == (a as real) * (b as real),
    decreases b,
{
    if b == 0 {
        assert((a as real) * (b as real) == 0real) by(nonlinear_arith)
            requires (b as real) == 0real;
    } else {
        let ghost bm = (b - 1) as nat;
        lemma_nat_mul_real_cast(a, bm);                               // (a*bm) as real == a·bm
        assert(b == bm + 1);
        assert(a * b == a * bm + a) by(nonlinear_arith) requires b == bm + 1;
        assert((a * b) as real == (a * bm) as real + (a as real));   // addition cast
        assert((b as real) == (bm as real) + 1real);                 // addition cast
        assert((a as real) * (b as real) == (a as real) * (bm as real) + (a as real))
            by(nonlinear_arith) requires (b as real) == (bm as real) + 1real;
    }
}

/// Connects the real tail-reject mass to the integer weight encoding (validity):
///   TR(c)·2^{K−c} + wenc(c−1) = wenc(K).   (Additive form avoids nat subtraction.)
pub proof fn lemma_fldr_tr_wenc(t: Ddg, c: nat)
    requires 1 <= c <= t.levels,
    ensures
        fldr_tr(t, c) * (pow2((t.levels - c) as nat) as real)
            + (w_of_lbl_to_l(t, t.n, (c - 1) as nat) as real)
            == w_of_lbl_to_l(t, t.n, t.levels) as real,
    decreases t.levels - c,
{
    let ghost k = t.levels;
    let ghost rjr = l_lbl_cnt_upto(t, c, t.n, (t.h)(c)) as real;
    let ghost pk = pow2((k - c) as nat) as real;
    // wenc(c) = wenc(c-1) + RJ(c)·2^{K-c}   (definitional + cast distribution)
    assert(w_of_lbl_to_l(t, t.n, c)
        == w_of_lbl_to_l(t, t.n, (c - 1) as nat)
            + l_lbl_cnt_upto(t, c, t.n, (t.h)(c)) * pow2((k - c) as nat));
    lemma_nat_mul_real_cast(l_lbl_cnt_upto(t, c, t.n, (t.h)(c)), pow2((k - c) as nat));
    assert((w_of_lbl_to_l(t, t.n, c) as real) == (w_of_lbl_to_l(t, t.n, (c - 1) as nat) as real) + rjr * pk);
    if c == k {
        assert(fldr_tr(t, c + 1) == 0real);
        lemma2_to64();
        assert(pow2((k - c) as nat) == 1);
    } else {
        lemma_fldr_tr_wenc(t, c + 1);
        let ghost a = fldr_tr(t, c + 1);
        let ghost p = pow2((k - c - 1) as nat) as real;
        assert((k - (c + 1)) as nat == (k - c - 1) as nat);
        assert(pow2((k - c) as nat) == 2 * pow2((k - c - 1) as nat));  // pow2 step
        assert(pk == 2real * p);
        // a·p + wenc(c) == wenc(K)  (IH);  goal: (rjr+½a)·pk + wenc(c-1) == wenc(K)
        assert(fldr_tr(t, c) * pk + (w_of_lbl_to_l(t, t.n, (c - 1) as nat) as real)
                == w_of_lbl_to_l(t, t.n, k) as real) by(nonlinear_arith)
            requires
                fldr_tr(t, c) == rjr + (1real / 2real) * a,
                pk == 2real * p,
                a * p + (w_of_lbl_to_l(t, t.n, c) as real) == (w_of_lbl_to_l(t, t.n, k) as real),
                (w_of_lbl_to_l(t, t.n, c) as real) == (w_of_lbl_to_l(t, t.n, (c - 1) as nat) as real) + rjr * pk;
    }
}

/// ρ := ½·TR(1) < 1   (the per-epoch reject probability), since m ≥ 1.
pub proof fn lemma_fldr_tr1_lt2(t: Ddg)
    requires valid_ddg(t), t.levels >= 1,
    ensures fldr_tr(t, 1) < 2real, fldr_tr(t, 1) >= 0real,
{
    lemma_fldr_tr_wenc(t, 1);
    lemma_fldr_tr_nonneg(t, 1);
    // tr(1)·2^{K-1} + wenc(0) == wenc(K) == 2^K − m, and 2^K = 2·2^{K-1}, m ≥ 1.
    assert(w_of_lbl_to_l(t, t.n, 0) == 0);
    assert(pow2(t.levels) == 2 * pow2((t.levels - 1) as nat));
    let ghost p = pow2((t.levels - 1) as nat) as real;
    assert(p >= 1real) by { lemma_pow2_pos((t.levels - 1) as nat); }
    assert(fldr_tr(t, 1) * p == (w_of_lbl_to_l(t, t.n, t.levels) as real));
    assert((w_of_lbl_to_l(t, t.n, t.levels) as real) == 2real * p - (t.m as real));
    assert(fldr_tr(t, 1) < 2real) by(nonlinear_arith)
        requires fldr_tr(t, 1) * p == 2real * p - (t.m as real), p >= 1real, (t.m as real) >= 1real;
}

/// 2^s ≥ 1 (so pow2 is a positive real divisor).
/// One epoch reduces the failure probability by the factor ρ = ½·TR(1):
///   Fail_k ≤ ρ·Fail_{k−K}   for k ≥ K+1.
pub proof fn lemma_fldr_fail_epoch(t: Ddg, k: nat)
    requires valid_ddg(t), t.levels >= 1, k >= t.levels + 1,
    ensures
        fldr_fail_f(t, 0, 0, k)
            <= (1real / 2real) * fldr_tr(t, 1) * fldr_fail_f(t, 0, 0, (k - t.levels) as nat),
{
    reveal_with_fuel(ddg_nodes, 2);
    assert(ddg_nodes(t, 1) == 2);                        // 2·(N(0) − h(0)) = 2·(1 − 0)
    // Fail_k = ½·FFS(1, 2, k−1)
    reveal_with_fuel(fldr_fail_ffs, 3);
    assert(fldr_fail_ffs(t, 1, 2, (k - 1) as nat)
        == fldr_fail_g(t, 1, 0, (k - 1) as nat) + fldr_fail_g(t, 1, 1, (k - 1) as nat));
    assert(fldr_fail_f(t, 0, 0, k)
        == (1real / 2real) * fldr_fail_ffs(t, 1, 2, (k - 1) as nat));
    lemma_fldr_ffs_bound(t, 1, (k - 1) as nat);          // FFS(1,2,k−1) ≤ TR(1)·Fail_{k−K}
    assert(((k - 1) as nat - (t.levels - 1)) as nat == (k - t.levels) as nat);
    let ghost ffs1 = fldr_fail_ffs(t, 1, 2, (k - 1) as nat);
    let ghost tr1 = fldr_tr(t, 1);
    let ghost flo = fldr_fail_f(t, 0, 0, (k - t.levels) as nat);
    lemma_fldr_tr_nonneg(t, 1);
    lemma_fldr_fail_f_bounds(t, 0, 0, (k - t.levels) as nat);
    assert((1real / 2real) * ffs1 <= (1real / 2real) * tr1 * flo) by(nonlinear_arith)
        requires ffs1 <= tr1 * flo;
}

/// Iterating the epoch step:  Fail_{1+jK} ≤ ρʲ   (ρ = ½·TR(1)).
#[verifier::spinoff_prover]
pub proof fn lemma_fldr_fail_geom(t: Ddg, j: nat)
    requires valid_ddg(t), t.levels >= 1,
    ensures
        fldr_fail_f(t, 0, 0, (1 + j * t.levels) as nat)
            <= pow((1real / 2real) * fldr_tr(t, 1), j),
    decreases j,
{
    let ghost rho = (1real / 2real) * fldr_tr(t, 1);
    lemma_fldr_tr_nonneg(t, 1);
    assert(rho >= 0real);
    if j == 0 {
        lemma_fldr_fail_f_bounds(t, 0, 0, 1);
        assert(pow(rho, 0nat) == 1real);
    } else {
        let ghost k = (1 + j * t.levels) as nat;
        assert(k >= t.levels + 1) by(nonlinear_arith)
            requires j >= 1, t.levels >= 1, k == 1 + j * t.levels;
        lemma_fldr_fail_epoch(t, k);
        assert((k - t.levels) as nat == (1 + (j - 1) * t.levels) as nat) by(nonlinear_arith)
            requires j >= 1, k == 1 + j * t.levels;
        lemma_fldr_fail_geom(t, (j - 1) as nat);
        assert(pow(rho, j) == rho * pow(rho, (j - 1) as nat));
        let ghost y = fldr_fail_f(t, 0, 0, (k - t.levels) as nat);
        lemma_fldr_fail_f_bounds(t, 0, 0, (k - t.levels) as nat);
        assert(fldr_fail_f(t, 0, 0, k) <= pow(rho, j)) by(nonlinear_arith)
            requires
                fldr_fail_f(t, 0, 0, k) <= rho * y,
                y <= pow(rho, (j - 1) as nat),
                pow(rho, j) == rho * pow(rho, (j - 1) as nat),
                rho >= 0real, y >= 0real;
    }
}

/// pow(x,j)·pow(1/x,j) = 1  (x > 0), and pow(x,j) > 0.
pub proof fn lemma_pow_recip(x: real, j: nat)
    requires x > 0real,
    ensures pow(x, j) * pow(1real / x, j) == 1real, pow(x, j) > 0real,
    decreases j,
{
    if j > 0 {
        lemma_pow_recip(x, (j - 1) as nat);
        assert(pow(x, j) == x * pow(x, (j - 1) as nat));
        assert(pow(1real / x, j) == (1real / x) * pow(1real / x, (j - 1) as nat));
        assert(pow(x, j) > 0real) by(nonlinear_arith)
            requires pow(x, j) == x * pow(x, (j - 1) as nat), x > 0real, pow(x, (j - 1) as nat) > 0real;
        assert(pow(x, j) * pow(1real / x, j) == 1real) by(nonlinear_arith)
            requires
                pow(x, j) == x * pow(x, (j - 1) as nat),
                pow(1real / x, j) == (1real / x) * pow(1real / x, (j - 1) as nat),
                pow(x, (j - 1) as nat) * pow(1real / x, (j - 1) as nat) == 1real,
                x > 0real;
    }
}

/// For 0 < ρ < 1 and δ > 0 there is j with ρʲ < δ  (geometric decay → 0).
pub proof fn lemma_pow_lt(rho: real, delta: real)
    requires 0real < rho < 1real, delta > 0real,
    ensures exists |j: nat| pow(rho, j) < delta,
{
    let ghost r = 1real / rho;
    assert(r > 1real) by(nonlinear_arith) requires 0real < rho < 1real, r == 1real / rho;
    let ghost target = 1real / delta + 1real;
    assert(target > 0real) by(nonlinear_arith) requires delta > 0real, target == 1real / delta + 1real;
    archimedean_pow(r, target);
    let ghost j = choose |j: nat| pow(r, j) >= target;
    assert(pow(r, j) >= target);
    lemma_pow_recip(rho, j);
    assert(pow(rho, j) < delta) by(nonlinear_arith)
        requires
            pow(rho, j) * pow(r, j) == 1real,
            pow(rho, j) > 0real,
            pow(r, j) >= target,
            target == 1real / delta + 1real,
            delta > 0real;
    assert(pow(rho, j) < delta);
}

// ── CORRECTNESS bound:  fldr_f(0,0,F) ≤ target ───────────────────────────
// Mirrors the termination decay bound, with an accept tail.  atr(c) is the accept
// analogue of tr(c).  Because a reject restarts at the root with strictly smaller
// fuel, Val_F ≤ T follows by (strong) induction on F — no limits.

/// Σ_{d<j, lab<n} ℰ(lab) ≥ 0 for ℰ ≥ 0.
pub proof fn lemma_fldr_ac_nonneg(t: Ddg, e: spec_fn(real) -> real, c: nat, j: nat)
    requires forall |x: real| (#[trigger] e(x)) >= 0real,
    ensures fldr_ac(t, e, c, j) >= 0real,
    decreases j,
{
    if j > 0 {
        lemma_fldr_ac_nonneg(t, e, c, (j - 1) as nat);
        if (t.lab)(c, (j - 1) as nat) < t.n {
            assert(e((t.lab)(c, (j - 1) as nat) as real) >= 0real);
        }
    }
}

/// vfsum at fuel 0 is 0  (fldr_f(·,0) = 0).
pub proof fn lemma_fldr_vfsum_zero(t: Ddg, e: spec_fn(real) -> real, c: nat, m: nat)
    ensures fldr_vfsum(t, e, c, m, 0) == 0real,
    decreases m,
{
    if m > 0 {
        lemma_fldr_vfsum_zero(t, e, c, (m - 1) as nat);
    }
}

/// At fuel 0 only accept leaves contribute:  VS(c,N(c),0) = AC(c,h(c)).
pub proof fn lemma_fldr_vs_base_zero(t: Ddg, e: spec_fn(real) -> real, c: nat)
    requires
        (t.h)(c) <= ddg_nodes(t, c),
        forall |d: nat| d < (t.h)(c) ==> #[trigger] (t.lab)(c, d) <= t.n,
    ensures fldr_vs(t, e, c, ddg_nodes(t, c), 0) == fldr_ac(t, e, c, (t.h)(c)),
{
    let ghost hh = (t.h)(c);
    let ghost m = (ddg_nodes(t, c) - hh) as nat;
    assert(ddg_nodes(t, c) == (hh + m) as nat);
    lemma_fldr_vs_internal(t, e, c, m, 0);          // VS(c,N(c),0) = VS(c,hh,0) + vfsum(c,m,0)
    lemma_fldr_vs_leaf(t, e, c, hh, 0);              // VS(c,hh,0) = AC(c,hh) + RJ·fldr_f(0,0,0)
    lemma_fldr_vfsum_zero(t, e, c, m);              // vfsum(c,m,0) = 0
    // fldr_f(t,e,0,0,0) == 0
}

pub proof fn lemma_fldr_atr_nonneg(t: Ddg, e: spec_fn(real) -> real, c: nat)
    requires forall |x: real| (#[trigger] e(x)) >= 0real,
    ensures fldr_atr(t, e, c) >= 0real,
    decreases t.levels + 1 - c,
{
    if c <= t.levels {
        lemma_fldr_atr_nonneg(t, e, c + 1);
        lemma_fldr_ac_nonneg(t, e, c, (t.h)(c));
    }
}

/// atr(c)·2^{K−c} + ewenc(c−1) = ewenc(K)  (connects the accept tail to the leaf-sum).
pub proof fn lemma_fldr_atr_wenc(t: Ddg, e: spec_fn(real) -> real, c: nat)
    requires 1 <= c <= t.levels,
    ensures
        fldr_atr(t, e, c) * (pow2((t.levels - c) as nat) as real)
            + fldr_ewenc(t, e, (c - 1) as nat) == fldr_ewenc(t, e, t.levels),
    decreases t.levels - c,
{
    let ghost k = t.levels;
    let ghost ac = fldr_ac(t, e, c, (t.h)(c));
    let ghost pk = pow2((k - c) as nat) as real;
    assert(fldr_ewenc(t, e, c) == fldr_ewenc(t, e, (c - 1) as nat) + ac * pk);
    if c == k {
        assert(fldr_atr(t, e, c + 1) == 0real);
        lemma2_to64();
        assert(pow2((k - c) as nat) == 1);
    } else {
        lemma_fldr_atr_wenc(t, e, c + 1);
        let ghost a = fldr_atr(t, e, c + 1);
        let ghost p = pow2((k - c - 1) as nat) as real;
        assert((k - (c + 1)) as nat == (k - c - 1) as nat);
        assert(pow2((k - c) as nat) == 2 * pow2((k - c - 1) as nat));
        assert(pk == 2real * p);
        assert(fldr_atr(t, e, c) * pk + fldr_ewenc(t, e, (c - 1) as nat)
                == fldr_ewenc(t, e, k)) by(nonlinear_arith)
            requires
                fldr_atr(t, e, c) == ac + (1real / 2real) * a,
                pk == 2real * p,
                a * p + fldr_ewenc(t, e, c) == fldr_ewenc(t, e, k),
                fldr_ewenc(t, e, c) == fldr_ewenc(t, e, (c - 1) as nat) + ac * pk;
    }
}

pub proof fn lemma_fldr_wsum_nonneg(t: Ddg, e: spec_fn(real) -> real, j: nat)
    requires forall |x: real| (#[trigger] e(x)) >= 0real,
    ensures fldr_wsum(t, e, j) >= 0real,
    decreases j,
{
    if j > 0 {
        lemma_fldr_wsum_nonneg(t, e, (j - 1) as nat);
        assert((t.weights)((j - 1) as nat) as real * e((j - 1) as real) >= 0real) by(nonlinear_arith)
            requires (t.weights)((j - 1) as nat) as real >= 0real, e((j - 1) as real) >= 0real;
    }
}

pub proof fn lemma_fldr_exp_nonneg(t: Ddg, e: spec_fn(real) -> real)
    requires forall |x: real| (#[trigger] e(x)) >= 0real, t.m >= 1,
    ensures fldr_exp(t, e) >= 0real,
{
    lemma_fldr_wsum_nonneg(t, e, t.n);
    assert(fldr_exp(t, e) >= 0real) by(nonlinear_arith)
        requires fldr_exp(t, e) == fldr_wsum(t, e, t.n) / (t.m as real),
            fldr_wsum(t, e, t.n) >= 0real, (t.m as real) >= 1real;
}

/// Downward value bound:  VS(c,N(c),g) ≤ atr(c) + tr(c)·tb,  given Val_{g2} ≤ tb for
/// all g2 ≤ g.  (Accept analogue of `lemma_fldr_ffs_bound`; works for every g.)
pub proof fn lemma_fldr_vs_bound(t: Ddg, e: spec_fn(real) -> real, c: nat, g: nat, tb: real)
    requires
        valid_ddg(t),
        forall |x: real| (#[trigger] e(x)) >= 0real,
        1 <= c <= t.levels,
        tb >= 0real,
        forall |g2: nat| g2 <= g ==> (#[trigger] fldr_f(t, e, 0, 0, g2)) <= tb,
    ensures
        fldr_vs(t, e, c, ddg_nodes(t, c), g) <= fldr_atr(t, e, c) + fldr_tr(t, c) * tb,
    decreases t.levels + 1 - c,
{
    assert((t.h)(c) <= ddg_nodes(t, c));
    assert(forall |d: nat| d < (t.h)(c) ==> #[trigger] (t.lab)(c, d) <= t.n);
    let ghost ac = fldr_ac(t, e, c, (t.h)(c));
    let ghost rj = l_lbl_cnt_upto(t, c, t.n, (t.h)(c)) as real;
    lemma_fldr_atr_nonneg(t, e, c + 1);
    lemma_fldr_tr_nonneg(t, c);
    assert(fldr_atr(t, e, c) == ac + (1real / 2real) * fldr_atr(t, e, c + 1));
    assert(fldr_tr(t, c) == rj + (1real / 2real) * fldr_tr(t, c + 1));
    if g == 0 {
        lemma_fldr_vs_base_zero(t, e, c);                    // VS(c,N(c),0) = ac
        assert(fldr_vs(t, e, c, ddg_nodes(t, c), g) <= fldr_atr(t, e, c) + fldr_tr(t, c) * tb)
            by(nonlinear_arith)
            requires
                fldr_vs(t, e, c, ddg_nodes(t, c), g) == ac,
                fldr_atr(t, e, c) == ac + (1real / 2real) * fldr_atr(t, e, c + 1),
                fldr_atr(t, e, c + 1) >= 0real, fldr_tr(t, c) >= 0real, tb >= 0real;
    } else {
        lemma_fldr_v_level(t, e, c, g);
        assert(fldr_f(t, e, 0, 0, g) <= tb);                 // hyp at g2 = g
        let ghost vg = fldr_f(t, e, 0, 0, g);
        if c == t.levels {
            assert(ddg_nodes(t, c + 1) == 0);
            assert(fldr_vs(t, e, c + 1, 0, (g - 1) as nat) == 0real);
            assert(fldr_atr(t, e, c + 1) == 0real);
            assert(fldr_tr(t, c + 1) == 0real);
            assert(fldr_vs(t, e, c, ddg_nodes(t, c), g) <= fldr_atr(t, e, c) + fldr_tr(t, c) * tb)
                by(nonlinear_arith)
                requires
                    fldr_vs(t, e, c, ddg_nodes(t, c), g) == ac + rj * vg,
                    vg <= tb, rj >= 0real,
                    fldr_atr(t, e, c) == ac, fldr_tr(t, c) == rj;
        } else {
            lemma_fldr_vs_bound(t, e, c + 1, (g - 1) as nat, tb);
            let ghost vs1 = fldr_vs(t, e, c + 1, ddg_nodes(t, c + 1), (g - 1) as nat);
            let ghost atr1 = fldr_atr(t, e, c + 1);
            let ghost tr1 = fldr_tr(t, c + 1);
            assert(fldr_vs(t, e, c, ddg_nodes(t, c), g) <= fldr_atr(t, e, c) + fldr_tr(t, c) * tb)
                by(nonlinear_arith)
                requires
                    fldr_vs(t, e, c, ddg_nodes(t, c), g) == ac + rj * vg + (1real / 2real) * vs1,
                    vs1 <= atr1 + tr1 * tb,
                    vg <= tb, rj >= 0real, tb >= 0real,
                    fldr_atr(t, e, c) == ac + (1real / 2real) * atr1,
                    fldr_tr(t, c) == rj + (1real / 2real) * tr1;
        }
    }
}

/// Correctness:  fldr_f(0,0,F) ≤ target = Σ_{i<n}(aᵢ/m)·ℰ(i),  by strong induction on F.
pub proof fn lemma_fldr_val_le_target(t: Ddg, e: spec_fn(real) -> real, ff: nat)
    requires valid_ddg(t), t.levels >= 1, forall |x: real| (#[trigger] e(x)) >= 0real,
    ensures fldr_f(t, e, 0, 0, ff) <= fldr_exp(t, e),
    decreases ff,
{
    lemma_fldr_exp_nonneg(t, e);
    if ff > 0 {
        assert forall |g2: nat| g2 <= (ff - 1) as nat implies
            (#[trigger] fldr_f(t, e, 0, 0, g2)) <= fldr_exp(t, e) by {
            lemma_fldr_val_le_target(t, e, g2);
        }
        let ghost v = fldr_exp(t, e);
        lemma_fldr_vs_bound(t, e, 1, (ff - 1) as nat, v);
        // root unfold: Val_ff = ½·VS(1,2,ff-1),  N(1) = 2
        reveal_with_fuel(ddg_nodes, 2);
        assert(ddg_nodes(t, 1) == 2);
        reveal_with_fuel(fldr_vs, 3);
        assert(fldr_vs(t, e, 1, 2, (ff - 1) as nat)
            == fldr_g(t, e, 1, 0, (ff - 1) as nat) + fldr_g(t, e, 1, 1, (ff - 1) as nat));
        assert(fldr_f(t, e, 0, 0, ff) == (1real / 2real) * fldr_vs(t, e, 1, 2, (ff - 1) as nat));
        // arithmetic: ½(atr(1) + tr(1)·T) = T
        lemma_fldr_atr_wenc(t, e, 1);
        lemma_fldr_tr_wenc(t, 1);
        lemma_fldr_leafsum(t, e);
        let ghost p = pow2((t.levels - 1) as nat) as real;
        assert(p >= 1real) by { lemma_pow2_pos((t.levels - 1) as nat); }
        assert(pow2(t.levels) == 2 * pow2((t.levels - 1) as nat));
        // atr(1)·p == wsum ;  tr(1)·p == 2^K − m ;  2^K = 2p ;  T = wsum/m
        assert(fldr_atr(t, e, 1) * p == fldr_wsum(t, e, t.n));
        assert(fldr_tr(t, 1) * p == (w_of_lbl_to_l(t, t.n, t.levels) as real));
        assert((w_of_lbl_to_l(t, t.n, t.levels) as real) == 2real * p - (t.m as real));
        // product form of T = wsum/m  (avoids division inside nonlinear_arith)
        assert(fldr_exp(t, e) * (t.m as real) == fldr_wsum(t, e, t.n)) by(nonlinear_arith)
            requires fldr_exp(t, e) == fldr_wsum(t, e, t.n) / (t.m as real), (t.m as real) >= 1real;
        // VS(1, N(1), ff−1) ≤ atr(1) + tr(1)·T  (vs_bound, with N(1) = 2)
        let ghost b = fldr_atr(t, e, 1) + fldr_tr(t, 1) * v;
        assert(fldr_vs(t, e, 1, 2, (ff - 1) as nat) <= b);
        // b·p = atr(1)·p + tr(1)·v·p = wsum + v·(2p−m) = 2p·v  (since v·m = wsum)
        assert(fldr_tr(t, 1) * v * p == v * (2real * p - (t.m as real))) by(nonlinear_arith)
            requires fldr_tr(t, 1) * p == 2real * p - (t.m as real);
        assert(b * p == 2real * p * v) by(nonlinear_arith)
            requires
                b == fldr_atr(t, e, 1) + fldr_tr(t, 1) * v,
                fldr_atr(t, e, 1) * p == fldr_wsum(t, e, t.n),
                fldr_tr(t, 1) * v * p == v * (2real * p - (t.m as real)),
                v * (t.m as real) == fldr_wsum(t, e, t.n);
        assert(b == 2real * v) by(nonlinear_arith) requires b * p == 2real * p * v, p >= 1real;
        assert(fldr_f(t, e, 0, 0, ff) <= v) by(nonlinear_arith)
            requires
                fldr_f(t, e, 0, 0, ff) == (1real / 2real) * fldr_vs(t, e, 1, 2, (ff - 1) as nat),
                fldr_vs(t, e, 1, 2, (ff - 1) as nat) <= b,
                b == 2real * v;
    }
}

/// Almost-sure termination:  ∀δ>0 ∃k. fldr_fail_f(0,0,k) < δ.
pub proof fn lemma_fldr_fail_witness(t: Ddg, delta: real)
    requires valid_ddg(t), t.levels >= 1, delta > 0real,
    ensures exists |k: nat| fldr_fail_f(t, 0, 0, k) < delta,
{
    let ghost rho = (1real / 2real) * fldr_tr(t, 1);
    lemma_fldr_tr1_lt2(t);
    assert(0real <= rho < 1real);
    if rho <= 0real {
        lemma_fldr_fail_geom(t, 1);
        assert(pow(rho, 1nat) == rho);
        assert(fldr_fail_f(t, 0, 0, (1 + 1 * t.levels) as nat) < delta);
    } else {
        lemma_pow_lt(rho, delta);
        let ghost j = choose |j: nat| pow(rho, j) < delta;
        lemma_fldr_fail_geom(t, j);
        assert(fldr_fail_f(t, 0, 0, (1 + j * t.levels) as nat) < delta);
    }
}

// ── (6) Executable sampler ────────────────────────────────────────────────────

/// N(c) ≤ 2^c  (each internal node has ≤ two children).  Under `valid_ddg` the
/// subtraction N(c−1)−h(c−1) is exact (h ≤ N), so no `nat`-clamp reasoning is needed.
pub proof fn lemma_ddg_nodes_le_pow2(t: Ddg, c: nat)
    requires valid_ddg(t), c <= t.levels + 1,
    ensures ddg_nodes(t, c) <= pow2(c),
    decreases c,
{
    if c > 0 {
        lemma_ddg_nodes_le_pow2(t, (c - 1) as nat);
        let ghost a = ddg_nodes(t, (c - 1) as nat);
        let ghost b = (t.h)((c - 1) as nat);
        assert(b <= a);                              // valid: h(c−1) ≤ N(c−1) (h(0)=0)
        assert((a - b) as nat == a - b);             // exact (b ≤ a)
        assert(ddg_nodes(t, c) == 2 * (a - b));
        assert(pow2(c) == 2 * pow2((c - 1) as nat));
    }
}

/// pow2 is monotone:  s ≤ t ⟹ 2^s ≤ 2^t.  (vstd gives the strict case.)
pub proof fn lemma_pow2_mono(s: nat, t: nat)
    requires s <= t,
    ensures pow2(s) <= pow2(t),
{
    if s < t {
        lemma_pow2_strictly_increases(s, t);
    }
}

/// k < 2^k.  Proved as k + 1 ≤ 2^k by induction on the broadcast unfold.
pub proof fn lemma_pow2_gt(k: nat)
    ensures k < pow2(k),
    decreases k,
{
    if k == 0 {
        lemma2_to64();
    } else {
        lemma_pow2_gt((k - 1) as nat);
        lemma_pow2_pos((k - 1) as nat);
    }
}

/// 2^62 as a concrete u64 — used to bound the doubling in `pow2_exec`.
#[verifier::spinoff_prover]
pub proof fn lemma_pow2_62()
    ensures pow2(62) == 4611686018427387904u64,
{
    lemma2_to64();
    lemma_pow2_adds(62, 2);
    // pow2(64) == pow2(62) * pow2(2) == pow2(62) * 4
    assert(pow2(64) == 0x10000000000000000);
    assert(pow2(2) == 4);
    assert(pow2(62) * 4 == 0x10000000000000000);
    assert(pow2(62) == 4611686018427387904) by(nonlinear_arith)
        requires pow2(62) * 4 == 0x10000000000000000;
}

/// The DDG tree closes exactly:  N(K) = h(K).  (From N(K+1)=0 and h(K) ≤ N(K).)
pub proof fn lemma_ddg_close(t: Ddg)
    requires valid_ddg(t),
    ensures ddg_nodes(t, t.levels) == (t.h)(t.levels),
{
    assert(ddg_nodes(t, (t.levels + 1) as nat) == 0);                       // valid
    assert(ddg_nodes(t, (t.levels + 1) as nat)
        == 2 * ((ddg_nodes(t, t.levels) - (t.h)(t.levels)) as nat));        // def
    assert((t.h)(t.levels) <= ddg_nodes(t, t.levels));                      // valid (1≤K≤K)
}

/// Split off the next bit:  x mod 2m = (x mod m) + ((x/m) mod 2)·m.
pub proof fn lemma_bit_breakdown(x: nat, m: nat)
    requires m > 0,
    ensures (x as int) % (2 * (m as int))
        == (x as int) % (m as int) + (((x as int) / (m as int)) % 2) * (m as int),
{
    let xi = x as int;
    let mi = m as int;
    let q = xi / mi;
    let r = xi % mi;
    lemma_fundamental_div_mod(xi, mi);          // xi == mi*q + r, 0 <= r < mi
    lemma_fundamental_div_mod(q, 2);            // q == 2*(q/2) + q%2
    let lo = mi * (q % 2) + r;
    assert(xi == (q / 2) * (2 * mi) + lo) by(nonlinear_arith)
        requires xi == mi * q + r, q == 2 * (q / 2) + q % 2, lo == mi * (q % 2) + r;
    assert(0 <= lo < 2 * mi) by(nonlinear_arith)
        requires 0 <= r < mi, 0 <= q % 2 < 2, lo == mi * (q % 2) + r, mi > 0;
    lemma_fundamental_div_mod_converse(xi, 2 * mi, q / 2, lo);
}

/// Binary reconstruction:  bitval(x, k) = x mod 2^k.
pub proof fn lemma_bitval_eq(x: nat, k: nat)
    ensures (bitval(x, k) as int) == (x as int) % (pow2(k) as int),
    decreases k,
{
    if k == 0 {
        lemma2_to64();
        assert(pow2(0) == 1);
        assert((x as int) % 1 == 0);
    } else {
        lemma_bitval_eq(x, (k - 1) as nat);
        let m = pow2((k - 1) as nat);
        lemma_pow2_unfold(k);
        assert(pow2(k) == 2 * m);
        lemma_pow2_pos((k - 1) as nat);
        lemma_bit_breakdown(x, m);
    }
}

/// For x < 2^K the bits reconstruct x exactly.
pub proof fn lemma_bitval_full(x: nat, k: nat)
    requires x < pow2(k),
    ensures bitval(x, k) == x,
{
    lemma_bitval_eq(x, k);
    lemma_pow2_pos(k);
    lemma_fundamental_div_mod_converse(x as int, pow2(k) as int, 0, x as int);
}

/// Top c bits + bottom (k−c) bits = all k bits.
pub proof fn lemma_topbits_bitval(x: nat, k: nat, c: nat)
    requires c <= k,
    ensures topbits(x, k, c) + bitval(x, (k - c) as nat) == bitval(x, k),
    decreases c,
{
    if c > 0 {
        lemma_topbits_bitval(x, k, (c - 1) as nat);
        // bitval at (k−c+1) unfolds:  bitval(x,k−c+1) = bitval(x,k−c) + bit(x,k−c)·2^{k−c}
        assert((k - (c - 1) as nat) as nat == (k - c) as nat + 1);
        assert(bitval(x, (k - (c - 1) as nat) as nat)
            == bitval(x, (k - c) as nat) + bit(x, (k - c) as nat) * pow2((k - c) as nat));
    }
}

/// Encoding:  for x < 2^k, the top k bits reconstruct x.
pub proof fn lemma_topbits_full(x: nat, k: nat)
    requires x < pow2(k),
    ensures topbits(x, k, k) == x,
{
    lemma_topbits_bitval(x, k, k);
    assert(bitval(x, 0) == 0);
    lemma_bitval_full(x, k);
}

/// pcnt is non-decreasing in its range.
pub proof fn lemma_pcnt_mono(pctx: PCtx, c: nat, a: nat, b: nat)
    requires a <= b,
    ensures pcnt(pctx, c, a) <= pcnt(pctx, c, b),
    decreases b,
{
    if b > a {
        lemma_pcnt_mono(pctx, c, a, (b - 1) as nat);
    }
}

/// A present label l sits at position pcnt(c,l):  sel(c, pcnt(c,l), upper) = l.
pub proof fn lemma_sel_at(pctx: PCtx, c: nat, l: nat, upper: nat)
    requires pres(pctx, c, l) == 1, l < upper,
    ensures sel(pctx, c, pcnt(pctx, c, l), upper) == l,
    decreases upper,
{
    if upper > l + 1 {
        lemma_pcnt_mono(pctx, c, (l + 1) as nat, (upper - 1) as nat);
        assert(pcnt(pctx, c, (l + 1) as nat) == pcnt(pctx, c, l) + 1);
        lemma_sel_at(pctx, c, l, (upper - 1) as nat);
    }
}

/// The select construction realizes the bit-histogram:
///   l_lbl_cnt_upto(built, c, ℓ, pcnt(c,upto)) = (ℓ < upto ? pres(c,ℓ) : 0).
pub proof fn lemma_count_built(pctx: PCtx, c: nat, l: nat, upto: nat)
    requires l <= pctx.n, upto <= pctx.n + 1,
    ensures
        l_lbl_cnt_upto(built_ddg(pctx), c, l, pcnt(pctx, c, upto))
            == (if l < upto { pres(pctx, c, l) } else { 0nat }),
    decreases upto,
{
    if upto > 0 {
        lemma_count_built(pctx, c, l, (upto - 1) as nat);
        let ghost up1 = (upto - 1) as nat;
        if pres(pctx, c, up1) == 1 {
            lemma_sel_at(pctx, c, up1, (pctx.n + 1) as nat);
            // pcnt(c,upto) = pcnt(c,up1)+1; lab(c, pcnt(c,up1)) = sel(c,pcnt(c,up1),n+1) = up1
            assert(pcnt(pctx, c, upto) == pcnt(pctx, c, up1) + 1);
            assert((built_ddg(pctx).lab)(c, pcnt(pctx, c, up1)) == up1);
        } else {
            assert(pcnt(pctx, c, upto) == pcnt(pctx, c, up1));
        }
    }
}

/// The built table's per-label encoding equals the bit-histogram:
///   w_of_lbl_to_l(built, ℓ, c) = topbits(ew(ℓ), K, c).
pub proof fn lemma_wenc_eq_topbits(pctx: PCtx, l: nat, c: nat)
    requires l <= pctx.n, c <= pctx.levels,
    ensures w_of_lbl_to_l(built_ddg(pctx), l, c) == topbits(ew(pctx, l), pctx.levels, c),
    decreases c,
{
    if c > 0 {
        lemma_wenc_eq_topbits(pctx, l, (c - 1) as nat);
        assert((built_ddg(pctx).h)(c) == pcnt(pctx, c, (pctx.n + 1) as nat));
        lemma_count_built(pctx, c, l, (pctx.n + 1) as nat);   // l_lbl_cnt_upto(built,c,l,h(c)) = pres(pctx,c,l)
        assert((built_ddg(pctx).levels - c) as nat == (pctx.levels - c) as nat);
    }
}

/// Hence each label's leaves encode its (extended) weight, when ew(ℓ) < 2ᴷ.
pub proof fn lemma_built_wenc(pctx: PCtx, l: nat)
    requires l <= pctx.n, ew(pctx, l) < pow2(pctx.levels),
    ensures w_of_lbl_to_l(built_ddg(pctx), l, pctx.levels) == ew(pctx, l),
{
    lemma_wenc_eq_topbits(pctx, l, pctx.levels);
    lemma_topbits_full(ew(pctx, l), pctx.levels);
}

/// One level of the row-sum:  rowtop(c,n) = rowtop(c−1,n) + pcnt(c,n)·2^{K−c}.
pub proof fn lemma_rowtop_step(pctx: PCtx, c: nat, n: nat)
    requires c >= 1,
    ensures rowtop(pctx, c, n) == rowtop(pctx, (c - 1) as nat, n) + pcnt(pctx, c, n) * pow2((pctx.levels - c) as nat),
    decreases n,
{
    if n > 0 {
        lemma_rowtop_step(pctx, c, (n - 1) as nat);
        let ghost l = (n - 1) as nat;
        let ghost p = pow2((pctx.levels - c) as nat);
        // topbits(ew(l),K,c) = topbits(ew(l),K,c-1) + pres(pctx,c,l)*p
        assert(topbits(ew(pctx, l), pctx.levels, c)
            == topbits(ew(pctx, l), pctx.levels, (c - 1) as nat) + pres(pctx, c, l) * p);
        // pcnt(c,n) = pcnt(c,n-1) + pres(c,n-1=l)
        assert(pcnt(pctx, c, n) == pcnt(pctx, c, l) + pres(pctx, c, l));
        assert(rowtop(pctx, c, n) == rowtop(pctx, c, l) + topbits(ew(pctx, l), pctx.levels, c));
        assert(rowtop(pctx, (c - 1) as nat, n)
            == rowtop(pctx, (c - 1) as nat, l) + topbits(ew(pctx, l), pctx.levels, (c - 1) as nat));
        assert(rowtop(pctx, c, n) == rowtop(pctx, (c - 1) as nat, n) + pcnt(pctx, c, n) * p)
            by(nonlinear_arith)
            requires
                rowtop(pctx, c, n) == rowtop(pctx, c, l) + topbits(ew(pctx, l), pctx.levels, c),
                rowtop(pctx, c, l) == rowtop(pctx, (c - 1) as nat, l) + pcnt(pctx, c, l) * p,
                rowtop(pctx, (c - 1) as nat, n) == rowtop(pctx, (c - 1) as nat, l) + topbits(ew(pctx, l), pctx.levels, (c - 1) as nat),
                topbits(ew(pctx, l), pctx.levels, c) == topbits(ew(pctx, l), pctx.levels, (c - 1) as nat) + pres(pctx, c, l) * p,
                pcnt(pctx, c, n) == pcnt(pctx, c, l) + pres(pctx, c, l);
    } else {
        assert(pcnt(pctx, c, 0) == 0);
        assert(pcnt(pctx, c, 0) * pow2((pctx.levels - c) as nat) == 0);
    }
}

pub proof fn lemma_rowtop_zero(pctx: PCtx, n: nat)
    ensures rowtop(pctx, 0, n) == 0,
    decreases n,
{
    if n > 0 {
        lemma_rowtop_zero(pctx, (n - 1) as nat);
    }
}

/// filled(c) = rowtop(c, n+1)  (cells covered = bit-histogram row-sum).
pub proof fn lemma_filled_eq_rowtop(pctx: PCtx, c: nat)
    requires c <= pctx.levels,
    ensures filled(pctx, c) == rowtop(pctx, c, (pctx.n + 1) as nat),
    decreases c,
{
    if c == 0 {
        lemma_rowtop_zero(pctx, (pctx.n + 1) as nat);
    } else {
        lemma_filled_eq_rowtop(pctx, (c - 1) as nat);
        lemma_rowtop_step(pctx, c, (pctx.n + 1) as nat);
    }
}

/// rowtop(K, n) = Σ_{ℓ<n} ew(ℓ)  (each label's top-K bits reconstruct its weight).
pub proof fn lemma_rowtop_ew(pctx: PCtx, n: nat)
    requires forall |l: nat| l < n ==> #[trigger] ew(pctx, l) < pow2(pctx.levels),
    ensures rowtop(pctx, pctx.levels, n) == ewsum(pctx, n),
    decreases n,
{
    if n > 0 {
        lemma_rowtop_ew(pctx, (n - 1) as nat);
        lemma_topbits_full(ew(pctx, (n - 1) as nat), pctx.levels);
    }
}

/// Every extended weight (real or reject) is < 2ᴷ.
pub proof fn lemma_ew_bound(pctx: PCtx, l: nat)
    requires pctx.wf(), l <= pctx.n,
    ensures ew(pctx, l) < pow2(pctx.levels),
{
}

pub proof fn lemma_filled_mono(pctx: PCtx, a: nat, b: nat)
    requires a <= b,
    ensures filled(pctx, a) <= filled(pctx, b),
    decreases b,
{
    if b > a {
        lemma_filled_mono(pctx, a, (b - 1) as nat);
    }
}

/// The leaves fill all 2ᴷ base cells:  filled(K) = 2ᴷ  ( = Σ_ℓ ew(ℓ) = m + reject ).
pub proof fn lemma_filled_total(pctx: PCtx)
    requires pctx.wf(),
    ensures filled(pctx, pctx.levels) == pow2(pctx.levels),
{
    assert forall |l: nat| l < pctx.n + 1 implies #[trigger] ew(pctx, l) < pow2(pctx.levels) by {
        lemma_ew_bound(pctx, l);
    }
    lemma_filled_eq_rowtop(pctx, pctx.levels);
    lemma_rowtop_ew(pctx, (pctx.n + 1) as nat);
    assert(ewsum(pctx, (pctx.n + 1) as nat) == ewsum(pctx, pctx.n) + ew(pctx, pctx.n));
    assert(ew(pctx, pctx.n) == pctx.rej);
}

/// No leaves at level 0:  bit K of any weight (< 2ᴷ) is 0.
pub proof fn lemma_pres0_zero(pctx: PCtx, l: nat)
    requires pctx.wf(), l <= pctx.n,
    ensures pres(pctx, 0, l) == 0,
{
    lemma_ew_bound(pctx, l);
    lemma_fundamental_div_mod_converse(ew(pctx, l) as int, pow2(pctx.levels) as int, 0, ew(pctx, l) as int);
}

pub proof fn lemma_pcnt0_zero(pctx: PCtx, upto: nat)
    requires pctx.wf(), upto <= pctx.n + 1,
    ensures pcnt(pctx, 0, upto) == 0,
    decreases upto,
{
    if upto > 0 {
        lemma_pcnt0_zero(pctx, (upto - 1) as nat);
        lemma_pres0_zero(pctx, (upto - 1) as nat);
    }
}

/// N(c)·2^{K−c} + filled(c−1) = 2ᴷ   (the "unfilled cells" invariant), for 1 ≤ c ≤ K.
pub proof fn lemma_n_filled(pctx: PCtx, c: nat)
    requires pctx.wf(), 1 <= c <= pctx.levels,
    ensures
        ddg_nodes(built_ddg(pctx), c) * pow2((pctx.levels - c) as nat) + filled(pctx, (c - 1) as nat)
            == pow2(pctx.levels),
    decreases c,
{
    let ghost t = built_ddg(pctx);
    if c == 1 {
        lemma_pcnt0_zero(pctx, (pctx.n + 1) as nat);            // (t.h)(0) = pcnt(pctx,0,n+1) = 0
        reveal_with_fuel(ddg_nodes, 2);
        assert(ddg_nodes(t, 1) == 2);
        assert(pow2(pctx.levels) == 2 * pow2((pctx.levels - 1) as nat));
    } else {
        let ghost cm = (c - 1) as nat;
        lemma_n_filled(pctx, cm);                            // N(cm)·P_{cm} + filled(cm−1) = 2ᴷ
        lemma_filled_total(pctx);
        lemma_filled_mono(pctx, cm, pctx.levels);                      // filled(cm) ≤ 2ᴷ
        let ghost nd1 = ddg_nodes(t, cm);
        let ghost hd1 = (t.h)(cm);
        let ghost pd = pow2((pctx.levels - c) as nat);
        let ghost pdm = pow2((pctx.levels - cm) as nat);
        assert(pdm == 2 * pd);
        assert(filled(pctx, cm) == filled(pctx, (cm - 1) as nat) + hd1 * pdm);
        // h(cm) ≤ N(cm):  hd1·pdm = filled(cm)−filled(cm−1) ≤ 2ᴷ−filled(cm−1) = nd1·pdm
        assert(pd >= 1) by { lemma_pow2_pos((pctx.levels - c) as nat); }
        assert(hd1 <= nd1) by(nonlinear_arith)
            requires
                nd1 * pdm + filled(pctx, (cm - 1) as nat) == pow2(pctx.levels),
                filled(pctx, cm) == filled(pctx, (cm - 1) as nat) + hd1 * pdm,
                filled(pctx, cm) <= pow2(pctx.levels),
                pdm == 2 * pd, pd >= 1;
        assert(ddg_nodes(t, c) == 2 * (nd1 - hd1));
        assert(ddg_nodes(t, c) * pd + filled(pctx, cm) == pow2(pctx.levels)) by(nonlinear_arith)
            requires
                nd1 * pdm + filled(pctx, (cm - 1) as nat) == pow2(pctx.levels),
                filled(pctx, cm) == filled(pctx, (cm - 1) as nat) + hd1 * pdm,
                pdm == 2 * pd,
                ddg_nodes(t, c) == 2 * (nd1 - hd1),
                hd1 <= nd1;
    }
}

/// Every level's leaf count fits:  h(c) ≤ N(c)  (1 ≤ c ≤ K).
pub proof fn lemma_h_le_n(pctx: PCtx, c: nat)
    requires pctx.wf(), 1 <= c <= pctx.levels,
    ensures (built_ddg(pctx).h)(c) <= ddg_nodes(built_ddg(pctx), c),
{
    let ghost t = built_ddg(pctx);
    lemma_n_filled(pctx, c);
    lemma_filled_total(pctx);
    lemma_filled_mono(pctx, c, pctx.levels);
    let ghost pd = pow2((pctx.levels - c) as nat);
    assert(filled(pctx, c) == filled(pctx, (c - 1) as nat) + (t.h)(c) * pd);
    assert(pd >= 1) by { lemma_pow2_pos((pctx.levels - c) as nat); }
    assert((t.h)(c) <= ddg_nodes(t, c)) by(nonlinear_arith)
        requires
            ddg_nodes(t, c) * pd + filled(pctx, (c - 1) as nat) == pow2(pctx.levels),
            filled(pctx, c) == filled(pctx, (c - 1) as nat) + (t.h)(c) * pd,
            filled(pctx, c) <= pow2(pctx.levels),
            pd >= 1;
}

/// The tree closes exactly:  N(K+1) = 0.
#[verifier::spinoff_prover]
pub proof fn lemma_built_close(pctx: PCtx)
    requires pctx.wf(),
    ensures ddg_nodes(built_ddg(pctx), (pctx.levels + 1) as nat) == 0,
{
    let ghost t = built_ddg(pctx);
    lemma_n_filled(pctx, pctx.levels);                 // N(K)·1 + filled(K−1) = 2ᴷ
    lemma_filled_total(pctx);                    // filled(K) = 2ᴷ
    lemma2_to64();
    assert(pow2((pctx.levels - pctx.levels) as nat) == 1);
    assert(filled(pctx, pctx.levels) == filled(pctx, (pctx.levels - 1) as nat) + (t.h)(pctx.levels) * pow2((pctx.levels - pctx.levels) as nat));
    assert((t.h)(pctx.levels) == ddg_nodes(t, pctx.levels));
    assert(ddg_nodes(t, (pctx.levels + 1) as nat)
        == 2 * ((ddg_nodes(t, pctx.levels) - (t.h)(pctx.levels)) as nat));
}

/// Σ ew over real labels = the built table's weight sum (= m).
pub proof fn lemma_ewsum_wsum(pctx: PCtx, j: nat)
    requires j <= pctx.n,
    ensures ewsum(pctx, j) == fldr_wsum_nat(built_ddg(pctx), j),
    decreases j,
{
    if j > 0 {
        lemma_ewsum_wsum(pctx, (j - 1) as nat);
    }
}

/// A position below the leaf count selects a real label:  sel(c,d,upper) < upper.
pub proof fn lemma_sel_lt(pctx: PCtx, c: nat, d: nat, upper: nat)
    requires d < pcnt(pctx, c, upper),
    ensures sel(pctx, c, d, upper) < upper,
    decreases upper,
{
    if upper > 0 {
        if pres(pctx, c, (upper - 1) as nat) == 1 && pcnt(pctx, c, (upper - 1) as nat) == d {
        } else {
            assert(d < pcnt(pctx, c, (upper - 1) as nat));
            lemma_sel_lt(pctx, c, d, (upper - 1) as nat);
        }
    }
}

/// the DDG built from a well-formed weight vector is a valid DDG.
pub proof fn lemma_built_valid(pctx: PCtx)
    requires pctx.wf(),
    ensures valid_ddg(built_ddg(pctx)),
{
    let ghost t = built_ddg(pctx);
    lemma_ewsum_wsum(pctx, pctx.n);                          // t.m = Σ weights
    lemma_pcnt0_zero(pctx, (pctx.n + 1) as nat);            // h(0) = 0
    lemma_built_close(pctx);                              // N(K+1) = 0
    assert forall |c: nat| 1 <= c <= t.levels implies (t.h)(c) <= #[trigger] ddg_nodes(t, c) by {
        lemma_h_le_n(pctx, c);
    }
    assert forall |c: nat, d: nat| d < (t.h)(c) implies #[trigger] (t.lab)(c, d) <= t.n by {
        lemma_sel_lt(pctx, c, d, (pctx.n + 1) as nat);
    }
    assert forall |l: nat| l < t.n implies #[trigger] w_of_lbl_to_l(t, l, t.levels) == (t.weights)(l) by {
        lemma_ew_bound(pctx, l);
        lemma_built_wenc(pctx, l);
    }
    lemma_ew_bound(pctx, pctx.n);
    lemma_built_wenc(pctx, pctx.n);                          // w_of_lbl_to_l(t,n,K) = reject = 2ᴷ − m
}

// ── Agreement: two Ddgs that match on the cells valid_ddg reads are equi-valid ──

/// ddg_nodes depends only on h below c.
pub proof fn lemma_ddg_nodes_agree(t1: Ddg, t2: Ddg, c: nat)
    requires forall |j: nat| j < c ==> #[trigger] (t1.h)(j) == (t2.h)(j),
    ensures ddg_nodes(t1, c) == ddg_nodes(t2, c),
    decreases c,
{
    if c > 0 {
        lemma_ddg_nodes_agree(t1, t2, (c - 1) as nat);
    }
}

/// l_lbl_cnt_upto depends only on lab below j.
pub proof fn lemma_l_lbl_cnt_upto_agree(t1: Ddg, t2: Ddg, c: nat, l: nat, j: nat)
    requires forall |d: nat| d < j ==> #[trigger] (t1.lab)(c, d) == (t2.lab)(c, d),
    ensures l_lbl_cnt_upto(t1, c, l, j) == l_lbl_cnt_upto(t2, c, l, j),
    decreases j,
{
    if j > 0 {
        lemma_l_lbl_cnt_upto_agree(t1, t2, c, l, (j - 1) as nat);
    }
}

/// w_of_lbl_to_l depends only on (h, lab) on levels 1..c at the live positions.
pub proof fn lemma_w_of_lbl_to_l_agree(t1: Ddg, t2: Ddg, l: nat, cc: nat)
    requires
        t1.levels == t2.levels,
        forall |c: nat| 1 <= c <= cc ==> #[trigger] (t1.h)(c) == (t2.h)(c),
        forall |c: nat, d: nat| 1 <= c <= cc && d < (t1.h)(c) ==> #[trigger] (t1.lab)(c, d) == (t2.lab)(c, d),
    ensures w_of_lbl_to_l(t1, l, cc) == w_of_lbl_to_l(t2, l, cc),
    decreases cc,
{
    if cc > 0 {
        lemma_w_of_lbl_to_l_agree(t1, t2, l, (cc - 1) as nat);
        assert((t1.h)(cc) == (t2.h)(cc));
        assert(forall |d: nat| d < (t1.h)(cc) ==> #[trigger] (t1.lab)(cc, d) == (t2.lab)(cc, d));
        lemma_l_lbl_cnt_upto_agree(t1, t2, cc, l, (t1.h)(cc));
    }
}

/// When the PCtx weights agree with the Vec on real labels, `ewsum` is `vsum`.
#[verifier::spinoff_prover]
pub proof fn lemma_ewsum_eq_vsum(pctx: PCtx, s: Seq<u64>, j: nat)
    requires
        j <= pctx.n,
        pctx.n == s.len(),
        forall |l: int| 0 <= l < pctx.n ==> (pctx.weights)(l as nat) == s[l] as nat,
    ensures ewsum(pctx, j) == vsum(s, j),
    decreases j,
{
    if j > 0 {
        lemma_ewsum_eq_vsum(pctx, s, (j - 1) as nat);
        assert(ew(pctx, (j - 1) as nat) == (pctx.weights)((j - 1) as nat));   // j−1 < n
    }
}

/// Transfer `valid_ddg` from the built DDG `bt` to the table view `t` when they share
/// scalar fields/weights and agree on the cells `valid_ddg` reads (h on 0..K, lab on
/// d < h(c) for c ≤ K).
/// fldr_wsum_nat depends only on the weight function (equal here).
#[verifier::spinoff_prover]
pub proof fn lemma_wsum_agree(t1: Ddg, t2: Ddg, j: nat)
    requires t1.weights == t2.weights,
    ensures fldr_wsum_nat(t1, j) == fldr_wsum_nat(t2, j),
    decreases j,
{
    if j > 0 {
        lemma_wsum_agree(t1, t2, (j - 1) as nat);
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_preprocess_valid(t: Ddg, bt: Ddg)
    requires
        valid_ddg(bt),
        t.n == bt.n,
        t.m == bt.m,
        t.levels == bt.levels,
        t.weights == bt.weights,
        forall |c: nat| c <= t.levels ==> (#[trigger] (t.h)(c)) == (bt.h)(c),
        forall |c: nat| c > t.levels ==> (#[trigger] (t.h)(c)) == 0nat,
        forall |c: nat, d: nat| c <= t.levels && d < (bt.h)(c) ==>
            (#[trigger] (t.lab)(c, d)) == (bt.lab)(c, d),
    ensures valid_ddg(t),
{
    // h(0): same as bt
    assert((t.h)(0) == (bt.h)(0));
    // N(K+1) = 0
    lemma_ddg_nodes_agree(t, bt, (t.levels + 1) as nat);
    // h(c) ≤ N(c), 1 ≤ c ≤ K
    assert forall |c: nat| 1 <= c <= t.levels implies (t.h)(c) <= #[trigger] ddg_nodes(t, c) by {
        lemma_ddg_nodes_agree(t, bt, c);
        assert((t.h)(c) == (bt.h)(c));
    }
    // labels in range:  c > K ⇒ h(c) = 0 ⇒ d < h(c) is false (vacuous);  c ≤ K ⇒ matches bt.
    assert forall |c: nat, d: nat| d < (t.h)(c) implies #[trigger] (t.lab)(c, d) <= t.n by {
        if c <= t.levels {
            assert((t.h)(c) == (bt.h)(c));
            assert((t.lab)(c, d) == (bt.lab)(c, d));
        }
    }
    // (h, lab) agree on the live cells of levels 1..K — fed to the wenc agreement lemma.
    assert forall |c: nat, d: nat| 1 <= c <= t.levels && d < (t.h)(c) implies
        (#[trigger] (t.lab)(c, d)) == (bt.lab)(c, d) by {
        assert((t.h)(c) == (bt.h)(c));      // bridges d < t.h(c) to d < bt.h(c)
    }
    // per-label encodings (real labels)
    assert forall |lbl: nat| lbl < t.n implies #[trigger] w_of_lbl_to_l(t, lbl, t.levels) == (t.weights)(lbl) by {
        lemma_w_of_lbl_to_l_agree(t, bt, lbl, t.levels);
        assert(w_of_lbl_to_l(bt, lbl, t.levels) == (bt.weights)(lbl));
    }
    // reject encoding
    lemma_w_of_lbl_to_l_agree(t, bt, t.n, t.levels);
    assert(w_of_lbl_to_l(bt, t.n, t.levels) == (pow2(bt.levels) - bt.m) as nat);

    // remaining scalar conjuncts, bridged from bt
    assert(ddg_nodes(t, (t.levels + 1) as nat) == 0);
    lemma_wsum_agree(t, bt, t.n);                       // fldr_wsum_nat(t,n) = fldr_wsum_nat(bt,n)
    assert(t.m == fldr_wsum_nat(t, t.n));
}

// ── A runnable end-to-end instance ────────────────────────────────────────────

/// Σ weights·ℰ vanishes when ℰ ≡ 0  (so `fldr_exp` is 0 — any positive credit funds it).
#[verifier::spinoff_prover]
pub proof fn lemma_fldr_wsum_zero(t: Ddg, e: spec_fn(real) -> real, j: nat)
    requires forall |x: real| (#[trigger] e(x)) == 0real,
    ensures fldr_wsum(t, e, j) == 0real,
    decreases j,
{
    if j > 0 {
        lemma_fldr_wsum_zero(t, e, (j - 1) as nat);
    }
}

} // verus!
