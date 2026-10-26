//! Two more layouts of the FLDR table, each a [`DdgTable`], so `sample_fldr`
//! sample them with no new sampler proof:
//!
//! - [`FldrH`]: the layout of the AISTATS'20 paper and its C code
//!   (`fldr_preprocess_int`): h[j] for j = 0..k−1 and a flat (n+1)×k matrix
//!   with H[d·k + j] the label of the d-th leaf of level j+1, −1 elsewhere.
//! - [`FldrFlat`]: the layout of ryco117's `fast_loaded_dice_roller`
//!   (`level_label_matrix`, issue #18): one row of n+2 entries per level,
//!   holding the leaf count followed by the labels.
//!
//! Both are built by a preprocessing pass that follows the original code and
//! proves the table's view agrees with `built_ddg`, so `lemma_built_valid`
//! gives `valid_ddg`, exactly as for `fldr_preprocess`.
//!
//! `sample_748_h` and `sample_748_flat` run the (7, 4, 8) example of the paper
//! on each layout.

use vstd::prelude::*;

verus! {

use crate::fldr::*;
#[cfg(verus_keep_ghost)]
use crate::fldr_helper::*;
use crate::ec::*;
#[cfg(verus_keep_ghost)]
use crate::ec::ErrorCreditCarrier::Value;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::{pow2, lemma_pow2_pos, lemma_pow2_strictly_increases, lemma2_to64};
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse;

// ── Shared facts ──────────────────────────────────────────────────────────────

/// a·w + o with o < w determines a and o.
proof fn lemma_idx_inj(a: nat, o: nat, b: nat, q: nat, w: nat)
    requires o < w, q < w, a * w + o == b * w + q,
    ensures a == b, o == q,
{
    lemma_fundamental_div_mod_converse((a * w + o) as int, w as int, a as int, o as int);
    lemma_fundamental_div_mod_converse((b * w + q) as int, w as int, b as int, q as int);
}

/// a·w + o < (a+1)·w ≤ cnt·w for a < cnt, o < w.
proof fn lemma_idx_lt(a: nat, o: nat, w: nat, cnt: nat)
    requires o < w, a < cnt,
    ensures a * w + o < cnt * w,
{
    assert(a * w + o < cnt * w) by(nonlinear_arith) requires o < w, a < cnt;
}

proof fn lemma_mul_le(a: nat, b: nat, c: nat, d: nat)
    requires a <= c, b <= d,
    ensures a * b <= c * d,
{
    assert(a * b <= c * d) by(nonlinear_arith) requires a <= c, b <= d;
}

proof fn lemma_pcnt_le(pctx: PCtx, c: nat, upto: nat)
    ensures pcnt(pctx, c, upto) <= upto,
    decreases upto,
{
    if upto > 0 { lemma_pcnt_le(pctx, c, (upto - 1) as nat); }
}

/// The preprocessing context of a weight vector.
pub open spec fn pctx_of(weights: Seq<u64>, rej: nat, levels: nat) -> PCtx {
    PCtx {
        weights: |i: nat| if i < weights.len() { weights[i as int] as nat } else { 0nat },
        n: weights.len() as nat,
        rej,
        levels,
    }
}

/// The input of the preprocessing passes (as `fldr_preprocess`).
pub open spec fn preprocess_input(weights: Seq<u64>, m: u64, levels: u64) -> bool {
    &&& 1 <= levels <= 62
    &&& pow2(levels as nat) <= usize::MAX as nat
    &&& 1 <= m && m as nat <= pow2(levels as nat)
    &&& m as nat == vsum(weights, weights.len() as nat)
    &&& weights.len() < 0x4000000000000000
    &&& (weights.len() + 2) * (levels as nat) <= usize::MAX as nat
    &&& forall |i: int| 0 <= i < weights.len() ==> (weights[i] as nat) < pow2(levels as nat)
}

/// The table view and `built_ddg` agree where `valid_ddg` looks, so the view
/// is valid.
proof fn lemma_view_valid(t: Ddg, pctx: PCtx)
    requires
        pctx.wf(),
        t.n == pctx.n, t.levels == pctx.levels, t.weights == pctx.weights, t.m == ewsum(pctx, pctx.n),
        (t.h)(0) == 0,
        forall |c: nat| 1 <= c <= t.levels ==> (#[trigger] (t.h)(c)) == pcnt(pctx, c, (pctx.n + 1) as nat),
        forall |c: nat| c > t.levels ==> (#[trigger] (t.h)(c)) == 0nat,
        forall |c: nat, d: nat| 1 <= c <= t.levels && d < pcnt(pctx, c, (pctx.n + 1) as nat) ==>
            (#[trigger] (t.lab)(c, d)) == sel(pctx, c, d, (pctx.n + 1) as nat),
    ensures valid_ddg(t),
{
    let bt = built_ddg(pctx);
    lemma_pcnt0_zero(pctx, (pctx.n + 1) as nat);
    assert forall |c: nat| c <= t.levels implies (#[trigger] (t.h)(c)) == (bt.h)(c) by {}
    assert forall |c: nat, d: nat| c <= t.levels && d < (bt.h)(c) implies (#[trigger] (t.lab)(c, d)) == (bt.lab)(c, d) by {}
    lemma_built_valid(pctx);
    lemma_preprocess_valid(t, bt);
}

// ── The AISTATS layout: h[k] and H[(n+1)·k] ──────────────────────────────────

/// The FLDR table as in Saad et al. AISTATS'20 (Alg. 5) and its C code.
/// `h[j]` and `H[d·k + j]` describe level j+1 (the paper is 0-indexed in j).
pub struct FldrH {
    pub n: u64,
    pub m: u64,
    pub k: u64,
    pub weights: Vec<u64>,
    pub h: Vec<u64>,
    pub hm: Vec<i64>,
}

impl View for FldrH {
    type V = Ddg;
    open spec fn view(&self) -> Ddg {
        let k = self.k as nat;
        Ddg {
            n: self.n as nat,
            weights: |i: nat| if i < self.weights@.len() { self.weights@[i as int] as nat } else { 0nat },
            m: self.m as nat,
            levels: k,
            h: |c: nat| if 1 <= c <= k && c - 1 < self.h@.len() { self.h@[c - 1] as nat } else { 0nat },
            lab: |c: nat, d: nat|
                if 1 <= c <= k && d <= self.n && d * k + (c - 1) < self.hm@.len() && self.hm@[d * k + (c - 1)] >= 0 {
                    self.hm@[d * k + (c - 1)] as nat
                } else {
                    self.n as nat
                },
        }
    }
}

impl DdgTable for FldrH {
    open spec fn wf(&self) -> bool {
        &&& valid_ddg(self@)
        &&& self.k >= 1
        &&& pow2(self.k as nat) <= 4611686018427387904
        &&& pow2(self.k as nat) <= usize::MAX as nat
        &&& self.h@.len() == self.k
        &&& self.hm@.len() == (self.n as nat + 1) * (self.k as nat)
        &&& (self.n as nat + 1) * (self.k as nat) <= usize::MAX as nat
        &&& self.n as nat + 2 <= usize::MAX as nat
        &&& forall |j: int| 0 <= j < self.k ==> #[trigger] self.h@[j] <= self.n + 1
    }

    proof fn wf_props(&self) {}

    fn levels(&self) -> (r: u64) { self.k }

    fn n(&self) -> (r: u64) { self.n }

    fn get_h(&self, c: u64) -> (r: u64) {
        if c == 0 {
            0
        } else {
            proof {
                lemma_pow2_62();
                if self.k > 62 { lemma_pow2_strictly_increases(62nat, self.k as nat); }
            }
            self.h[(c - 1) as usize]
        }
    }

    fn get_lab(&self, c: u64, d: u64) -> (r: u64) {
        proof {
            lemma_pow2_62();
            if self.k > 62 { lemma_pow2_strictly_increases(62nat, self.k as nat); }
            assert(c >= 1);
            assert(self.h@[c - 1] <= self.n + 1);
            assert((d as nat) < self.n as nat + 1);
            lemma_idx_lt(d as nat, (c - 1) as nat, self.k as nat, self.n as nat + 1);
        }
        let dd = d as usize;
        let kk = self.k as usize;
        let i = dd * kk + (c - 1) as usize;
        let v = self.hm[i];
        proof {
            // d < h(c) ≤ N(c) and valid_ddg give a label ≤ n, and the view reads H.
            if !(v >= 0) {
                assert((self@.lab)(c as nat, d as nat) == self.n as nat);
            }
        }
        if v >= 0 { v as u64 } else { self.n }
    }
}

/// `fldr_preprocess_int` of the AISTATS C code:
///
/// ```text
///   for j in 0..k: d = 0
///       for i in 0..n+1:
///           w = (a[i] >> ((k−1) − j)) & 1;  h[j] += w
///           if w: H[d·k + j] = i;  d += 1
/// ```
///
/// The bit is read with a division, as in `build_level`.
pub fn fldr_preprocess_h(weights: Vec<u64>, m: u64, levels: u64) -> (tab: FldrH)
    requires preprocess_input(weights@, m, levels),
    ensures
        tab.wf(),
        tab.n as nat == weights@.len(),
        tab.m == m,
        tab.k == levels,
        tab.weights@ == weights@,
{
    let n: usize = weights.len();
    let k: usize = levels as usize;
    let rej_u: u64 = pow2_exec(levels) - m;
    let ghost pctx = pctx_of(weights@, rej_u as nat, levels as nat);
    proof { lemma_ewsum_eq_vsum(pctx, weights@, pctx.n); }
    let ghost w1 = (n + 1) as nat;
    let mut h: Vec<u64> = Vec::new();
    while h.len() < k
        invariant h.len() <= k, forall |j: int| 0 <= j < h.len() ==> #[trigger] h@[j] == 0,
        decreases k - h.len(),
    {
        h.push(0);
    }
    proof {
        lemma_mul_le(w1, k as nat, (n + 2) as nat, k as nat);
        lemma_mul_le(1, (n + 2) as nat, k as nat, (n + 2) as nat);
        assert((n + 2) * (k as nat) == (k as nat) * (n + 2)) by(nonlinear_arith);
        assert((n as nat + 1) * (k as nat) <= usize::MAX as nat);
    }
    let total: usize = (n + 1) * k;
    let mut hm: Vec<i64> = Vec::new();
    while hm.len() < total
        invariant hm.len() <= total,
        decreases total - hm.len(),
    {
        hm.push(-1);
    }
    let mut j: usize = 0;
    while j < k
        invariant
            n == weights.len(), k == levels, 1 <= k <= 62, j <= k, total == w1 * k,
            w1 == n + 1, n < 0x4000000000000000, n + 2 <= usize::MAX,
            pctx == pctx_of(weights@, rej_u as nat, levels as nat), pctx.wf(),
            h.len() == k, hm.len() == total,
            forall |j2: int| 0 <= j2 < j ==> #[trigger] h@[j2] as nat == pcnt(pctx, (j2 + 1) as nat, w1),
            forall |j2: int| j <= j2 < k ==> #[trigger] h@[j2] == 0,
            forall |j2: int, d: int| 0 <= j2 < j && 0 <= d < h@[j2] ==>
                #[trigger] hm@[d * k + j2] == sel(pctx, (j2 + 1) as nat, d as nat, w1) as i64,
        decreases k - j,
    {
        let p: u64 = pow2_exec(levels - 1 - j as u64);
        let mut d: usize = 0;
        let mut i: usize = 0;
        while i <= n
            invariant
                n == weights.len(), k == levels, 1 <= k <= 62, j < k, i <= n + 1, total == w1 * k,
                w1 == n + 1, n < 0x4000000000000000, n + 2 <= usize::MAX,
                pctx == pctx_of(weights@, rej_u as nat, levels as nat), pctx.wf(),
                p as nat == pow2((levels - 1 - j) as nat),
                h.len() == k, hm.len() == total,
                d as nat == h@[j as int] as nat, d as nat == pcnt(pctx, (j + 1) as nat, i as nat),
                forall |j2: int| 0 <= j2 < j ==> #[trigger] h@[j2] as nat == pcnt(pctx, (j2 + 1) as nat, w1),
                forall |j2: int| j < j2 < k ==> #[trigger] h@[j2] == 0,
                forall |j2: int, d2: int| 0 <= j2 < j && 0 <= d2 < h@[j2] ==>
                    #[trigger] hm@[d2 * k + j2] == sel(pctx, (j2 + 1) as nat, d2 as nat, w1) as i64,
                forall |d2: int| 0 <= d2 < d ==>
                    #[trigger] hm@[d2 * k + j] == sel(pctx, (j + 1) as nat, d2 as nat, i as nat) as i64,
            decreases n + 1 - i,
        {
            let a_i: u64 = if i < n { weights[i] } else { rej_u };
            proof {
                lemma_pow2_pos((levels - 1 - j) as nat);
                lemma_pcnt_le(pctx, (j + 1) as nat, i as nat);
                assert((levels as nat - (j + 1) as nat) as nat == (levels - 1 - j) as nat);
                assert(ew(pctx, i as nat) == a_i as nat);
            }
            let w: u64 = (a_i / p) % 2;
            h.set(j, h[j] + w);
            if w == 1 {
                proof {
                    lemma_idx_lt(d as nat, j as nat, k as nat, w1);
                    assert(d * k <= total);
                }
                let ghost hm0 = hm@;
                hm.set(d * k + j, i as i64);
                proof {
                    assert forall |j2: int, d2: int| 0 <= j2 < j && 0 <= d2 < h@[j2] implies
                        #[trigger] hm@[d2 * k + j2] == sel(pctx, (j2 + 1) as nat, d2 as nat, w1) as i64 by {
                        if d2 * k + j2 == d * k + j {
                            lemma_idx_inj(d2 as nat, j2 as nat, d as nat, j as nat, k as nat);
                        }
                    }
                    assert forall |d2: int| 0 <= d2 < d + 1 implies
                        #[trigger] hm@[d2 * k + j] == sel(pctx, (j + 1) as nat, d2 as nat, (i + 1) as nat) as i64 by {
                        if d2 < d {
                            if d2 * k + j == d * k + j {
                                lemma_idx_inj(d2 as nat, j as nat, d as nat, j as nat, k as nat);
                            }
                            assert(hm0[d2 * k + j] == hm@[d2 * k + j]);
                        }
                    }
                }
                d = d + 1;
            }
            i = i + 1;
        }
        j = j + 1;
    }
    let tab = FldrH { n: n as u64, m, k: levels, weights, h, hm };
    proof {
        let t = tab@;
        assert forall |c: nat| 1 <= c <= t.levels implies (#[trigger] (t.h)(c)) == pcnt(pctx, c, (pctx.n + 1) as nat) by {
            assert(h@[c - 1] as nat == pcnt(pctx, ((c - 1) + 1) as nat, w1));
        }
        assert forall |c: nat, d: nat| 1 <= c <= t.levels && d < pcnt(pctx, c, (pctx.n + 1) as nat) implies
            (#[trigger] (t.lab)(c, d)) == sel(pctx, c, d, (pctx.n + 1) as nat) by {
            let j2 = (c - 1) as int;
            assert(h@[j2] as nat == pcnt(pctx, (j2 + 1) as nat, w1));
            lemma_pcnt_le(pctx, c, w1);
            lemma_sel_lt(pctx, c, d, w1);
            lemma_idx_lt(d, (c - 1) as nat, k as nat, w1);
            assert(hm@[d * k + j2] == sel(pctx, c, d, w1) as i64);
        }
        lemma_view_valid(t, pctx);
        assert forall |j2: int| 0 <= j2 < k implies #[trigger] h@[j2] <= n + 1 by {
            lemma_pcnt_le(pctx, (j2 + 1) as nat, w1);
        }
        lemma_pow2_mono(levels as nat, 62);
        lemma_pow2_62();
    }
    tab
}

// ── The ryco117 layout: one flat row of n+2 entries per level ────────────────

/// `fast_loaded_dice_roller::Generator::level_label_matrix`: row j (level
/// j+1) starts at j·(n+2) with the leaf count, and its labels follow.
pub struct FldrFlat {
    pub n: u64,
    pub m: u64,
    pub levels: u64,
    pub weights: Vec<u64>,
    pub mat: Vec<u64>,
}

impl View for FldrFlat {
    type V = Ddg;
    open spec fn view(&self) -> Ddg {
        let k = self.levels as nat;
        let w = self.n as nat + 2;
        Ddg {
            n: self.n as nat,
            weights: |i: nat| if i < self.weights@.len() { self.weights@[i as int] as nat } else { 0nat },
            m: self.m as nat,
            levels: k,
            h: |c: nat| if 1 <= c <= k && (c - 1) * w < self.mat@.len() { self.mat@[(c - 1) * w] as nat } else { 0nat },
            lab: |c: nat, d: nat|
                if 1 <= c <= k && d <= self.n && (c - 1) * w + 1 + d < self.mat@.len() {
                    self.mat@[(c - 1) * w + 1 + d] as nat
                } else {
                    self.n as nat
                },
        }
    }
}

impl DdgTable for FldrFlat {
    open spec fn wf(&self) -> bool {
        &&& valid_ddg(self@)
        &&& self.levels >= 1
        &&& pow2(self.levels as nat) <= 4611686018427387904
        &&& pow2(self.levels as nat) <= usize::MAX as nat
        &&& self.mat@.len() == (self.n as nat + 2) * (self.levels as nat)
        &&& (self.n as nat + 2) * (self.levels as nat) <= usize::MAX as nat
        &&& self.n as nat + 2 <= usize::MAX as nat
        &&& forall |j: int| 0 <= j < self.levels ==> #[trigger] self.mat@[j * (self.n + 2)] <= self.n + 1
    }

    proof fn wf_props(&self) {}

    fn levels(&self) -> (r: u64) { self.levels }

    fn n(&self) -> (r: u64) { self.n }

    fn get_h(&self, c: u64) -> (r: u64) {
        if c == 0 {
            0
        } else {
            proof {
                lemma_pow2_62();
                if self.levels > 62 { lemma_pow2_strictly_increases(62nat, self.levels as nat); }
                lemma_idx_lt((c - 1) as nat, 0, self.n as nat + 2, self.levels as nat);
            }
            let w = self.n as usize + 2;
            let cc = (c - 1) as usize;
            self.mat[cc * w]
        }
    }

    fn get_lab(&self, c: u64, d: u64) -> (r: u64) {
        proof {
            lemma_pow2_62();
            if self.levels > 62 { lemma_pow2_strictly_increases(62nat, self.levels as nat); }
            assert(c >= 1);
            let w = self.n as nat + 2;
            assert(self.mat@[(c - 1) * w] <= self.n + 1);
            assert((d as nat) < self.n as nat + 1);
            lemma_idx_lt((c - 1) as nat, 1 + d as nat, w, self.levels as nat);
            assert((self.levels as nat) * w == w * (self.levels as nat)) by(nonlinear_arith);
        }
        let w = self.n as usize + 2;
        let cc = (c - 1) as usize;
        let dd = d as usize;
        self.mat[cc * w + 1 + dd]
    }
}

/// `Generator::new` of `fast_loaded_dice_roller`, with the reject label n
/// always present (its weight is 0 when m is a power of two):
///
/// ```text
///   for j in 0..depth: for (i, w) in a:
///       if (w >> (depth − j − 1)) & 1 > 0:
///           k = j·(n+2);  M[k] += 1;  M[k + M[k]] = i
/// ```
pub fn fldr_preprocess_flat(weights: Vec<u64>, m: u64, levels: u64) -> (tab: FldrFlat)
    requires preprocess_input(weights@, m, levels),
    ensures
        tab.wf(),
        tab.n as nat == weights@.len(),
        tab.m == m,
        tab.levels == levels,
        tab.weights@ == weights@,
{
    let n: usize = weights.len();
    let k: usize = levels as usize;
    proof {
        lemma_mul_le(1, (n + 2) as nat, levels as nat, (n + 2) as nat);
        assert((n + 2) * (levels as nat) == (levels as nat) * (n + 2)) by(nonlinear_arith);
    }
    let w2: usize = n + 2;
    let rej_u: u64 = pow2_exec(levels) - m;
    let ghost pctx = pctx_of(weights@, rej_u as nat, levels as nat);
    proof { lemma_ewsum_eq_vsum(pctx, weights@, pctx.n); }
    let ghost w1 = (n + 1) as nat;
    let total: usize = w2 * k;
    let mut mat: Vec<u64> = Vec::new();
    while mat.len() < total
        invariant mat.len() <= total, forall |x: int| 0 <= x < mat.len() ==> #[trigger] mat@[x] == 0,
        decreases total - mat.len(),
    {
        mat.push(0);
    }
    proof {
        assert forall |j2: int, o: int| 0 <= j2 < k && 0 <= o < w2 implies #[trigger] mat@[j2 * w2 + o] == 0 by {
            lemma_idx_lt(j2 as nat, o as nat, w2 as nat, k as nat);
            assert((k as nat) * (w2 as nat) == total) by(nonlinear_arith) requires total == w2 * k;
        }
    }
    let mut j: usize = 0;
    while j < k
        invariant
            n == weights.len(), k == levels, 1 <= k <= 62, j <= k, total == w2 * k, w2 == n + 2,
            w1 == n + 1, n < 0x4000000000000000,
            pctx == pctx_of(weights@, rej_u as nat, levels as nat), pctx.wf(),
            mat.len() == total,
            forall |j2: int| 0 <= j2 < j ==> #[trigger] mat@[j2 * w2] as nat == pcnt(pctx, (j2 + 1) as nat, w1),
            forall |j2: int, d: int| 0 <= j2 < j && 0 <= d < mat@[j2 * w2] ==>
                #[trigger] mat@[j2 * w2 + 1 + d] as nat == sel(pctx, (j2 + 1) as nat, d as nat, w1),
            forall |j2: int, o: int| j <= j2 < k && 0 <= o < w2 ==> #[trigger] mat@[j2 * w2 + o] == 0,
        decreases k - j,
    {
        let p: u64 = pow2_exec(levels - 1 - j as u64);
        proof {
            lemma_idx_lt(j as nat, 0, w2 as nat, k as nat);
            assert((k as nat) * (w2 as nat) == total) by(nonlinear_arith) requires total == w2 * k;
        }
        let base: usize = j * w2;
        proof {
            assert(base + w2 <= total) by(nonlinear_arith) requires base == j * w2, j < k, total == w2 * k;
            assert(mat@[j * w2 + 0] == 0);
        }
        let mut i: usize = 0;
        while i <= n
            invariant
                n == weights.len(), k == levels, 1 <= k <= 62, j < k, i <= n + 1, total == w2 * k, w2 == n + 2,
                w1 == n + 1, n < 0x4000000000000000, base == j * w2, base + w2 <= total,
                pctx == pctx_of(weights@, rej_u as nat, levels as nat), pctx.wf(),
                p as nat == pow2((levels - 1 - j) as nat),
                mat.len() == total,
                mat@[base as int] as nat == pcnt(pctx, (j + 1) as nat, i as nat),
                forall |j2: int| 0 <= j2 < j ==> #[trigger] mat@[j2 * w2] as nat == pcnt(pctx, (j2 + 1) as nat, w1),
                forall |j2: int, d: int| 0 <= j2 < j && 0 <= d < mat@[j2 * w2] ==>
                    #[trigger] mat@[j2 * w2 + 1 + d] as nat == sel(pctx, (j2 + 1) as nat, d as nat, w1),
                forall |j2: int, o: int| j < j2 < k && 0 <= o < w2 ==> #[trigger] mat@[j2 * w2 + o] == 0,
                forall |d: int| 0 <= d < mat@[base as int] ==>
                    #[trigger] mat@[base + 1 + d] as nat == sel(pctx, (j + 1) as nat, d as nat, i as nat),
            decreases n + 1 - i,
        {
            let a_i: u64 = if i < n { weights[i] } else { rej_u };
            proof {
                lemma_pow2_pos((levels - 1 - j) as nat);
                lemma_pcnt_le(pctx, (j + 1) as nat, i as nat);
                assert((levels as nat - (j + 1) as nat) as nat == (levels - 1 - j) as nat);
                assert(ew(pctx, i as nat) == a_i as nat);
                lemma_idx_lt(j as nat, 0, w2 as nat, k as nat);
            }
            if (a_i / p) % 2 == 1 {
                let ghost m0 = mat@;
                let cnt = mat[base] + 1;
                proof { lemma_idx_lt(j as nat, cnt as nat, w2 as nat, k as nat); }
                mat.set(base, cnt);
                mat.set(base + cnt as usize, i as u64);
                proof {
                    assert forall |j2: int| 0 <= j2 < j implies #[trigger] mat@[j2 * w2] as nat == pcnt(pctx, (j2 + 1) as nat, w1) by {
                        if j2 * w2 == base + cnt { lemma_idx_inj(j2 as nat, 0, j as nat, cnt as nat, w2 as nat); }
                        if j2 * w2 == base { lemma_idx_inj(j2 as nat, 0, j as nat, 0, w2 as nat); }
                    }
                    assert forall |j2: int, d: int| 0 <= j2 < j && 0 <= d < mat@[j2 * w2] implies
                        #[trigger] mat@[j2 * w2 + 1 + d] as nat == sel(pctx, (j2 + 1) as nat, d as nat, w1) by {
                        assert(mat@[j2 * w2] == m0[j2 * w2]);
                        lemma_pcnt_le(pctx, (j2 + 1) as nat, w1);
                        if j2 * w2 + 1 + d == base + cnt { lemma_idx_inj(j2 as nat, (1 + d) as nat, j as nat, cnt as nat, w2 as nat); }
                        if j2 * w2 + 1 + d == base { lemma_idx_inj(j2 as nat, (1 + d) as nat, j as nat, 0, w2 as nat); }
                    }
                    assert forall |j2: int, o: int| j < j2 < k && 0 <= o < w2 implies #[trigger] mat@[j2 * w2 + o] == 0 by {
                        if j2 * w2 + o == base + cnt { lemma_idx_inj(j2 as nat, o as nat, j as nat, cnt as nat, w2 as nat); }
                        if j2 * w2 + o == base { lemma_idx_inj(j2 as nat, o as nat, j as nat, 0, w2 as nat); }
                    }
                    assert forall |d: int| 0 <= d < mat@[base as int] implies
                        #[trigger] mat@[base + 1 + d] as nat == sel(pctx, (j + 1) as nat, d as nat, (i + 1) as nat) by {
                        if d + 1 < cnt {
                            assert(mat@[base + 1 + d] == m0[base + 1 + d]);
                        }
                    }
                }
            }
            i = i + 1;
        }
        j = j + 1;
    }
    let tab = FldrFlat { n: n as u64, m, levels, weights, mat };
    proof {
        let t = tab@;
        assert forall |c: nat| 1 <= c <= t.levels implies (#[trigger] (t.h)(c)) == pcnt(pctx, c, (pctx.n + 1) as nat) by {
            let j2 = (c - 1) as int;
            lemma_idx_lt(j2 as nat, 0, w2 as nat, k as nat);
            assert(mat@[j2 * w2] as nat == pcnt(pctx, (j2 + 1) as nat, w1));
        }
        assert forall |c: nat, d: nat| 1 <= c <= t.levels && d < pcnt(pctx, c, (pctx.n + 1) as nat) implies
            (#[trigger] (t.lab)(c, d)) == sel(pctx, c, d, (pctx.n + 1) as nat) by {
            let j2 = (c - 1) as int;
            assert(mat@[j2 * w2] as nat == pcnt(pctx, (j2 + 1) as nat, w1));
            lemma_pcnt_le(pctx, c, w1);
            lemma_idx_lt(j2 as nat, 1 + d, w2 as nat, k as nat);
            assert(mat@[j2 * w2 + 1 + d] as nat == sel(pctx, c, d, w1));
        }
        lemma_view_valid(t, pctx);
        assert forall |j2: int| 0 <= j2 < k implies #[trigger] mat@[j2 * (n as u64 + 2)] <= n + 1 by {
            lemma_pcnt_le(pctx, (j2 + 1) as nat, w1);
            assert(mat@[j2 * w2] as nat == pcnt(pctx, (j2 + 1) as nat, w1));
        }
        lemma_pow2_mono(levels as nat, 62);
        lemma_pow2_62();
    }
    tab
}

// ── The running example (7, 4, 8) in both layouts ────────────────────────────

pub fn sample_748_h(
    Ghost(e): Ghost<spec_fn(nat) -> real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(eps): Ghost<real>,
) -> ((value, out_credit): (u64, Tracked<ErrorCreditResource>))
    requires
        forall |x: nat| (#[trigger] e(x)) >= 0real,
        eps >= (7real * e(0nat) + 4real * e(1nat) + 8real * e(2nat)) / 19real,
        input_credit@ =~= (Value { car: eps }),
    ensures
        value < 3,
        out_credit@@ =~= (Value { car: e(value as nat) }),
{
    let mut w: Vec<u64> = Vec::new();
    w.push(7);
    w.push(4);
    w.push(8);
    proof { reveal_with_fuel(vsum, 4); reveal_with_fuel(fldr_wsum, 4); lemma2_to64(); }
    let tab = fldr_preprocess_h(w, 19, 5);
    sample_fldr(&tab, Ghost(e), Tracked(input_credit), Ghost(eps))
}

pub fn sample_748_flat(
    Ghost(e): Ghost<spec_fn(nat) -> real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(eps): Ghost<real>,
) -> ((value, out_credit): (u64, Tracked<ErrorCreditResource>))
    requires
        forall |x: nat| (#[trigger] e(x)) >= 0real,
        eps >= (7real * e(0nat) + 4real * e(1nat) + 8real * e(2nat)) / 19real,
        input_credit@ =~= (Value { car: eps }),
    ensures
        value < 3,
        out_credit@@ =~= (Value { car: e(value as nat) }),
{
    let mut w: Vec<u64> = Vec::new();
    w.push(7);
    w.push(4);
    w.push(8);
    proof { reveal_with_fuel(vsum, 4); reveal_with_fuel(fldr_wsum, 4); lemma2_to64(); }
    let tab = fldr_preprocess_flat(w, 19, 5);
    sample_fldr(&tab, Ghost(e), Tracked(input_credit), Ghost(eps))
}

} // verus!
