// FLDR — the Fast Loaded Dice Roller: sample outcome i ∈ {0,…,n−1} with probability
// aᵢ/m  (m = Σ aᵢ),  using only fair coin flips.
//
// References:
//   - [AISTATS 20]  https://arxiv.org/abs/2003.03830   (the FLDR paper)
//   - [FM 26]       https://arxiv.org/abs/2509.06410   (verification using distr. inv.)
// Rust implementations: 
//    https://github.com/ryco117/fast_loaded_dice_roller
//    https://github.com/vks/rand/blob/fldr/rand_distr/src/weighted_fldr.rs
//
// Algoirthm:
// Preprocess the integer weights a₀,…,a_{n−1} (total m, K = ⌈log₂ m⌉) into the
// Knuth–Yao DDG (discrete-distribution-generating tree): a binary tree whose leaves
// are labelled by outcomes, plus a reject label `n` carrying weight 2ᴷ − m so the
// total leaf mass is 2ᴷ.  A leaf at depth c has probability 2⁻ᶜ, and the leaves of
// outcome i carry total mass aᵢ/2ᴷ.  The extra `reject` label is the value `n` itself
// (the real outcomes are 0..n−1, so `n` is "none of them"); its leaves hold the slack
// mass 2ᴷ − m that pads the total up to a power of two.
//
// Sampling walks down the tree one coin flip at a time, tracking the current depth `c`
// and the position `d` of the current node.
// At each level the `h[c]` leaves come first (positions 0..h[c]−1) and the internal nodes
// follow (positions ≥ h[c]).  On a real leaf it outputs that leaf's label; on a reject
// leaf (label = `n`) it discards the walk and starts over at the root:
//
//   c ← 0; d ← 0                                    // start at the root (level 0, position 0)
//   loop {
//       b ← flip();  c ← c+1;  d ← 2d + b           // descend one level (left/right child)
//       if d < h[c] {                               // d is one of the h[c] leaves here
//           if lab[c][d] ≠ n { return lab[c][d] }   // real outcome → accept and return it
//           else { d ← 0; c ← 0 }                   // reject (label n) → restart at the root
//       } else { d ← d − h[c] }                     // internal node → renumber and keep going
//   }
// `h[c]` = number of leaves at level c;  `lab[c][d]` = label (an outcome in 0..n−1, or the
// reject label n) of the d-th leaf at level c.
//
// We prove the Expectation-Preservation Rule for the loaded distribution:
//
//            ε ≥ Σ_{i<n} (aᵢ/m)·ℰ(i)
//   ───────────────────────────────────────────────
//   [{ ↯(ε) }] sample_fldr(weights) [{ i. ↯(ℰ(i)) }]
//
//  The credit distributions are similar to `fdr.rs`
//
//  (1) VALUE — the conditional expectation  fldr_f(c,d,k) = E[ℰ(out) | (c,d)] using
//      ≤ k flips (0 if the coins runs out before accepting):
//        fldr_f(c,d,0) = 0
//        fldr_f(c,d,k) = ½·( fldr_g(c+1,2d,k−1) + fldr_g(c+1,2d+1,k−1) )
//        fldr_g(c,d,k) = ℰ(lab[c][d])      if d < h[c], lab[c][d] < n   (accept)
//                      = fldr_f(0,0,k)     if d < h[c], lab[c][d] = n   (reject, restart)
//                      = fldr_f(c,d−h[c],k) if d ≥ h[c]                 (internal, descend)
//      Correctness: fldr_f(0,0,k) ≤ Σ(aᵢ/m)ℰ(i).  Because a reject restarts at the
//      root with *strictly smaller* fuel (every leaf is at depth ≥ 1), this follows
//      by induction on k — no limits — from the DDG leaf-sum identity
//      Σ_{accept leaves} 2⁻ᶜ·ℰ(lab) = Σ(aᵢ/2ᴷ)ℰ(i) and Σ_{reject leaves} 2⁻ᶜ = 1−m/2ᴷ.
//
//  (2) TERMINATION — the failure probability  fldr_fail_f(c,d,k) = 1 − P(accept within
//      k flips)  (independent of ℰ): same shape, accept ↦ 0, k = 0 ↦ 1.  One full
//      root-to-leaf traversal (≤ K flips) rejects with probability ρ = (2ᴷ−m)/2ᴷ < 1,
//      so fldr_fail_f(0,0,jK) ≤ ρʲ → 0.
//
// ── Preprocessing: weights → DDG table ────────────────────────────────────────
// The sampler above is funded by a *validated* table; building and validating that
// table is the second half of the development.
//
// Algorithm.  Pad the weights to a power of two with a reject label n of weight
// aₙ = 2ᴷ − m (K = ⌈log₂ m⌉), so the extended weights a₀,…,aₙ sum to 2ᴷ.  Now read
// the binary expansion of each aℓ:  aℓ/2ᴷ = 0.b₁b₂…bₖ, and label ℓ gets a leaf at
// level c (1 ≤ c ≤ K) exactly when bit (K−c) of aℓ is 1, i.e. b_c = 1.  A leaf at
// level c carries mass 2⁻ᶜ, so label ℓ's leaves sum to Σ_c b_c·2⁻ᶜ = aℓ/2ᴷ — its
// target share.  h[c] is the number of labels present at level c, and lab[c] lists
// them (ascending label order). 
//
// Verification.  At the spec level `built_ddg(pctx)` models the construction from an
// abstract weight context `pctx`:
//  h(c) = pcnt = #labels, lab(c,·) = sel = the present labels in order.  
// `lemma_built_valid` proves that, under `pctx.wf()` (aₙ = 2ᴷ − m, m = Σ aᵢ ≥ 1, every aᵢ < 2ᴷ), 
// `built_ddg(pctx)` satisfies `valid_ddg`.
// Two facts carry it:
//  · Per-label encoding:  w_of_lbl_to_l(ℓ,K) = Σ_c count(c,ℓ)·2^{K−c} = aℓ — exactly the
//    binary reconstruction Σ_c b_c·2^{K−c} = aℓ (lemma_built_wenc / topbits).
//  · The tree is well-formed:  the "filled-cells" identity Σ_c h(c)·2^{K−c} = Σ_ℓ aℓ
//    = 2ᴷ (every base cell covered once) forces the running node count
//    N(c) = 2·(N(c−1) − h(c−1)) to stay ≥ h(c) and hit 0 at level K+1 — so each level
//    has enough nodes for its leaves and the tree closes exactly (lemma_n_filled,
//    lemma_h_le_n, lemma_built_close).
// The executable `fldr_preprocess(weights, m, K)` fills the Vec-backed `h`/`lab`
// level by level — each (label, level) membership test is a `bit` = `pow2_exec`
// division — and `lemma_preprocess_valid` transfers `valid_ddg(built_ddg)` to the table's 
// `view()` through the agreement lemmas, discharging `wf()`.

use vstd::prelude::*;

verus! {
use crate::ub::*;
use crate::rand_primitives::{thin_air, rand_1_u64};
#[cfg(verus_keep_ghost)]
use crate::math::pow::{pow, archimedean_pow};
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse};
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::{pow2, lemma_pow2_pos, lemma_pow2_unfold, lemma_pow2_strictly_increases, lemma_pow2_adds, lemma2_to64};

broadcast use {lemma_pow2_pos, lemma_pow2_unfold, lemma_pow2_strictly_increases};

#[cfg(verus_keep_ghost)]
use crate::fldr_helper::*;

// ── The preprocessed DDG table (spec view) ────────────────────────────────────

/// A preprocessed FLDR table: the Knuth–Yao DDG of a weight vector.  `n` real
/// outcomes 0..n−1; the label `n` means *reject*.  `m = Σ_{i<n} weights(i)` and
/// `levels = K = ⌈log₂ m⌉`.  `h(c)` is the number of leaves at level c (1 ≤ c ≤ K);
/// `lab(c, d)` is the label (in 0..n) of the d-th leaf at level c, for d < h(c).
pub struct Ddg {
    pub n: nat,
    pub weights: spec_fn(nat) -> nat,
    pub m: nat,
    pub levels: nat,
    pub h: spec_fn(nat) -> nat,
    pub lab: spec_fn(nat, nat) -> nat,
}

// ── (1) VALUE: the conditional-expectation approximations ─────────────────────

/// Fuel-bounded conditional expectation  E[ℰ(out) | internal DDG node (c, d)]  using
/// ≤ `k` coin flips — the value the credit carries.  One flip turns the internal
/// node (c, d) into its two children (c+1, 2d) and (c+1, 2d+1), each w.p. ½.
pub open spec fn fldr_f(t: Ddg, e: spec_fn(real) -> real, c: nat, d: nat, k: nat) -> real
    decreases k, 0nat,
{
    if k == 0 {
        0real
    } else {
        (fldr_g(t, e, c + 1, 2 * d, (k - 1) as nat)
            + fldr_g(t, e, c + 1, 2 * d + 1, (k - 1) as nat)) / 2real
    }
}

/// Classify the node (c, d) just reached: a leaf (d < h(c)) is an accept (output its
/// label) or a reject (restart at the root); an internal node (d ≥ h(c)) descends,
/// continuing from relative position d − h(c).
pub open spec fn fldr_g(t: Ddg, e: spec_fn(real) -> real, c: nat, d: nat, k: nat) -> real
    decreases k, 1nat,
{
    if d < (t.h)(c) {
        if (t.lab)(c, d) < t.n {
            e((t.lab)(c, d) as real)                       // accept
        } else {
            fldr_f(t, e, 0, 0, k)                          // reject, restart at root
        }
    } else {
        fldr_f(t, e, c, (d - (t.h)(c)) as nat, k)          // internal, descend
    }
}

// ── Value level-sum machinery (mirrors the fail machinery, with an accept term) ─
// VS(c,j,F) = Σ_{d<j} fldr_g(c,d,F).  Leaf part: accept leaves contribute Σ ℰ(lab)
// (= AC(c,j)), reject leaves contribute RJ(c)·Val_F (Val_F := fldr_f(0,0,F)).

/// Σ_{d<j} fldr_g(t,e,c,d,F).
pub open spec fn fldr_vs(t: Ddg, e: spec_fn(real) -> real, c: nat, j: nat, k: nat) -> real
    decreases j,
{
    if j == 0 { 0real }
    else { fldr_vs(t, e, c, (j - 1) as nat, k) + fldr_g(t, e, c, (j - 1) as nat, k) }
}

/// Σ_{d<j} fldr_f(t,e,c,d,F).
pub open spec fn fldr_vfsum(t: Ddg, e: spec_fn(real) -> real, c: nat, j: nat, k: nat) -> real
    decreases j,
{
    if j == 0 { 0real }
    else { fldr_vfsum(t, e, c, (j - 1) as nat, k) + fldr_f(t, e, c, (j - 1) as nat, k) }
}

/// Σ_{d<j} ( fldr_g(t,e,c,2d,F) + fldr_g(t,e,c,2d+1,F) ).
pub open spec fn fldr_vpairsum(t: Ddg, e: spec_fn(real) -> real, c: nat, j: nat, k: nat) -> real
    decreases j,
{
    if j == 0 { 0real }
    else {
        fldr_vpairsum(t, e, c, (j - 1) as nat, k)
            + fldr_g(t, e, c, (2 * ((j - 1) as nat)) as nat, k)
            + fldr_g(t, e, c, (2 * ((j - 1) as nat) + 1) as nat, k)
    }
}

/// Σ_{d<j, lab(c,d)<n} ℰ(lab(c,d))  — the accept-leaf value sum at level c.
pub open spec fn fldr_ac(t: Ddg, e: spec_fn(real) -> real, c: nat, j: nat) -> real
    decreases j,
{
    if j == 0 {
        0real
    } else {
        fldr_ac(t, e, c, (j - 1) as nat)
            + (if (t.lab)(c, (j - 1) as nat) < t.n { e((t.lab)(c, (j - 1) as nat) as real) } else { 0real })
    }
}

// ── Leaf-sum identity: regroup the accept-leaf value sum AC by label ──────────
// AC(c,j) = Σ_{ℓ<n} count(c,ℓ,j)·ℰ(ℓ).  Proved via the single-level grouping below;
// the double sum over (level, position) is then accumulated by induction on levels.

/// Σ_{ℓ<nn} count(c,ℓ,j)·ℰ(ℓ)  — the per-level accept sum grouped by label.
pub open spec fn fldr_sumlab(t: Ddg, e: spec_fn(real) -> real, c: nat, j: nat, nn: nat) -> real
    decreases nn,
{
    if nn == 0 {
        0real
    } else {
        fldr_sumlab(t, e, c, j, (nn - 1) as nat)
            + (l_lbl_cnt_upto(t, c, (nn - 1) as nat, j) as real) * e((nn - 1) as real)
    }
}

// Accumulate the single-level grouping over levels:  the e-weighted accept encoding
// ewenc(K) = Σ_{c=1}^K AC(c,h(c))·2^{K−c}  equals  Σ_{ℓ<n} weights(ℓ)·ℰ(ℓ).

/// Σ_{c=1}^{cc} AC(c,h(c))·2^{K−c}  — e-weighted accept-leaf encoding over levels 1..cc.
pub open spec fn fldr_ewenc(t: Ddg, e: spec_fn(real) -> real, cc: nat) -> real
    decreases cc,
{
    if cc == 0 {
        0real
    } else {
        fldr_ewenc(t, e, (cc - 1) as nat)
            + fldr_ac(t, e, cc, (t.h)(cc)) * (pow2((t.levels - cc) as nat) as real)
    }
}

/// Σ_{ℓ<nn} wenc(ℓ,cc)·ℰ(ℓ)  — the per-label weight encoding summed over labels.
pub open spec fn fldr_rhs_acc(t: Ddg, e: spec_fn(real) -> real, cc: nat, nn: nat) -> real
    decreases nn,
{
    if nn == 0 {
        0real
    } else {
        fldr_rhs_acc(t, e, cc, (nn - 1) as nat)
            + (w_of_lbl_to_l(t, (nn - 1) as nat, cc) as real) * e((nn - 1) as real)
    }
}

// ── (2) Validity of the preprocessed table + the loaded target ────────────────

/// Σ_{i<j} weights(i)   (nat) — used to pin down m = total weight.
pub open spec fn fldr_wsum_nat(t: Ddg, j: nat) -> nat
    decreases j,
{
    if j == 0 { 0 } else { fldr_wsum_nat(t, (j - 1) as nat) + (t.weights)((j - 1) as nat) }
}

/// Σ_{i<j} weights(i)·ℰ(i)   (real).
pub open spec fn fldr_wsum(t: Ddg, e: spec_fn(real) -> real, j: nat) -> real
    decreases j,
{
    if j == 0 {
        0real
    } else {
        fldr_wsum(t, e, (j - 1) as nat) + (t.weights)((j - 1) as nat) as real * e((j - 1) as real)
    }
}

/// The expectation of `e` (ℰ) over the discrete distribution encoded by the weights,
/// i.e. 𝔼_{i~p}[ℰ(i)] with p_i = aᵢ/m:  Σ_{i<n} (aᵢ/m)·ℰ(i) = (1/m)·Σ_{i<n} aᵢ·ℰ(i).
/// The sampler precondition requires the credit ε to dominate this expectation.
pub open spec fn fldr_exp(t: Ddg, e: spec_fn(real) -> real) -> real {
    fldr_wsum(t, e, t.n) / (t.m as real)
}

/// Number of DDG nodes entering level c:  N(0)=1 (the root), N(c)=2·(N(c−1)−h(c−1)).
/// Leaves at level c−1 are removed; each remaining internal node has two children.
pub open spec fn ddg_nodes(t: Ddg, c: nat) -> nat
    decreases c,
{
    if c == 0 {
        1
    } else {
        2 * ((ddg_nodes(t, (c - 1) as nat) - (t.h)((c - 1) as nat)) as nat)
    }
}

/// #{ d < j : lab(c,d) = lbl }  — leaves of label `lbl` among the first j leaves at level c.
pub open spec fn l_lbl_cnt_upto(t: Ddg, c: nat, lbl: nat, j: nat) -> nat
    decreases j,
{
    if j == 0 {
        0
    } else {
        l_lbl_cnt_upto(t, c, lbl, (j - 1) as nat)
            + (if (t.lab)(c, (j - 1) as nat) == lbl { 1nat } else { 0nat })
    }
}

/// Σ_{c=1}^{l} count(c, lbl)·2^{K−c}  — the weight encoded by label `lbl`'s
/// leaves over levels 1..l  (a leaf at level c covers 2^{K−c} of the 2^K base cells).
pub open spec fn w_of_lbl_to_l(t: Ddg, lbl: nat, l: nat) -> nat
    decreases l,
{
    if l == 0 {
        0
    } else {
        w_of_lbl_to_l(t, lbl, (l - 1) as nat)
            + l_lbl_cnt_upto(t, l, lbl, (t.h)(l)) * pow2((t.levels - l) as nat)
    }
}

/// The table `t` is a well-formed Knuth–Yao DDG for its weight vector:
///  - m = Σ weights ≥ 1
///  - h(0) = 0 (the root, at level 0, is internal);
///  - the tree closes exactly after K = levels levels: N(K+1) = 0;
///  - every level c ∈ 1..K has h(c) ≤ N(c) leaves, each labelled in 0..=n (n = reject);
///  - each real label ℓ's leaves encode its weight:  Σ_c count(c,ℓ)·2^{K−c} = aₗ;
///  - the reject label n encodes the slack 2^K − m.
/// (These are exactly the obligations the preprocessing must discharge.)
pub open spec fn valid_ddg(t: Ddg) -> bool {
    &&& t.m >= 1
    &&& t.m == fldr_wsum_nat(t, t.n)
    &&& (t.h)(0) == 0
    &&& ddg_nodes(t, (t.levels + 1) as nat) == 0
    &&& (forall |c: nat| 1 <= c <= t.levels ==> (t.h)(c) <= #[trigger] ddg_nodes(t, c))
    &&& (forall |c: nat, d: nat| d < (t.h)(c) ==> #[trigger] (t.lab)(c, d) <= t.n)
    &&& (forall |lbl: nat| lbl < t.n ==> #[trigger] w_of_lbl_to_l(t, lbl, t.levels) == (t.weights)(lbl))
    &&& pow2(t.levels) >= t.m
    &&& w_of_lbl_to_l(t, t.n, t.levels) == (pow2(t.levels) - t.m) as nat
}

// credit distribution for termination
pub open spec fn fldr_fail_f(t: Ddg, c: nat, d: nat, k: nat) -> real
    decreases k, 0nat,
{
    if k == 0 {
        1real
    } else {
        (fldr_fail_g(t, c + 1, 2 * d, (k - 1) as nat)
            + fldr_fail_g(t, c + 1, 2 * d + 1, (k - 1) as nat)) / 2real
    }
}

pub open spec fn fldr_fail_g(t: Ddg, c: nat, d: nat, k: nat) -> real
    decreases k, 1nat,
{
    if d < (t.h)(c) {
        if (t.lab)(c, d) < t.n {
            0real                                  // accept → no failure
        } else {
            fldr_fail_f(t, 0, 0, k)                // reject → restart at root
        }
    } else {
        fldr_fail_f(t, c, (d - (t.h)(c)) as nat, k)  // internal, descend
    }
}

// ── Level-sum machinery for the epoch bound (mirrors fdr.rs's FS machinery) ────
// FFS(c,j,k) = Σ_{d<j} fail_g(c,d,k).  The reject leaves of level c contribute
// RJ(c)·Fail_F (Fail_F := fail_f(0,0,k)); the internal nodes recurse to level c+1.
// One level:  FFS(c, N(c), k) = RJ(c)·Fail_F + ½·FFS(c+1, N(c+1), k−1).

/// Σ_{d<j} fldr_fail_g(t,c,d,k).
pub open spec fn fldr_fail_ffs(t: Ddg, c: nat, j: nat, k: nat) -> real
    decreases j,
{
    if j == 0 { 0real }
    else { fldr_fail_ffs(t, c, (j - 1) as nat, k) + fldr_fail_g(t, c, (j - 1) as nat, k) }
}

/// Σ_{d<j} fldr_fail_f(t,c,d,k).
pub open spec fn fldr_fail_fsum(t: Ddg, c: nat, j: nat, k: nat) -> real
    decreases j,
{
    if j == 0 { 0real }
    else { fldr_fail_fsum(t, c, (j - 1) as nat, k) + fldr_fail_f(t, c, (j - 1) as nat, k) }
}

/// Σ_{d<j} ( fldr_fail_g(t,c,2d,k) + fldr_fail_g(t,c,2d+1,k) ).
pub open spec fn fldr_fail_pairsum(t: Ddg, c: nat, j: nat, k: nat) -> real
    decreases j,
{
    if j == 0 { 0real }
    else {
        fldr_fail_pairsum(t, c, (j - 1) as nat, k)
            + fldr_fail_g(t, c, (2 * ((j - 1) as nat)) as nat, k)
            + fldr_fail_g(t, c, (2 * ((j - 1) as nat) + 1) as nat, k)
    }
}

/// Tail reject mass from level c:  TR(c) = Σ_{c'=c}^{K} RJ(c')·2^{−(c'−c)},
/// where RJ(c') = #reject leaves at level c'.  Satisfies TR(c) = RJ(c) + ½·TR(c+1).
pub open spec fn fldr_tr(t: Ddg, c: nat) -> real
    decreases t.levels + 1 - c,
{
    if c > t.levels {
        0real
    } else {
        (l_lbl_cnt_upto(t, c, t.n, (t.h)(c)) as real) + (1real / 2real) * fldr_tr(t, c + 1)
    }
}

/// Accept tail:  atr(c) = Σ_{c'=c}^K AC(c',h(c'))·2^{−(c'−c)} = AC(c,h(c)) + ½·atr(c+1).
pub open spec fn fldr_atr(t: Ddg, e: spec_fn(real) -> real, c: nat) -> real
    decreases t.levels + 1 - c,
{
    if c > t.levels {
        0real
    } else {
        fldr_ac(t, e, c, (t.h)(c)) + (1real / 2real) * fldr_atr(t, e, c + 1)
    }
}

/// Runtime DDG table.  `h[0..=K]` (h[0]=0) are the per-level leaf counts; `lab[c]`
/// holds the h[c] labels at level c; `weights`/`m`/`levels` carry the totals.
pub struct FldrTable {
    pub n: u64,
    pub m: u64,
    pub levels: u64,
    pub weights: Vec<u64>,
    pub h: Vec<u64>,
    pub lab: Vec<Vec<u64>>,
}

impl FldrTable {
    pub open spec fn view(self) -> Ddg {
        Ddg {
            n: self.n as nat,
            weights: |i: nat| if i < self.weights@.len() { self.weights@[i as int] as nat } else { 0nat },
            m: self.m as nat,
            levels: self.levels as nat,
            h: |c: nat| if c < self.h@.len() { self.h@[c as int] as nat } else { 0nat },
            lab: |c: nat, d: nat|
                if c < self.lab@.len() && d < self.lab@[c as int]@.len() {
                    self.lab@[c as int]@[d as int] as nat
                } else {
                    self.n as nat
                },
        }
    }

    pub open spec fn wf(self) -> bool {
        &&& valid_ddg(self.view())
        &&& self.levels >= 1
        &&& pow2(self.levels as nat) <= 4611686018427387904   // 2^62, for u64 overflow safety
        &&& pow2(self.levels as nat) <= usize::MAX as nat     // positions fit usize (Vec indices)
        &&& self.h@.len() == self.levels + 1
        &&& self.lab@.len() == self.levels + 1
        &&& forall|c: int| 0 <= c <= self.levels ==> (#[trigger] self.lab@[c]@.len()) == self.h@[c]
    }
}

/// Executable 2^k, for k ≤ 62 (so the result fits in u64 within the wf bound).
#[verifier::spinoff_prover]
pub fn pow2_exec(k: u64) -> (r: u64)
    requires k <= 62,
    ensures r as nat == pow2(k as nat),
{
    let mut r: u64 = 1;
    let mut i: u64 = 0;
    proof { lemma2_to64(); }                            // pow2(0) == 1
    while i < k
        invariant
            i <= k,
            k <= 62,
            r as nat == pow2(i as nat),
        decreases k - i,
    {
        proof {
            lemma_pow2_62();
            lemma_pow2_mono(i as nat, 61);                  // i ≤ 61 in the body
            assert(pow2(61) * 2 == pow2(62));
            assert(pow2((i + 1) as nat) == 2 * pow2(i as nat));
        }
        r = 2 * r;
        i = i + 1;
    }
    r
}

/// Fast Loaded Dice Roller [AISTATS 2020, Alg. 5] — samples outcome i with 
/// probability aᵢ/m using fair coins; always returns.
/// 
/// The Expectation-Preservation Rule:
///
///   ε ≥ Σ_{i<n} (aᵢ/m)·ℰ(i)
///   ─────────────────────────────────────────────────
///   [{ ↯(ε) }] sample_fldr(tab) [{ i. ↯(ℰ(i)) }]
///
/// `tab` is a well-formed (preprocessed, validated) DDG table.  Correctness is funded
/// by the value credit, almost-sure termination by the failure-probability credit.
pub fn sample_fldr(
    tab: &FldrTable,
    Ghost(e): Ghost<spec_fn(real) -> real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(eps): Ghost<real>,
) -> (ret: (u64, Tracked<ErrorCreditResource>))
    requires
        tab.wf(),
        forall |x: real| (#[trigger] e(x)) >= 0real,
        eps >= fldr_exp(tab.view(), e),
        input_credit.view() =~= (ErrorCreditCarrier::Value { car: eps }),
    ensures
        ret.0 < tab.n,
        ret.1@.view() =~= (ErrorCreditCarrier::Value { car: e(ret.0 as real) }),
{
    let ghost t = tab.view();
    proof { lemma_fldr_exp_nonneg(t, e); }
    let Tracked(slack) = thin_air();
    let ghost s0 = choose |sv: real| sv > 0real && (slack.view() =~= (ErrorCreditCarrier::Value { car: sv }));
    let tracked mut credit = ec_combine(input_credit, slack, eps, s0);   // ↯(eps + s0)
    let ghost mut k: nat;
    proof {
        lemma_fldr_fail_witness(t, s0);
        k = choose |kk: nat| fldr_fail_f(t, 0, 0, kk) < s0;
        lemma_fldr_val_le_target(t, e, k);
        assert(eps + s0 >= fldr_f(t, e, 0, 0, k) + fldr_fail_f(t, 0, 0, k)) by(nonlinear_arith)
            requires
                fldr_f(t, e, 0, 0, k) <= fldr_exp(t, e),
                eps >= fldr_exp(t, e),
                fldr_fail_f(t, 0, 0, k) < s0;
    }
    let ghost mut g_ce = eps + s0;

    let mut c: u64 = 0;
    let mut d: u64 = 0;
    proof {
        assert((t.h)(0) == 0);                       // valid
        assert(ddg_nodes(t, 0) == 1);
    }

    loop
        invariant
            t == tab.view(),
            tab.wf(),
            (c as nat) < tab.levels as nat,
            (d as nat) + (t.h)(c as nat) < ddg_nodes(t, c as nat),
            forall |x: real| (#[trigger] e(x)) >= 0real,
            credit.view() =~= (ErrorCreditCarrier::Value { car: g_ce }),
            g_ce >= fldr_f(t, e, c as nat, d as nat, k) + fldr_fail_f(t, c as nat, d as nat, k),
        decreases k,
    {
        proof {
            if k == 0 {
                ec_contradict(&credit);              // fail_f(c,d,0)=1 ⇒ g_ce ≥ 1, impossible
            }
        }
        let ghost kk0 = k;
        let ghost cn = c as nat;
        let ghost dn = d as nat;
        // coin alloc: b ↦ fldr_g(cn+1, 2d+b, k−1) + fldr_fail_g(cn+1, 2d+b, k−1)
        let ghost alloc = |x: real| {
            let dd: nat = if x == 1real { 2 * dn + 1 } else { 2 * dn };
            fldr_g(t, e, cn + 1, dd, (kk0 - 1) as nat) + fldr_fail_g(t, cn + 1, dd, (kk0 - 1) as nat)
        };
        proof {
            assert forall |i: nat| (#[trigger] alloc(i as real)) >= 0real by {
                lemma_fldr_g_nonneg(t, e, cn + 1, 2 * dn, (kk0 - 1) as nat);
                lemma_fldr_g_nonneg(t, e, cn + 1, 2 * dn + 1, (kk0 - 1) as nat);
                lemma_fldr_fail_g_bounds(t, cn + 1, 2 * dn, (kk0 - 1) as nat);
                lemma_fldr_fail_g_bounds(t, cn + 1, 2 * dn + 1, (kk0 - 1) as nat);
            }
            let ghost fg0 = fldr_g(t, e, cn + 1, 2 * dn, (kk0 - 1) as nat);
            let ghost fg1 = fldr_g(t, e, cn + 1, 2 * dn + 1, (kk0 - 1) as nat);
            let ghost lg0 = fldr_fail_g(t, cn + 1, 2 * dn, (kk0 - 1) as nat);
            let ghost lg1 = fldr_fail_g(t, cn + 1, 2 * dn + 1, (kk0 - 1) as nat);
            assert((alloc(0real) + alloc(1real)) / 2real
                == fldr_f(t, e, cn, dn, kk0) + fldr_fail_f(t, cn, dn, kk0)) by(nonlinear_arith)
                requires
                    alloc(0real) == fg0 + lg0, alloc(1real) == fg1 + lg1,
                    fldr_f(t, e, cn, dn, kk0) == (fg0 + fg1) / 2real,
                    fldr_fail_f(t, cn, dn, kk0) == (lg0 + lg1) / 2real;
        }

        let (b, Tracked(out)) = rand_1_u64(Tracked(credit), Ghost(alloc));
        proof { credit = out; g_ce = alloc(b as real); k = (kk0 - 1) as nat; }

        // overflow safety:  d < N(cn) ≤ 2^cn ≤ 2^levels ≤ 2^62
        proof {
            lemma_ddg_nodes_le_pow2(t, cn);
            lemma_pow2_mono(cn, tab.levels as nat);
        }
        let c1: u64 = c + 1;
        let new_d: u64 = 2 * d + b;

        // basic facts about (c1, new_d) and the view; new_d < N(cn+1)
        proof {
            assert(cn + 1 == c1 as nat);
            assert((c1 as nat) <= tab.levels as nat);
            assert((t.h)(cn + 1) == tab.h@[c1 as int] as nat);
            assert(b == 0 || b == 1);
            assert(alloc(b as real)
                == fldr_g(t, e, cn + 1, new_d as nat, (kk0 - 1) as nat)
                   + fldr_fail_g(t, cn + 1, new_d as nat, (kk0 - 1) as nat));
            assert((t.h)(cn) <= ddg_nodes(t, cn));                            // valid
            assert(ddg_nodes(t, cn + 1) == 2 * ((ddg_nodes(t, cn) - (t.h)(cn)) as nat));
            assert((new_d as nat) < ddg_nodes(t, cn + 1)) by(nonlinear_arith)
                requires
                    (dn as int) + (t.h)(cn) < ddg_nodes(t, cn),
                    (t.h)(cn) <= ddg_nodes(t, cn),
                    ddg_nodes(t, cn + 1) == 2 * ((ddg_nodes(t, cn) - (t.h)(cn)) as nat),
                    new_d == 2 * dn + (b as nat), b <= 1;
            // positions fit usize:  new_d < N(cn+1) ≤ 2^{cn+1} ≤ 2^levels ≤ usize::MAX
            lemma_ddg_nodes_le_pow2(t, (cn + 1) as nat);
            lemma_pow2_mono((cn + 1) as nat, tab.levels as nat);
            lemma_pow2_gt((cn + 1) as nat);                       // c1 = cn+1 < 2^{cn+1} ≤ 2^levels ≤ usize::MAX
            assert((new_d as nat) < usize::MAX as nat);
            assert((c1 as nat) < usize::MAX as nat);
        }

        let hd1: u64 = tab.h[c1 as usize];
        proof {
            assert(hd1 == tab.h@[c1 as int]);
            assert((hd1 as nat) == (t.h)(cn + 1));
        }

        if new_d < hd1 {
            // leaf at (c1, new_d)
            proof {
                assert((new_d as nat) < (t.h)(cn + 1));
                assert(tab.lab@[c1 as int]@.len() == tab.h@[c1 as int]);      // wf
                assert((new_d as nat) < tab.lab@[c1 as int]@.len());
                assert((t.lab)(cn + 1, new_d as nat) == tab.lab@[c1 as int]@[new_d as int] as nat);
            }
            let lab = tab.lab[c1 as usize][new_d as usize];
            proof { assert((t.lab)(cn + 1, new_d as nat) == lab as nat); }
            if lab < tab.n {
                proof {
                    assert((t.lab)(cn + 1, new_d as nat) < t.n);
                    assert(g_ce == e((lab as nat) as real));
                    assert(((lab as nat) as real) == lab as real);
                }
                return (lab, Tracked(credit));
            } else {
                // reject → restart at the root
                proof {
                    assert((t.lab)(cn + 1, new_d as nat) >= t.n);
                    assert(g_ce == fldr_f(t, e, 0, 0, k) + fldr_fail_f(t, 0, 0, k));
                    assert((t.h)(0) == 0);
                    assert(ddg_nodes(t, 0) == 1);
                }
                c = 0;
                d = 0;
            }
        } else {
            // internal → descend to (c1, new_d − h(c1))
            proof {
                assert((new_d as nat) >= (t.h)(cn + 1));
                lemma_ddg_close(t);                                          // N(K) = h(K)
                assert((c1 as nat) < tab.levels as nat) by {
                    if (c1 as nat) == tab.levels as nat {
                        assert(ddg_nodes(t, tab.levels as nat) == (t.h)(tab.levels as nat));
                    }
                }
                assert(g_ce == fldr_f(t, e, cn + 1, ((new_d as nat) - (t.h)(cn + 1)) as nat, k)
                            + fldr_fail_f(t, cn + 1, ((new_d as nat) - (t.h)(cn + 1)) as nat, k));
                assert(((new_d as nat) - (t.h)(cn + 1)) as nat + (t.h)(cn + 1) == new_d as nat);
            }
            d = new_d - hd1;
            c = c1;
            proof {
                assert((d as nat) == ((new_d as nat) - (t.h)(cn + 1)) as nat);
            }
        }
    }
}

// ── Binary reconstruction ──────────────

/// The j-th bit of x.
pub open spec fn bit(x: nat, j: nat) -> nat { (x / pow2(j)) % 2 }

/// Σ_{j<k} bit(x,j)·2^j  — value of the low k bits.
pub open spec fn bitval(x: nat, k: nat) -> nat
    decreases k,
{
    if k == 0 { 0 } else { bitval(x, (k - 1) as nat) + bit(x, (k - 1) as nat) * pow2((k - 1) as nat) }
}

/// Σ_{c'=1}^{c} bit(x, kk−c')·2^{kk−c'}  — the value contributed by the top c bits.
/// (Level c ↔ bit kk−c; this is the FLDR per-label weight encoding's shape.)
pub open spec fn topbits(x: nat, kk: nat, c: nat) -> nat
    decreases c,
{
    if c == 0 {
        0
    } else {
        topbits(x, kk, (c - 1) as nat) + bit(x, (kk - c) as nat) * pow2((kk - c) as nat)
    }
}

// ── The DDG built from a weight vector ────────────────────────────────────────
// Preprocessing context: weights a₀..a_{n−1}, reject weight `rej = 2ᴷ − m` at label n,
// K = `levels`.  At level c the leaves are the labels whose bit (K−c) is set.

pub struct PCtx {
    pub weights: spec_fn(nat) -> nat,
    pub n: nat,
    pub rej: nat,
    pub levels: nat,
}

/// Extended weight: a real outcome's weight, or the reject weight at label n.
pub open spec fn ew(pctx: PCtx, l: nat) -> nat {
    if l < pctx.n { (pctx.weights)(l) } else { pctx.rej }
}

/// Is label l a leaf at level c?  (its bit K−c, ∈ {0,1}).
pub open spec fn pres(pctx: PCtx, c: nat, l: nat) -> nat {
    bit(ew(pctx, l), (pctx.levels - c) as nat)
}

/// #{ l < upto : pres(c,l) = 1 }  — present labels below `upto` at level c.
pub open spec fn pcnt(pctx: PCtx, c: nat, upto: nat) -> nat
    decreases upto,
{
    if upto == 0 { 0 } else { pcnt(pctx, c, (upto - 1) as nat) + pres(pctx, c, (upto - 1) as nat) }
}

/// The present label at count d among {0..upto−1} (sentinel n+1 if none).
pub open spec fn sel(pctx: PCtx, c: nat, d: nat, upto: nat) -> nat
    decreases upto,
{
    if upto == 0 {
        pctx.n + 1
    } else if pres(pctx, c, (upto - 1) as nat) == 1 && pcnt(pctx, c, (upto - 1) as nat) == d {
        (upto - 1) as nat
    } else {
        sel(pctx, c, d, (upto - 1) as nat)
    }
}

/// The DDG built from `pctx`.  The total weight is derived intrinsically by
/// summing the real weights: `m = Σ_{i<n} weights(i) = ewsum(pctx, pctx.n)`.
/// h(c) = #leaves at level c, lab(c,d) = the d-th such leaf's label.
pub open spec fn built_ddg(pctx: PCtx) -> Ddg {
    Ddg {
        n: pctx.n,
        weights: pctx.weights,
        m: ewsum(pctx, pctx.n),
        levels: pctx.levels,
        h: |c: nat| pcnt(pctx, c, (pctx.n + 1) as nat),
        lab: |c: nat, d: nat| sel(pctx, c, d, (pctx.n + 1) as nat),
    }
}

// ── Node-count: the tree closes (N(K+1)=0) and h(c) ≤ N(c) ────────────────────
// Σ_c h(c)·2^{K−c} = Σ_ℓ ew(ℓ) = 2ᴷ.  Proved by the row-sum (over labels) of the
// bit-histogram, accumulated level-by-level (same shape as the leaf-sum identity).

/// Σ_{ℓ<nn} topbits(ew(ℓ), K, c)  — cells covered by levels 1..c, summed over labels < nn.
pub open spec fn rowtop(pctx: PCtx, c: nat, nn: nat) -> nat
    decreases nn,
{
    if nn == 0 { 0 } else { rowtop(pctx, c, (nn - 1) as nat) + topbits(ew(pctx, (nn - 1) as nat), pctx.levels, c) }
}

/// Σ_{j=1}^{c} h(j)·2^{K−j}  — cells covered by leaves at levels 1..c.
pub open spec fn filled(pctx: PCtx, c: nat) -> nat
    decreases c,
{
    if c == 0 {
        0
    } else {
        filled(pctx, (c - 1) as nat) + pcnt(pctx, c, (pctx.n + 1) as nat) * pow2((pctx.levels - c) as nat)
    }
}

/// Σ_{ℓ<nn} ew(ℓ).
pub open spec fn ewsum(pctx: PCtx, nn: nat) -> nat
    decreases nn,
{
    if nn == 0 { 0 } else { ewsum(pctx, (nn - 1) as nat) + ew(pctx, (nn - 1) as nat) }
}

impl PCtx {
    /// Well-formed preprocessing input:  reject = 2ᴷ−m, m = Σ weights ≥ 1, each weight < 2ᴷ.
    /// The total weight `m` is the derived sum `ewsum(self, self.n)` (not a separate input).
    pub open spec fn wf(self) -> bool {
        &&& self.levels >= 1
        &&& self.rej == (pow2(self.levels) - ewsum(self, self.n)) as nat
        &&& pow2(self.levels) >= ewsum(self, self.n)
        &&& ewsum(self, self.n) >= 1
        &&& (forall |l: nat| l < self.n ==> #[trigger] (self.weights)(l) < pow2(self.levels))
    }
}

// ── Executable preprocessing: build the runtime table and discharge wf() ──────

/// Σ_{i<j} s[i]  (nat) — the integer total of a weight Vec, for relating the exec
/// sum to the spec `ewsum`.
pub open spec fn vsum(s: Seq<u64>, j: nat) -> nat
    decreases j,
{
    if j == 0 { 0nat } else { vsum(s, (j - 1) as nat) + s[(j - 1) as int] as nat }
}

// ── FLDR paper, inner loop of PREPROCESS (Alg. 5, lines 7–12) ─────────────────
// For a fixed level / binary digit `j`, scan every label and collect those present
// at that level — i.e. build column `j` of the paper's matrix `H[d][j]`
// (`a_{n+1} = 2^k − m` is the reject weight):
//
//   BUILD_LEVEL(a, k, j):
//       d ← 0                                     // # labels present at level j so far
//       for i ← 1 to n+1:
//           w ← (a_i >> (k−1−j)) & 1               // bit (k−1−j) of a_i
//           if w == 1:
//               H_j[d] ← i;  d ← d + 1            // d-th leaf at level j is label i
//       return H_j                                // h[j] = d = len(H_j)
//
// Differences from the paper:
//   - 0-indexed: outcomes are 0..n−1 and the reject label is `n` (paper: 1..n, reject n+1);
//     the scan runs l = 0..n, reading weight aₗ (or `rej_u` at l = n).
//   - Level `c` here ↔ bit (K−c): c = 1..K ↔ paper digits j = 0..K−1, and c = 0 is an
//     extra (always empty) root row so the array index equals the tree level.
//   - The bit test is a division/modulo  (aₗ / 2^{K−c}) % 2  rather than a shift-and-mask,
//     intentially avoid bit-vector reasoning.
//   - Returns the level's label list as a fresh Vec (the paper writes column `j` of its
//     [n+1]×k matrix `H[d][j]` in place); h[c] is recovered as `labd.len()`.
//   - `Ghost(pctx)`, the loop invariant, and the proof blocks are verification-only.
//
/// Build the labels at level `c`:  the list of labels ℓ ∈ {0,…,n} (n = reject) whose
/// extended weight has bit (K−c) set, in increasing order.  Matches `pcnt`/`sel`.
#[verifier::spinoff_prover]
pub fn build_level(
    weights: &Vec<u64>,
    rej_u: u64,
    levels: u64,
    c: u64,
    Ghost(pctx): Ghost<PCtx>,
) -> (labd: Vec<u64>)
    requires
        c <= levels,
        levels <= 62,
        pctx.levels == levels as nat,
        pctx.n == weights@.len(),
        pctx.rej == rej_u as nat,
        weights@.len() + 1 <= usize::MAX as nat,
        pow2(levels as nat) <= usize::MAX as nat,
        forall |l: int| 0 <= l < pctx.n ==> (pctx.weights)(l as nat) == weights@[l] as nat,
    ensures
        labd@.len() == pcnt(pctx, c as nat, (pctx.n + 1) as nat),
        forall |d: int| 0 <= d < labd@.len() ==>
            labd@[d] as nat == sel(pctx, c as nat, d as nat, (pctx.n + 1) as nat),
{
    let nn: usize = weights.len();
    let pj: u64 = pow2_exec(levels - c);
    proof { lemma_pow2_pos((levels - c) as nat); }       // pj ≥ 1, division is safe

    let mut labd: Vec<u64> = Vec::new();
    let mut l: usize = 0;
    while l <= nn
        invariant
            l <= nn + 1,
            nn + 1 <= usize::MAX as nat,
            nn == pctx.n,
            nn == weights@.len(),
            c <= levels,
            pctx.levels == levels as nat,
            pctx.rej == rej_u as nat,
            pj as nat == pow2((levels - c) as nat),
            pj >= 1,
            forall |ll: int| 0 <= ll < pctx.n ==> (pctx.weights)(ll as nat) == weights@[ll] as nat,
            labd@.len() == pcnt(pctx, c as nat, l as nat),
            forall |d: int| 0 <= d < labd@.len() ==>
                labd@[d] as nat == sel(pctx, c as nat, d as nat, l as nat),
        decreases nn + 1 - l,
    {
        let ewl: u64 = if l < nn { weights[l] } else { rej_u };
        proof {
            assert(ewl as nat == ew(pctx, l as nat));
            // pres(pctx,c,l) = bit(ew, K−c) = (ew / 2^{K−c}) % 2, matched by exec div/mod.
            assert(pres(pctx, c as nat, l as nat)
                == (ew(pctx, l as nat) / pow2((levels - c) as nat)) % 2);
            assert((ewl / pj) as nat == (ewl as nat) / (pj as nat));
            assert((ewl % 2) as nat == (ewl as nat) % 2);
        }
        let present: bool = (ewl / pj) % 2 == 1;
        let ghost ln = l as nat;
        if present {
            proof {
                assert(pres(pctx, c as nat, ln) == 1);
                lemma_sel_at(pctx, c as nat, ln, (ln + 1) as nat);   // sel(c, pcnt(c,l), l+1) = l
                assert forall |d: int| 0 <= d < labd@.len() implies
                    #[trigger] sel(pctx, c as nat, d as nat, (ln + 1) as nat) == sel(pctx, c as nat, d as nat, ln) by {
                    lemma_sel_stable(pctx, c as nat, d as nat, ln);  // d < pcnt(c,l) = labd.len()
                }
            }
            labd.push(l as u64);
        } else {
            proof {
                assert(pres(pctx, c as nat, ln) == 0);
                assert forall |d: int| 0 <= d < labd@.len() implies
                    #[trigger] sel(pctx, c as nat, d as nat, (ln + 1) as nat) == sel(pctx, c as nat, d as nat, ln) by {
                    lemma_sel_stable(pctx, c as nat, d as nat, ln);
                }
            }
        }
        l = l + 1;
    }
    labd
}

// FLDR paper, Alg. 5 (PREPROCESS half, lines 1–12)
//   PREPROCESS(a₁, …, aₙ):
//       k ← ⌈log₂ m⌉                              // m = Σ aᵢ
//       a_{n+1} ← 2^k − m                         // reject mass, pads total to 2^k
//       h ← int[k];  H ← int[n+1][k]              // note: H is indexed [leaf][level]
//       for j ← 0 to k−1:                         // one column per binary digit
//           d ← 0                                 // # labels present at this level so far
//           for i ← 1 to n+1:
//               w ← (aᵢ >> ((k−1)−j)) & 1         // bit ((k−1)−j) of aᵢ
//               h[j] ← h[j] + w                   // count leaves at level j
//               if w == 1:
//                   H[d][j] ← i;  d ← d + 1       // d-th leaf at level j is label i
//       return (h, H, k)
//
// Differences from the paper:
//   - `levels` (= k) is an input with well-formedness precondition
//      computing ⌈log₂⌉ is the caller's responsibility
//   - 0-indexed outcomes 0..n−1, reject label = `n` (rather than: 1..n, reject = n+1).
//   - Builds K+1 rows c = 0..K (row 0 is the empty root level, so the array index equals
//     the tree level c); the paper builds k columns j = 0..k−1 for bits k−1..0.
//   - The table is TRANSPOSED: we store `lab[c][d]` (level-major: a Vec per level, each
//     listing that level's leaf labels), whereas the paper stores `H[d][j]` (leaf-major).
//     So our `lab[c]` is column j=c of the paper's H; `h[c]` is recovered as `lab[c].len()`.
//   - Each level's list is produced by `build_level` returning a Vec (paper fills H in place).
//   - a_{n+1} = 2^k − m is `rej_u = pow2_exec(levels) − m` (same formula).
//   - `levels ≤ 62` keeps 2^levels within u64; the ghost `pctx`, the proof blocks, and
//     `lemma_built_valid`/`wf()` are verification-only (no paper analogue).
//
/// build the validated FLDR table from a weight vector.
/// The caller supplies the total `m = Σ weights` and `levels = K = ⌈log₂ m⌉`
/// (with their well-formedness obligations); this builds the per-level leaf counts
/// and label lists and discharges `wf()` — so the result feeds straight into
/// `sample_fldr`.  Correctness rests on the spec-level `lemma_built_valid`.
#[verifier::spinoff_prover]
pub fn fldr_preprocess(weights: Vec<u64>, m: u64, levels: u64) -> (tab: FldrTable)
    requires
        levels >= 1,
        levels <= 62,
        pow2(levels as nat) <= usize::MAX as nat,
        m >= 1,
        m as nat <= pow2(levels as nat),
        m as nat == vsum(weights@, weights@.len() as nat),
        weights@.len() + 1 <= usize::MAX as nat,
        forall |i: int| 0 <= i < weights@.len() ==> (weights@[i] as nat) < pow2(levels as nat),
    ensures
        tab.wf(),
        tab.n as nat == weights@.len(),
        tab.m == m,
        tab.levels == levels,
        tab.weights@ == weights@,
{
    let rej_u: u64 = pow2_exec(levels) - m;                  // 2ᴷ − m ≥ 0 (m ≤ 2ᴷ)

    // The abstract preprocessing context — its weight function IS the table view's.
    let ghost wfun = |i: nat| if i < weights@.len() { weights@[i as int] as nat } else { 0nat };
    let ghost pctx = PCtx {
        weights: wfun,
        n: weights@.len() as nat,
        rej: rej_u as nat,
        levels: levels as nat,
    };

    // pctx.wf(): the obligations of well-formed preprocessing input.
    proof {
        assert(pctx.rej == (pow2(pctx.levels) - (m as nat)) as nat);
        lemma_ewsum_eq_vsum(pctx, weights@, pctx.n);               // ewsum(pctx,n) = vsum = m
        assert(ewsum(pctx, pctx.n) == m as nat);
        assert(pctx.wf());
        lemma_built_valid(pctx);                      // valid_ddg(built_ddg(pctx))
    }

    let mut h: Vec<u64> = Vec::new();
    let mut lab: Vec<Vec<u64>> = Vec::new();
    let mut c: u64 = 0;
    while c <= levels
        invariant
            c <= levels + 1,
            levels <= 62,
            pctx.levels == levels as nat,
            pctx.n == weights@.len(),
            pctx.rej == rej_u as nat,
            weights@.len() + 1 <= usize::MAX as nat,
            pow2(levels as nat) <= usize::MAX as nat,
            forall |i: int| 0 <= i < pctx.n ==> (pctx.weights)(i as nat) == weights@[i] as nat,
            h@.len() == c as nat,
            lab@.len() == c as nat,
            forall |cc: int| 0 <= cc < c ==> #[trigger] h@[cc] as nat == pcnt(pctx, cc as nat, (pctx.n + 1) as nat),
            forall |cc: int| 0 <= cc < c ==> #[trigger] lab@[cc]@.len() == h@[cc],
            forall |cc: int, d: int| 0 <= cc < c && 0 <= d < lab@[cc]@.len() ==>
                #[trigger] lab@[cc]@[d] as nat == sel(pctx, cc as nat, d as nat, (pctx.n + 1) as nat),
        decreases levels + 1 - c,
    {
        let labd: Vec<u64> = build_level(&weights, rej_u, levels, c, Ghost(pctx));
        let hd: u64 = labd.len() as u64;
        proof { assert(hd as nat == labd@.len()); }
        h.push(hd);
        lab.push(labd);
        c = c + 1;
    }

    let n_u: u64 = weights.len() as u64;
    let tab = FldrTable { n: n_u, m, levels, weights, h, lab };

    proof {
        let ghost t = tab.view();
        let ghost bt = built_ddg(pctx);
        // The view and the built DDG share scalar fields and weight function …
        assert(t.n == bt.n && t.m == bt.m && t.levels == bt.levels);
        assert(t.weights == bt.weights);
        // … and agree on h(c) for 0 ≤ c ≤ K and lab(c,d) for d < h(c), c ≤ K.
        assert forall |cc: nat| cc <= levels as nat implies (#[trigger] (t.h)(cc)) == (bt.h)(cc) by {
            assert((t.h)(cc) == tab.h@[cc as int] as nat);   // cc < h.len() = K+1
            assert(tab.h@[cc as int] as nat == pcnt(pctx, cc, (pctx.n + 1) as nat));
        }
        assert forall |cc: nat| cc > levels as nat implies (#[trigger] (t.h)(cc)) == 0nat by {
            assert(tab.h@.len() == levels as nat + 1);       // cc ≥ K+1 = h.len() ⇒ view = 0
        }
        assert forall |cc: nat, d: nat| cc <= levels as nat && d < (bt.h)(cc)
            implies (#[trigger] (t.lab)(cc, d)) == (bt.lab)(cc, d) by {
            assert((bt.h)(cc) == pcnt(pctx, cc, (pctx.n + 1) as nat));
            assert((t.h)(cc) == tab.h@[cc as int] as nat);
            assert(tab.h@[cc as int] as nat == pcnt(pctx, cc, (pctx.n + 1) as nat));
            assert(d < tab.lab@[cc as int]@.len());          // len = h[cc] = pcnt
            assert((t.lab)(cc, d) == tab.lab@[cc as int]@[d as int] as nat);
            assert(tab.lab@[cc as int]@[d as int] as nat == sel(pctx, cc, d, (pctx.n + 1) as nat));
        }
        // Transfer valid_ddg from bt (lemma_built_valid) to t via the agreement lemmas.
        lemma_built_valid(pctx);
        lemma_preprocess_valid(t, bt);

        // remaining wf() conjuncts
        lemma_pow2_mono(levels as nat, 62);
        lemma_pow2_62();                                     // pow2(levels) ≤ 2^62
        assert forall |cc: int| 0 <= cc <= levels implies
            (#[trigger] tab.lab@[cc]@.len()) == tab.h@[cc] by {}
    }
    tab
}

#[verifier::spinoff_prover]
pub fn run_fldr_zero() -> (ret: u64)
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
    let (r, _) = sample_748(Ghost(e), Tracked(credit), Ghost(eps));
    r
}

#[verifier::spinoff_prover]
pub fn example_fldr() -> (ret: u64)
    ensures ret < 3,
{
    run_fldr_zero()
}

/// Derive the finite spec from general FLDR spec
#[verifier::spinoff_prover]
pub fn sample_748(
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
    w.push(7);
    w.push(4);
    w.push(8);
    proof { reveal_with_fuel(vsum, 4); reveal_with_fuel(fldr_wsum, 4); lemma2_to64(); }
    let tab = fldr_preprocess(w, 19, 5);
    sample_fldr(&tab, Ghost(e), Tracked(input_credit), Ghost(eps))
}

} // verus!

