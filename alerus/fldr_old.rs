//! FLDR — the Fast Loaded Dice Roller: sample outcome i ∈ {0,…,n−1} with probability
//! aᵢ/m  (m = Σ aᵢ),  using only fair coin flips.
//!
//! References:
//!   - [AISTATS 20](https://arxiv.org/abs/2003.03830)
//!   - [FM 26](https://arxiv.org/abs/2509.06410)
//! 
//! Rust implementations: 
//!   - https://github.com/ryco117/fast_loaded_dice_roller
//!   - https://github.com/vks/rand/blob/fldr/rand_distr/src/weighted_fldr.rs
//!
//! Algoirthm:
//! Preprocess the integer weights a₀,…,a_{n−1} (total m, K = ⌈log₂ m⌉) into the
//! Knuth–Yao DDG (discrete-distribution-generating tree): a binary tree whose leaves
//! are labelled by outcomes, plus a reject label `n` carrying weight 2ᴷ − m so the
//! total leaf mass is 2ᴷ.  A leaf at depth c has probability 2⁻ᶜ, and the leaves of
//! outcome i carry total mass aᵢ/2ᴷ.  The extra `reject` label is the value `n` itself
//! (the real outcomes are 0..n−1, so `n` is "none of them"); its leaves hold the slack
//! mass 2ᴷ − m that pads the total up to a power of two.
//!
//! Sampling walks down the tree one coin flip at a time, tracking the current depth `c`
//! and the position `d` of the current node.
//! At each level the `h[c]` leaves come first (positions 0..h[c]−1) and the internal nodes
//! follow (positions ≥ h[c]).  On a real leaf it outputs that leaf's label; on a reject
//! leaf (label = `n`) it discards the walk and starts over at the root:
//!
//! ```text
//!   c ← 0; d ← 0                                    // start at the root (level 0, position 0)
//!   loop {
//!       b ← flip();  c ← c+1;  d ← 2d + b           // descend one level (left/right child)
//!       if d < h[c] {                               // d is one of the h[c] leaves here
//!           if lab[c][d] ≠ n { return lab[c][d] }   // real outcome → accept and return it
//!           else { d ← 0; c ← 0 }                   // reject (label n) → restart at the root
//!       } else { d ← d − h[c] }                     // internal node → renumber and keep going
//!   }
//! ```
//! `h[c]` = number of leaves at level c;  `lab[c][d]` = label (an outcome in 0..n−1, or the
//! reject label n) of the d-th leaf at level c.
//!
//! We prove the Expectation-Preservation Rule for the loaded distribution:
//!
//! ```text
//!            ε ≥ Σ_{i<n} (aᵢ/m)·ℰ(i)
//!   ───────────────────────────────────────────────
//!   [{ ↯(ε) }] sample_fldr(weights) [{ i. ↯(ℰ(i)) }]
//! ```
//!
//!  The credit distributions are similar to `fdr.rs`
//!
//!  (1) VALUE — the conditional expectation  fldr_f(c,d,k) = E[ℰ(out) | (c,d)] using
//!      ≤ k flips (0 if the coins runs out before accepting):
//! ```text
//!        fldr_f(c,d,0) = 0
//!        fldr_f(c,d,k) = ½·( fldr_g(c+1,2d,k−1) + fldr_g(c+1,2d+1,k−1) )
//!        fldr_g(c,d,k) = ℰ(lab[c][d])      if d < h[c], lab[c][d] < n   (accept)
//!                      = fldr_f(0,0,k)     if d < h[c], lab[c][d] = n   (reject, restart)
//!                      = fldr_f(c,d−h[c],k) if d ≥ h[c]                 (internal, descend)
//! ```
//!      Correctness: fldr_f(0,0,k) ≤ Σ(aᵢ/m)ℰ(i).  Because a reject restarts at the
//!      root with *strictly smaller* fuel (every leaf is at depth ≥ 1), this follows
//!      by induction on k — no limits — from the DDG leaf-sum identity
//!      Σ_{accept leaves} 2⁻ᶜ·ℰ(lab) = Σ(aᵢ/2ᴷ)ℰ(i) and Σ_{reject leaves} 2⁻ᶜ = 1−m/2ᴷ.
//!
//!  (2) TERMINATION — the failure probability  fldr_fail_f(c,d,k) = 1 − P(accept within
//!      k flips)  (independent of ℰ): same shape, accept ↦ 0, k = 0 ↦ 1.  One full
//!      root-to-leaf traversal (≤ K flips) rejects with probability ρ = (2ᴷ−m)/2ᴷ < 1,
//!      so fldr_fail_f(0,0,jK) ≤ ρʲ → 0.
//!
//! ── Preprocessing: weights → DDG table ────────────────────────────────────────
//! The sampler above is funded by a *validated* table; building and validating that
//! table is the second half of the development.
//!
//! Algorithm.  Pad the weights to a power of two with a reject label n of weight
//! aₙ = 2ᴷ − m (K = ⌈log₂ m⌉), so the extended weights a₀,…,aₙ sum to 2ᴷ.  Now read
//! the binary expansion of each aℓ:  aℓ/2ᴷ = 0.b₁b₂…bₖ, and label ℓ gets a leaf at
//! level c (1 ≤ c ≤ K) exactly when bit (K−c) of aℓ is 1, i.e. b_c = 1.  A leaf at
//! level c carries mass 2⁻ᶜ, so label ℓ's leaves sum to Σ_c b_c·2⁻ᶜ = aℓ/2ᴷ — its
//! target share.  h[c] is the number of labels present at level c, and lab[c] lists
//! them (ascending label order). 
//!
//! Verification.  At the spec level `built_ddg(pctx)` models the construction from an
//! abstract weight context `pctx`:
//!  h(c) = pcnt = #labels, lab(c,·) = sel = the present labels in order.  
//! `lemma_built_valid` proves that, under `pctx.wf()` (aₙ = 2ᴷ − m, m = Σ aᵢ ≥ 1, every aᵢ < 2ᴷ), 
//! `built_ddg(pctx)` satisfies `valid_ddg`.
//! Two facts carry it:
//!  · Per-label encoding:  w_of_lbl_to_l(ℓ,K) = Σ_c count(c,ℓ)·2^{K−c} = aℓ — exactly the
//!    binary reconstruction Σ_c b_c·2^{K−c} = aℓ (lemma_built_wenc / topbits).
//!  · The tree is well-formed:  the "filled-cells" identity Σ_c h(c)·2^{K−c} = Σ_ℓ aℓ
//!    = 2ᴷ (every base cell covered once) forces the running node count
//!    N(c) = 2·(N(c−1) − h(c−1)) to stay ≥ h(c) and hit 0 at level K+1 — so each level
//!    has enough nodes for its leaves and the tree closes exactly (lemma_n_filled,
//!    lemma_h_le_n, lemma_built_close).
//! The executable `fldr_preprocess(weights, m, K)` fills the Vec-backed `h`/`lab`
//! level by level — each (label, level) membership test is a `bit` = `pow2_exec`
//! division — and `lemma_preprocess_valid` transfers `valid_ddg(built_ddg)` to the table's 
//! `view()` through the agreement lemmas, discharging `wf()`.

use vstd::prelude::*;

verus! {
use crate::ec::*;
#[cfg(verus_keep_ghost)]
use crate::ec::ErrorCreditCarrier::Value;
use crate::rand_primitives::{thin_air, rand_2_u64};
#[cfg(verus_keep_ghost)]
use crate::math::pow::{pow, archimedean_pow};
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse};
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::{pow2, lemma_pow2_pos, lemma_pow2_unfold, lemma_pow2_strictly_increases, lemma_pow2_adds, lemma2_to64};

broadcast use {lemma_pow2_pos, lemma_pow2_unfold, lemma_pow2_strictly_increases};

#[cfg(verus_keep_ghost)]
use crate::fldr_helper::*;
use crate::fldr::*;

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
        &&& valid_ddg(self@)
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
    Ghost(e): Ghost<spec_fn(nat) -> real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(eps): Ghost<real>,
) -> ((value, out_credit): (u64, Tracked<ErrorCreditResource>))
    requires
        tab.wf(),
        forall |x: nat| (#[trigger] e(x)) >= 0real,
        eps >= fldr_exp(tab@, e),
        input_credit@ =~= (Value { car: eps }),
    ensures
        value < tab.n,
        out_credit@@ =~= (Value { car: e(value as nat) }),
{
    let ghost t = tab@;
    proof { lemma_fldr_exp_nonneg(t, e); }       // ⇒ eps ≥ 0, for ec_combine below
    let Tracked(slack) = thin_air();
    let ghost s0 = choose |sv: real| sv > 0real && (slack@ =~= (Value { car: sv }));
    let tracked mut credit = ec_combine(input_credit, slack, eps, s0);   // ↯(eps + s0)
    let ghost mut k: nat;
    proof {
        lemma_fldr_fail_witness(t, s0);
        k = choose |k: nat| fldr_fail_f(t, 0, 0, k) < s0;
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

    loop
        invariant
            t == tab@,
            tab.wf(),
            (c as nat) < tab.levels as nat,
            (d as nat) + (t.h)(c as nat) < num_nodes(t, c as nat),
            forall |x: nat| (#[trigger] e(x)) >= 0real,
            credit@ =~= (Value { car: g_ce }),
            g_ce >= fldr_f(t, e, c as nat, d as nat, k) + fldr_fail_f(t, c as nat, d as nat, k),
        decreases k,
    {
        proof {
            if k == 0 {
                ec_contradict(&credit);              // fail_f(c,d,0)=1 ⇒ g_ce ≥ 1, impossible
            }
        }
        let ghost k0 = k;
        let ghost cn = c as nat;
        let ghost dn = d as nat;
        // coin alloc: b ↦ fldr_g(cn+1, 2d+b, k−1) + fldr_fail_g(cn+1, 2d+b, k−1)
        let ghost alloc = |x: nat| {
            let d1: nat = if x == 1 { 2 * dn + 1 } else { 2 * dn };
            fldr_g(t, e, cn + 1, d1, (k0 - 1) as nat) + fldr_fail_g(t, cn + 1, d1, (k0 - 1) as nat)
        };
        proof {
            assert forall |i: nat| (#[trigger] alloc(i)) >= 0real by {
                lemma_fldr_g_nonneg(t, e, cn + 1, 2 * dn, (k0 - 1) as nat);
                lemma_fldr_g_nonneg(t, e, cn + 1, 2 * dn + 1, (k0 - 1) as nat);
                lemma_fldr_fail_g_bounds(t, cn + 1, 2 * dn, (k0 - 1) as nat);
                lemma_fldr_fail_g_bounds(t, cn + 1, 2 * dn + 1, (k0 - 1) as nat);
            }
            let ghost fg0 = fldr_g(t, e, cn + 1, 2 * dn, (k0 - 1) as nat);
            let ghost fg1 = fldr_g(t, e, cn + 1, 2 * dn + 1, (k0 - 1) as nat);
            let ghost lg0 = fldr_fail_g(t, cn + 1, 2 * dn, (k0 - 1) as nat);
            let ghost lg1 = fldr_fail_g(t, cn + 1, 2 * dn + 1, (k0 - 1) as nat);
            assert((alloc(0) + alloc(1)) / 2real
                == fldr_f(t, e, cn, dn, k0) + fldr_fail_f(t, cn, dn, k0)) by(nonlinear_arith)
                requires
                    alloc(0) == fg0 + lg0, alloc(1) == fg1 + lg1,
                    fldr_f(t, e, cn, dn, k0) == (fg0 + fg1) / 2real,
                    fldr_fail_f(t, cn, dn, k0) == (lg0 + lg1) / 2real;
        }

        let (b, Tracked(out)) = rand_2_u64(Tracked(credit), Ghost(alloc));
        proof { credit = out; g_ce = alloc(b as nat); k = (k0 - 1) as nat; }

        // descend one level:  c ← c+1,  d ← 2d + b.  (2d can't overflow:
        // d < N(cn) ≤ 2^cn ≤ 2^levels ≤ 2^62.)
        proof {
            lemma_num_nodes_le_pow2(t, cn);
            lemma_pow2_mono(cn, tab.levels as nat);
        }
        c = c + 1;
        d = 2 * d + b;

        // g_ce now tracks the child node (c, d); d < N(c) keeps the loop invariant,
        // and N(c) ≤ 2^c ≤ 2^levels ≤ usize::MAX makes the Vec indices below safe.
        proof {
            assert(alloc(b as nat)
                == fldr_g(t, e, cn + 1, d as nat, k)
                   + fldr_fail_g(t, cn + 1, d as nat, k));
            assert((d as nat) < num_nodes(t, cn + 1)) by(nonlinear_arith)
                requires
                    (dn as int) + (t.h)(cn) < num_nodes(t, cn),
                    (t.h)(cn) <= num_nodes(t, cn),
                    num_nodes(t, cn + 1) == 2 * ((num_nodes(t, cn) - (t.h)(cn)) as nat),
                    d == 2 * dn + (b as nat), b <= 1;
            lemma_num_nodes_le_pow2(t, (cn + 1) as nat);
            lemma_pow2_mono((cn + 1) as nat, tab.levels as nat);
            lemma_pow2_gt((cn + 1) as nat);
        }

        let hc: u64 = tab.h[c as usize];

        if d < hc {
            // leaf at (c, d):  lab[c][d] is the label reached
            let lab = tab.lab[c as usize][d as usize];
            if lab < tab.n {
                proof { assert(g_ce == e(lab as nat)); }   // accept: fldr_g = ℰ(lab)
                return (lab, Tracked(credit));
            } else {
                // reject → restart at the root
                proof { assert(g_ce == fldr_f(t, e, 0, 0, k) + fldr_fail_f(t, 0, 0, k)); }
                c = 0;
                d = 0;
            }
        } else {
            // internal → renumber within the level:  d ← d − h(c)
            proof {
                lemma_ddg_close(t);                                  // N(K) = h(K) ⇒ c < levels
                assert((c as nat) < tab.levels as nat) by {
                    if (c as nat) == tab.levels as nat {
                        assert(num_nodes(t, tab.levels as nat) == (t.h)(tab.levels as nat));
                    }
                }
                assert(g_ce == fldr_f(t, e, cn + 1, ((d as nat) - (t.h)(cn + 1)) as nat, k)
                            + fldr_fail_f(t, cn + 1, ((d as nat) - (t.h)(cn + 1)) as nat, k));
            }
            d = d - hc;
        }
    }
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
    j: u64,
    Ghost(pctx): Ghost<PCtx>,
) -> (labd: Vec<u64>)
    requires
        j <= levels,
        levels <= 62,
        pctx.levels == levels as nat,
        pctx.n == weights@.len(),
        pctx.rej == rej_u as nat,
        weights@.len() + 1 <= usize::MAX as nat,
        pow2(levels as nat) <= usize::MAX as nat,
        forall |l: int| 0 <= l < pctx.n ==> (pctx.weights)(l as nat) == weights@[l] as nat,
    ensures
        labd@.len() == pcnt(pctx, j as nat, (pctx.n + 1) as nat),
        forall |d: int| 0 <= d < labd@.len() ==>
            labd@[d] as nat == sel(pctx, j as nat, d as nat, (pctx.n + 1) as nat),
{
    let n: usize = weights.len();
    let p_j: u64 = pow2_exec(levels - j);                 // p_j ≥ 1 (broadcast lemma_pow2_pos)

    let mut labd: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    while i <= n
        invariant
            i <= n + 1,
            n + 1 <= usize::MAX as nat,
            n == pctx.n,
            n == weights@.len(),
            pctx.levels == levels as nat,
            pctx.rej == rej_u as nat,
            p_j as nat == pow2((levels - j) as nat),
            forall |l: int| 0 <= l < pctx.n ==> (pctx.weights)(l as nat) == weights@[l] as nat,
            labd@.len() == pcnt(pctx, j as nat, i as nat),
            forall |d: int| 0 <= d < labd@.len() ==>
                labd@[d] as nat == sel(pctx, j as nat, d as nat, i as nat),
        decreases n + 1 - i,
    {
        let a_i: u64 = if i < n { weights[i] } else { rej_u };   // aᵢ  (reject weight at i = n)
        let w: bool = (a_i / p_j) % 2 == 1;                        // bit (K−j) of aᵢ
        if w {
            labd.push(i as u64);
        }
        i = i + 1;
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
    proof { lemma_ewsum_eq_vsum(pctx, weights@, pctx.n); }   // ewsum(pctx,n) = vsum = m ⇒ pctx.wf()

    // Paper Alg. 5 outer loop:  one column `j` per level (0..K); `build_level` fills it.
    let mut h: Vec<u64> = Vec::new();
    let mut lab: Vec<Vec<u64>> = Vec::new();
    let mut j: u64 = 0;
    while j <= levels
        invariant
            j <= levels + 1,
            levels <= 62,
            pctx.levels == levels as nat,
            pctx.n == weights@.len(),
            pctx.rej == rej_u as nat,
            weights@.len() + 1 <= usize::MAX as nat,
            pow2(levels as nat) <= usize::MAX as nat,
            forall |i: int| 0 <= i < pctx.n ==> (pctx.weights)(i as nat) == weights@[i] as nat,
            h@.len() == j as nat,
            lab@.len() == j as nat,
            forall |c: int| 0 <= c < j ==> #[trigger] h@[c] as nat == pcnt(pctx, c as nat, (pctx.n + 1) as nat),
            forall |c: int| 0 <= c < j ==> #[trigger] lab@[c]@.len() == h@[c],
            forall |c: int, d: int| 0 <= c < j && 0 <= d < lab@[c]@.len() ==>
                #[trigger] lab@[c]@[d] as nat == sel(pctx, c as nat, d as nat, (pctx.n + 1) as nat),
        decreases levels + 1 - j,
    {
        let labd: Vec<u64> = build_level(&weights, rej_u, levels, j, Ghost(pctx));
        h.push(labd.len() as u64);
        lab.push(labd);
        j = j + 1;
    }

    let n_u: u64 = weights.len() as u64;
    let tab = FldrTable { n: n_u, m, levels, weights, h, lab };

    proof {
        let ghost t = tab@;
        let ghost bt = built_ddg(pctx);
        // The view and the built DDG share scalar fields/weights, and agree on h(j) for
        // 0 ≤ j ≤ K and lab(j,d) for d < h(j), j ≤ K.
        assert forall |c: nat| c <= levels as nat implies (#[trigger] (t.h)(c)) == (bt.h)(c) by {}
        assert forall |c: nat| c > levels as nat implies (#[trigger] (t.h)(c)) == 0nat by {}
        assert forall |c: nat, d: nat| c <= levels as nat && d < (bt.h)(c)
            implies (#[trigger] (t.lab)(c, d)) == (bt.lab)(c, d) by {}
        // Transfer valid_ddg from bt (lemma_built_valid) to t via the agreement lemmas.
        lemma_built_valid(pctx);
        lemma_preprocess_valid(t, bt);
        lemma_pow2_mono(levels as nat, 62);
        lemma_pow2_62();                                     // pow2(levels) ≤ 2^62 (wf conjunct)
    }
    tab
}

#[verifier::spinoff_prover]
pub fn run_fldr_zero() -> (ret: u64)
    ensures ret < 3,
{
    let ghost e = |x: nat| 0real;
    let Tracked(credit) = thin_air();
    let ghost eps = choose |sv: real|
        sv > 0real && (credit@ =~= (Value { car: sv }));
    proof {
        assert((7real * e(0nat) + 4real * e(1nat) + 8real * e(2nat)) / 19real == 0real)
            by(nonlinear_arith)
            requires e(0nat) == 0real, e(1nat) == 0real, e(2nat) == 0real;
        assert(eps >= (7real * e(0nat) + 4real * e(1nat) + 8real * e(2nat)) / 19real);  // eps > 0 ≥ 0
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
    let tab = fldr_preprocess(w, 19, 5);
    sample_fldr(&tab, Ghost(e), Tracked(input_credit), Ghost(eps))
}

} // verus!

