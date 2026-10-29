//! The samplers of Section 5 for M / Z_kl, 0 ≤ l ≤ k (Algorithm 8 and its
//! cached variant):
//!
//! ```text
//!   Σ_r M_r = Z_kl        ε ≥ Σ_r (M_r / Z_kl)·ℰ(r)        ℰ ≥ 0
//!   -------------------------------------------------------------
//!   [{ ↯(ε) }] sample_ky_matrix(P, k, l) [{ r. ↯(ℰ(r)) }]
//! ```
//!
//! Each is `walk::sample` on a layout of the tree: [`MatrixWalk`] scans
//! column c of P, [`CachedWalk`] reads h and T, `Encoded` walks the packed
//! array. Labels are 0-based (the original returns r + 1).

use vstd::prelude::*;

verus! {

use crate::ec::*;
#[cfg(verus_keep_ghost)]
use crate::ec::ErrorCreditCarrier::Value;
use crate::ddg_walk::walk;
use crate::ddg_walk::walk::{DdgWalk, Step};
use crate::ddg_walk::encoding::Encoded;
use crate::optas::tree::OptasSpec;
#[cfg(verus_keep_ghost)]
use crate::ddg_walk::walk::{DdgSpec, LDdg, lnum, next_depth, is_internal, child};
#[cfg(verus_keep_ghost)]
use crate::optas::tree::{optas_ddg, optas_lab, optas_point, lemma_optas_point, lemma_optas_valid, lemma_optas_lab, lemma_optas_lab_unique};
#[cfg(verus_keep_ghost)]
use crate::fldr::bit;
#[cfg(verus_keep_ghost)]
use crate::optas::ztype::*;
#[cfg(verus_keep_ghost)]
use crate::optas::matrix::*;
#[cfg(verus_keep_ghost)]
use crate::optas::utils::{zkl, wf_kl, proper_kl, frac_int, frac_x, frac_y, lemma_zkl};
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::{pow2, lemma_pow2_pos, lemma2_to64};

/// The input of the samplers: P is the matrix of M / Z_kl, and M is proper.
pub open spec fn sampler_input(p: Seq<Vec<u8>>, ms: Seq<u128>, k: nat, l: nat) -> bool {
    &&& wf_kl(ms, k, l)
    &&& proper_kl(ms, k, l)
    &&& is_matrix(p, ms, k, l)
    &&& ms.len() < 0x4000000000000000
}

// ── Lemmas ────────────────────────────────────────────────────────────────────

/// In the degenerate case (k, l) = (1, 0), P[r][0] = M_r ∈ {0, 1}.
pub proof fn lemma_degenerate_bit(p: Seq<Vec<u8>>, ms: Seq<u128>, r: nat)
    requires sampler_input(p, ms, 1, 0), r < ms.len(),
    ensures ms[r as int] <= 1, p[r as int]@[0] as nat == ms[r as int] as nat,
{
    lemma2_to64();
    assert(zkl(1, 0) == 1);
    lemma_w_le_sum(ms, 0, r);
    let m = ms[r as int] as nat;
    assert(frac_x(m, 1, 0) == 0 && frac_y(m, 1, 0) == m);
    assert(frac_int(m, 1, 0) == m);
    assert(bit(m, 0) == m % 2);
}

/// Column c of P, read at the true level j (whose residues agree with c's).
pub proof fn lemma_col_level(p: Seq<Vec<u8>>, ms: Seq<u128>, k: nat, l: nat, c: nat, j: nat, r: nat)
    requires
        sampler_input(p, ms, k, l), !(k == 1 && l == 0), c < k, r < ms.len(),
        ddg_rho(ms, zkl(k, l), j, r) == ddg_rho(ms, zkl(k, l), c, r),
    ensures p[r as int]@[c as int] as nat == ddg_bit(ms, zkl(k, l), j + 1, r),
{
    lemma_zkl(k, l);
    lemma_mat_bit_ddg(ms, k, l, r, c);
    lemma_ddg_bit_agree(ms, zkl(k, l), j + 1, c + 1, r);
}

pub proof fn lemma_col_pre_level(p: Seq<Vec<u8>>, ms: Seq<u128>, k: nat, l: nat, c: nat, j: nat, r: nat)
    requires
        sampler_input(p, ms, k, l), !(k == 1 && l == 0), c < k, r <= ms.len(),
        forall |r2: nat| r2 < ms.len() ==> #[trigger] ddg_rho(ms, zkl(k, l), j, r2) == ddg_rho(ms, zkl(k, l), c, r2),
    ensures col_pre(p, c, r) == ddg_pre(ms, zkl(k, l), j + 1, r),
    decreases r,
{
    if r > 0 {
        lemma_col_pre_level(p, ms, k, l, c, j, (r - 1) as nat);
        lemma_col_level(p, ms, k, l, c, j, (r - 1) as nat);
    }
}

/// Leaf number d < pre(n) of level j exists.
pub proof fn lemma_pre_witness(w: Seq<u128>, z: nat, j: nat, n: nat, d: nat) -> (r: nat)
    requires z > 0, n <= w.len(), d < ddg_pre(w, z, j, n),
    ensures r < n, ddg_bit(w, z, j, r) == 1, ddg_pre(w, z, j, r) == d,
    decreases n,
{
    let n1 = (n - 1) as nat;
    if j > 0 { lemma_ddg_step(w, z, (j - 1) as nat, n1); } else {
        assert(ddg_bit(w, z, j, n1) <= 1);
    }
    if d < ddg_pre(w, z, j, n1) {
        lemma_pre_witness(w, z, j, n1, d)
    } else {
        n1
    }
}

/// After the residues of the true level j agree with those of column c,
/// so do those of the next level and column (through the back-edge).
pub proof fn lemma_next_column(ms: Seq<u128>, k: nat, l: nat, j: nat, c: nat)
    requires
        0 < k, l <= k, c < k,
        forall |r: nat| r < ms.len() ==> #[trigger] ddg_rho(ms, zkl(k, l), j, r) == ddg_rho(ms, zkl(k, l), c, r),
    ensures
        forall |r: nat| r < ms.len() ==> #[trigger] ddg_rho(ms, zkl(k, l), j + 1, r) == ddg_rho(ms, zkl(k, l), c + 1, r),
        c + 1 == k && l < k ==>
            forall |r: nat| r < ms.len() ==> #[trigger] ddg_rho(ms, zkl(k, l), j + 1, r) == ddg_rho(ms, zkl(k, l), l, r),
        c + 1 == k && l == k ==>
            forall |r: nat| r < ms.len() ==> #[trigger] ddg_rho(ms, zkl(k, l), j + 1, r) == 0,
{
    lemma_zkl(k, l);
    let z = zkl(k, l);
    assert forall |r: nat| r < ms.len() implies #[trigger] ddg_rho(ms, z, j + 1, r) == ddg_rho(ms, z, c + 1, r) by {
        lemma_ddg_step(ms, z, j, r);
        lemma_ddg_step(ms, z, c, r);
    }
    if c + 1 == k && l < k {
        assert forall |r: nat| r < ms.len() implies #[trigger] ddg_rho(ms, z, j + 1, r) == ddg_rho(ms, z, l, r) by {
            lemma_ddg_step(ms, z, j, r);
            lemma_ddg_step(ms, z, c, r);
            lemma_ddg_wrap(ms, k, l, r);
        }
    }
    if c + 1 == k && l == k {
        assert forall |r: nat| r < ms.len() implies #[trigger] ddg_rho(ms, z, j + 1, r) == 0 by {
            lemma_ddg_step(ms, z, j, r);
            lemma_ddg_step(ms, z, c, r);
            lemma_ddg_rho_pow2(ms, k, k, r);
        }
    }
}

/// The root is internal and worth ddg_f(0, 0, f).
pub proof fn lemma_root_internal(ms: Seq<u128>, k: nat, l: nat, e: spec_fn(nat) -> real, f: nat)
    requires wf_kl(ms, k, l), proper_kl(ms, k, l), !(k == 1 && l == 0),
    ensures
        ddg_num_internal(ms, zkl(k, l), 0) == 1,
        ddg_g(ms, zkl(k, l), e, 0, 0, 0, f) == ddg_f(ms, zkl(k, l), e, 0, 0, f),
{
    lemma_zkl(k, l);
    let z = zkl(k, l);
    lemma_h0_zero(ms, k, l, 0);
    lemma_ddg_shape(ms, z, 0);
    lemma_ddg_g_internal(ms, z, e, 0, 0, 0, f);
}

pub proof fn lemma_h0_zero(ms: Seq<u128>, k: nat, l: nat, r: nat)
    requires wf_kl(ms, k, l), proper_kl(ms, k, l), !(k == 1 && l == 0), r <= ms.len(),
    ensures ddg_h(ms, zkl(k, l), 0, r) == 0,
    decreases ms.len() - r,
{
    if r < ms.len() {
        lemma_h0_zero(ms, k, l, r + 1);
        lemma_zkl(k, l);
        lemma2_to64();
        let m = ms[r as int] as nat;
        assert(pow2(0) == 1) by { lemma2_to64(); }
        assert(pow2(0) * m == m);
        assert(m < zkl(k, l));
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(m as int, zkl(k, l) as int, 0, m as int);
        assert(m / zkl(k, l) == 0);
    }
}

/// Initial credit: ↯(ε + s₀) covers the root with fuel f.
pub proof fn lemma_root_bound(ms: Seq<u128>, k: nat, l: nat, e: spec_fn(nat) -> real, eps: real, s0: real, f: nat)
    requires
        wf_kl(ms, k, l), proper_kl(ms, k, l), !(k == 1 && l == 0),
        forall |i: nat| (#[trigger] e(i)) >= 0real,
        eps >= ddg_exp(ms, zkl(k, l), e),
        l < k ==> s0 > 0real && (ms.len() as real) / (pow2(f) as real) < s0,
        l == k ==> s0 == 0real && f == k,
    ensures
        0real <= ddg_f(ms, zkl(k, l), e, 0, 0, f) <= eps + s0,
{
    lemma_zkl(k, l);
    let z = zkl(k, l);
    lemma_root_internal(ms, k, l, e, f);
    lemma_ddg_val_le_target(ms, z, e, f);
    lemma_ddg_f_nonneg(ms, z, e, 0, 0, f);
    if l == k {
        assert forall |r: nat| r < ms.len() implies #[trigger] ddg_rho(ms, z, f, r) == 0 by {
            lemma_ddg_rho_pow2(ms, k, f, r);
        }
        lemma_ddg_internal_zero(ms, z, f);
        lemma_pow2_pos(f);
        assert((0int as real) / (pow2(f) as real) == 0real);
    }
}

// ── The matrix layouts ────────────────────────────────────────────────────────

/// In the degenerate case (k, l) = (1, 0), the label with M_r = 1: the one
/// row with P[r][0] = 1 (`if len(P) == 1: return 1`).
pub fn degenerate_label(p: &Vec<Vec<u8>>, Ghost(ms): Ghost<Seq<u128>>) -> (r: usize)
    requires sampler_input(p@, ms, 1, 0),
    ensures r as nat == optas_point(ms), r < p.len(),
{
    let n = p.len();
    proof { lemma_optas_point(ms, |i: nat| 0real); }
    let mut r: usize = 0;
    while r < n
        invariant n == p.len() == ms.len(), sampler_input(p@, ms, 1, 0), r <= optas_point(ms) < n,
            ms[optas_point(ms) as int] == 1,
            forall |i: int| 0 <= i < ms.len() && i != optas_point(ms) ==> #[trigger] ms[i] == 0,
        decreases n - r,
    {
        proof { lemma_degenerate_bit(p@, ms, r as nat); lemma_degenerate_bit(p@, ms, optas_point(ms)); }
        if p[r][0] == 1 {
            return r;
        }
        r = r + 1;
    }
    r
}

/// The column of a position c < k: the next one is c + 1,
/// or l after k − 1.
fn next_column(c: u64, k: u64, l: u64) -> (r: u64)
    requires c < k,
    ensures r as nat == if c + 1 == k { l as nat } else { c as nat + 1 },
{
    if c == k - 1 { l } else { c + 1 }
}

/// Facts about the internal node (c, d) of the tree of M / Z_kl.
proof fn lemma_internal_pos(ms: Seq<u128>, k: nat, l: nat, c: nat, d: nat)
    requires
        wf_kl(ms, k, l), proper_kl(ms, k, l), !(k == 1 && l == 0),
        is_internal(optas_ddg(ms, k, l), c, d),
    ensures
        zkl(k, l) > 0, c < k, d < ms.len(),
        (optas_ddg(ms, k, l).h)(c + 1) == ddg_h(ms, zkl(k, l), c + 1, 0),
        forall |x: nat| x < (optas_ddg(ms, k, l).h)(c + 1) ==> (#[trigger] (optas_ddg(ms, k, l).lab)(c + 1, x)) < ms.len(),
        (optas_ddg(ms, k, l).h)(c + 1) < 2 * d + 2 ==>
            next_depth(optas_ddg(ms, k, l), c + 1) == if c + 1 == k { l } else { c + 1 },
{
    let t = optas_ddg(ms, k, l);
    lemma_zkl(k, l);
    lemma_optas_valid(ms, k, l);
    lemma_ddg_shape(ms, zkl(k, l), c);
    if (t.h)(c + 1) < 2 * d + 2 && c + 1 == k && l == k {
        assert(lnum(t, c + 1) == 2 * lnum(t, c) - (t.h)(c + 1) as int);
    }
}

/// The leaf x < h of depth j ≥ 1 is the row r with a one there and x ones
/// above it.
proof fn lemma_leaf_label(ms: Seq<u128>, z: nat, j: nat, x: nat, r: nat)
    requires z > 0, j >= 1, r < ms.len(), ddg_bit(ms, z, j, r) == 1, ddg_pre(ms, z, j, r) == x,
    ensures x < ddg_h(ms, z, j, 0), optas_lab(ms, z, j, x) == r,
{
    lemma_ddg_pre_h(ms, z, j, ms.len() as nat);
    lemma_ddg_pre_mono(ms, z, j, r, ms.len() as nat);
    if r + 1 < ms.len() { lemma_ddg_pre_mono(ms, z, j, r + 1, ms.len() as nat); }
    lemma_ddg_pre_h(ms, z, j, (r + 1) as nat);
    lemma_ddg_pre_h(ms, z, j, r);
    lemma_optas_lab(ms, z, j, x);
    lemma_optas_lab_unique(ms, z, j, r, optas_lab(ms, z, j, x));
}

/// The matrix P of M / Z_kl, walked as in `sample_ky_matrix`: the position
/// is (column c, internal node d), and the leaves below column c are the
/// ones in it, found by scanning P.
pub struct MatrixWalk<'a> {
    pub p: &'a Vec<Vec<u8>>,
    pub k: u64,
    pub l: u64,
    pub ms: Ghost<Seq<u128>>,
}

impl<'a> DdgWalk for MatrixWalk<'a> {
    type Spec = OptasSpec;
    type Pos = (u64, u64);

    open spec fn wf(&self) -> bool { sampler_input(self.p@, self.ms@, self.k as nat, self.l as nat) }

    open spec fn spec(&self) -> OptasSpec { OptasSpec { ms: self.ms@, k: self.k as nat, l: self.l as nat } }

    proof fn lemma_wf(&self) {}

    open spec fn pos(&self, q: (u64, u64)) -> (nat, nat) { (q.0 as nat, q.1 as nat) }

    open spec fn valid_pos(&self, q: (u64, u64)) -> bool { true }

    open spec fn swap(&self) -> bool { true }

    fn is_exact(&self) -> (r: bool) { self.l == self.k }

    fn root(&self) -> (r: Step<(u64, u64)>) {
        if self.k == 1 && self.l == 0 {
            Step::Done(degenerate_label(self.p, self.ms) as u64)
        } else {
            Step::Next((0, 0))
        }
    }

    /// `d = 2*d + (1 - b)`, then `for r in range(N): d = d - P[r][c]; if d == -1: return r`.
    fn step(&self, q: (u64, u64), b: u64) -> (res: Step<(u64, u64)>) {
        let ghost ms = self.ms@;
        let ghost (kn, ln) = (self.k as nat, self.l as nat);
        let ghost z = zkl(kn, ln);
        let c = q.0;
        let d = q.1;
        proof {
            lemma_internal_pos(ms, kn, ln, c as nat, d as nat);
            lemma_is_matrix_bits(self.p@, ms, kn, ln);
        }
        let x = 2 * d + (1 - b);
        proof { assert(x as nat == child(d as nat, b as nat, true)); }
        let n = self.p.len();
        let mut r: usize = 0;
        let mut y: u64 = x;
        while r < n
            invariant
                n == self.p.len() == ms.len(), r <= n, c < self.k, self.wf(), ms == self.ms@, z == zkl(kn, ln), z > 0,
                kn == self.k, ln == self.l, !(kn == 1 && ln == 0),
                x as nat == y as nat + ddg_pre(ms, z, c as nat + 1, r as nat),
                x as nat == child(d as nat, b as nat, true), c == q.0, d == q.1, b <= 1,
            decreases n - r,
        {
            proof {
                lemma_col_level(self.p@, ms, kn, ln, c as nat, c as nat, r as nat);
                lemma_ddg_pre_mono(ms, z, c as nat + 1, r as nat, (r + 1) as nat);
                assert(self.p@[r as int].len() == kn);
            }
            if self.p[r][c as usize] == 1 {
                if y == 0 {
                    proof {
                        lemma_leaf_label(ms, z, c as nat + 1, x as nat, r as nat);
                        assert((self.spec().ddg().lab)(c as nat + 1, x as nat) == optas_lab(ms, z, c as nat + 1, x as nat));
                    }
                    return Step::Done(r as u64);
                }
                y = y - 1;
            }
            r = r + 1;
        }
        proof {
            lemma_ddg_pre_h(ms, z, c as nat + 1, n as nat);
            assert(ddg_h(ms, z, c as nat + 1, n as nat) == 0);
        }
        Step::Next((next_column(c, self.k, self.l), y))
    }
}

/// The cached tables of `sample_ky_matrix_cached`: h[c] counts the leaves
/// below column c and T[x][c] is the label of leaf x.
pub struct CachedWalk<'a> {
    pub k: u64,
    pub l: u64,
    pub h: &'a Vec<u64>,
    pub t: &'a Vec<Vec<i64>>,
    pub p: Ghost<Seq<Vec<u8>>>,
    pub ms: Ghost<Seq<u128>>,
}

impl<'a> DdgWalk for CachedWalk<'a> {
    type Spec = OptasSpec;
    type Pos = (u64, u64);

    open spec fn wf(&self) -> bool {
        let (p, k) = (self.p@, self.k as nat);
        &&& sampler_input(p, self.ms@, k, self.l as nat)
        &&& self.h.len() == k
        &&& forall |c: int| 0 <= c < k ==> (#[trigger] self.h@[c]) as nat == col_pre(p, c as nat, p.len() as nat)
        &&& is_hamming_matrix(self.t@, p, k)
    }

    open spec fn spec(&self) -> OptasSpec { OptasSpec { ms: self.ms@, k: self.k as nat, l: self.l as nat } }

    proof fn lemma_wf(&self) {}

    open spec fn pos(&self, q: (u64, u64)) -> (nat, nat) { (q.0 as nat, q.1 as nat) }

    open spec fn valid_pos(&self, q: (u64, u64)) -> bool { true }

    open spec fn swap(&self) -> bool { true }

    fn is_exact(&self) -> (r: bool) { self.l == self.k }

    /// `if len(T) == 1: return 1`: T[0][0] is the label with M_r = 1.
    fn root(&self) -> (r: Step<(u64, u64)>) {
        if self.k == 1 && self.l == 0 {
            let ghost (p, ms) = (self.p@, self.ms@);
            let ghost r0 = optas_point(ms);
            proof {
                lemma_optas_point(ms, |i: nat| 0real);
                lemma_degenerate_bit(p, ms, r0);
                lemma_col0_zero(p, ms, r0);
                assert(self.t@[0].len() == 1);
            }
            Step::Done(self.t[0][0] as u64)
        } else {
            Step::Next((0, 0))
        }
    }

    /// `d = 2*d + (1 - b); if d < h[c]: return T[d][c]`.
    fn step(&self, q: (u64, u64), b: u64) -> (res: Step<(u64, u64)>) {
        let ghost (p, ms) = (self.p@, self.ms@);
        let ghost (kn, ln) = (self.k as nat, self.l as nat);
        let ghost z = zkl(kn, ln);
        let ghost n = ms.len();
        let c = q.0;
        let d = q.1;
        proof {
            lemma_internal_pos(ms, kn, ln, c as nat, d as nat);
            lemma_is_matrix_bits(p, ms, kn, ln);
            assert forall |r2: nat| r2 < n implies #[trigger] ddg_rho(ms, z, c as nat, r2) == ddg_rho(ms, z, c as nat, r2) by {}
            lemma_col_pre_level(p, ms, kn, ln, c as nat, c as nat, n);
            lemma_ddg_pre_h(ms, z, c as nat + 1, n);
        }
        let x = 2 * d + (1 - b);
        proof { assert(x as nat == child(d as nat, b as nat, true)); }
        let hc = self.h[c as usize];
        proof {
            assert(hc as nat == col_pre(p, c as nat, n));
            assert(hc as nat == (self.spec().ddg().h)(c as nat + 1));
        }
        if x < hc {
            let ghost r0 = lemma_pre_witness(ms, z, c as nat + 1, n, x as nat);
            proof {
                lemma_col_pre_level(p, ms, kn, ln, c as nat, c as nat, r0);
                lemma_col_level(p, ms, kn, ln, c as nat, c as nat, r0);
                lemma_col_pre_le(p, kn, c as nat, n);
                lemma_leaf_label(ms, z, c as nat + 1, x as nat, r0);
                assert(self.t@[x as int].len() == kn);
                assert(self.t@[x as int]@[c as int] == r0 as i64);
                assert((self.spec().ddg().lab)(c as nat + 1, x as nat) == optas_lab(ms, z, c as nat + 1, x as nat));
                assert(r0 < n < 0x4000000000000000);
                assert(x < self.t.len());
            }
            let v = self.t[x as usize][c as usize];
            proof { assert(v == r0 as i64); assert((v as u64) as nat == r0); }
            Step::Done(v as u64)
        } else {
            Step::Next((next_column(c, self.k, self.l), x - hc))
        }
    }
}

/// In the degenerate case, column 0 has no one above the label.
proof fn lemma_col0_zero(p: Seq<Vec<u8>>, ms: Seq<u128>, r0: nat)
    requires sampler_input(p, ms, 1, 0), r0 < ms.len(),
        forall |i: int| 0 <= i < ms.len() && i != r0 ==> #[trigger] ms[i] == 0,
    ensures col_pre(p, 0, r0) == 0,
    decreases r0,
{
    if r0 > 0 {
        lemma_col0_zero_prefix(p, ms, r0, (r0 - 1) as nat);
    }
}

proof fn lemma_col0_zero_prefix(p: Seq<Vec<u8>>, ms: Seq<u128>, r0: nat, r: nat)
    requires sampler_input(p, ms, 1, 0), r < r0 < ms.len(),
        forall |i: int| 0 <= i < ms.len() && i != r0 ==> #[trigger] ms[i] == 0,
    ensures col_pre(p, 0, r + 1) == 0,
    decreases r,
{
    if r > 0 { lemma_col0_zero_prefix(p, ms, r0, (r - 1) as nat); }
    lemma_degenerate_bit(p, ms, r);
    assert(ms[r as int] == 0);
    assert(col_pre(p, 0, r + 1) == col_pre(p, 0, r) + p[r as int]@[0] as nat);
}

// ── The samplers ──────────────────────────────────────────────────────────────

/// `sample_ky_matrix(P, k, l)` (Algorithm 8): `walk::sample` on `MatrixWalk`.
pub fn sample_ky_matrix(
    p: &Vec<Vec<u8>>,
    k: u64,
    l: u64,
    Ghost(ms): Ghost<Seq<u128>>,
    Ghost(e): Ghost<spec_fn(nat) -> real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(eps): Ghost<real>,
) -> ((value, out_credit): (usize, Tracked<ErrorCreditResource>))
    requires
        sampler_input(p@, ms, k as nat, l as nat),
        forall |i: nat| (#[trigger] e(i)) >= 0real,
        eps >= ddg_exp(ms, zkl(k as nat, l as nat), e),
        input_credit@ =~= (Value { car: eps }),
    ensures
        value < p.len(),
        out_credit@@ =~= (Value { car: e(value as nat) }),
{
    let w = MatrixWalk { p, k, l, ms: Ghost(ms) };
    let (v, out) = walk::sample(&w, Ghost(e), Tracked(input_credit), Ghost(eps));
    proof { assert(w.spec().ddg().n == ms.len()); }
    (v as usize, out)
}

/// `sample_ky_matrix_cached(k, l, h, T)`: the same walk, with the leaves of
/// column c counted by h[c] and labeled by T[·][c] instead of scanning P.
pub fn sample_ky_matrix_cached(
    k: u64,
    l: u64,
    h: &Vec<u64>,
    t: &Vec<Vec<i64>>,
    Ghost(p): Ghost<Seq<Vec<u8>>>,
    Ghost(ms): Ghost<Seq<u128>>,
    Ghost(e): Ghost<spec_fn(nat) -> real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(eps): Ghost<real>,
) -> ((value, out_credit): (usize, Tracked<ErrorCreditResource>))
    requires
        sampler_input(p, ms, k as nat, l as nat),
        h.len() == k,
        forall |c: int| 0 <= c < k ==> (#[trigger] h@[c]) as nat == col_pre(p, c as nat, p.len() as nat),
        is_hamming_matrix(t@, p, k as nat),
        forall |i: nat| (#[trigger] e(i)) >= 0real,
        eps >= ddg_exp(ms, zkl(k as nat, l as nat), e),
        input_credit@ =~= (Value { car: eps }),
    ensures
        value < ms.len(),
        out_credit@@ =~= (Value { car: e(value as nat) }),
{
    let w = CachedWalk { k, l, h, t, p: Ghost(p), ms: Ghost(ms) };
    let (v, out) = walk::sample(&w, Ghost(e), Tracked(input_credit), Ghost(eps));
    proof { assert(w.spec().ddg().n == ms.len()); assert(ms.len() == t.len()); }
    (v as usize, out)
}

/// `sample_ky_encoding(enc)`: `walk::sample` on the packed tree.
pub fn sample_ky_encoding(
    enc: &Encoded<OptasSpec>,
    Ghost(e): Ghost<spec_fn(nat) -> real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(eps): Ghost<real>,
) -> ((value, out_credit): (u64, Tracked<ErrorCreditResource>))
    requires
        enc.wf(),
        forall |i: nat| (#[trigger] e(i)) >= 0real,
        eps >= ddg_exp(enc.spec@.ms, zkl(enc.spec@.k, enc.spec@.l), e),
        input_credit@ =~= (Value { car: eps }),
    ensures
        (value as nat) < enc.spec@.ms.len(),
        out_credit@@ =~= (Value { car: e(value as nat) }),
{
    walk::sample(enc, Ghost(e), Tracked(input_credit), Ghost(eps))
}

} // verus!
