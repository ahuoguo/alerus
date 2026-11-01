//! The probability matrix P of a Z_kl-type distribution
//! (Algorithm 4) and the cached tables h, T of `sample_ky_matrix_cached`.
//!
//! P[r][c] is bit c+1 of the concise binary expansion of M_r / Z_kl
//! (`frac_to_bits`), i.e. label r has a leaf at level c+1 of the DDG tree.
//! The point mass (k = 1, l = 0, Z_kl = 1) is the exception: there
//! P[r][0] = M_r, the integer part.
//! `lemma_mat_bit_ddg` connects it to the tree semantics of `ztype.rs`.

use vstd::prelude::*;

verus! {

#[cfg(verus_keep_ghost)]
use crate::fldr::bit;
#[cfg(verus_keep_ghost)]
use crate::optas::ztype::*;
use crate::optas::utils::{frac_to_bits, reduce_fractions};
#[cfg(verus_keep_ghost)]
use crate::optas::utils::{zkl, frac_bit, frac_int, wf_kl, proper_kl, same_dist,
    lemma_zkl, lemma_frac_int_floor};

// ── The matrix ────────────────────────────────────────────────────────────────

/// P[r][c] = `frac_to_bits(M_r, k, l)[c]`.
pub open spec fn mat_bit(ms: Seq<u128>, k: nat, l: nat, r: nat, c: nat) -> nat {
    frac_bit(ms[r as int] as nat, k, l, c)
}

/// `p` is the n × k probability matrix of M / Z_kl.
pub open spec fn is_matrix(p: Seq<Vec<u8>>, ms: Seq<u128>, k: nat, l: nat) -> bool {
    &&& p.len() == ms.len()
    &&& forall |r: int| 0 <= r < p.len() ==> (#[trigger] p[r]).len() == k
    &&& forall |r: int, c: int| 0 <= r < p.len() && 0 <= c < k ==>
        (#[trigger] p[r]@[c]) as nat == mat_bit(ms, k, l, r as nat, c as nat)
}

/// For a proper (non-degenerate) M, column c of P is level c+1 of the DDG tree.
pub proof fn lemma_mat_bit_ddg(ms: Seq<u128>, k: nat, l: nat, r: nat, c: nat)
    requires wf_kl(ms, k, l), proper_kl(ms, k, l), !(k == 1 && l == 0), r < ms.len(), c < k,
    ensures mat_bit(ms, k, l, r, c) == ddg_bit(ms, zkl(k, l), c + 1, r),
{
    lemma_zkl(k, l);
    let m = ms[r as int] as nat;
    lemma_frac_int_floor(m, k, l);
    assert(frac_int(m, k, l) == ddg_fl(ms, zkl(k, l), k, r));
    lemma_ddg_row_bit(ms, zkl(k, l), k, c + 1, r);
    assert((k - (c + 1)) as nat == (k - 1 - c) as nat);
}

/// `make_matrix(Ms, k, l)` (Algorithm 4): one `frac_to_bits` row per label.
pub fn make_matrix(ms: &Vec<u128>, k: u64, l: u64) -> (p: Vec<Vec<u8>>)
    requires wf_kl(ms@, k as nat, l as nat), proper_kl(ms@, k as nat, l as nat),
    ensures is_matrix(p@, ms@, k as nat, l as nat),
{
    let mut p: Vec<Vec<u8>> = Vec::new();
    let mut r: usize = 0;
    while r < ms.len()
        invariant
            wf_kl(ms@, k as nat, l as nat), proper_kl(ms@, k as nat, l as nat),
            r <= ms.len(), p.len() == r,
            forall |i: int| 0 <= i < r ==> (#[trigger] p@[i]).len() == k,
            forall |i: int, c: int| 0 <= i < r && 0 <= c < k ==>
                (#[trigger] p@[i]@[c]) as nat == mat_bit(ms@, k as nat, l as nat, i as nat, c as nat),
        decreases ms.len() - r,
    {
        proof {
            lemma_zkl(k as nat, l as nat);
            lemma_w_le_sum(ms@, 0, r as nat);
            assert(ms@[r as int] < zkl(k as nat, l as nat) || (k == 1 && l == 0));
            if k == 1 && l == 0 {
                vstd::arithmetic::power2::lemma2_to64();
                assert(zkl(1, 0) == 1);
            }
        }
        let row = frac_to_bits(ms[r], k, l);
        p.push(row);
        r = r + 1;
    }
    p
}

/// `make_ddg_matrix(Ms, k, l)`: reduce M / Z_kl to lowest terms, then build
/// P. Also returns the reduced weights (ghost). The original returns `[[1]]`
/// when the reduced distribution is degenerate, which loses which label has
/// probability 1; here the degenerate case keeps all n rows (k = 1, l = 0,
/// and the one row with M_r = 1 reads [1]).
pub fn make_ddg_matrix(ms: &Vec<u128>, k: u64, l: u64) -> (r: (Vec<Vec<u8>>, u64, u64, Ghost<Seq<u128>>))
    requires wf_kl(ms@, k as nat, l as nat),
    ensures
        wf_kl(r.3@, r.1 as nat, r.2 as nat),
        proper_kl(r.3@, r.1 as nat, r.2 as nat),
        same_dist(ms@, zkl(k as nat, l as nat), r.3@, zkl(r.1 as nat, r.2 as nat)),
        is_matrix(r.0@, r.3@, r.1 as nat, r.2 as nat),
        r.1 <= k,
{
    let (ms2, k2, l2) = reduce_fractions(ms, k, l);
    let p = make_matrix(&ms2, k2, l2);
    (p, k2, l2, Ghost(ms2@))
}

// ── Hamming vector and matrix ─────────────────────────────────────────────────

/// Σ_{r' < r} P[r'][c]: the ones in column c above row r.
pub open spec fn col_pre(p: Seq<Vec<u8>>, c: nat, r: nat) -> nat
    decreases r,
{
    if r == 0 { 0 } else { col_pre(p, c, (r - 1) as nat) + p[(r - 1) as int]@[c as int] as nat }
}

/// A 0/1 matrix with n rows of length k.
pub open spec fn is_bits(p: Seq<Vec<u8>>, k: nat) -> bool {
    &&& forall |r: int| 0 <= r < p.len() ==> (#[trigger] p[r]).len() == k
    &&& forall |r: int, c: int| 0 <= r < p.len() && 0 <= c < k ==> (#[trigger] p[r]@[c]) <= 1
}

pub proof fn lemma_is_matrix_bits(p: Seq<Vec<u8>>, ms: Seq<u128>, k: nat, l: nat)
    requires is_matrix(p, ms, k, l),
    ensures is_bits(p, k),
{
    assert forall |r: int, c: int| 0 <= r < p.len() && 0 <= c < k implies (#[trigger] p[r]@[c]) <= 1 by {
        assert((p[r]@[c]) as nat == bit(frac_int(ms[r] as nat, k, l), (k - 1 - c) as nat));
    }
}

pub proof fn lemma_col_pre_le(p: Seq<Vec<u8>>, k: nat, c: nat, r: nat)
    requires is_bits(p, k), c < k, r <= p.len(),
    ensures col_pre(p, c, r) <= r,
    decreases r,
{
    if r > 0 { lemma_col_pre_le(p, k, c, (r - 1) as nat); }
}

/// `make_hamming_vector(P)`: h[c] = Σ_r P[r][c], the leaves at level c+1.
pub fn make_hamming_vector(p: &Vec<Vec<u8>>, k: usize) -> (h: Vec<u64>)
    requires p.len() >= 1, p@[0].len() == k, is_bits(p@, k as nat), p.len() < 0x4000000000000000,
    ensures h.len() == k, forall |c: int| 0 <= c < k ==> (#[trigger] h@[c]) as nat == col_pre(p@, c as nat, p.len() as nat),
{
    let n = p.len();
    let mut h: Vec<u64> = Vec::new();
    let mut c: usize = 0;
    while c < k
        invariant n == p.len() < 0x4000000000000000, is_bits(p@, k as nat), c <= k, h.len() == c,
            forall |c2: int| 0 <= c2 < c ==> (#[trigger] h@[c2]) as nat == col_pre(p@, c2 as nat, n as nat),
        decreases k - c,
    {
        let mut s: u64 = 0;
        let mut r: usize = 0;
        while r < n
            invariant n == p.len() < 0x4000000000000000, is_bits(p@, k as nat), c < k, r <= n,
                s as nat == col_pre(p@, c as nat, r as nat),
            decreases n - r,
        {
            proof { lemma_col_pre_le(p@, k as nat, c as nat, r as nat); }
            s = s + p[r][c] as u64;
            r = r + 1;
        }
        h.push(s);
        c = c + 1;
    }
    h
}

/// The cached table T: T[col_pre(c, r)][c] = r for every one P[r][c] = 1.
pub open spec fn is_hamming_matrix(t: Seq<Vec<i64>>, p: Seq<Vec<u8>>, k: nat) -> bool {
    &&& t.len() == p.len()
    &&& forall |d: int| 0 <= d < t.len() ==> (#[trigger] t[d]).len() == k
    &&& forall |r: int, c: int| 0 <= r < p.len() && 0 <= c < k && p[r]@[c] == 1 ==>
        #[trigger] t[col_pre(p, c as nat, r as nat) as int]@[c] == r as i64
}

proof fn lemma_col_pre_step(p: Seq<Vec<u8>>, c: nat, r: nat)
    ensures col_pre(p, c, r + 1) == col_pre(p, c, r) + p[r as int]@[c as int] as nat,
{
}

proof fn lemma_col_pre_strict(p: Seq<Vec<u8>>, k: nat, c: nat, a: nat, b: nat)
    requires is_bits(p, k), c < k, a < b <= p.len(), p[a as int]@[c as int] == 1,
    ensures col_pre(p, c, a) < col_pre(p, c, b),
    decreases b - a,
{
    if a + 1 < b {
        lemma_col_pre_strict(p, k, c, a, (b - 1) as nat);
    }
}

/// The rows of the ones in column c, in order: `ones[d]` is the row of the
/// d-th one.
fn column_ones(p: &Vec<Vec<u8>>, Ghost(k): Ghost<nat>, c: usize) -> (ones: Vec<i64>)
    requires is_bits(p@, k), c < k, p.len() < 0x4000000000000000,
    ensures
        ones.len() == col_pre(p@, c as nat, p.len() as nat),
        forall |r: int| 0 <= r < p.len() && p@[r]@[c as int] == 1 ==>
            #[trigger] ones@[col_pre(p@, c as nat, r as nat) as int] == r as i64,
{
    let n = p.len();
    let mut ones: Vec<i64> = Vec::new();
    let mut r: usize = 0;
    while r < n
        invariant
            n == p.len() < 0x4000000000000000, is_bits(p@, k), c < k, r <= n,
            ones.len() == col_pre(p@, c as nat, r as nat),
            forall |r2: int| 0 <= r2 < r && p@[r2]@[c as int] == 1 ==>
                #[trigger] ones@[col_pre(p@, c as nat, r2 as nat) as int] == r2 as i64,
        decreases n - r,
    {
        proof {
            lemma_col_pre_le(p@, k, c as nat, r as nat);
            lemma_col_pre_step(p@, c as nat, r as nat);
        }
        let ghost o0 = ones@;
        if p[r][c] == 1 {
            ones.push(r as i64);
        }
        proof {
            assert forall |r2: int| 0 <= r2 < r + 1 && p@[r2]@[c as int] == 1 implies
                #[trigger] ones@[col_pre(p@, c as nat, r2 as nat) as int] == r2 as i64 by {
                if r2 < r {
                    lemma_col_pre_strict(p@, k, c as nat, r2 as nat, r as nat);
                    assert(ones@[col_pre(p@, c as nat, r2 as nat) as int] == o0[col_pre(p@, c as nat, r2 as nat) as int]);
                }
            }
        }
        r = r + 1;
    }
    ones
}

/// `make_hamming_matrix(P)`: T[d][c] is the row of the d-th one in column c
/// (−1 elsewhere, as in the original; the ensures states only the ones).
/// The rows of the ones are collected per column first, so the cost is
/// O(n·k).
pub fn make_hamming_matrix(p: &Vec<Vec<u8>>, k: usize) -> (t: Vec<Vec<i64>>)
    requires p.len() >= 1, p@[0].len() == k, is_bits(p@, k as nat), p.len() < 0x4000000000000000,
    ensures is_hamming_matrix(t@, p@, k as nat),
{
    let n = p.len();
    let mut cols: Vec<Vec<i64>> = Vec::new();
    let mut c: usize = 0;
    while c < k
        invariant
            n == p.len() < 0x4000000000000000, is_bits(p@, k as nat), c <= k, cols.len() == c,
            forall |c2: int| 0 <= c2 < c ==> (#[trigger] cols@[c2]).len() == col_pre(p@, c2 as nat, n as nat),
            forall |r: int, c2: int| 0 <= r < n && 0 <= c2 < c && p@[r]@[c2] == 1 ==>
                #[trigger] cols@[c2]@[col_pre(p@, c2 as nat, r as nat) as int] == r as i64,
        decreases k - c,
    {
        let ones = column_ones(p, Ghost(k as nat), c);
        let ghost c0 = cols@;
        cols.push(ones);
        proof {
            assert forall |r: int, c2: int| 0 <= r < n && 0 <= c2 < c + 1 && p@[r]@[c2] == 1 implies
                #[trigger] cols@[c2]@[col_pre(p@, c2 as nat, r as nat) as int] == r as i64 by {
                if c2 < c { assert(cols@[c2] == c0[c2]); }
            }
        }
        c = c + 1;
    }
    let mut t: Vec<Vec<i64>> = Vec::new();
    let mut d: usize = 0;
    while d < n
        invariant
            n == p.len(), cols.len() == k, d <= n, t.len() == d,
            forall |d2: int| 0 <= d2 < d ==> (#[trigger] t@[d2]).len() == k,
            forall |d2: int, c2: int| 0 <= d2 < d && 0 <= c2 < k && d2 < cols@[c2].len() ==>
                #[trigger] t@[d2]@[c2] == cols@[c2]@[d2],
        decreases n - d,
    {
        let mut row: Vec<i64> = Vec::new();
        let mut c: usize = 0;
        while c < k
            invariant
                cols.len() == k, c <= k, row.len() == c,
                forall |c2: int| 0 <= c2 < c && d < cols@[c2].len() ==> #[trigger] row@[c2] == cols@[c2]@[d as int],
            decreases k - c,
        {
            let col = &cols[c];
            if d < col.len() { row.push(col[d]); } else { row.push(-1); }
            c = c + 1;
        }
        t.push(row);
        d = d + 1;
    }
    proof {
        assert forall |r: int, c2: int| 0 <= r < p.len() && 0 <= c2 < k && p@[r]@[c2] == 1 implies
            #[trigger] t@[col_pre(p@, c2 as nat, r as nat) as int]@[c2] == r as i64 by {
            let d = col_pre(p@, c2 as nat, r as nat);
            lemma_col_pre_le(p@, k as nat, c2 as nat, r as nat);
            lemma_col_pre_strict(p@, k as nat, c2 as nat, r as nat, n as nat);
            assert(cols@[c2].len() == col_pre(p@, c2 as nat, n as nat));
            assert(d < cols@[c2].len() && d < n);
            assert(t@[d as int]@[c2] == cols@[c2]@[d as int]);
            assert(cols@[c2]@[col_pre(p@, c2 as nat, r as nat) as int] == r as i64);
        }
    }
    t
}

} // verus!
