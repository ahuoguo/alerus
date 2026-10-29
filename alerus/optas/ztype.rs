//! The unrolled DDG tree of M / Z (no back-edges), from which `tree.rs`
//! proves `OptasSpec`'s laws. No counterpart in optas.
//!
//! Level j has a leaf labeled r iff bit j of M_r / Z is 1 (`ddg_bit`), and
//! A(j) = 2^j − Σ_r ⌊2^j M_r / Z⌋ of its nodes are internal. The credit
//! `ddg_g` is fuel-indexed as in `fldr.rs`; the root is worth at most
//! E_{M/Z}[ℰ] + n/2^f (`lemma_ddg_val_le_target`).

use vstd::prelude::*;

verus! {

#[cfg(verus_keep_ghost)]
use crate::fldr_helper::lemma_nat_mul_real_cast;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::{pow2, lemma_pow2_pos, lemma_pow2_unfold, lemma_pow2_adds, lemma2_to64};
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::{
    lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse, lemma_div_denominator,
};

// ── Weight sums ───────────────────────────────────────────────────────────────

/// Σ_{r' ∈ [r, n)} M_{r'}.
pub open spec fn wsum_nat(w: Seq<u128>, r: nat) -> nat
    decreases w.len() - r,
{
    if r >= w.len() { 0 } else { w[r as int] as nat + wsum_nat(w, r + 1) }
}

/// Σ_{r' ∈ [r, n)} M_{r'}·ℰ(r').
pub open spec fn wsum(w: Seq<u128>, e: spec_fn(nat) -> real, r: nat) -> real
    decreases w.len() - r,
{
    if r >= w.len() { 0real } else { (w[r as int] as real) * e(r) + wsum(w, e, r + 1) }
}

pub proof fn lemma_w_le_sum(w: Seq<u128>, r0: nat, r: nat)
    requires r0 <= r < w.len(),
    ensures w[r as int] as nat <= wsum_nat(w, r0),
    decreases r - r0,
{
    if r0 < r { lemma_w_le_sum(w, r0 + 1, r); }
}

// ── The unrolled DDG tree of M / Z ───────────────────────────────────────────

/// ⌊2^j M_r / Z⌋: the first j bits of M_r / Z, as an integer.
pub open spec fn ddg_fl(w: Seq<u128>, z: nat, j: nat, r: nat) -> nat {
    (pow2(j) * (w[r as int] as nat)) / z
}

/// 2^j M_r mod Z: the residue after j bits.
pub open spec fn ddg_rho(w: Seq<u128>, z: nat, j: nat, r: nat) -> nat {
    (pow2(j) * (w[r as int] as nat)) % z
}

/// Bit j of M_r / Z: label r has a leaf at level j.
pub open spec fn ddg_bit(w: Seq<u128>, z: nat, j: nat, r: nat) -> nat {
    ddg_fl(w, z, j, r) % 2
}

/// Σ_{r' ∈ [r, n)} bit j of M_{r'} / Z: leaves at level j with label ≥ r.
pub open spec fn ddg_h(w: Seq<u128>, z: nat, j: nat, r: nat) -> nat
    decreases w.len() - r,
{
    if r >= w.len() { 0 } else { ddg_bit(w, z, j, r) + ddg_h(w, z, j, r + 1) }
}

/// Σ_{r' ∈ [r, n)} ⌊2^j M_{r'} / Z⌋.
pub open spec fn ddg_fs(w: Seq<u128>, z: nat, j: nat, r: nat) -> nat
    decreases w.len() - r,
{
    if r >= w.len() { 0 } else { ddg_fl(w, z, j, r) + ddg_fs(w, z, j, r + 1) }
}

/// Internal nodes at level j: A(j) = 2^j − Σ_r ⌊2^j M_r / Z⌋.
pub open spec fn ddg_num_internal(w: Seq<u128>, z: nat, j: nat) -> int {
    pow2(j) as int - ddg_fs(w, z, j, 0) as int
}

/// E_{M/Z}[ℰ] = Σ_r (M_r / Z)·ℰ(r).
pub open spec fn ddg_exp(w: Seq<u128>, z: nat, e: spec_fn(nat) -> real) -> real {
    wsum(w, e, 0) / (z as real)
}

// ── Fuel-indexed credit values ───────────────────────────────────────────────

/// Credit at internal node d of level j with f flips left. Out of fuel, the
/// node is worth 1 (the failure credit).
pub open spec fn ddg_f(w: Seq<u128>, z: nat, e: spec_fn(nat) -> real, j: nat, d: nat, f: nat) -> real
    decreases f, 0nat,
{
    if f == 0 {
        1real
    } else {
        (ddg_g(w, z, e, j + 1, 2 * d + 1, 0, (f - 1) as nat)
            + ddg_g(w, z, e, j + 1, 2 * d, 0, (f - 1) as nat)) / 2real
    }
}

/// Credit at node x of level j while the inner loop scans labels from r.
pub open spec fn ddg_g(w: Seq<u128>, z: nat, e: spec_fn(nat) -> real, j: nat, x: nat, r: nat, f: nat) -> real
    decreases f, if r < w.len() { (w.len() - r) as nat + 1 } else { 1nat },
{
    if r >= w.len() {
        ddg_f(w, z, e, j, x, f)
    } else if ddg_bit(w, z, j, r) == 1 {
        if x == 0 { e(r) } else { ddg_g(w, z, e, j, (x - 1) as nat, r + 1, f) }
    } else {
        ddg_g(w, z, e, j, x, r + 1, f)
    }
}

/// Σ_{x<m} ddg_g(j, x, r, f).
pub open spec fn ddg_vs(w: Seq<u128>, z: nat, e: spec_fn(nat) -> real, j: nat, r: nat, m: nat, f: nat) -> real
    decreases m,
{
    if m == 0 { 0real } else { ddg_vs(w, z, e, j, r, (m - 1) as nat, f) + ddg_g(w, z, e, j, (m - 1) as nat, r, f) }
}

/// Σ_{d<m} ddg_f(j, d, f).
pub open spec fn ddg_vfsum(w: Seq<u128>, z: nat, e: spec_fn(nat) -> real, j: nat, m: nat, f: nat) -> real
    decreases m,
{
    if m == 0 { 0real } else { ddg_vfsum(w, z, e, j, (m - 1) as nat, f) + ddg_f(w, z, e, j, (m - 1) as nat, f) }
}

/// Σ_{r' ≥ r} (bit j of M_{r'}/Z)·ℰ(r'): the leaf credits at level j.
pub open spec fn ddg_ac(w: Seq<u128>, z: nat, e: spec_fn(nat) -> real, j: nat, r: nat) -> real
    decreases w.len() - r,
{
    if r >= w.len() { 0real } else { (ddg_bit(w, z, j, r) as real) * e(r) + ddg_ac(w, z, e, j, r + 1) }
}

/// Σ_{r' ≥ r} ℰ(r')·(2^j M_{r'} mod Z)/Z: the expected credit of the mass below
/// level j.
pub open spec fn ddg_atr(w: Seq<u128>, z: nat, e: spec_fn(nat) -> real, j: nat, r: nat) -> real
    decreases w.len() - r,
{
    if r >= w.len() { 0real } else { e(r) * (ddg_rho(w, z, j, r) as real) / (z as real) + ddg_atr(w, z, e, j, r + 1) }
}

// ── Nonnegativity ─────────────────────────────────────────────────────────────

pub proof fn lemma_ddg_g_nonneg(w: Seq<u128>, z: nat, e: spec_fn(nat) -> real, j: nat, x: nat, r: nat, f: nat)
    requires forall |i: nat| (#[trigger] e(i)) >= 0real,
    ensures ddg_g(w, z, e, j, x, r, f) >= 0real,
    decreases f, if r < w.len() { (w.len() - r) as nat + 1 } else { 1nat },
{
    if r >= w.len() {
        lemma_ddg_f_nonneg(w, z, e, j, x, f);
    } else if ddg_bit(w, z, j, r) == 1 {
        if x != 0 { lemma_ddg_g_nonneg(w, z, e, j, (x - 1) as nat, r + 1, f); }
    } else {
        lemma_ddg_g_nonneg(w, z, e, j, x, r + 1, f);
    }
}

pub proof fn lemma_ddg_f_nonneg(w: Seq<u128>, z: nat, e: spec_fn(nat) -> real, j: nat, d: nat, f: nat)
    requires forall |i: nat| (#[trigger] e(i)) >= 0real,
    ensures ddg_f(w, z, e, j, d, f) >= 0real,
    decreases f, 0nat,
{
    if f > 0 {
        lemma_ddg_g_nonneg(w, z, e, j + 1, 2 * d + 1, 0, (f - 1) as nat);
        lemma_ddg_g_nonneg(w, z, e, j + 1, 2 * d, 0, (f - 1) as nat);
    }
}

pub proof fn lemma_ddg_atr_nonneg(w: Seq<u128>, z: nat, e: spec_fn(nat) -> real, j: nat, r: nat)
    requires forall |i: nat| (#[trigger] e(i)) >= 0real, z > 0,
    ensures ddg_atr(w, z, e, j, r) >= 0real,
    decreases w.len() - r,
{
    if r < w.len() {
        lemma_ddg_atr_nonneg(w, z, e, j, r + 1);
        let ev = e(r);
        let rv = ddg_rho(w, z, j, r) as real;
        assert(ev * rv / (z as real) >= 0real) by(nonlinear_arith)
            requires ev >= 0real, rv >= 0real, z > 0;
    }
}

// ── The scan: one level's credit sum ──────────────────────────────────────────

pub proof fn lemma_ddg_vs_end(w: Seq<u128>, z: nat, e: spec_fn(nat) -> real, j: nat, r: nat, m: nat, f: nat)
    requires r >= w.len(),
    ensures ddg_vs(w, z, e, j, r, m, f) == ddg_vfsum(w, z, e, j, m, f),
    decreases m,
{
    if m > 0 { lemma_ddg_vs_end(w, z, e, j, r, (m - 1) as nat, f); }
}

pub proof fn lemma_ddg_vs_skip(w: Seq<u128>, z: nat, e: spec_fn(nat) -> real, j: nat, r: nat, m: nat, f: nat)
    requires r < w.len(), ddg_bit(w, z, j, r) != 1,
    ensures ddg_vs(w, z, e, j, r, m, f) == ddg_vs(w, z, e, j, r + 1, m, f),
    decreases m,
{
    if m > 0 { lemma_ddg_vs_skip(w, z, e, j, r, (m - 1) as nat, f); }
}

pub proof fn lemma_ddg_vs_take(w: Seq<u128>, z: nat, e: spec_fn(nat) -> real, j: nat, r: nat, m: nat, f: nat)
    requires r < w.len(), ddg_bit(w, z, j, r) == 1,
    ensures ddg_vs(w, z, e, j, r, m + 1, f) == e(r) + ddg_vs(w, z, e, j, r + 1, m, f),
    decreases m,
{
    assert(ddg_vs(w, z, e, j, r, 0, f) == 0real);
    if m > 0 { lemma_ddg_vs_take(w, z, e, j, r, (m - 1) as nat, f); }
}

/// Σ_{x < h + m} ddg_g(j, x, r, f) = (leaf credits) + Σ_{d<m} ddg_f(j, d, f).
pub proof fn lemma_ddg_vs_leaf(w: Seq<u128>, z: nat, e: spec_fn(nat) -> real, j: nat, r: nat, m: nat, f: nat)
    ensures
        ddg_vs(w, z, e, j, r, ddg_h(w, z, j, r) + m, f) == ddg_ac(w, z, e, j, r) + ddg_vfsum(w, z, e, j, m, f),
    decreases w.len() - r,
{
    if r >= w.len() {
        lemma_ddg_vs_end(w, z, e, j, r, m, f);
    } else if ddg_bit(w, z, j, r) == 1 {
        lemma_ddg_vs_leaf(w, z, e, j, r + 1, m, f);
        lemma_ddg_vs_take(w, z, e, j, r, ddg_h(w, z, j, r + 1) + m, f);
        assert((ddg_bit(w, z, j, r) as real) == 1real);
    } else {
        lemma_ddg_vs_leaf(w, z, e, j, r + 1, m, f);
        lemma_ddg_vs_skip(w, z, e, j, r, ddg_h(w, z, j, r + 1) + m, f);
        let pb = ddg_bit(w, z, j, r) as real;
        assert(pb * e(r) == 0real) by(nonlinear_arith) requires pb == 0real;
    }
}

/// Σ_{d<m} ddg_f(j, d, f+1) = ½ Σ_{x<2m} ddg_g(j+1, x, 0, f).
pub proof fn lemma_ddg_vfsum_half_vs(w: Seq<u128>, z: nat, e: spec_fn(nat) -> real, j: nat, m: nat, f: nat)
    ensures ddg_vfsum(w, z, e, j, m, f + 1) == ddg_vs(w, z, e, j + 1, 0, 2 * m, f) / 2real,
    decreases m,
{
    if m > 0 {
        let m1 = (m - 1) as nat;
        lemma_ddg_vfsum_half_vs(w, z, e, j, m1, f);
        assert(ddg_vs(w, z, e, j + 1, 0, 2 * m1 + 1, f)
            == ddg_vs(w, z, e, j + 1, 0, 2 * m1, f) + ddg_g(w, z, e, j + 1, 2 * m1, 0, f));
        assert(ddg_vs(w, z, e, j + 1, 0, 2 * m, f)
            == ddg_vs(w, z, e, j + 1, 0, 2 * m1 + 1, f) + ddg_g(w, z, e, j + 1, 2 * m1 + 1, 0, f));
    }
}

/// Out of fuel, every internal node is worth 1.
pub proof fn lemma_ddg_vfsum_zero(w: Seq<u128>, z: nat, e: spec_fn(nat) -> real, j: nat, m: nat)
    ensures ddg_vfsum(w, z, e, j, m, 0) == m as real,
    decreases m,
{
    if m > 0 { lemma_ddg_vfsum_zero(w, z, e, j, (m - 1) as nat); }
}

// ── One bit of a fraction ─────────────────────────────────────────────────────

/// Doubling a = qZ + ρ:  ⌊2a/Z⌋ = 2q + b and 2a mod Z = 2ρ − bZ, where
/// b = ⌊2ρ/Z⌋ ∈ {0, 1} is the parity of ⌊2a/Z⌋.
pub proof fn lemma_ddg_double(a: nat, z: nat)
    requires z > 0,
    ensures
        (2 * (a % z)) / z <= 1,
        (2 * a) / z == 2 * (a / z) + (2 * (a % z)) / z,
        ((2 * a) / z) % 2 == (2 * (a % z)) / z,
        2 * (a % z) == z * ((2 * (a % z)) / z) + (2 * a) % z,
{
    let q = a / z;
    let rho = a % z;
    lemma_fundamental_div_mod(a as int, z as int);
    let b: nat = if 2 * rho >= z { 1 } else { 0 };
    let rho2: nat = (2 * rho - b * z) as nat;
    assert(0 <= rho2 < z);
    lemma_fundamental_div_mod_converse((2 * rho) as int, z as int, b as int, rho2 as int);
    assert(2 * a == (2 * q + b) * z + rho2) by(nonlinear_arith)
        requires a == z * q + rho, 2 * rho == b * z + rho2;
    lemma_fundamental_div_mod_converse((2 * a) as int, z as int, (2 * q + b) as int, rho2 as int);
    lemma_fundamental_div_mod_converse((2 * q + b) as int, 2, q as int, b as int);
}

/// Bit j+1 of M_r/Z and the next residue depend only on the residue after j bits.
pub proof fn lemma_ddg_step(w: Seq<u128>, z: nat, j: nat, r: nat)
    requires z > 0,
    ensures
        ddg_bit(w, z, j + 1, r) == (2 * ddg_rho(w, z, j, r)) / z,
        ddg_bit(w, z, j + 1, r) <= 1,
        ddg_fl(w, z, j + 1, r) == 2 * ddg_fl(w, z, j, r) + ddg_bit(w, z, j + 1, r),
        2 * ddg_rho(w, z, j, r) == z * ddg_bit(w, z, j + 1, r) + ddg_rho(w, z, j + 1, r),
        ddg_rho(w, z, j + 1, r) == (2 * ddg_rho(w, z, j, r)) % z,
{
    let a = pow2(j) * (w[r as int] as nat);
    lemma_pow2_unfold(j + 1);
    assert(pow2(j + 1) * (w[r as int] as nat) == 2 * a) by(nonlinear_arith)
        requires pow2(j + 1) == 2 * pow2(j), a == pow2(j) * (w[r as int] as nat);
    lemma_ddg_double(a, z);
    let rho2 = (2 * a) % z;
    lemma_fundamental_div_mod((2 * a) as int, z as int);
    let bb = (2 * (a % z)) / z;
    lemma_fundamental_div_mod_converse((2 * (a % z)) as int, z as int, bb as int, rho2 as int);
}

/// The executable level c reads the same bits as level j when their previous
/// residues agree.
pub proof fn lemma_ddg_bit_agree(w: Seq<u128>, z: nat, j: nat, c: nat, r: nat)
    requires z > 0, j >= 1, c >= 1, ddg_rho(w, z, (j - 1) as nat, r) == ddg_rho(w, z, (c - 1) as nat, r),
    ensures ddg_bit(w, z, j, r) == ddg_bit(w, z, c, r),
{
    lemma_ddg_step(w, z, (j - 1) as nat, r);
    lemma_ddg_step(w, z, (c - 1) as nat, r);
}

/// For c ≤ k, bit (k − c) of T_r = ⌊2^k M_r / Z⌋ is bit c of M_r / Z.
pub proof fn lemma_ddg_row_bit(w: Seq<u128>, z: nat, k: nat, c: nat, r: nat)
    requires z > 0, c <= k,
    ensures (ddg_fl(w, z, k, r) / pow2((k - c) as nat)) % 2 == ddg_bit(w, z, c, r),
{
    let m = w[r as int] as nat;
    let q = pow2((k - c) as nat);
    lemma_pow2_pos((k - c) as nat);
    lemma_pow2_adds(c, (k - c) as nat);
    let a = pow2(c) * m;
    assert(pow2(k) * m == a * q) by(nonlinear_arith)
        requires pow2(k) == pow2(c) * q, a == pow2(c) * m;
    lemma_div_denominator((a * q) as int, z as int, q as int);
    // (a q) / (z q) = a / z
    lemma_fundamental_div_mod(a as int, z as int);
    let t = a / z;
    let s = a % z;
    assert(a * q == t * (z * q) + s * q) by(nonlinear_arith) requires a == z * t + s;
    assert(s * q < z * q) by(nonlinear_arith) requires s < z, q > 0;
    lemma_fundamental_div_mod_converse((a * q) as int, (z * q) as int, t as int, (s * q) as int);
}

/// The back-edge: 2^k M ≡ 2^l M (mod 2^k − 2^l).
pub proof fn lemma_ddg_wrap(w: Seq<u128>, k: nat, l: nat, r: nat)
    requires l < k, pow2(k) > pow2(l),
    ensures ddg_rho(w, (pow2(k) - pow2(l)) as nat, k, r) == ddg_rho(w, (pow2(k) - pow2(l)) as nat, l, r),
{
    let z = (pow2(k) - pow2(l)) as nat;
    let m = w[r as int] as nat;
    let b = pow2(l) * m;
    lemma_fundamental_div_mod(b as int, z as int);
    let t = b / z;
    let s = b % z;
    assert(pow2(k) * m == (t + m) * z + s) by(nonlinear_arith)
        requires b == z * t + s, z == pow2(k) - pow2(l), b == pow2(l) * m;
    lemma_fundamental_div_mod_converse((pow2(k) * m) as int, z as int, (t + m) as int, s as int);
}

// ── Node counts ───────────────────────────────────────────────────────────────

pub proof fn lemma_ddg_fs_step(w: Seq<u128>, z: nat, j: nat, r: nat)
    requires z > 0,
    ensures ddg_fs(w, z, j + 1, r) == 2 * ddg_fs(w, z, j, r) + ddg_h(w, z, j + 1, r),
    decreases w.len() - r,
{
    if r < w.len() {
        lemma_ddg_fs_step(w, z, j, r + 1);
        lemma_ddg_step(w, z, j, r);
    }
}

/// Z·Σ⌊2^j M/Z⌋ ≤ 2^j·ΣM, and 2^j·ΣM + #labels ≤ Z·(Σ⌊2^j M/Z⌋ + #labels).
pub proof fn lemma_ddg_fs_bounds(w: Seq<u128>, z: nat, j: nat, r: nat)
    requires z > 0, r <= w.len(),
    ensures
        z * ddg_fs(w, z, j, r) <= pow2(j) * wsum_nat(w, r),
        pow2(j) * wsum_nat(w, r) + (w.len() - r) <= z * (ddg_fs(w, z, j, r) + (w.len() - r)),
    decreases w.len() - r,
{
    if r < w.len() {
        lemma_ddg_fs_bounds(w, z, j, r + 1);
        let a = pow2(j) * (w[r as int] as nat);
        lemma_fundamental_div_mod(a as int, z as int);
        let fl = a / z;
        let f1 = ddg_fs(w, z, j, r + 1);
        let s1 = wsum_nat(w, r + 1);
        let n1 = (w.len() - (r + 1)) as nat;
        assert(pow2(j) * wsum_nat(w, r) == a + pow2(j) * s1) by(nonlinear_arith)
            requires wsum_nat(w, r) == (w[r as int] as nat) + s1, a == pow2(j) * (w[r as int] as nat);
        let rho = a % z;
        let pj = pow2(j);
        let ws = wsum_nat(w, r);
        assert(ddg_fs(w, z, j, r) == fl + f1);
        assert(z * (fl + f1) <= pj * ws && pj * ws + (n1 + 1) <= z * (fl + f1 + (n1 + 1))) by(nonlinear_arith)
            requires
                pj * ws == a + pj * s1,
                z * f1 <= pj * s1,
                pj * s1 + n1 <= z * (f1 + n1),
                a == z * fl + rho, 0 <= rho < z;
        assert(w.len() - r == n1 + 1);
    } else {
        assert(ddg_fs(w, z, j, r) == 0 && wsum_nat(w, r) == 0);
        assert(z * 0 == 0 && pow2(j) * 0 == 0);
    }
}

pub proof fn lemma_ddg_fs_top(w: Seq<u128>, z: nat, r: nat)
    requires z > 0, wsum_nat(w, 0) == z,
    ensures ddg_fs(w, z, 0, r) == ddg_h(w, z, 0, r),
    decreases w.len() - r,
{
    if r < w.len() {
        lemma_ddg_fs_top(w, z, r + 1);
        lemma_w_le_sum(w, 0, r);
        let m = w[r as int] as nat;
        lemma_ddg_pow2_one_mul(m);
        lemma_fundamental_div_mod(m as int, z as int);
        assert(m / z <= 1) by(nonlinear_arith)
            requires m <= z, z > 0, m == z * (m / z) + m % z, m % z >= 0;
    }
}

/// The tree shape, at every level of the unrolled tree.
pub proof fn lemma_ddg_shape(w: Seq<u128>, z: nat, j: nat)
    requires z > 0, wsum_nat(w, 0) == z,
    ensures
        0 <= ddg_num_internal(w, z, j) < w.len(),
        2 * ddg_num_internal(w, z, j) == ddg_h(w, z, j + 1, 0) + ddg_num_internal(w, z, j + 1),
        ddg_h(w, z, j, 0) <= w.len(),
        j == 0 ==> ddg_h(w, z, 0, 0) + ddg_num_internal(w, z, 0) == 1,
{
    lemma_ddg_fs_bounds(w, z, j, 0);
    lemma_pow2_pos(j);
    let fs = ddg_fs(w, z, j, 0);
    let n = w.len() as nat;
    assert(n > 0) by { if n == 0 { assert(wsum_nat(w, 0) == 0); } }
    assert(fs <= pow2(j)) by(nonlinear_arith) requires z * fs <= pow2(j) * z, z > 0;
    assert(pow2(j) < fs + n) by(nonlinear_arith)
        requires pow2(j) * z + n <= z * (fs + n), z > 0, n > 0;
    lemma_ddg_fs_step(w, z, j, 0);
    lemma_pow2_unfold(j + 1);
    lemma_ddg_h_le(w, z, j, 0);
    if j == 0 {
        lemma_ddg_fs_top(w, z, 0);
        lemma2_to64();
    }
}

pub proof fn lemma_ddg_h_le(w: Seq<u128>, z: nat, j: nat, r: nat)
    requires z > 0, r <= w.len(),
    ensures ddg_h(w, z, j, r) <= w.len() - r,
    decreases w.len() - r,
{
    if r < w.len() { lemma_ddg_h_le(w, z, j, r + 1); }
}

// ── Level sums ────────────────────────────────────────────────────────────────

/// 2·atr(j) = ac(j+1) + atr(j+1): the residue mass splits into the leaves
/// at the next level and the residue below it (`ddg_atr`, `ddg_ac`).
pub proof fn lemma_ddg_atr_step(w: Seq<u128>, z: nat, e: spec_fn(nat) -> real, j: nat, r: nat)
    requires z > 0,
    ensures 2real * ddg_atr(w, z, e, j, r) == ddg_ac(w, z, e, j + 1, r) + ddg_atr(w, z, e, j + 1, r),
    decreases w.len() - r,
{
    if r < w.len() {
        lemma_ddg_atr_step(w, z, e, j, r + 1);
        lemma_ddg_step(w, z, j, r);
        let rho = ddg_rho(w, z, j, r);
        let rho1 = ddg_rho(w, z, j + 1, r);
        let b = ddg_bit(w, z, j + 1, r);
        lemma_nat_mul_real_cast(z, b);
        let zr = z as real;
        let ev = e(r);
        assert(2real * (ev * (rho as real) / zr) == (b as real) * ev + ev * (rho1 as real) / zr) by(nonlinear_arith)
            requires 2real * (rho as real) == zr * (b as real) + (rho1 as real), zr > 0real;
    }
}

/// At the root: ac(0) + atr(0) = E_{M/Z}[ℰ].
pub proof fn lemma_ddg_atr_wenc(w: Seq<u128>, z: nat, e: spec_fn(nat) -> real, r: nat)
    requires z > 0, wsum_nat(w, 0) == z,
    ensures ddg_ac(w, z, e, 0, r) + ddg_atr(w, z, e, 0, r) == wsum(w, e, r) / (z as real),
    decreases w.len() - r,
{
    let zr = z as real;
    if r < w.len() {
        lemma_ddg_atr_wenc(w, z, e, r + 1);
        lemma_w_le_sum(w, 0, r);
        let m = w[r as int] as nat;
        lemma_ddg_pow2_one_mul(m);
        lemma_fundamental_div_mod(m as int, z as int);
        let t = m / z;
        let s = m % z;
        assert(t <= 1) by(nonlinear_arith) requires m <= z, z > 0, m == z * t + s, s >= 0;
        assert(ddg_bit(w, z, 0, r) == t);
        lemma_nat_mul_real_cast(z, t);
        let ev = e(r);
        assert((t as real) * ev + ev * (s as real) / zr + wsum(w, e, r + 1) / zr
            == ((m as real) * ev + wsum(w, e, r + 1)) / zr) by(nonlinear_arith)
            requires (m as real) == zr * (t as real) + (s as real), zr > 0real;
    } else {
        assert(0real / zr == 0real);
    }
}

/// The internal nodes of level j with f flips left are worth at most
/// atr(j) + A(j+f)/2^f.
pub proof fn lemma_ddg_v_level(w: Seq<u128>, z: nat, e: spec_fn(nat) -> real, j: nat, f: nat)
    requires z > 0, wsum_nat(w, 0) == z, forall |i: nat| (#[trigger] e(i)) >= 0real,
    ensures
        ddg_vfsum(w, z, e, j, ddg_num_internal(w, z, j) as nat, f)
            <= ddg_atr(w, z, e, j, 0) + (ddg_num_internal(w, z, j + f) as real) / (pow2(f) as real),
    decreases f,
{
    lemma_ddg_shape(w, z, j);
    lemma_ddg_atr_nonneg(w, z, e, j, 0);
    lemma_pow2_pos(f);
    if f == 0 {
        lemma_ddg_vfsum_zero(w, z, e, j, ddg_num_internal(w, z, j) as nat);
        lemma2_to64();
        assert(j + f == j);
        assert((ddg_num_internal(w, z, j) as real) / 1real == ddg_num_internal(w, z, j) as real);
    } else {
        let f1 = (f - 1) as nat;
        let a = ddg_num_internal(w, z, j) as nat;
        let a1 = ddg_num_internal(w, z, j + 1) as nat;
        lemma_ddg_shape(w, z, j + 1);
        lemma_ddg_v_level(w, z, e, j + 1, f1);
        lemma_ddg_vfsum_half_vs(w, z, e, j, a, f1);
        lemma_ddg_vs_leaf(w, z, e, j + 1, 0, a1, f1);
        lemma_ddg_atr_step(w, z, e, j, 0);
        assert(j + 1 + f1 == j + f);
        lemma_pow2_unfold(f);
        let t = ddg_num_internal(w, z, j + f) as real;
        let p1 = pow2(f1) as real;
        assert((t / p1) / 2real == t / (pow2(f) as real)) by(nonlinear_arith)
            requires pow2(f) as real == 2real * p1, p1 > 0real;
    }
}

/// The root, with f flips: at most E_{M/Z}[ℰ] + n/2^f.
pub proof fn lemma_ddg_val_le_target(w: Seq<u128>, z: nat, e: spec_fn(nat) -> real, f: nat)
    requires z > 0, wsum_nat(w, 0) == z, forall |i: nat| (#[trigger] e(i)) >= 0real,
    ensures
        ddg_g(w, z, e, 0, 0, 0, f) <= ddg_exp(w, z, e) + (ddg_num_internal(w, z, f) as real) / (pow2(f) as real),
        ddg_g(w, z, e, 0, 0, 0, f) <= ddg_exp(w, z, e) + (w.len() as real) / (pow2(f) as real),
{
    lemma_ddg_shape(w, z, 0);
    lemma_ddg_shape(w, z, f);
    lemma_ddg_vs_leaf(w, z, e, 0, 0, ddg_num_internal(w, z, 0) as nat, f);
    lemma_ddg_v_level(w, z, e, 0, f);
    lemma_ddg_atr_wenc(w, z, e, 0);
    assert(ddg_vs(w, z, e, 0, 0, 0, f) == 0real);
    assert(ddg_vs(w, z, e, 0, 0, 1, f) == ddg_g(w, z, e, 0, 0, 0, f));
    lemma_pow2_pos(f);
    let a = ddg_num_internal(w, z, f) as real;
    let pf = pow2(f) as real;
    assert(a / pf <= (w.len() as real) / pf) by(nonlinear_arith)
        requires a <= w.len() as real, pf > 0real;
}

/// Enough fuel makes the failure part smaller than any s₀ > 0.
pub proof fn lemma_ddg_fail_witness(n: nat, s0: real) -> (f: nat)
    requires s0 > 0real,
    ensures (n as real) / (pow2(f) as real) < s0,
{
    let f: nat = ((n as real / s0).floor() + 1) as nat;
    assert((f as real) > n as real / s0);
    lemma_ddg_pow2_ge(f);
    lemma_pow2_pos(f);
    let pf = pow2(f) as real;
    assert((n as real) / pf < s0) by(nonlinear_arith)
        requires (f as real) > n as real / s0, pf >= f as real, s0 > 0real, pf > 0real;
    f
}

pub proof fn lemma_ddg_pow2_one_mul(m: nat)
    ensures pow2(0) * m == m,
{
    lemma2_to64();
    assert(pow2(0) == 1);
}

pub proof fn lemma_wsum_nonneg(w: Seq<u128>, e: spec_fn(nat) -> real, r: nat)
    requires forall |i: nat| (#[trigger] e(i)) >= 0real,
    ensures wsum(w, e, r) >= 0real,
    decreases w.len() - r,
{
    if r < w.len() {
        lemma_wsum_nonneg(w, e, r + 1);
        let x = w[r as int] as real;
        assert(x * e(r) >= 0real) by(nonlinear_arith) requires x >= 0real, e(r) >= 0real;
    }
}

pub proof fn lemma_ddg_pow2_ge(f: nat)
    ensures pow2(f) >= f,
    decreases f,
{
    if f > 0 {
        lemma_ddg_pow2_ge((f - 1) as nat);
        lemma_pow2_unfold(f);
        lemma_pow2_pos((f - 1) as nat);
    }
}

// ── Facts used by the matrix samplers ─────────────────────────────────────────

/// If every residue after j bits is 0, level j has no internal nodes.
pub proof fn lemma_ddg_internal_zero(w: Seq<u128>, z: nat, j: nat)
    requires z > 0, wsum_nat(w, 0) == z, forall |r: nat| r < w.len() ==> #[trigger] ddg_rho(w, z, j, r) == 0,
    ensures ddg_num_internal(w, z, j) == 0,
{
    lemma_ddg_fs_exact(w, z, j, 0);
    lemma_pow2_pos(j);
    let fs = ddg_fs(w, z, j, 0);
    assert(fs == pow2(j)) by(nonlinear_arith) requires z * fs == pow2(j) * z, z > 0;
}

proof fn lemma_ddg_fs_exact(w: Seq<u128>, z: nat, j: nat, r: nat)
    requires z > 0, forall |r: nat| r < w.len() ==> #[trigger] ddg_rho(w, z, j, r) == 0,
    ensures z * ddg_fs(w, z, j, r) == pow2(j) * wsum_nat(w, r),
    decreases w.len() - r,
{
    if r < w.len() {
        lemma_ddg_fs_exact(w, z, j, r + 1);
        let a = pow2(j) * (w[r as int] as nat);
        lemma_fundamental_div_mod(a as int, z as int);
        assert(ddg_rho(w, z, j, r) == 0);
        let f1 = ddg_fs(w, z, j, r + 1);
        let s1 = wsum_nat(w, r + 1);
        assert(z * (a / z + f1) == pow2(j) * ((w[r as int] as nat) + s1)) by(nonlinear_arith)
            requires a == z * (a / z) + 0, z * f1 == pow2(j) * s1, a == pow2(j) * (w[r as int] as nat);
    } else {
        assert(z * 0 == 0 && pow2(j) * 0 == 0);
    }
}

/// With Z = 2^k, every residue after j ≥ k bits is 0.
pub proof fn lemma_ddg_rho_pow2(w: Seq<u128>, k: nat, j: nat, r: nat)
    requires k <= j,
    ensures ddg_rho(w, pow2(k), j, r) == 0,
{
    lemma_pow2_adds(k, (j - k) as nat);
    lemma_pow2_pos(k);
    let m = w[r as int] as nat;
    assert(pow2(j) * m == (pow2((j - k) as nat) * m) * pow2(k)) by(nonlinear_arith)
        requires pow2(j) == pow2(k) * pow2((j - k) as nat);
    lemma_fundamental_div_mod_converse((pow2(j) * m) as int, pow2(k) as int, (pow2((j - k) as nat) * m) as int, 0);
}

/// Scanning past all leaves of level j from r lands on internal node x − h.
pub proof fn lemma_ddg_g_internal(w: Seq<u128>, z: nat, e: spec_fn(nat) -> real, j: nat, x: nat, r: nat, f: nat)
    requires x >= ddg_h(w, z, j, r),
    ensures ddg_g(w, z, e, j, x, r, f) == ddg_f(w, z, e, j, (x - ddg_h(w, z, j, r)) as nat, f),
    decreases w.len() - r,
{
    if r < w.len() {
        if ddg_bit(w, z, j, r) == 1 {
            lemma_ddg_g_internal(w, z, e, j, (x - 1) as nat, r + 1, f);
        } else {
            lemma_ddg_g_internal(w, z, e, j, x, r + 1, f);
        }
    }
}

/// Σ_{r' < r} bit j of M_{r'}/Z: the leaves of level j before label r.
pub open spec fn ddg_pre(w: Seq<u128>, z: nat, j: nat, r: nat) -> nat
    decreases r,
{
    if r == 0 { 0 } else { ddg_pre(w, z, j, (r - 1) as nat) + ddg_bit(w, z, j, (r - 1) as nat) }
}

/// Leaf number pre(r) of level j is labeled r (when bit j of M_r/Z is 1).
pub proof fn lemma_ddg_g_pre(w: Seq<u128>, z: nat, e: spec_fn(nat) -> real, j: nat, r: nat, r1: nat, f: nat)
    requires r1 <= r < w.len(), ddg_bit(w, z, j, r) == 1, z > 0,
    ensures ddg_g(w, z, e, j, (ddg_pre(w, z, j, r) - ddg_pre(w, z, j, r1)) as nat, r1, f) == e(r),
    decreases r - r1,
{
    lemma_ddg_pre_mono(w, z, j, r1, r);
    if r1 < r {
        lemma_ddg_pre_mono(w, z, j, r1 + 1, r);
        lemma_ddg_step(w, z, (j - 1) as nat, r1);
        lemma_ddg_g_pre(w, z, e, j, r, r1 + 1, f);
        if ddg_bit(w, z, j, r1) == 1 {
            assert(ddg_pre(w, z, j, r) - ddg_pre(w, z, j, r1) >= 1);
        }
    }
}

pub proof fn lemma_ddg_pre_mono(w: Seq<u128>, z: nat, j: nat, a: nat, b: nat)
    requires a <= b,
    ensures ddg_pre(w, z, j, a) <= ddg_pre(w, z, j, b),
        a < b ==> ddg_pre(w, z, j, a + 1) == ddg_pre(w, z, j, a) + ddg_bit(w, z, j, a),
    decreases b - a,
{
    if a < b { lemma_ddg_pre_mono(w, z, j, a + 1, b); }
}

/// pre(r) + h(r) = h(0): the leaves before r and from r make up the level.
pub proof fn lemma_ddg_pre_h(w: Seq<u128>, z: nat, j: nat, r: nat)
    requires r <= w.len(),
    ensures ddg_pre(w, z, j, r) + ddg_h(w, z, j, r) == ddg_h(w, z, j, 0),
    decreases r,
{
    if r > 0 { lemma_ddg_pre_h(w, z, j, (r - 1) as nat); }
}

/// The same distribution has the same expectation.
pub proof fn lemma_ddg_exp_scale(w: Seq<u128>, z: nat, w2: Seq<u128>, z2: nat, e: spec_fn(nat) -> real)
    requires z > 0, z2 > 0, w2.len() == w.len(),
        forall |r: int| 0 <= r < w.len() ==> (#[trigger] w2[r] as nat) * z == (w[r] as nat) * z2,
    ensures ddg_exp(w2, z2, e) == ddg_exp(w, z, e),
{
    lemma_wsum_scale(w, z, w2, z2, e, 0);
    let zr = z as real;
    let z2r = z2 as real;
    let a = wsum(w, e, 0);
    let b = wsum(w2, e, 0);
    assert(b / z2r == a / zr) by(nonlinear_arith) requires b * zr == a * z2r, zr > 0real, z2r > 0real;
}

proof fn lemma_wsum_scale(w: Seq<u128>, z: nat, w2: Seq<u128>, z2: nat, e: spec_fn(nat) -> real, r: nat)
    requires w2.len() == w.len(),
        forall |r: int| 0 <= r < w.len() ==> (#[trigger] w2[r] as nat) * z == (w[r] as nat) * z2,
    ensures wsum(w2, e, r) * (z as real) == wsum(w, e, r) * (z2 as real),
    decreases w.len() - r,
{
    if r < w.len() {
        lemma_wsum_scale(w, z, w2, z2, e, r + 1);
        let a = w[r as int] as nat;
        let b = w2[r as int] as nat;
        lemma_nat_mul_real_cast(b, z);
        lemma_nat_mul_real_cast(a, z2);
        let ev = e(r);
        let t1 = wsum(w, e, r + 1);
        let t2 = wsum(w2, e, r + 1);
        assert(((b as real) * ev + t2) * (z as real) == ((a as real) * ev + t1) * (z2 as real)) by(nonlinear_arith)
            requires (b as real) * (z as real) == (a as real) * (z2 as real), t2 * (z as real) == t1 * (z2 as real);
    } else {
        assert(0real * (z as real) == 0real && 0real * (z2 as real) == 0real);
    }
}

pub proof fn lemma_all_zero_sum(ms: Seq<u128>, r: nat)
    requires r <= ms.len(), forall |i: int| 0 <= i < ms.len() ==> #[trigger] ms[i] == 0,
    ensures wsum_nat(ms, r) == 0,
    decreases ms.len() - r,
{
    if r < ms.len() { lemma_all_zero_sum(ms, r + 1); }
}

/// Σ M = 1 with M_r0 ≠ 0: M_r0 = 1 and every other weight is 0.
pub proof fn lemma_unit(ms: Seq<u128>, r0: nat)
    requires r0 < ms.len(), ms[r0 as int] != 0, wsum_nat(ms, 0) == 1,
    ensures ms[r0 as int] == 1, forall |i: int| 0 <= i < ms.len() && i != r0 ==> #[trigger] ms[i] == 0,
{
    lemma_w_le_sum(ms, 0, r0);
    assert forall |i: int| 0 <= i < ms.len() && i != r0 implies #[trigger] ms[i] == 0 by {
        if i < r0 { lemma_two_le_sum(ms, 0, i as nat, r0); } else { lemma_two_le_sum(ms, 0, r0, i as nat); }
    }
}

/// M_a + M_b ≤ Σ M for a < b.
proof fn lemma_two_le_sum(ms: Seq<u128>, r: nat, a: nat, b: nat)
    requires r <= a < b < ms.len(),
    ensures ms[a as int] as nat + ms[b as int] as nat <= wsum_nat(ms, r),
    decreases a - r,
{
    if r < a { lemma_two_le_sum(ms, r + 1, a, b); } else { lemma_w_le_sum(ms, r + 1, b); }
}

/// A unit weight vector: the expectation is ℰ at the one label.
pub proof fn lemma_wsum_unit(w: Seq<u128>, e: spec_fn(nat) -> real, r0: nat, r: nat)
    requires r0 < w.len(), r <= w.len(), w[r0 as int] == 1,
        forall |i: int| 0 <= i < w.len() && i != r0 ==> #[trigger] w[i] == 0,
    ensures wsum(w, e, r) == if r <= r0 { e(r0) } else { 0real },
    decreases w.len() - r,
{
    if r < w.len() {
        lemma_wsum_unit(w, e, r0, r + 1);
        if r == r0 { assert(1real * e(r0) == e(r0)); } else { assert(0real * e(r) == 0real); }
    }
}

} // verus!
