//! Algorithm 3 for TV: the Z-type distribution M / Z closest to p = a / Σa.
//!
//! ```text
//!   optimize_unorm(Z, p):            filter out zeros; optimize_unorm_strict; pad
//!   optimize_unorm_strict(Z, p):
//!     1. get_initial_ms:    M_i ← ⌊Z p_i⌋, plus 1 if that lowers the error
//!     2. prune_initial_ms:  apply the best (decrement, increment) swap while it helps
//!     3. fix_shortfall:     move Σ M toward Z one unit at a time, cheapest first
//! ```
//!
//! Errors are exact integers: |p_i − M_i/Z|/2 scaled by 2Zt is
//! |Z a_i − M_i t| (`kern`). The output satisfies `tv_optimal_out`
//! (Σ M = Z, |M_i − Z p_i| ≤ 1), from which `lemma_optimal` proves
//! TV-optimality (Theorem 4.7). For TV the pruning loop never fires.

use vstd::prelude::*;

verus! {

#[cfg(verus_keep_ghost)]
use crate::optas::ztype::{wsum_nat, lemma_w_le_sum};
#[cfg(verus_keep_ghost)]
use crate::optas::divergences::*;
#[cfg(verus_keep_ghost)]
use crate::optas::utils::normalize_vector;
use crate::optas::utils::{argmin2, argmin};
#[cfg(verus_keep_ghost)]
use crate::fldr_helper::lemma_nat_mul_real_cast;

// ── Scalar error terms ────────────────────────────────────────────────────────

/// The paper's ∞, larger than any finite error (all of which are ≤ t ≤ 2^124 < 2^125).
pub open spec fn inf() -> int { 0x20000000000000000000000000000000 }

pub open spec fn iabs(x: int) -> int { if x >= 0 { x } else { -x } }

/// |Z a − m t|: the TV error of M_i = m, scaled by 2Zt.
pub open spec fn kern(z: nat, ai: nat, t: nat, m: int) -> int {
    iabs((z * ai) as int - m * (t as int))
}

/// `get_delta_error`: the change in error from M_i = m to m + d (d = ±1).
pub open spec fn derr(z: nat, ai: nat, t: nat, m: int, d: int) -> int {
    if d == -1 && m == 0 {
        inf()
    } else if d == 1 && m == z {
        inf()
    } else {
        kern(z, ai, t, m + d) - kern(z, ai, t, m)
    }
}

/// ⌊Z a_i / t⌋ and Z a_i mod t.
pub open spec fn ofl(a: Seq<u128>, t: nat, z: nat, i: nat) -> nat { (z * (a[i as int] as nat)) / t }
pub open spec fn orm(a: Seq<u128>, t: nat, z: nat, i: nat) -> nat { (z * (a[i as int] as nat)) % t }

/// Each M_i is ⌊Z p_i⌋, or ⌊Z p_i⌋ + 1 when Z p_i is not an integer.
pub open spec fn near(a: Seq<u128>, t: nat, z: nat, m: Seq<u128>) -> bool {
    &&& m.len() == a.len()
    &&& forall |i: nat| i < m.len() ==>
        (#[trigger] m[i as int]) == ofl(a, t, z, i) || (m[i as int] == ofl(a, t, z, i) + 1 && orm(a, t, z, i) > 0)
}

/// Rounded-up labels have remainders at least those of rounded-down labels.
pub open spec fn exch(a: Seq<u128>, t: nat, z: nat, m: Seq<u128>) -> bool {
    forall |i: nat, j: nat| i < m.len() && j < m.len()
        && #[trigger] m[i as int] == ofl(a, t, z, i) + 1 && #[trigger] m[j as int] == ofl(a, t, z, j)
        ==> orm(a, t, z, j) <= orm(a, t, z, i)
}

/// Σ_{i ≥ r} |Z a_i − M_i t|: 2Zt times the L1 half of the TV distance.
pub open spec fn cost(a: Seq<u128>, t: nat, z: nat, m: Seq<u128>, r: nat) -> int
    decreases m.len() - r,
{
    if r >= m.len() { 0 } else { kern(z, a[r as int] as nat, t, m[r as int] as int) + cost(a, t, z, m, r + 1) }
}

/// The target p_i = a_i / t.
pub open spec fn ratio(a: Seq<u128>, t: nat) -> spec_fn(nat) -> real {
    |i: nat| (a[i as int] as real) / (t as real)
}

pub open spec fn flsum(a: Seq<u128>, t: nat, z: nat, r: nat) -> nat
    decreases a.len() - r,
{
    if r >= a.len() { 0 } else { ofl(a, t, z, r) + flsum(a, t, z, r + 1) }
}

pub open spec fn rmsum(a: Seq<u128>, t: nat, z: nat, r: nat) -> nat
    decreases a.len() - r,
{
    if r >= a.len() { 0 } else { orm(a, t, z, r) + rmsum(a, t, z, r + 1) }
}

// ── Classification of the error changes ──────────────────────────────────────

/// Under `near`, the error changes are: rounding up a rounded-down label costs
/// t − 2ρ (or ∞ only when ρ = 0); rounding it down costs ≥ t; rounding down a
/// rounded-up label costs 2ρ − t, and rounding it up costs ≥ t.
proof fn lemma_derr(z: nat, ai: nat, t: nat, m: nat)
    requires
        0 < t <= 0x10000000000000000000000000000000, ai <= t,
        m == (z * ai) / t || (m == (z * ai) / t + 1 && (z * ai) % t > 0),
    ensures
        m <= z,
        m == (z * ai) / t ==> derr(z, ai, t, m as int, 1) == t - 2 * ((z * ai) % t)
            || (derr(z, ai, t, m as int, 1) == inf() && (z * ai) % t == 0),
        m == (z * ai) / t ==> derr(z, ai, t, m as int, -1) == t || derr(z, ai, t, m as int, -1) == inf(),
        m != (z * ai) / t ==> derr(z, ai, t, m as int, 1) == t || derr(z, ai, t, m as int, 1) == inf(),
        m != (z * ai) / t ==> derr(z, ai, t, m as int, -1) == 2 * ((z * ai) % t) - t,
        derr(z, ai, t, m as int, 1) > -(t as int),
        derr(z, ai, t, m as int, -1) >= -(t as int),
        derr(z, ai, t, m as int, 1) <= inf(),
        derr(z, ai, t, m as int, -1) <= inf(),
        derr(z, ai, t, m as int, 1) >= t ==> derr(z, ai, t, m as int, 1) == t || derr(z, ai, t, m as int, 1) == inf(),
{
    let x = z * ai;
    let f = x / t;
    let rho = x % t;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, t as int);
    assert(x <= z * t) by(nonlinear_arith) requires ai <= t, x == z * ai;
    assert(f <= z) by(nonlinear_arith) requires x == t * f + rho, rho >= 0, x <= z * t, t > 0;
    if f == z {
        assert(rho == 0) by(nonlinear_arith) requires x == t * f + rho, x <= z * t, f == z, rho >= 0;
    }
    if m == f + 1 {
        assert(f < z) by(nonlinear_arith) requires x == t * f + rho, rho > 0, x <= z * t, t > 0;
    }
    assert(x as int - (f as int) * (t as int) == rho
        && x as int - (f as int + 1) * (t as int) == rho - t
        && x as int - (f as int - 1) * (t as int) == rho + t
        && x as int - (f as int + 2) * (t as int) == rho - 2 * t) by(nonlinear_arith)
        requires x == t * f + rho;
}

// ── Sums ──────────────────────────────────────────────────────────────────────

/// t·Σ⌊Z a_i/t⌋ + Σ(Z a_i mod t) = Z·Σ a_i.
proof fn lemma_split_sum(a: Seq<u128>, t: nat, z: nat, r: nat)
    requires t > 0,
    ensures t * flsum(a, t, z, r) + rmsum(a, t, z, r) == z * wsum_nat(a, r),
    decreases a.len() - r,
{
    if r < a.len() {
        lemma_split_sum(a, t, z, r + 1);
        let ai = a[r as int] as nat;
        let x = z * ai;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, t as int);
        lemma_split_step(t, z, ai, x, x / t, x % t, flsum(a, t, z, r + 1), rmsum(a, t, z, r + 1), wsum_nat(a, r + 1));
        assert(flsum(a, t, z, r) == x / t + flsum(a, t, z, r + 1));
        assert(rmsum(a, t, z, r) == x % t + rmsum(a, t, z, r + 1));
        assert(wsum_nat(a, r) == ai + wsum_nat(a, r + 1));
    } else {
        assert(flsum(a, t, z, r) == 0 && rmsum(a, t, z, r) == 0 && wsum_nat(a, r) == 0);
        assert(t * 0 == 0 && z * 0 == 0);
    }
}

proof fn lemma_split_step(t: nat, z: nat, ai: nat, x: nat, f: nat, rho: nat, f1: nat, r1: nat, w1: nat)
    requires x == t * f + rho, t * f1 + r1 == z * w1, x == z * ai,
    ensures t * (f + f1) + (rho + r1) == z * (ai + w1),
{
    assert(t * (f + f1) + (rho + r1) == z * (ai + w1)) by(nonlinear_arith)
        requires x == t * f + rho, t * f1 + r1 == z * w1, x == z * ai;
}

/// If no rounded-down label has a positive remainder, the rounded-up labels
/// carry all the remainder: Σρ ≤ (t − 1)·Σ(M − ⌊Zp⌋).
proof fn lemma_rm_le(a: Seq<u128>, t: nat, z: nat, m: Seq<u128>, r: nat)
    requires
        t > 0, near(a, t, z, m), r <= m.len(),
        forall |i: nat| i < m.len() && #[trigger] m[i as int] == ofl(a, t, z, i) ==> orm(a, t, z, i) == 0,
    ensures
        wsum_nat(m, r) >= flsum(a, t, z, r),
        rmsum(a, t, z, r) <= (t - 1) * (wsum_nat(m, r) - flsum(a, t, z, r)),
    decreases m.len() - r,
{
    if r < m.len() {
        lemma_rm_le(a, t, z, m, r + 1);
        let x = z * (a[r as int] as nat);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, t as int);
        let v: int = m[r as int] as int - ofl(a, t, z, r) as int;
        let d1: int = wsum_nat(m, r + 1) as int - flsum(a, t, z, r + 1) as int;
        let rho = orm(a, t, z, r);
        assert(rho < t) by { vstd::arithmetic::div_mod::lemma_mod_bound(x as int, t as int); }
        assert(m[r as int] == ofl(a, t, z, r) || m[r as int] == ofl(a, t, z, r) + 1);
        assert(rho <= (t - 1) * v) by {
            if v == 0 {
                assert(m[r as int] == ofl(a, t, z, r));
                assert(rho == 0);
                assert((t - 1) * v == 0) by(nonlinear_arith) requires v == 0;
            } else {
                assert(v == 1);
                assert((t - 1) * v == t - 1) by(nonlinear_arith) requires v == 1;
            }
        }
        assert(rho + rmsum(a, t, z, r + 1) <= (t - 1) * (v + d1)) by(nonlinear_arith)
            requires rho <= (t - 1) * v, rmsum(a, t, z, r + 1) <= (t - 1) * d1;
    }
}

proof fn lemma_m_eq_fl(a: Seq<u128>, t: nat, z: nat, m: Seq<u128>, r: nat)
    requires
        near(a, t, z, m), r <= m.len(),
        forall |i: nat| i < m.len() ==> #[trigger] m[i as int] == ofl(a, t, z, i),
    ensures wsum_nat(m, r) == flsum(a, t, z, r),
    decreases m.len() - r,
{
    if r < m.len() { lemma_m_eq_fl(a, t, z, m, r + 1); }
}

/// A shortfall leaves a rounded-down label with a positive remainder.
proof fn lemma_exists_up(a: Seq<u128>, t: nat, z: nat, m: Seq<u128>) -> (i: nat)
    requires t > 0, near(a, t, z, m), wsum_nat(a, 0) == t, wsum_nat(m, 0) < z,
    ensures i < m.len(), m[i as int] == ofl(a, t, z, i), orm(a, t, z, i) > 0,
{
    if forall |i: nat| i < m.len() && #[trigger] m[i as int] == ofl(a, t, z, i) ==> orm(a, t, z, i) == 0 {
        lemma_rm_le(a, t, z, m, 0);
        lemma_split_sum(a, t, z, 0);
        let fs = flsum(a, t, z, 0);
        let rs = rmsum(a, t, z, 0);
        let ms = wsum_nat(m, 0);
        assert(false) by(nonlinear_arith)
            requires t * fs + rs == z * t, rs <= (t - 1) * (ms - fs), ms >= fs, ms < z, t > 0;
        0
    } else {
        choose |i: nat| i < m.len() && #[trigger] m[i as int] == ofl(a, t, z, i) && orm(a, t, z, i) > 0
    }
}

/// An excess leaves a rounded-up label.
proof fn lemma_exists_down(a: Seq<u128>, t: nat, z: nat, m: Seq<u128>) -> (i: nat)
    requires t > 0, near(a, t, z, m), wsum_nat(a, 0) == t, wsum_nat(m, 0) > z,
    ensures i < m.len(), m[i as int] == ofl(a, t, z, i) + 1,
{
    if forall |i: nat| i < m.len() ==> #[trigger] m[i as int] == ofl(a, t, z, i) {
        lemma_m_eq_fl(a, t, z, m, 0);
        lemma_split_sum(a, t, z, 0);
        let fs = flsum(a, t, z, 0);
        let rs = rmsum(a, t, z, 0);
        assert(false) by(nonlinear_arith)
            requires t * fs + rs == z * t, fs > z, t > 0, rs >= 0;
        0
    } else {
        let i = choose |i: nat| !(i < m.len() ==> #[trigger] m[i as int] == ofl(a, t, z, i));
        i
    }
}

proof fn lemma_wsum_update(m: Seq<u128>, j: nat, v: u128, r: nat)
    requires j < m.len(), r <= m.len(),
    ensures
        r <= j ==> wsum_nat(m.update(j as int, v), r) + m[j as int] == wsum_nat(m, r) + v,
        r > j ==> wsum_nat(m.update(j as int, v), r) == wsum_nat(m, r),
    decreases m.len() - r,
{
    if r < m.len() { lemma_wsum_update(m, j, v, r + 1); }
}

// ── Optimality ────────────────────────────────────────────────────────────────

/// The smallest remainder among rounded-up labels ≥ r (t if there are none).
pub open spec fn thr(a: Seq<u128>, t: nat, z: nat, m: Seq<u128>, r: nat) -> nat
    decreases m.len() - r,
{
    if r >= m.len() {
        t
    } else if m[r as int] == ofl(a, t, z, r) + 1 {
        let rest = thr(a, t, z, m, r + 1);
        if orm(a, t, z, r) < rest { orm(a, t, z, r) } else { rest }
    } else {
        thr(a, t, z, m, r + 1)
    }
}

/// θ separates the remainders: rounded-down ≤ θ ≤ rounded-up, and θ ≤ t.
proof fn lemma_thr(a: Seq<u128>, t: nat, z: nat, m: Seq<u128>, r: nat)
    requires t > 0, near(a, t, z, m), exch(a, t, z, m),
    ensures
        thr(a, t, z, m, r) <= t,
        forall |i: nat| r <= i < m.len() && #[trigger] m[i as int] == ofl(a, t, z, i) + 1
            ==> thr(a, t, z, m, r) <= orm(a, t, z, i),
        forall |j: nat| j < m.len() && #[trigger] m[j as int] == ofl(a, t, z, j)
            ==> orm(a, t, z, j) <= thr(a, t, z, m, r),
    decreases m.len() - r,
{
    if r < m.len() {
        lemma_thr(a, t, z, m, r + 1);
        assert forall |j: nat| j < m.len() && #[trigger] m[j as int] == ofl(a, t, z, j)
            implies orm(a, t, z, j) <= thr(a, t, z, m, r) by {
            if m[r as int] == ofl(a, t, z, r) + 1 {
                assert(orm(a, t, z, j) <= orm(a, t, z, r));
            }
        }
    } else {
        assert forall |j: nat| j < m.len() && #[trigger] m[j as int] == ofl(a, t, z, j)
            implies orm(a, t, z, j) <= thr(a, t, z, m, r) by {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod((z * (a[j as int] as nat)) as int, t as int);
        }
    }
}

/// One label: |ρ − u t| ≥ |ρ − v t| + (t − 2θ)(u − v) for every integer u,
/// where v ∈ {0, 1} is the chosen rounding and θ separates as in `lemma_thr`.
proof fn lemma_kern_line(rho: int, t: int, th: int, v: int, u: int)
    requires
        0 <= rho < t, 0 <= th <= t,
        v == 0 || v == 1,
        v == 0 ==> rho <= th,
        v == 1 ==> th <= rho,
    ensures iabs(rho - u * t) >= iabs(rho - v * t) + (t - 2 * th) * (u - v),
{
    if u >= 1 {
        assert(rho - u * t < 0) by(nonlinear_arith) requires u >= 1, rho < t, t > 0;
        if v == 0 {
            assert(u * t - rho >= rho + (t - 2 * th) * u) by(nonlinear_arith)
                requires u >= 1, rho <= th, rho >= 0;
        } else {
            assert(u * t - rho >= (t - rho) + (t - 2 * th) * (u - 1)) by(nonlinear_arith)
                requires u >= 1, th >= 0;
        }
    } else {
        assert(rho - u * t >= 0) by(nonlinear_arith) requires u <= 0, rho >= 0, t > 0;
        if v == 0 {
            assert(rho - u * t >= rho + (t - 2 * th) * u) by(nonlinear_arith)
                requires u <= 0, th <= t;
        } else {
            assert(rho - u * t >= (t - rho) + (t - 2 * th) * (u - 1)) by(nonlinear_arith)
                requires u <= 0, th <= rho, th <= t, rho < t;
        }
    }
}

/// cost(M') ≥ cost(M) + (t − 2θ)(ΣM' − ΣM).
proof fn lemma_cost_line(a: Seq<u128>, t: nat, z: nat, m: Seq<u128>, m2: Seq<u128>, th: nat, r: nat)
    requires
        t > 0, near(a, t, z, m), m2.len() == m.len(), r <= m.len(), th <= t,
        forall |i: nat| i < m.len() && #[trigger] m[i as int] == ofl(a, t, z, i) + 1 ==> th <= orm(a, t, z, i),
        forall |j: nat| j < m.len() && #[trigger] m[j as int] == ofl(a, t, z, j) ==> orm(a, t, z, j) <= th,
    ensures
        cost(a, t, z, m2, r) >= cost(a, t, z, m, r) + (t - 2 * th) * (wsum_nat(m2, r) - wsum_nat(m, r)),
    decreases m.len() - r,
{
    if r < m.len() {
        lemma_cost_line(a, t, z, m, m2, th, r + 1);
        let ai = a[r as int] as nat;
        let x = z * ai;
        let f = ofl(a, t, z, r);
        let rho = orm(a, t, z, r);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, t as int);
        let v: int = m[r as int] as int - f as int;
        let u: int = m2[r as int] as int - f as int;
        lemma_kern_line(rho as int, t as int, th as int, v, u);
        assert(kern(z, ai, t, m2[r as int] as int) == iabs(rho - u * t)) by(nonlinear_arith)
            requires x == t * f + rho, u == m2[r as int] as int - f, x == z * ai;
        assert(kern(z, ai, t, m[r as int] as int) == iabs(rho - v * t)) by(nonlinear_arith)
            requires x == t * f + rho, v == m[r as int] as int - f, x == z * ai;
        let c1 = cost(a, t, z, m2, r + 1);
        let c0 = cost(a, t, z, m, r + 1);
        let s = t - 2 * th;
        let d1 = wsum_nat(m2, r + 1) - wsum_nat(m, r + 1);
        assert(s * (u - v) + s * d1 == s * (u - v + d1)) by(nonlinear_arith);
        assert(cost(a, t, z, m2, r) == kern(z, ai, t, m2[r as int] as int) + c1);
        assert(cost(a, t, z, m, r) == kern(z, ai, t, m[r as int] as int) + c0);
        assert(wsum_nat(m2, r) - wsum_nat(m, r) == (u - v) + d1);
        let k2 = kern(z, ai, t, m2[r as int] as int);
        let k0 = kern(z, ai, t, m[r as int] as int);
        let w2 = wsum_nat(m2, r) - wsum_nat(m, r);
        assert(k2 + c1 >= k0 + c0 + s * w2) by(nonlinear_arith)
            requires k2 >= k0 + s * (u - v), c1 >= c0 + s * d1, w2 == (u - v) + d1;
    } else {
        assert(wsum_nat(m2, r) == 0 && wsum_nat(m, r) == 0 && cost(a, t, z, m2, r) == 0 && cost(a, t, z, m, r) == 0);
        assert((t - 2 * th) * 0 == 0);
    }
}

/// M has the least TV cost among all Z-type distributions.
proof fn lemma_cost_optimal(a: Seq<u128>, t: nat, z: nat, m: Seq<u128>, m2: Seq<u128>)
    requires
        t > 0, near(a, t, z, m), exch(a, t, z, m),
        wsum_nat(m, 0) == z, m2.len() == m.len(), wsum_nat(m2, 0) == z,
    ensures cost(a, t, z, m, 0) <= cost(a, t, z, m2, 0),
{
    lemma_thr(a, t, z, m, 0);
    let th = thr(a, t, z, m, 0);
    lemma_cost_line(a, t, z, m, m2, th, 0);
    assert((t - 2 * th) * (wsum_nat(m2, 0) - wsum_nat(m, 0)) == 0) by(nonlinear_arith)
        requires wsum_nat(m2, 0) == wsum_nat(m, 0);
}

// ── TV in terms of the cost ───────────────────────────────────────────────────

/// kernel_tv(a_i/t, M_i/Z) = |Z a_i − M_i t| / (2Zt).
proof fn lemma_kernel_tv_kern(z: nat, ai: nat, t: nat, mi: nat)
    requires z > 0, t > 0,
    ensures kernel_tv((ai as real) / (t as real), (mi as real) / (z as real))
        == (kern(z, ai, t, mi as int) as real) / (2real * ((z * t) as real)),
{
    let zr = z as real;
    let tr = t as real;
    let zt = (z * t) as real;
    lemma_nat_mul_real_cast(z, t);
    lemma_nat_mul_real_cast(z, ai);
    lemma_nat_mul_real_cast(mi, t);
    assert(zt > 0real) by(nonlinear_arith) requires zt == zr * tr, zr > 0real, tr > 0real;
    let x = (z * ai) as real - (mi * t) as real;
    let d = (ai as real) / tr - (mi as real) / zr;
    assert(d == x / zt) by(nonlinear_arith)
        requires zt == zr * tr, zr > 0real, tr > 0real,
            x == (z * ai) as real - (mi * t) as real,
            (z * ai) as real == zr * (ai as real), (mi * t) as real == (mi as real) * tr,
            d == (ai as real) / tr - (mi as real) / zr;
    let k = kern(z, ai, t, mi as int);
    assert((k as real) == rabs(x));
    if x >= 0real {
        assert(rabs(d) == x / zt) by(nonlinear_arith) requires d == x / zt, x >= 0real, zt > 0real;
    } else {
        assert(rabs(d) == -x / zt) by(nonlinear_arith) requires d == x / zt, x < 0real, zt > 0real;
    }
    assert(rabs(x) / zt / 2real == rabs(x) / (2real * zt)) by(nonlinear_arith) requires zt > 0real;
}

/// TV(a/t, M/Z) = cost(M) / (2Zt).
pub proof fn lemma_tv_cost(a: Seq<u128>, t: nat, z: nat, m: Seq<u128>, r: nat)
    requires t > 0, z > 0, m.len() == a.len(), r <= m.len(),
    ensures tv(ratio(a, t), normalize_vector(z, m), a.len(), r)
        == (cost(a, t, z, m, r) as real) / (2real * ((z * t) as real)),
    decreases m.len() - r,
{
    let den = 2real * ((z * t) as real);
    lemma_nat_mul_real_cast(z, t);
    assert(den > 0real) by(nonlinear_arith) requires den == 2real * ((z * t) as real), (z * t) as real == (z as real) * (t as real), z > 0, t > 0;
    if r < m.len() {
        lemma_tv_cost(a, t, z, m, r + 1);
        lemma_kernel_tv_kern(z, a[r as int] as nat, t, m[r as int] as nat);
        let k = kern(z, a[r as int] as nat, t, m[r as int] as int);
        let c1 = cost(a, t, z, m, r + 1);
        assert(((k + c1) as real) == (k as real) + (c1 as real));
        assert((k as real) / den + (c1 as real) / den == ((k as real) + (c1 as real)) / den) by(nonlinear_arith)
            requires den > 0real;
    } else {
        assert(0real / den == 0real);
    }
}

proof fn lemma_psum_ratio(a: Seq<u128>, t: nat, r: nat)
    requires t > 0,
    ensures psum(ratio(a, t), a.len(), r) == (wsum_nat(a, r) as real) / (t as real),
    decreases a.len() - r,
{
    if r < a.len() {
        lemma_psum_ratio(a, t, r + 1);
        let tr = t as real;
        assert((a[r as int] as real) / tr + (wsum_nat(a, r + 1) as real) / tr
            == ((a[r as int] as nat + wsum_nat(a, r + 1)) as real) / tr) by(nonlinear_arith) requires tr > 0real;
    } else {
        assert(0real / (t as real) == 0real);
    }
}

proof fn lemma_psum_normalize(m: Seq<u128>, z: nat, n: nat, r: nat)
    requires z > 0, n == m.len(),
    ensures psum(normalize_vector(z, m), n, r) == (wsum_nat(m, r) as real) / (z as real),
    decreases n - r,
{
    if r < n {
        lemma_psum_normalize(m, z, n, r + 1);
        let zr = z as real;
        assert((m[r as int] as real) / zr + (wsum_nat(m, r + 1) as real) / zr
            == ((m[r as int] as nat + wsum_nat(m, r + 1)) as real) / zr) by(nonlinear_arith) requires zr > 0real;
    } else {
        assert(0real / (z as real) == 0real);
    }
}

/// Both p = a/Σa and M/Z (Σ M = Z) are distributions.
pub proof fn lemma_distributions(a: Seq<u128>, z: nat, m: Seq<u128>)
    requires wsum_nat(a, 0) > 0, z > 0, m.len() == a.len(), wsum_nat(m, 0) == z,
    ensures
        psum(ratio(a, wsum_nat(a, 0)), a.len(), 0) == 1real,
        psum(normalize_vector(z, m), a.len(), 0) == 1real,
{
    let t = wsum_nat(a, 0);
    lemma_psum_ratio(a, t, 0);
    lemma_psum_normalize(m, z, a.len(), 0);
    assert((t as real) / (t as real) == 1real) by(nonlinear_arith) requires t > 0;
    assert((z as real) / (z as real) == 1real) by(nonlinear_arith) requires z > 0;
}

/// Theorem 4.7 (TV): M from Algorithm 3 is closest to p among all Z-type
/// distributions, both as TV and as the positive part used by the specs.
pub proof fn lemma_optimal(a: Seq<u128>, z: nat, m: Seq<u128>, m2: Seq<u128>)
    requires
        wsum_nat(a, 0) > 0, z > 0,
        near(a, wsum_nat(a, 0), z, m), exch(a, wsum_nat(a, 0), z, m), wsum_nat(m, 0) == z,
        m2.len() == a.len(), wsum_nat(m2, 0) == z,
    ensures
        tv(ratio(a, wsum_nat(a, 0)), normalize_vector(z, m), a.len(), 0)
            <= tv(ratio(a, wsum_nat(a, 0)), normalize_vector(z, m2), a.len(), 0),
        tv_pos(normalize_vector(z, m), ratio(a, wsum_nat(a, 0)), a.len(), 0)
            <= tv_pos(normalize_vector(z, m2), ratio(a, wsum_nat(a, 0)), a.len(), 0),
{
    let t = wsum_nat(a, 0);
    lemma_cost_optimal(a, t, z, m, m2);
    lemma_tv_cost(a, t, z, m, 0);
    lemma_tv_cost(a, t, z, m2, 0);
    lemma_nat_mul_real_cast(z, t);
    let d = 2real * ((z * t) as real);
    assert(d > 0real) by(nonlinear_arith) requires d == 2real * ((z * t) as real), (z * t) as real == (z as real) * (t as real), z > 0, t > 0;
    let c1 = cost(a, t, z, m, 0) as real;
    let c2 = cost(a, t, z, m2, 0) as real;
    assert(c1 / d <= c2 / d) by(nonlinear_arith) requires c1 <= c2, d > 0real;
    lemma_distributions(a, z, m);
    lemma_distributions(a, z, m2);
    lemma_tv_pos_eq_tv(normalize_vector(z, m), ratio(a, t), a.len());
    lemma_tv_pos_eq_tv(normalize_vector(z, m2), ratio(a, t), a.len());
}

/// Theorem B.2's conclusion, |M_i − Z p_i| ≤ 1: the hypothesis of
/// Theorem 4.17 (`lemma_tv_bound` in approx.rs).
pub proof fn lemma_near_bound(a: Seq<u128>, z: nat, m: Seq<u128>)
    requires wsum_nat(a, 0) > 0, near(a, wsum_nat(a, 0), z, m),
    ensures
        psum(ratio(a, wsum_nat(a, 0)), a.len(), 0) == 1real,
        forall |i: nat| i < m.len() ==>
            -1real <= (m[i as int] as real) - (z as real) * #[trigger] ratio(a, wsum_nat(a, 0))(i) <= 1real,
{
    let t = wsum_nat(a, 0);
    lemma_psum_ratio(a, t, 0);
    assert((t as real) / (t as real) == 1real) by(nonlinear_arith) requires t > 0;
    assert forall |i: nat| i < m.len() implies
        -1real <= (m[i as int] as real) - (z as real) * #[trigger] ratio(a, t)(i) <= 1real by {
        let ai = a[i as int] as nat;
        let x = z * ai;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, t as int);
        let f = x / t;
        let rho = x % t;
        lemma_nat_mul_real_cast(z, ai);
        lemma_nat_mul_real_cast(t, f);
        let tr = t as real;
        assert((z as real) * ((ai as real) / tr) == (f as real) + (rho as real) / tr) by(nonlinear_arith)
            requires (x as real) == (z as real) * (ai as real), (x as real) == (t * f) as real + (rho as real),
                (t * f) as real == tr * (f as real), tr > 0real, x == t * f + rho;
        assert(0real <= (rho as real) / tr < 1real) by(nonlinear_arith) requires rho < t, tr == t as real, t > 0;
    }
}

// ── Executable ────────────────────────────────────────────────────────────────

/// Σ v, as u128 (for Σ v ≤ 2^125).
pub fn sum_u128(v: &Vec<u128>) -> (s: u128)
    requires v.len() < 0x4000000000000000, wsum_nat(v@, 0) <= 2 * 0x10000000000000000000000000000000,
    ensures s as nat == wsum_nat(v@, 0),
{
    let mut i = v.len();
    let mut s: u128 = 0;
    while i > 0
        invariant
            i <= v.len() < 0x4000000000000000,
            wsum_nat(v@, 0) <= 2 * 0x10000000000000000000000000000000,
            s as nat == wsum_nat(v@, i as nat),
        decreases i,
    {
        i = i - 1;
        proof { lemma_wsum_suffix_le(v@, i as nat); }
        s = s + v[i];
    }
    s
}

/// Σ_{r' ≥ r} ≤ Σ_{r' ≥ 0}.
pub proof fn lemma_wsum_suffix_le(v: Seq<u128>, r: nat)
    ensures wsum_nat(v, r) <= wsum_nat(v, 0),
    decreases r,
{
    if r > 0 && r <= v.len() {
        lemma_wsum_suffix_le(v, (r - 1) as nat);
    }
}

/// ⌊z·a / t⌋ and z·a mod t, without forming z·a: double-and-add over the
/// bits of z, keeping every intermediate below 2t.
pub fn muldivmod(z: u128, a: u128, t: u128) -> (r: (u128, u128))
    requires 0 < t <= 0x10000000000000000000000000000000, a <= t, z <= 0x10000000000000000000000000000000,
    ensures
        (r.0 as nat) * (t as nat) + (r.1 as nat) == (z as nat) * (a as nat),
        r.1 < t,
        r.0 <= z,
{
    let mut zz: u128 = z;
    // low·a = q·t + rr, where low is the bits of z already consumed
    let mut q: u128 = 0;
    let mut rr: u128 = 0;
    // p·a = qa·t + ra, where p = 2^(bits consumed)
    let mut qa: u128 = 0;
    let mut ra: u128 = a;
    if ra == t {
        qa = 1;
        ra = 0;
    }
    let ghost mut p: nat = 1;
    let ghost mut low: nat = 0;
    let ghost zn = z as nat;
    let ghost an = a as nat;
    let ghost tn = t as nat;
    proof {
        assert(1 * an == (qa as nat) * tn + (ra as nat)) by(nonlinear_arith)
            requires (an == tn && qa == 1 && ra == 0) || (an < tn && qa == 0 && ra as nat == an);
    }
    while zz > 0
        invariant
            0 < t <= 0x10000000000000000000000000000000, a <= t, z <= 0x10000000000000000000000000000000, zn == z, an == a, tn == t,
            zn == (zz as nat) * p + low, low < p, p >= 1,
            zz > 0 ==> p <= zn,
            low * an == (q as nat) * tn + (rr as nat), rr < t, (q as nat) <= low,
            p * an == (qa as nat) * tn + (ra as nat), ra < t, (qa as nat) <= p,
        decreases zz,
    {
        let ghost q0 = q as nat;
        let ghost r0 = rr as nat;
        let ghost qa0 = qa as nat;
        let ghost ra0 = ra as nat;
        let ghost p0 = p;
        let ghost low0 = low;
        let ghost zz0 = zz as nat;
        if zz % 2 == 1 {
            // low ← low + p
            proof {
                assert(low + p <= zn) by(nonlinear_arith) requires zn == zz0 * p + low, zz0 >= 1, p >= 1;
                assert((q as nat) + (qa as nat) <= zn) by(nonlinear_arith)
                    requires (q as nat) <= low, (qa as nat) <= p, low + p <= zn;
            }
            rr = rr + ra;
            q = q + qa;
            if rr >= t {
                rr = rr - t;
                q = q + 1;
                proof {
                    assert((q as nat) * tn + (rr as nat) == (q0 + qa0) * tn + (r0 + ra0)) by(nonlinear_arith)
                        requires q as nat == q0 + qa0 + 1, rr as nat + tn == r0 + ra0;
                }
            }
            proof {
                low = low + p;
                assert(low * an == (q as nat) * tn + (rr as nat)) by(nonlinear_arith)
                    requires low == low0 + p0, low0 * an == q0 * tn + r0, p0 * an == qa0 * tn + ra0,
                        (q as nat) * tn + (rr as nat) == (q0 + qa0) * tn + (r0 + ra0);
                assert((q as nat) <= low) by(nonlinear_arith)
                    requires low * an == (q as nat) * tn + (rr as nat), an <= tn, tn > 0;
            }
        }
        // p ← 2p
        proof {
            assert(2 * p <= 2 * zn) by(nonlinear_arith) requires zz0 >= 1, zn == zz0 * p0 + low0, p == p0;
            assert(2 * (qa as nat) <= 2 * zn) by(nonlinear_arith) requires (qa as nat) <= p, 2 * p <= 2 * zn;
        }
        let ghost qa1 = qa as nat;
        let ghost ra1 = ra as nat;
        ra = 2 * ra;
        qa = 2 * qa;
        if ra >= t {
            ra = ra - t;
            qa = qa + 1;
            proof {
                assert((qa as nat) * tn + (ra as nat) == (2 * qa1) * tn + 2 * ra1) by(nonlinear_arith)
                    requires qa as nat == 2 * qa1 + 1, ra as nat + tn == 2 * ra1;
            }
        }
        zz = zz / 2;
        proof {
            let pp = p;
            p = 2 * pp;
            assert(p * an == (qa as nat) * tn + (ra as nat)) by(nonlinear_arith)
                requires p == 2 * pp, pp * an == qa1 * tn + ra1,
                    (qa as nat) * tn + (ra as nat) == (2 * qa1) * tn + 2 * ra1;
            assert((qa as nat) <= p) by(nonlinear_arith)
                requires p * an == (qa as nat) * tn + (ra as nat), an <= tn, tn > 0;
            // z = zz·p + low with the new zz, p
            if zz0 % 2 == 1 {
                assert(zn == (zz as nat) * p + low) by(nonlinear_arith)
                    requires zn == zz0 * pp + low0, low == low0 + pp, zz0 == 2 * (zz as nat) + 1, p == 2 * pp;
                assert(low < p) by(nonlinear_arith) requires low == low0 + pp, low0 < pp, p == 2 * pp;
            } else {
                assert(zn == (zz as nat) * p + low) by(nonlinear_arith)
                    requires zn == zz0 * pp + low0, low == low0, zz0 == 2 * (zz as nat), p == 2 * pp;
                assert(low < p) by(nonlinear_arith) requires low == low0, low0 < pp, p == 2 * pp;
            }
            if zz > 0 {
                assert(p <= zn) by(nonlinear_arith) requires zn == (zz as nat) * p + low, zz >= 1;
            }
        }
    }
    proof {
        assert(low == zn) by(nonlinear_arith) requires zn == 0 * p + low;
        assert((q as nat) <= zn);
    }
    (q, rr)
}

/// The error change, from the quotient and remainder of z·a by t:
/// kern(m) = |(q − m)·t + r|.
pub proof fn lemma_derr_qr(z: nat, ai: nat, t: nat, m: int, d: int, q: nat, r: nat)
    requires t > 0, z * ai == q * t + r, r < t, d == 1 || d == -1,
        !(d == -1 && m == 0), !(d == 1 && m == z),
    ensures derr(z, ai, t, m, d) == (
        if d == 1 {
            if m < q { -(t as int) } else if m > q { t as int } else { t - 2 * r }
        } else {
            if m <= q { t as int } else if m > q + 1 { -(t as int) } else { 2 * r - t }
        }),
{
    lemma_kern_qr(z, ai, t, m, q, r);
    lemma_kern_qr(z, ai, t, m + d, q, r);
    if m + d <= q && m <= q {
        assert(((q - (m + d)) * t + r) - ((q - m) * t + r) == -d * t) by(nonlinear_arith);
    } else if m + d > q && m > q {
        assert(((m + d - q) * t - r) - ((m - q) * t - r) == d * t) by(nonlinear_arith);
    } else if m + d > q {
        assert(m == q && d == 1);
        assert(((m + d - q) * t - r) - ((q - m) * t + r) == t - 2 * r) by(nonlinear_arith) requires m == q, d == 1;
    } else {
        assert(m == q + 1 && d == -1);
        assert(((q - (m + d)) * t + r) - ((m - q) * t - r) == 2 * r - t) by(nonlinear_arith) requires m == q + 1, d == -1;
    }
}

proof fn lemma_kern_qr(z: nat, ai: nat, t: nat, m: int, q: nat, r: nat)
    requires t > 0, z * ai == q * t + r, r < t,
    ensures kern(z, ai, t, m) == if m <= q { (q - m) * t + r } else { (m - q) * t - r },
{
    assert((z * ai) as int - m * (t as int) == (q - m) * t + r) by(nonlinear_arith) requires z * ai == q * t + r;
    if m <= q {
        assert((q - m) * t + r >= 0) by(nonlinear_arith) requires m <= q, t > 0, r >= 0;
    } else {
        assert((q - m) * t + r < 0) by(nonlinear_arith) requires m > q, t > r;
        assert(-((q - m) * t + r) == (m - q) * t - r) by(nonlinear_arith);
    }
}

/// `get_delta_error(Z, p_i, M, delta, kernel_tv)`, scaled by 2Zt: the change
/// in error from M_i = m to m + delta (delta = ±1), or ∞ at the boundary.
pub fn get_delta_error(z: u128, ai: u128, t: u128, m: u128, delta: i8) -> (d: i128)
    requires 0 < t <= 0x10000000000000000000000000000000, z <= 0x10000000000000000000000000000000, ai <= t, m <= z, delta == 1 || delta == -1,
    ensures d as int == derr(z as nat, ai as nat, t as nat, m as int, delta as int),
{
    if delta == -1 && m == 0 {
        return 0x20000000000000000000000000000000;
    }
    if delta == 1 && m == z {
        return 0x20000000000000000000000000000000;
    }
    let (q, r) = muldivmod(z, ai, t);
    proof { lemma_derr_qr(z as nat, ai as nat, t as nat, m as int, delta as int, q as nat, r as nat); }
    let ti = t as i128;
    if delta == 1 {
        if m < q { -ti } else if m > q { ti } else { ti - 2 * (r as i128) }
    } else {
        if m <= q { ti } else if m > q + 1 { -ti } else { 2 * (r as i128) - ti }
    }
}

/// The p_target of the original, as weights a (p_i = a_i / Σa), and Z.
pub open spec fn wf_target(a: Seq<u128>, z: nat) -> bool {
    &&& a.len() >= 1
    &&& a.len() < 0x4000000000000000
    &&& 0 < wsum_nat(a, 0) <= 0x10000000000000000000000000000000
    &&& 1 <= z <= 0x10000000000000000000000000000000
}

/// What Algorithm 3 returns (TV): Σ M = Z, `near` and `exch`.
pub open spec fn tv_optimal_out(a: Seq<u128>, z: nat, m: Seq<u128>) -> bool {
    &&& m.len() == a.len()
    &&& wsum_nat(m, 0) == z
    &&& near(a, wsum_nat(a, 0), z, m)
    &&& exch(a, wsum_nat(a, 0), z, m)
}

/// `get_initial_Ms`: round each Z p_i down, then up if that is closer.
pub open spec fn initial_out(a: Seq<u128>, t: nat, z: nat, m: Seq<u128>) -> bool {
    &&& m.len() == a.len()
    &&& forall |k: nat| k < a.len() ==>
        (#[trigger] m[k as int] == ofl(a, t, z, k) + 1 && 2 * orm(a, t, z, k) > t)
        || (m[k as int] == ofl(a, t, z, k) && 2 * orm(a, t, z, k) <= t)
}

pub fn get_initial_ms(z: u128, a: &Vec<u128>, t: u128) -> (m: Vec<u128>)
    requires wf_target(a@, z as nat), t as nat == wsum_nat(a@, 0),
    ensures initial_out(a@, t as nat, z as nat, m@), near(a@, t as nat, z as nat, m@), exch(a@, t as nat, z as nat, m@),
{
    let n = a.len();
    let ghost tn = t as nat;
    let ghost zn = z as nat;
    let ghost av = a@;
    assert forall |i: nat| i < n implies (#[trigger] av[i as int]) <= t by {
        lemma_w_le_sum(av, 0, i);
    }
    let mut m: Vec<u128> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == a.len(), av == a@, i <= n, m.len() == i,
            tn == t, zn == z, 0 < t <= 0x10000000000000000000000000000000, 1 <= z <= 0x10000000000000000000000000000000,
            forall |i: nat| i < n ==> (#[trigger] av[i as int]) <= t,
            forall |k: nat| k < i ==>
                (#[trigger] m@[k as int] == ofl(av, tn, zn, k) + 1 && 2 * orm(av, tn, zn, k) > tn)
                || (m@[k as int] == ofl(av, tn, zn, k) && 2 * orm(av, tn, zn, k) <= tn),
        decreases n - i,
    {
        let ai = a[i];
        let (f, _rho) = muldivmod(z, ai, t);
        proof {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                ((zn * (ai as nat)) as int), tn as int, f as int, _rho as int);
            lemma_derr(zn, ai as nat, tn, f as nat);
        }
        let mut mi: u128 = f;
        if get_delta_error(z, ai, t, mi, 1) < 0 {
            mi = mi + 1;
        }
        m.push(mi);
        i = i + 1;
    }
    proof {
        assert(near(av, tn, zn, m@));
        assert(exch(av, tn, zn, m@));
    }
    m
}

/// `find_optimal_indexes`: the lowest-cost decrement and increment, at
/// distinct labels.
pub fn find_optimal_indexes(errs_dec: &Vec<i128>, errs_inc: &Vec<i128>) -> (r: (usize, usize))
    requires
        errs_dec.len() == errs_inc.len(), errs_dec.len() >= 2,
        forall |i: int| 0 <= i < errs_dec.len() ==> -inf() <= #[trigger] errs_dec[i] <= inf(),
        forall |i: int| 0 <= i < errs_inc.len() ==> -inf() <= #[trigger] errs_inc[i] <= inf(),
    ensures
        r.0 < errs_dec.len(), r.1 < errs_dec.len(), r.0 != r.1,
        forall |i: int, j: int| 0 <= i < errs_dec.len() && 0 <= j < errs_dec.len() && i != j ==>
            errs_dec[r.0 as int] + errs_inc[r.1 as int] <= #[trigger] errs_dec[i] + #[trigger] errs_inc[j],
{
    let (j_min_dec0, j_min_dec1) = argmin2(errs_dec);
    let (j_min_inc0, j_min_inc1) = argmin2(errs_inc);
    if j_min_dec0 != j_min_inc0 {
        (j_min_dec0, j_min_inc0)
    } else {
        let cost0 = errs_dec[j_min_dec0] + errs_inc[j_min_inc1];
        let cost1 = errs_dec[j_min_dec1] + errs_inc[j_min_inc0];
        // A pair (i, j), i ≠ j, costs at least cost0 if i is the common
        // minimum (then j is not) and at least cost1 otherwise.
        if cost0 <= cost1 { (j_min_dec0, j_min_inc1) } else { (j_min_dec1, j_min_inc0) }
    }
}

/// `prune_initial_Ms`. For TV the loop body is unreachable: a swap lowering
/// the error would need a rounded-up label with a smaller remainder than a
/// rounded-down one, which `exch` rules out. So the input comes back, and the
/// original's MAXITER assertion is not needed. The original also runs this
/// for n = 1, where `argmin2` returns index −1;
/// here it is skipped.
pub fn prune_initial_ms(z: u128, a: &Vec<u128>, t: u128, ms: Vec<u128>) -> (m: Vec<u128>)
    requires
        wf_target(a@, z as nat), t as nat == wsum_nat(a@, 0), ms.len() == a.len(),
        near(a@, t as nat, z as nat, ms@), exch(a@, t as nat, z as nat, ms@),
    ensures m@ == ms@,
{
    let n = a.len();
    let mut m = ms;
    if n < 2 {
        return m;
    }
    let ghost tn = t as nat;
    let ghost zn = z as nat;
    let ghost av = a@;
    let ghost m_in = m@;
    assert forall |i: nat| i < n implies (#[trigger] av[i as int]) <= t by {
        lemma_w_le_sum(av, 0, i);
    }
    let mut errs_dec: Vec<i128> = Vec::new();
    let mut errs_inc: Vec<i128> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == a.len(), av == a@, i <= n, m.len() == n, m@ == m_in,
            errs_dec.len() == i, errs_inc.len() == i,
            tn == t, zn == z, 0 < t <= 0x10000000000000000000000000000000, 1 <= z <= 0x10000000000000000000000000000000,
            forall |i: nat| i < n ==> (#[trigger] av[i as int]) <= t,
            near(av, tn, zn, m@),
            forall |k: nat| k < i ==> #[trigger] errs_dec@[k as int] as int == derr(zn, av[k as int] as nat, tn, m@[k as int] as int, -1),
            forall |k: nat| k < i ==> #[trigger] errs_inc@[k as int] as int == derr(zn, av[k as int] as nat, tn, m@[k as int] as int, 1),
            forall |k: int| 0 <= k < i ==> -inf() <= #[trigger] errs_dec@[k] <= inf(),
            forall |k: int| 0 <= k < i ==> -inf() <= #[trigger] errs_inc@[k] <= inf(),
        decreases n - i,
    {
        proof { lemma_derr(zn, av[i as int] as nat, tn, m@[i as int] as nat); }
        errs_dec.push(get_delta_error(z, a[i], t, m[i], -1));
        errs_inc.push(get_delta_error(z, a[i], t, m[i], 1));
        i = i + 1;
    }
    let (mut j_min_dec, mut j_min_inc) = find_optimal_indexes(&errs_dec, &errs_inc);
    while errs_dec[j_min_dec] + errs_inc[j_min_inc] < 0
        invariant
            n == a.len(), av == a@, m.len() == n, n >= 2, m@ == m_in,
            errs_dec.len() == n, errs_inc.len() == n, j_min_dec < n, j_min_inc < n,
            tn == t, zn == z, 0 < t <= 0x10000000000000000000000000000000, 1 <= z <= 0x10000000000000000000000000000000,
            forall |i: nat| i < n ==> (#[trigger] av[i as int]) <= t,
            near(av, tn, zn, m@),
            exch(av, tn, zn, m@),
            forall |k: nat| k < n ==> #[trigger] errs_dec@[k as int] as int == derr(zn, av[k as int] as nat, tn, m@[k as int] as int, -1),
            forall |k: nat| k < n ==> #[trigger] errs_inc@[k as int] as int == derr(zn, av[k as int] as nat, tn, m@[k as int] as int, 1),
            forall |k: int| 0 <= k < n ==> -inf() <= #[trigger] errs_dec@[k] <= inf(),
            forall |k: int| 0 <= k < n ==> -inf() <= #[trigger] errs_inc@[k] <= inf(),
        decreases 0nat,
    {
        proof {
            let jdn = j_min_dec as nat;
            let jin = j_min_inc as nat;
            lemma_derr(zn, av[jdn as int] as nat, tn, m@[jdn as int] as nat);
            lemma_derr(zn, av[jin as int] as nat, tn, m@[jin as int] as nat);
            assert(errs_dec@[jdn as int] as int == derr(zn, av[jdn as int] as nat, tn, m@[jdn as int] as int, -1));
            assert(errs_inc@[jin as int] as int == derr(zn, av[jin as int] as nat, tn, m@[jin as int] as int, 1));
            assert(m@[jdn as int] == ofl(av, tn, zn, jdn) || m@[jdn as int] == ofl(av, tn, zn, jdn) + 1);
            assert(m@[jin as int] == ofl(av, tn, zn, jin) || m@[jin as int] == ofl(av, tn, zn, jin) + 1);
            assert(false);
        }
        // Apply the optimal move.
        m.set(j_min_dec, m[j_min_dec] - 1);
        m.set(j_min_inc, m[j_min_inc] + 1);
        // Update the costs.
        errs_dec.set(j_min_dec, get_delta_error(z, a[j_min_dec], t, m[j_min_dec], -1));
        errs_inc.set(j_min_inc, get_delta_error(z, a[j_min_inc], t, m[j_min_inc], 1));
        // Update the optimal indexes.
        let r = find_optimal_indexes(&errs_dec, &errs_inc);
        j_min_dec = r.0;
        j_min_inc = r.1;
    }
    m
}

/// `fix_shortfall`: move Σ M to Z one unit at a time, at the cheapest label.
pub fn fix_shortfall(z: u128, a: &Vec<u128>, t: u128, ms: Vec<u128>) -> (m: Vec<u128>)
    requires
        wf_target(a@, z as nat), t as nat == wsum_nat(a@, 0), ms.len() == a.len(),
        near(a@, t as nat, z as nat, ms@), exch(a@, t as nat, z as nat, ms@),
    ensures tv_optimal_out(a@, z as nat, m@),
{
    let n = a.len();
    let mut m = ms;
    let ghost tn = t as nat;
    let ghost zn = z as nat;
    let ghost av = a@;
    assert forall |i: nat| i < n implies (#[trigger] av[i as int]) <= t by {
        lemma_w_le_sum(av, 0, i);
    }
    proof {
        lemma_split_sum(av, tn, zn, 0);
        lemma_m_le(av, tn, zn, m@, 0);
        assert(tn * flsum(av, tn, zn, 0) <= zn * tn);
        assert(flsum(av, tn, zn, 0) <= zn) by(nonlinear_arith)
            requires tn * flsum(av, tn, zn, 0) <= zn * tn, tn > 0;
    }
    let msum = sum_u128(&m);
    let mut shortfall: i128 = msum as i128 - z as i128;
    let delta: i8 = if shortfall < 0 { 1 } else { -1 };
    let mut errs_delta: Vec<i128> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == a.len(), av == a@, i <= n, m.len() == n, errs_delta.len() == i,
            tn == t, zn == z, 0 < t <= 0x10000000000000000000000000000000, 1 <= z <= 0x10000000000000000000000000000000,
            delta == 1 || delta == -1,
            forall |i: nat| i < n ==> (#[trigger] av[i as int]) <= t,
            near(av, tn, zn, m@),
            forall |k: nat| k < i ==> #[trigger] errs_delta@[k as int] as int
                == derr(zn, av[k as int] as nat, tn, m@[k as int] as int, delta as int),
        decreases n - i,
    {
        proof { lemma_derr(zn, av[i as int] as nat, tn, m@[i as int] as nat); }
        errs_delta.push(get_delta_error(z, a[i], t, m[i], delta));
        i = i + 1;
    }
    while shortfall != 0
        invariant
            n == a.len(), av == a@, m.len() == n, errs_delta.len() == n, n >= 1,
            tn == t, zn == z, 0 < t <= 0x10000000000000000000000000000000, 1 <= z <= 0x10000000000000000000000000000000,
            wsum_nat(av, 0) == tn,
            forall |i: nat| i < n ==> (#[trigger] av[i as int]) <= t,
            near(av, tn, zn, m@),
            exch(av, tn, zn, m@),
            shortfall as int == wsum_nat(m@, 0) - zn,
            delta == 1 ==> shortfall <= 0,
            delta == -1 ==> shortfall >= 0,
            delta == 1 || delta == -1,
            forall |k: nat| k < n ==> #[trigger] errs_delta@[k as int] as int
                == derr(zn, av[k as int] as nat, tn, m@[k as int] as int, delta as int),
        decreases if shortfall >= 0 { shortfall as int } else { -shortfall },
    {
        let j_min = argmin(&errs_delta);
        let ghost jn = j_min as nat;
        let ghost m0 = m@;
        proof {
            lemma_derr(zn, av[jn as int] as nat, tn, m0[jn as int] as nat);
            assert(errs_delta@[jn as int] as int == derr(zn, av[jn as int] as nat, tn, m0[jn as int] as int, delta as int));
        }
        if delta == 1 {
            proof {
                let i0 = lemma_exists_up(av, tn, zn, m0);
                lemma_derr(zn, av[i0 as int] as nat, tn, m0[i0 as int] as nat);
                assert(errs_delta@[i0 as int] as int == derr(zn, av[i0 as int] as nat, tn, m0[i0 as int] as int, 1));
                assert(errs_delta@[jn as int] <= errs_delta@[i0 as int]);
                assert(m0[jn as int] == ofl(av, tn, zn, jn) || m0[jn as int] == ofl(av, tn, zn, jn) + 1);
                assert(m0[jn as int] == ofl(av, tn, zn, jn));
                assert forall |k: nat| k < n && #[trigger] m0[k as int] == ofl(av, tn, zn, k)
                    implies orm(av, tn, zn, k) <= orm(av, tn, zn, jn) by {
                    lemma_derr(zn, av[k as int] as nat, tn, m0[k as int] as nat);
                    assert(errs_delta@[k as int] as int == derr(zn, av[k as int] as nat, tn, m0[k as int] as int, 1));
                    assert(errs_delta@[jn as int] <= errs_delta@[k as int]);
                }
            }
            m.set(j_min, m[j_min] + 1);
        } else {
            proof {
                let i0 = lemma_exists_down(av, tn, zn, m0);
                lemma_derr(zn, av[i0 as int] as nat, tn, m0[i0 as int] as nat);
                assert(errs_delta@[i0 as int] as int == derr(zn, av[i0 as int] as nat, tn, m0[i0 as int] as int, -1));
                assert(errs_delta@[jn as int] <= errs_delta@[i0 as int]);
                assert(m0[jn as int] == ofl(av, tn, zn, jn) || m0[jn as int] == ofl(av, tn, zn, jn) + 1);
                assert(m0[jn as int] == ofl(av, tn, zn, jn) + 1);
                assert forall |k: nat| k < n && #[trigger] m0[k as int] == ofl(av, tn, zn, k) + 1
                    implies orm(av, tn, zn, jn) <= orm(av, tn, zn, k) by {
                    lemma_derr(zn, av[k as int] as nat, tn, m0[k as int] as nat);
                    assert(errs_delta@[k as int] as int == derr(zn, av[k as int] as nat, tn, m0[k as int] as int, -1));
                    assert(errs_delta@[jn as int] <= errs_delta@[k as int]);
                }
            }
            m.set(j_min, m[j_min] - 1);
        }
        proof {
            lemma_wsum_update(m0, jn, m@[jn as int], 0);
            assert(m@ == m0.update(jn as int, m@[jn as int]));
            assert(near(av, tn, zn, m@));
            assert forall |i: nat, k: nat| i < n && k < n
                && #[trigger] m@[i as int] == ofl(av, tn, zn, i) + 1 && #[trigger] m@[k as int] == ofl(av, tn, zn, k)
                implies orm(av, tn, zn, k) <= orm(av, tn, zn, i) by {
                if i != jn && k != jn {
                    assert(m0[i as int] == m@[i as int] && m0[k as int] == m@[k as int]);
                }
            }
            lemma_derr(zn, av[jn as int] as nat, tn, m@[jn as int] as nat);
        }
        let e = get_delta_error(z, a[j_min], t, m[j_min], delta);
        errs_delta.set(j_min, e);
        shortfall = shortfall + delta as i128;
    }
    m
}

/// `optimize_unorm_strict(Z, p)` (requires p > 0 elementwise).
pub fn optimize_unorm_strict(z: u128, a: &Vec<u128>) -> (m: Vec<u128>)
    requires wf_target(a@, z as nat), forall |i: int| 0 <= i < a.len() ==> #[trigger] a@[i] > 0,
    ensures tv_optimal_out(a@, z as nat, m@),
{
    let t = sum_u128(a);
    // STEP 1: Initial guess.
    let ms_initial = get_initial_ms(z, a, t);
    // STEP 2: Pruning.
    let ms_prune = prune_initial_ms(z, a, t, ms_initial);
    // STEP 3: Making up shortfall.
    fix_shortfall(z, a, t, ms_prune)
}

// ── optimize_unorm: filter the zeros, then pad ───────────────────────────────

/// #{i' < i : a_i' > 0}.
pub open spec fn nz_cnt(a: Seq<u128>, i: nat) -> nat
    decreases i,
{
    if i == 0 { 0 } else { nz_cnt(a, (i - 1) as nat) + (if a[(i - 1) as int] > 0 { 1nat } else { 0nat }) }
}

/// Σ_{i' < i} s_i'.
pub open spec fn psum_nat(s: Seq<u128>, i: nat) -> nat
    decreases i,
{
    if i == 0 { 0 } else { psum_nat(s, (i - 1) as nat) + s[(i - 1) as int] as nat }
}

proof fn lemma_psum_wsum(s: Seq<u128>, i: nat)
    requires i <= s.len(),
    ensures psum_nat(s, i) + wsum_nat(s, i) == wsum_nat(s, 0),
    decreases i,
{
    if i > 0 { lemma_psum_wsum(s, (i - 1) as nat); }
}

proof fn lemma_nz_cnt_mono(a: Seq<u128>, i: nat, j: nat)
    requires i <= j <= a.len(),
    ensures nz_cnt(a, i) <= nz_cnt(a, j), i < j && a[i as int] > 0 ==> nz_cnt(a, i) < nz_cnt(a, j),
    decreases j - i,
{
    if i < j {
        lemma_nz_cnt_mono(a, i, (j - 1) as nat);
        if a[i as int] > 0 && i + 1 < j { lemma_nz_cnt_mono(a, i + 1, (j - 1) as nat); }
    }
}

/// `optimize_unorm(Z, p)`: optimize over the labels with p_i > 0 and give
/// the others M_i = 0.
pub fn optimize_unorm(z: u128, a: &Vec<u128>) -> (m: Vec<u128>)
    requires wf_target(a@, z as nat),
    ensures tv_optimal_out(a@, z as nat, m@),
{
    let n = a.len();
    let ghost av = a@;
    let ghost t = wsum_nat(av, 0);
    // STEP 1: Filter out zeros.
    let mut af: Vec<u128> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == a.len(), av == a@, i <= n,
            af.len() == nz_cnt(av, i as nat),
            forall |i2: nat| i2 < i && av[i2 as int] > 0 ==> #[trigger] af@[nz_cnt(av, i2) as int] == av[i2 as int],
            forall |j: int| 0 <= j < af.len() ==> #[trigger] af@[j] > 0,
            psum_nat(af@, af.len() as nat) == psum_nat(av, i as nat),
        decreases n - i,
    {
        if a[i] > 0 {
            let ghost af0 = af@;
            proof { lemma_psum_push(af0, a[i as int], af0.len() as nat); }
            af.push(a[i]);
            proof {
                assert forall |i2: nat| i2 < i + 1 && av[i2 as int] > 0 implies #[trigger] af@[nz_cnt(av, i2) as int] == av[i2 as int] by {
                    if i2 < i { lemma_nz_cnt_mono(av, i2, i as nat); }
                }
                lemma_psum_prefix(af@, (af.len() - 1) as nat);
            }
        }
        i = i + 1;
    }
    proof {
        lemma_psum_wsum(af@, af.len() as nat);
        lemma_psum_wsum(av, n as nat);
        assert(wsum_nat(af@, 0) == t);
        assert(af.len() >= 1) by { if af.len() == 0 { assert(psum_nat(af@, 0) == 0); } }
        lemma_nz_cnt_le(av, n as nat);
    }
    // STEP 2: Get the solution on the non-zero elements.
    let ms_opt_trunc = optimize_unorm_strict(z, &af);
    // STEP 3: Pad the solution.
    let mut m: Vec<u128> = Vec::new();
    let mut jj: usize = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            n == a.len(), av == a@, i <= n, m.len() == i,
            jj as nat == nz_cnt(av, i as nat), af.len() == nz_cnt(av, n as nat),
            ms_opt_trunc.len() == af.len(),
            forall |i2: nat| i2 < n && av[i2 as int] > 0 ==> #[trigger] af@[nz_cnt(av, i2) as int] == av[i2 as int],
            forall |i2: nat| i2 < i ==> #[trigger] m@[i2 as int] == (if av[i2 as int] > 0 { ms_opt_trunc@[nz_cnt(av, i2) as int] } else { 0 }),
            psum_nat(m@, i as nat) == psum_nat(ms_opt_trunc@, jj as nat),
        decreases n - i,
    {
        proof { lemma_nz_cnt_mono(av, i as nat, n as nat); }
        if a[i] > 0 {
            proof { lemma_psum_push(m@, ms_opt_trunc@[jj as int], i as nat); }
            m.push(ms_opt_trunc[jj]);
            proof { lemma_psum_prefix(m@, i as nat); }
            jj = jj + 1;
        } else {
            proof { lemma_psum_push(m@, 0, i as nat); }
            m.push(0);
            proof { lemma_psum_prefix(m@, i as nat); }
        }
        i = i + 1;
    }
    proof {
        let tz = wsum_nat(af@, 0);
        let mf = ms_opt_trunc@;
        lemma_psum_wsum(m@, n as nat);
        lemma_psum_wsum(mf, mf.len() as nat);
        assert(near(av, t, z as nat, m@)) by {
            assert forall |i2: nat| i2 < m@.len() implies
                (#[trigger] m@[i2 as int]) == ofl(av, t, z as nat, i2)
                || (m@[i2 as int] == ofl(av, t, z as nat, i2) + 1 && orm(av, t, z as nat, i2) > 0) by {
                if av[i2 as int] > 0 {
                    let c = nz_cnt(av, i2);
                    lemma_nz_cnt_mono(av, i2, n as nat);
                    assert(mf[c as int] == ofl(af@, t, z as nat, c)
                        || (mf[c as int] == ofl(af@, t, z as nat, c) + 1 && orm(af@, t, z as nat, c) > 0));
                } else {
                    assert(ofl(av, t, z as nat, i2) == 0) by {
                        assert((z as nat) * 0 == 0);
                    }
                }
            }
        }
        assert forall |i2: nat, k: nat| i2 < m@.len() && k < m@.len()
            && #[trigger] m@[i2 as int] == ofl(av, t, z as nat, i2) + 1 && #[trigger] m@[k as int] == ofl(av, t, z as nat, k)
            implies orm(av, t, z as nat, k) <= orm(av, t, z as nat, i2) by {
            assert((z as nat) * 0 == 0);
            if av[i2 as int] > 0 && av[k as int] > 0 {
                lemma_nz_cnt_mono(av, i2, n as nat);
                lemma_nz_cnt_mono(av, k, n as nat);
                let c1 = nz_cnt(av, i2);
                let c2 = nz_cnt(av, k);
                assert(mf[c1 as int] == ofl(af@, t, z as nat, c1) + 1);
                assert(mf[c2 as int] == ofl(af@, t, z as nat, c2));
            } else if av[i2 as int] == 0 {
                assert(ofl(av, t, z as nat, i2) == 0);
            } else {
                assert(av[k as int] == 0);
                assert((z as nat) * (av[k as int] as nat) == 0);
                assert(t > 0);
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(0, t as int, 0, 0);
                assert(orm(av, t, z as nat, k) == 0);
            }
        }
    }
    m
}

proof fn lemma_psum_push(s: Seq<u128>, x: u128, k: nat)
    requires k <= s.len(),
    ensures psum_nat(s.push(x), k) == psum_nat(s, k),
    decreases k,
{
    if k > 0 { lemma_psum_push(s, x, (k - 1) as nat); }
}

proof fn lemma_psum_prefix(s: Seq<u128>, i: nat)
    requires i < s.len(),
    ensures psum_nat(s, i + 1) == psum_nat(s, i) + s[i as int] as nat,
{
}

proof fn lemma_nz_cnt_le(a: Seq<u128>, i: nat)
    requires i <= a.len(),
    ensures nz_cnt(a, i) <= i,
    decreases i,
{
    if i > 0 { lemma_nz_cnt_le(a, (i - 1) as nat); }
}

/// `get_optimal_probabilities(Z, p, kernel_tv)`: the numerators M (the
/// original returns `normalize_vector(Z, M)`, i.e. M / Z as `Fraction`s).
pub fn get_optimal_probabilities(z: u128, a: &Vec<u128>) -> (m: Vec<u128>)
    requires wf_target(a@, z as nat),
    ensures tv_optimal_out(a@, z as nat, m@),
{
    optimize_unorm(z, a)
}

/// `get_optimal_probabilities_strict(Z, p, kernel_tv)`.
pub fn get_optimal_probabilities_strict(z: u128, a: &Vec<u128>) -> (m: Vec<u128>)
    requires wf_target(a@, z as nat), forall |i: int| 0 <= i < a.len() ==> #[trigger] a@[i] > 0,
    ensures tv_optimal_out(a@, z as nat, m@),
{
    optimize_unorm_strict(z, a)
}

proof fn lemma_m_le(a: Seq<u128>, t: nat, z: nat, m: Seq<u128>, r: nat)
    requires near(a, t, z, m), r <= m.len(),
    ensures wsum_nat(m, r) <= flsum(a, t, z, r) + (m.len() - r),
    decreases m.len() - r,
{
    if r < m.len() { lemma_m_le(a, t, z, m, r + 1); }
}


} // verus!
