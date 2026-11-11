//! Number-theoretic helpers, the binary expansion of
//! M / Z_kl (`frac_to_bits`), and `reduce_fractions`. Exact integers only;
//! the one float in the original (`log2` in `reduce_fractions`) is an
//! integer power-of-two test here.

use vstd::prelude::*;

verus! {

#[cfg(verus_keep_ghost)]
use crate::fldr::bit;
#[cfg(verus_keep_ghost)]
use crate::fldr_helper::lemma_pow2_mono;
#[cfg(verus_keep_ghost)]
use crate::optas::ztype::{wsum_nat, lemma_w_le_sum};
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::{pow2, lemma_pow2_pos, lemma_pow2_unfold, lemma_pow2_adds,
    lemma_pow2_strictly_increases, lemma2_to64, lemma2_to64_rest};
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::{
    lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse, lemma_div_denominator,
};

// ── get_Zkl, get_Zb ───────────────────────────────────────────────────────────

/// `get_Zkl`: Z_kl = 2^k − 2^l·[l < k] (Proposition 3.1).
pub open spec fn zkl(k: nat, l: nat) -> nat {
    if l < k { (pow2(k) - pow2(l)) as nat } else { pow2(k) }
}

/// `get_Zb`: Z_b = 2^{k−l} − [l < k], the denominator of the repeating block.
pub open spec fn zb(k: nat, l: nat) -> nat {
    if l < k { (pow2((k - l) as nat) - 1) as nat } else { 1 }
}

/// Z_kl = 2^l·Z_b, 0 < Z_kl ≤ 2^k, Z_b < 2^{k−l} (or Z_b = 1 when l = k).
pub proof fn lemma_zkl(k: nat, l: nat)
    requires 0 < k, l <= k,
    ensures
        zkl(k, l) == pow2(l) * zb(k, l),
        0 < zkl(k, l) <= pow2(k),
        0 < zb(k, l) <= pow2((k - l) as nat),
        l < k ==> zb(k, l) < pow2((k - l) as nat),
        l < k ==> pow2(l) < pow2(k),
{
    lemma_pow2_pos(l);
    lemma_pow2_pos((k - l) as nat);
    lemma_pow2_adds(l, (k - l) as nat);
    if l < k {
        lemma_pow2_strictly_increases(l, k);
        assert(pow2((k - l) as nat) >= 2) by {
            lemma_pow2_unfold((k - l) as nat);
            lemma_pow2_pos((k - l - 1) as nat);
        }
        assert(pow2(k) - pow2(l) == pow2(l) * (pow2((k - l) as nat) - 1)) by(nonlinear_arith)
            requires pow2(k) == pow2(l) * pow2((k - l) as nat);
    } else {
        assert(k - l == 0);
        lemma2_to64();
    }
}

/// 2^62, 2^124 (the bound on Z, the weights and their sums) and 2^126.
pub proof fn lemma_pow2_consts()
    ensures pow2(124) == 0x10000000000000000000000000000000, pow2(62) == 0x4000000000000000,
        pow2(126) == 0x40000000000000000000000000000000,
{
    lemma2_to64_rest();
    lemma_pow2_adds(62, 62);
    lemma_pow2_adds(124, 2);
    lemma2_to64();
}

/// 2^k as a u128, k ≤ 126.
pub fn pow2_u128(k: u64) -> (r: u128)
    requires k <= 126,
    ensures r as nat == pow2(k as nat),
{
    let mut r: u128 = 1;
    let mut i: u64 = 0;
    proof { lemma2_to64(); }
    while i < k
        invariant i <= k, k <= 126, r as nat == pow2(i as nat),
        decreases k - i,
    {
        proof {
            lemma_pow2_unfold((i + 1) as nat);
            lemma_pow2_mono(i as nat, 125);
            lemma_pow2_consts();
            lemma_pow2_unfold(126);
        }
        r = 2 * r;
        i = i + 1;
    }
    r
}

pub fn get_zkl(k: u64, l: u64) -> (z: u128)
    requires 0 < k <= 124, l <= k,
    ensures z as nat == zkl(k as nat, l as nat),
{
    proof {
        lemma_zkl(k as nat, l as nat);
        lemma_pow2_mono(k as nat, 124);
        lemma_pow2_consts();
    }
    if l < k { pow2_u128(k) - pow2_u128(l) } else { pow2_u128(k) }
}

pub fn get_zb(k: u64, l: u64) -> (z: u128)
    requires 0 < k <= 124, l <= k,
    ensures z as nat == zb(k as nat, l as nat),
{
    proof {
        lemma_zkl(k as nat, l as nat);
        lemma_pow2_mono((k - l) as nat, 124);
        lemma_pow2_consts();
    }
    if l < k { pow2_u128(k - l) - 1 } else { 1 }
}

// ── argmin2, argmin ───────────────────────────────────────────────────────────

/// `argmin2`: the indexes of the smallest and second-smallest entries, with
/// the original's comparisons: ties for the smallest go to the later index
/// (`x <= v[j1]`), ties for the second smallest to the earlier
/// (`x < v[j2]`).
pub fn argmin2(v: &Vec<i128>) -> (r: (usize, usize))
    requires v.len() >= 2,
    ensures
        r.0 < v.len(), r.1 < v.len(), r.0 != r.1,
        forall |i: int| 0 <= i < v.len() ==> v[r.0 as int] <= #[trigger] v[i],
        forall |i: int| 0 <= i < v.len() && i != r.0 ==> v[r.1 as int] <= #[trigger] v[i],
{
    let n = v.len();
    let mut j1: usize = n;
    let mut j2: usize = n;
    let mut i: usize = 0;
    while i < n
        invariant
            n == v.len() >= 2,
            i <= n,
            i >= 1 ==> j1 < i,
            i >= 2 ==> j2 < i && j2 != j1,
            i < 2 ==> j2 == n,
            i == 0 ==> j1 == n,
            forall |k: int| 0 <= k < i ==> v[j1 as int] <= #[trigger] v[k],
            forall |k: int| 0 <= k < i && k != j1 ==> v[j2 as int] <= #[trigger] v[k],
        decreases n - i,
    {
        let x = v[i];
        if j1 == n || x <= v[j1] {
            j2 = j1;
            j1 = i;
        } else if j2 == n || x < v[j2] {
            j2 = i;
        }
        i = i + 1;
    }
    (j1, j2)
}

/// `argmin`: the index of the smallest entry. Like the original (`x <= m`),
/// ties go to the later index; the ensures states only minimality.
pub fn argmin(v: &Vec<i128>) -> (j: usize)
    requires v.len() >= 1,
    ensures j < v.len(), forall |i: int| 0 <= i < v.len() ==> v[j as int] <= #[trigger] v[i],
{
    let n = v.len();
    let mut j: usize = 0;
    let mut i: usize = 1;
    while i < n
        invariant
            n == v.len(), 1 <= i <= n, j < i,
            forall |k: int| 0 <= k < i ==> v[j as int] <= #[trigger] v[k],
        decreases n - i,
    {
        if v[i] <= v[j] { j = i; }
        i = i + 1;
    }
    j
}

// ── frac_to_bits ──────────────────────────────────────────────────────────────

/// The prefix x and the repeating block y of M / Z_kl, as in `frac_to_bits`:
/// M / Z_kl = 0.(x in l bits)(y in k−l bits)(y)(y)…
pub open spec fn frac_x(m: nat, k: nat, l: nat) -> nat {
    if l == k { m } else if l == 0 { 0 } else { m / zb(k, l) }
}

pub open spec fn frac_y(m: nat, k: nat, l: nat) -> nat {
    if l == k { 0 } else if l == 0 { m } else { m % zb(k, l) }
}

/// The k-bit row x·2^{k−l} + y (`encode_binary(x, l) + encode_binary(y, k − l)`).
pub open spec fn frac_int(m: nat, k: nat, l: nat) -> nat {
    pow2((k - l) as nat) * frac_x(m, k, l) + frac_y(m, k, l)
}

/// Column c ∈ [0, k) of the row: bit k−1−c of `frac_int`.
pub open spec fn frac_bit(m: nat, k: nat, l: nat, c: nat) -> nat {
    bit(frac_int(m, k, l), (k - 1 - c) as nat)
}

/// The block y fits in k − l bits.
pub proof fn lemma_frac_y_lt(m: nat, k: nat, l: nat)
    requires 0 < k, l <= k, m < zkl(k, l) || (k == 1 && l == 0 && m == 1),
    ensures frac_y(m, k, l) < pow2((k - l) as nat),
{
    lemma_zkl(k, l);
    if l == k {
        lemma_pow2_pos(0);
    } else if l == 0 {
        lemma2_to64();
        if k == 1 && m == 1 { lemma_pow2_unfold(1); }
    } else {
        lemma_fundamental_div_mod(m as int, zb(k, l) as int);
    }
}

/// For M < Z_kl, the row is the first k bits of M / Z_kl: x·2^{k−l} + y =
/// ⌊2^k M / Z_kl⌋.
pub proof fn lemma_frac_int_floor(m: nat, k: nat, l: nat)
    requires 0 < k, l <= k, m < zkl(k, l),
    ensures frac_int(m, k, l) == (pow2(k) * m) / zkl(k, l),
{
    lemma_zkl(k, l);
    let z = zkl(k, l);
    let s = (k - l) as nat;
    let ps = pow2(s);
    lemma_pow2_adds(l, s);
    lemma_pow2_pos(l);
    if l == k {
        lemma2_to64();
        assert(s == 0);
        assert(frac_int(m, k, l) == m);
        assert((pow2(k) * m) as int == (m as int) * (pow2(k) as int) + 0) by(nonlinear_arith);
        lemma_fundamental_div_mod_converse((pow2(k) * m) as int, pow2(k) as int, m as int, 0);
    } else {
        // z = 2^l·Z_b, with Z_b = 2^s − 1; write M = x·Z_b + y.
        let b = zb(k, l);
        let x = frac_x(m, k, l);
        let y = frac_y(m, k, l);
        if l == 0 {
            assert(x == 0 && y == m);
            lemma2_to64();
            assert(b == z);
        } else {
            lemma_fundamental_div_mod(m as int, b as int);
        }
        assert(m == b * x + y && y < b) by {
            if l == 0 { assert(b * 0 == 0); }
        }
        // 2^k M = z·(2^s x + y) + y, with y < b ≤ z.
        assert(pow2(k) * m == z * (ps * x + y) + pow2(l) * y) by(nonlinear_arith)
            requires pow2(k) == pow2(l) * ps, z == pow2(l) * b, b == ps - 1, m == b * x + y;
        assert(pow2(l) * y < z) by(nonlinear_arith) requires z == pow2(l) * b, y < b, pow2(l) > 0;
        assert((pow2(k) * m) as int == ((ps * x + y) as int) * (z as int) + (pow2(l) * y) as int) by(nonlinear_arith)
            requires pow2(k) * m == z * (ps * x + y) + pow2(l) * y;
        lemma_fundamental_div_mod_converse((pow2(k) * m) as int, z as int, (ps * x + y) as int, (pow2(l) * y) as int);
    }
}

/// bit i of 2^s x + y, for y < 2^s: the bits of y below s, those of x above.
pub proof fn lemma_bit_split(x: nat, y: nat, s: nat, i: nat)
    requires y < pow2(s),
    ensures bit(pow2(s) * x + y, i) == if i >= s { bit(x, (i - s) as nat) } else { bit(y, i) },
{
    let v = pow2(s) * x + y;
    lemma_pow2_pos(s);
    lemma_pow2_pos(i);
    if i >= s {
        let t = (i - s) as nat;
        lemma_pow2_adds(s, t);
        lemma_pow2_pos(t);
        lemma_div_denominator(v as int, pow2(s) as int, pow2(t) as int);
        assert(v as int == (x as int) * (pow2(s) as int) + y as int) by(nonlinear_arith) requires v == pow2(s) * x + y;
        lemma_fundamental_div_mod_converse(v as int, pow2(s) as int, x as int, y as int);
    } else {
        let t = (s - i) as nat;
        lemma_pow2_adds(i, t);
        lemma_pow2_pos(t);
        lemma_fundamental_div_mod(y as int, pow2(i) as int);
        let q = y / pow2(i);
        let rr = y % pow2(i);
        assert(v == pow2(i) * (pow2(t) * x + q) + rr) by(nonlinear_arith)
            requires v == pow2(s) * x + y, pow2(s) == pow2(i) * pow2(t), y == pow2(i) * q + rr;
        assert(v as int == ((pow2(t) * x + q) as int) * (pow2(i) as int) + rr as int) by(nonlinear_arith)
            requires v == pow2(i) * (pow2(t) * x + q) + rr;
        lemma_fundamental_div_mod_converse(v as int, pow2(i) as int, (pow2(t) * x + q) as int, rr as int);
        lemma_pow2_unfold(t);
        let h = pow2((t - 1) as nat) * x;
        assert(pow2(t) * x + q == 2 * h + q) by(nonlinear_arith)
            requires pow2(t) == 2 * pow2((t - 1) as nat), h == pow2((t - 1) as nat) * x;
        lemma_fundamental_div_mod(q as int, 2);
        lemma_fundamental_div_mod_converse((2 * h + q) as int, 2, (h + q / 2) as int, (q % 2) as int);
    }
}

/// `frac_to_bits(M, k, l)`: the first k bits of the concise binary expansion
/// of M / Z_kl, MSB first (`encode_binary(x, l) + encode_binary(y, k − l)`).
pub fn frac_to_bits(m: u128, k: u64, l: u64) -> (b: Vec<u8>)
    requires
        0 < k <= 124, l <= k,
        (m as nat) < zkl(k as nat, l as nat) || (k == 1 && l == 0 && m == 1),
    ensures
        b.len() == k,
        forall |c: nat| c < k ==> (#[trigger] b@[c as int]) as nat == frac_bit(m as nat, k as nat, l as nat, c),
{
    proof { lemma_zkl(k as nat, l as nat); }
    let zbv = get_zb(k, l);
    let (x, y): (u128, u128) = if l == k {
        (m, 0)
    } else if l == 0 {
        (0, m)
    } else {
        (m / zbv, m % zbv)
    };
    proof {
        lemma_zkl(k as nat, l as nat);
        lemma_frac_y_lt(m as nat, k as nat, l as nat);
        assert(x as nat == frac_x(m as nat, k as nat, l as nat));
        assert(y as nat == frac_y(m as nat, k as nat, l as nat));
    }
    let ghost s = (k - l) as nat;
    let mut b: Vec<u8> = Vec::new();
    let mut c: u64 = 0;
    while c < k
        invariant
            0 < k <= 124, l <= k, c <= k, b.len() == c, s == (k - l) as nat,
            x as nat == frac_x(m as nat, k as nat, l as nat),
            y as nat == frac_y(m as nat, k as nat, l as nat),
            (y as nat) < pow2(s),
            forall |c2: nat| c2 < c ==> (#[trigger] b@[c2 as int]) as nat == frac_bit(m as nat, k as nat, l as nat, c2),
        decreases k - c,
    {
        let ghost i = (k - 1 - c) as nat;
        proof {
            lemma_bit_split(x as nat, y as nat, s, i);
            lemma_pow2_pos(i);
        }
        let v: u8 = if c < l {
            let p = pow2_u128(l - 1 - c);
            proof { lemma_pow2_pos((l - 1 - c) as nat); assert((i - s) as nat == (l - 1 - c) as nat); }
            ((x / p) % 2) as u8
        } else {
            let p = pow2_u128(k - 1 - c);
            proof { lemma_pow2_pos((k - 1 - c) as nat); }
            ((y / p) % 2) as u8
        };
        b.push(v);
        c = c + 1;
    }
    b
}

// ── gcd, lcm, common denominators and numerators ─────────────────────────────

/// d·y1 + d·r1 form: d | y and d | r ⟹ d | y·q + r.
proof fn lemma_dvd_comb(d: nat, y: nat, q: nat, r: nat)
    requires d > 0, y % d == 0, r % d == 0,
    ensures (y * q + r) % d == 0,
{
    lemma_fundamental_div_mod(y as int, d as int);
    lemma_fundamental_div_mod(r as int, d as int);
    let y1 = y / d;
    let r1 = r / d;
    assert(y * q + r == d * (y1 * q + r1)) by(nonlinear_arith) requires y == d * y1, r == d * r1;
    assert((y * q + r) as int == ((y1 * q + r1) as int) * (d as int) + 0) by(nonlinear_arith) requires y * q + r == d * (y1 * q + r1);
    lemma_fundamental_div_mod_converse((y * q + r) as int, d as int, (y1 * q + r1) as int, 0);
}

/// `gcd` (math.gcd), by Euclid. Only the divisibility of a and b is needed.
pub fn gcd(a: u64, b: u64) -> (g: u64)
    requires a > 0,
    ensures g > 0, (a as nat) % (g as nat) == 0, (b as nat) % (g as nat) == 0,
{
    let mut x = a;
    let mut y = b;
    // Every common divisor of x and y divides a and b.
    while y != 0
        invariant
            x > 0,
            forall |d: nat| d > 0 && #[trigger] ((x as nat) % d) == 0 && (y as nat) % d == 0
                ==> (a as nat) % d == 0 && (b as nat) % d == 0,
        decreases y,
    {
        let r = x % y;
        proof {
            assert forall |d: nat| d > 0 && #[trigger] ((y as nat) % d) == 0 && (r as nat) % d == 0
                implies (a as nat) % d == 0 && (b as nat) % d == 0 by {
                lemma_fundamental_div_mod(x as int, y as int);
                lemma_dvd_comb(d, y as nat, (x / y) as nat, r as nat);
                assert((x as nat) == (y as nat) * ((x / y) as nat) + (r as nat));
            }
        }
        x = y;
        y = r;
    }
    proof {
        assert((x as nat) % (x as nat) == 0) by { lemma_fundamental_div_mod_converse(x as int, x as int, 1, 0); }
        assert(0nat % (x as nat) == 0);
    }
    x
}

/// `lcm(a, b) = a·b / gcd(a, b)`, or None past 2^62 (the bound on the
/// common denominator of the `(u64, u64)` fraction inputs).
pub fn lcm(a: u64, b: u64) -> (r: Option<u64>)
    requires a > 0, b > 0,
    ensures r matches Some(l) ==> l > 0 && l <= 0x4000000000000000
        && (l as nat) % (a as nat) == 0 && (l as nat) % (b as nat) == 0,
{
    let g = gcd(a, b);
    let bq = b / g;
    proof {
        lemma_fundamental_div_mod(b as int, g as int);
        lemma_fundamental_div_mod(a as int, g as int);
    }
    assert((a as int) * (bq as int) <= 0xffff_ffff_ffff_ffff * 0xffff_ffff_ffff_ffff) by(nonlinear_arith)
        requires a <= 0xffff_ffff_ffff_ffffu64, bq <= 0xffff_ffff_ffff_ffffu64;
    let v: u128 = (a as u128) * (bq as u128);
    if v > 0x4000000000000000 {
        return None;
    }
    proof {
        let aq = (a / g) as nat;
        assert(bq > 0) by(nonlinear_arith) requires b == g * bq + 0, b > 0;
        assert(v as nat == (a as nat) * (bq as nat));
        assert((v as nat) as int == (bq as int) * (a as int) + 0) by(nonlinear_arith) requires v as nat == (a as nat) * (bq as nat);
        lemma_fundamental_div_mod_converse((v as nat) as int, a as int, bq as int, 0);
        assert((v as nat) == (b as nat) * aq) by(nonlinear_arith)
            requires v as nat == (a as nat) * (bq as nat), (b as nat) == (g as nat) * (bq as nat),
                (a as nat) == (g as nat) * aq;
        assert((v as nat) as int == (aq as int) * (b as int) + 0) by(nonlinear_arith) requires (v as nat) == (b as nat) * aq;
        lemma_fundamental_div_mod_converse((v as nat) as int, b as int, aq as int, 0);
        assert(v > 0) by(nonlinear_arith) requires v as nat == (a as nat) * (bq as nat), a > 0, bq > 0;
    }
    Some(v as u64)
}

/// A probability given as an exact fraction `(numerator, denominator)`
/// (Python `fractions.Fraction`).
pub open spec fn fval(f: (u64, u64)) -> real {
    (f.0 as real) / (f.1 as real)
}

/// Fractions in [0, 1] with positive denominators.
pub open spec fn wf_fracs(p: Seq<(u64, u64)>) -> bool {
    forall |i: int| 0 <= i < p.len() ==> (#[trigger] p[i]).1 > 0 && p[i].0 <= p[i].1
}

/// `get_common_denominator`: the lcm of the denominators (None if it
/// exceeds 2^62).
pub fn get_common_denominator(p: &Vec<(u64, u64)>) -> (r: Option<u64>)
    requires wf_fracs(p@),
    ensures r matches Some(z) ==> z > 0 && z <= 0x4000000000000000
        && forall |i: int| 0 <= i < p.len() ==> (z as nat) % (#[trigger] p@[i].1 as nat) == 0,
{
    let mut z: u64 = 1;
    let mut i: usize = 0;
    proof { lemma2_to64(); }
    while i < p.len()
        invariant
            wf_fracs(p@), i <= p.len(), 0 < z <= 0x4000000000000000,
            forall |j: int| 0 <= j < i ==> (z as nat) % (#[trigger] p@[j].1 as nat) == 0,
        decreases p.len() - i,
    {
        let d = p[i].1;
        match lcm(z, d) {
            None => { return None; }
            Some(z2) => {
                proof {
                    assert forall |j: int| 0 <= j < i + 1 implies (z2 as nat) % (#[trigger] p@[j].1 as nat) == 0 by {
                        if j < i {
                            let dj = p@[j].1 as nat;
                            lemma_fundamental_div_mod(z2 as int, z as int);
                            lemma_fundamental_div_mod(z as int, dj as int);
                            lemma_dvd_comb(dj, z as nat, ((z2 as nat) / (z as nat)) as nat, 0);
                            assert((z2 as nat) == (z as nat) * ((z2 as nat) / (z as nat)));
                        }
                    }
                }
                z = z2;
            }
        }
        i = i + 1;
    }
    Some(z)
}

/// `get_common_numerators(Z, p)`: M_i = Z·p_i, exact because each
/// denominator divides Z.
pub fn get_common_numerators(z: u128, p: &Vec<(u64, u64)>) -> (ms: Vec<u128>)
    requires
        wf_fracs(p@), z > 0,
        forall |i: int| 0 <= i < p.len() ==> (z as nat) % (#[trigger] p@[i].1 as nat) == 0,
    ensures
        ms.len() == p.len(),
        forall |i: int| 0 <= i < p.len() ==> (#[trigger] ms@[i] as nat) <= z as nat
            && (ms@[i] as nat) * (p@[i].1 as nat) == (z as nat) * (p@[i].0 as nat),
{
    let mut ms: Vec<u128> = Vec::new();
    let mut i: usize = 0;
    while i < p.len()
        invariant
            wf_fracs(p@), z > 0, i <= p.len(), ms.len() == i,
            forall |j: int| 0 <= j < p.len() ==> (z as nat) % (#[trigger] p@[j].1 as nat) == 0,
            forall |j: int| 0 <= j < i ==> (#[trigger] ms@[j] as nat) <= z as nat
                && (ms@[j] as nat) * (p@[j].1 as nat) == (z as nat) * (p@[j].0 as nat),
        decreases p.len() - i,
    {
        let (num, den) = p[i];
        let q = z / (den as u128);
        proof {
            lemma_fundamental_div_mod(z as int, den as int);
            assert((q as int) * (num as int) <= z) by(nonlinear_arith)
                requires z == den * q + 0, num <= den, q >= 0;
        }
        let mi = q * (num as u128);
        proof {
            assert((mi as nat) * (den as nat) == (z as nat) * (num as nat)) by(nonlinear_arith)
                requires mi == q * num, z == den * q;
        }
        ms.push(mi);
        i = i + 1;
    }
    ms
}

/// `normalize_vector(Z, Ms)`: the distribution M / Z.
pub open spec fn normalize_vector(z: nat, ms: Seq<u128>) -> spec_fn(nat) -> real {
    |i: nat| (ms[i as int] as real) / (z as real)
}

// ── orderm2, get_binary_expansion_length ─────────────────────────────────────

/// `orderm2(M)`: the multiplicative order of 2 modulo odd M (the original
/// shells out to `bc`). Searches k ≤ 62 only; None if the order is larger.
pub fn orderm2(m: u64) -> (r: Option<u64>)
    requires 1 <= m <= 0x4000000000000000, m % 2 == 1,
    ensures r matches Some(k) ==> 1 <= k <= 62 && (pow2(k as nat) as int - 1) % (m as int) == 0
        && forall |j: nat| 1 <= j < k ==> (pow2(j) as int - 1) % (m as int) != 0,
{
    // x = 2^k mod m
    let mut k: u64 = 1;
    let mut x: u64 = 2 % m;
    proof {
        lemma2_to64();
        lemma_pow2_unfold(1);
    }
    while k <= 62
        invariant
            1 <= m <= 0x4000000000000000, 1 <= k <= 63,
            x < m, x as int == (pow2(k as nat) as int) % (m as int),
            forall |j: nat| 1 <= j < k ==> (pow2(j) as int - 1) % (m as int) != 0,
        decreases 63 - k,
    {
        proof {
            lemma_pow2_pos(k as nat);
            lemma_fundamental_div_mod(pow2(k as nat) as int, m as int);
        }
        if x == 1 % m {
            proof {
                // 2^k ≡ 1 (mod m)
                let q = (pow2(k as nat) as int) / (m as int);
                if m == 1 {
                    lemma_fundamental_div_mod_converse(pow2(k as nat) as int - 1, 1, pow2(k as nat) as int - 1, 0);
                } else {
                    assert(1int % (m as int) == 1) by { lemma_fundamental_div_mod_converse(1, m as int, 0, 1); }
                    assert(pow2(k as nat) as int - 1 == q * m + 0) by(nonlinear_arith)
                        requires pow2(k as nat) as int == m * q + x, x == 1;
                    lemma_fundamental_div_mod_converse(pow2(k as nat) as int - 1, m as int, q, 0);
                }
            }
            return Some(k);
        }
        proof {
            let q = (pow2(k as nat) as int) / (m as int);
            assert(m >= 2) by {
                if m == 1 { assert(x == 0); assert(1int % 1 == 0); }
            }
            assert(1int % (m as int) == 1) by { lemma_fundamental_div_mod_converse(1, m as int, 0, 1); }
            assert((pow2(k as nat) as int - 1) % (m as int) != 0) by {
                if (pow2(k as nat) as int - 1) % (m as int) == 0 {
                    lemma_fundamental_div_mod(pow2(k as nat) as int - 1, m as int);
                    let q1 = (pow2(k as nat) as int - 1) / (m as int);
                    assert(pow2(k as nat) as int == q1 * (m as int) + 1) by(nonlinear_arith)
                        requires pow2(k as nat) as int - 1 == (m as int) * q1 + 0;
                    lemma_fundamental_div_mod_converse(pow2(k as nat) as int, m as int, q1, 1);
                }
            }
            lemma_pow2_unfold((k + 1) as nat);
            assert(2 * (pow2(k as nat) as int) == m * (2 * q) + 2 * x) by(nonlinear_arith)
                requires pow2(k as nat) as int == m * q + x;
            lemma_fundamental_div_mod(2 * x as int, m as int);
            let q2 = (2 * x as int) / (m as int);
            assert(2 * (pow2(k as nat) as int) == m * (2 * q + q2) + (2 * x as int) % (m as int)) by(nonlinear_arith)
                requires 2 * (pow2(k as nat) as int) == m * (2 * q) + 2 * x, 2 * x as int == m * q2 + (2 * x as int) % (m as int);
            assert(pow2((k + 1) as nat) as int == (2 * q + q2) * (m as int) + (2 * x as int) % (m as int)) by(nonlinear_arith)
                requires 2 * (pow2(k as nat) as int) == m * (2 * q + q2) + (2 * x as int) % (m as int),
                    pow2((k + 1) as nat) == 2 * pow2(k as nat);
            lemma_fundamental_div_mod_converse(pow2((k + 1) as nat) as int, m as int, 2 * q + q2, (2 * x as int) % (m as int));
        }
        x = (2 * x) % m;
        k = k + 1;
    }
    None
}

/// `get_binary_expansion_length(Z)`: (k, l) such that 1/Z has an l-bit
/// prefix and a (k − l)-bit repeating block, i.e. Z divides Z_kl.
pub fn get_binary_expansion_length(z: u64) -> (r: Option<(u64, u64)>)
    requires 1 <= z <= 0x4000000000000000,
    ensures r matches Some((k, l)) ==> 0 < k <= 62 && l <= k
        && zkl(k as nat, l as nat) % (z as nat) == 0,
{
    if z % 2 == 1 {
        match orderm2(z) {
            None => None,
            Some(k) => {
                proof {
                    lemma2_to64();
                    lemma_pow2_strictly_increases(0, k as nat);
                    assert(zkl(k as nat, 0) as int == pow2(k as nat) as int - 1);
                }
                Some((k, 0))
            }
        }
    } else {
        let mut mp: u64 = z / 2;
        let mut w: u64 = 1;
        proof { lemma2_to64(); lemma_pow2_unfold(1); }
        while mp % 2 == 0
            invariant
                1 <= w <= 63, mp >= 1, z as nat == pow2(w as nat) * (mp as nat),
                z <= 0x4000000000000000,
            decreases mp,
        {
            proof {
                lemma_pow2_unfold((w + 1) as nat);
                assert(w + 1 <= 63) by {
                    if w + 1 > 63 {
                        lemma_pow2_mono(63, w as nat);
                        lemma2_to64_rest();
                        assert(pow2(63) == 0x8000000000000000);
                        assert(z as nat >= pow2(w as nat)) by(nonlinear_arith) requires z as nat == pow2(w as nat) * (mp as nat), mp >= 1;
                    }
                }
                assert(mp / 2 >= 1);
                assert(z as nat == pow2((w + 1) as nat) * ((mp / 2) as nat)) by(nonlinear_arith)
                    requires z as nat == pow2(w as nat) * (mp as nat), mp % 2 == 0,
                        pow2((w + 1) as nat) == 2 * pow2(w as nat), mp == 2 * (mp / 2);
            }
            mp = mp / 2;
            w = w + 1;
        }
        proof {
            lemma_pow2_pos(w as nat);
            assert(w <= 62) by {
                if w > 62 {
                    lemma_pow2_mono(63, w as nat);
                    lemma2_to64_rest();
                    assert(z as nat >= pow2(w as nat)) by(nonlinear_arith) requires z as nat == pow2(w as nat) * (mp as nat), mp >= 1;
                }
            }
        }
        if mp == 1 {
            proof {
                assert(zkl(w as nat, w as nat) == pow2(w as nat));
                assert(pow2(w as nat) as int == 1 * (z as int) + 0);
                lemma_fundamental_div_mod_converse(pow2(w as nat) as int, z as int, 1, 0);
            }
            Some((w, w))
        } else {
            proof {
                assert(mp <= z) by(nonlinear_arith) requires z as nat == pow2(w as nat) * (mp as nat), pow2(w as nat) >= 1;
            }
            match orderm2(mp) {
                None => None,
                Some(kp) => {
                    if kp > 62 - w {
                        return None;
                    }
                    let k = kp + w;
                    proof {
                        lemma_pow2_adds(w as nat, kp as nat);
                        lemma_pow2_strictly_increases(w as nat, k as nat);
                        lemma_fundamental_div_mod(pow2(kp as nat) as int - 1, mp as int);
                        let q = (pow2(kp as nat) as int - 1) / (mp as int);
                        assert(zkl(k as nat, w as nat) as int == (z as int) * q) by(nonlinear_arith)
                            requires zkl(k as nat, w as nat) as int == pow2(k as nat) - pow2(w as nat),
                                pow2(k as nat) == pow2(w as nat) * pow2(kp as nat),
                                pow2(kp as nat) as int - 1 == mp * q,
                                z as nat == pow2(w as nat) * (mp as nat);
                        assert(zkl(k as nat, w as nat) as int == q * (z as int) + 0) by(nonlinear_arith)
                            requires zkl(k as nat, w as nat) as int == (z as int) * q;
                        lemma_fundamental_div_mod_converse(zkl(k as nat, w as nat) as int, z as int, q, 0);
                    }
                    Some((k, w))
                }
            }
        }
    }
}

// ── reduce_fractions ──────────────────────────────────────────────────────────

/// The input to `reduce_fractions` / `make_matrix`: weights M summing to Z_kl.
pub open spec fn wf_kl(ms: Seq<u128>, k: nat, l: nat) -> bool {
    &&& 0 < k <= 124
    &&& l <= k
    &&& ms.len() >= 1
    &&& wsum_nat(ms, 0) == zkl(k, l)
}

/// Every M_r < Z_kl, except in the degenerate Z_kl = 1 (k = 1, l = 0).
pub open spec fn proper_kl(ms: Seq<u128>, k: nat, l: nat) -> bool {
    forall |r: int| 0 <= r < ms.len() ==> (#[trigger] ms[r] as nat) < zkl(k, l) || (k == 1 && l == 0)
}

/// M'/Z' = M/Z labelwise.
pub open spec fn same_dist(ms: Seq<u128>, z: nat, ms2: Seq<u128>, z2: nat) -> bool {
    &&& ms2.len() == ms.len()
    &&& forall |r: int| 0 <= r < ms.len() ==> (#[trigger] ms2[r] as nat) * z == (ms[r] as nat) * z2
}

proof fn lemma_sum_halve(ms: Seq<u128>, ms2: Seq<u128>, r: nat)
    requires ms2.len() == ms.len(), r <= ms.len(),
        forall |i: int| 0 <= i < ms.len() ==> (#[trigger] ms[i]) as nat == 2 * (ms2[i] as nat),
    ensures wsum_nat(ms, r) == 2 * wsum_nat(ms2, r),
    decreases ms.len() - r,
{
    if r < ms.len() { lemma_sum_halve(ms, ms2, r + 1); }
}

proof fn lemma_sum_const(ms: Seq<u128>, v: nat, r: nat)
    requires r <= ms.len(), forall |i: int| 0 <= i < ms.len() ==> (#[trigger] ms[i]) as nat == v,
    ensures wsum_nat(ms, r) == (ms.len() - r) * v,
    decreases ms.len() - r,
{
    if r < ms.len() {
        lemma_sum_const(ms, v, r + 1);
        assert(v + (ms.len() - (r + 1)) * v == (ms.len() - r) * v) by(nonlinear_arith);
    } else {
        assert((ms.len() - r) * v == 0) by(nonlinear_arith) requires ms.len() - r == 0;
    }
}

/// If one weight is the whole sum, the others are 0.
proof fn lemma_sum_one_full(ms: Seq<u128>, r0: nat, i: nat, r: nat)
    requires r0 < ms.len(), i < ms.len(), i != r0, r <= ms.len(),
        r <= r0 && r <= i ==> ms[r0 as int] as nat == wsum_nat(ms, r),
    ensures r <= r0 && r <= i ==> ms[i as int] == 0,
    decreases ms.len() - r,
{
    if r < ms.len() && r <= r0 && r <= i {
        if r == r0 {
            lemma_w_le_sum(ms, r + 1, i);
        } else if r == i {
            lemma_w_le_sum(ms, r + 1, r0);
        } else {
            lemma_w_le_sum(ms, r + 1, r0);
            lemma_sum_one_full(ms, r0, i, r + 1);
        }
    }
}

/// `reduce_fractions(Ms, k, l)`: simplify M / Z_kl, as the original does. Same
/// branches as the original; where it would fail an assertion (all M equal
/// but n not a power of two, e.g. the uniform distribution on 6), the input
/// is returned unchanged.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub fn reduce_fractions(ms: &Vec<u128>, k: u64, l: u64) -> (r: (Vec<u128>, u64, u64))
    requires wf_kl(ms@, k as nat, l as nat),
    ensures
        wf_kl(r.0@, r.1 as nat, r.2 as nat),
        r.1 <= k,
        proper_kl(r.0@, r.1 as nat, r.2 as nat),
        same_dist(ms@, zkl(k as nat, l as nat), r.0@, zkl(r.1 as nat, r.2 as nat)),
    decreases k,
{
    let n = ms.len();
    let z = get_zkl(k, l);
    proof {
        lemma_zkl(k as nat, l as nat);
        lemma_pow2_mono(k as nat, 124);
        lemma_pow2_consts();
    }
    // any(M == Zkl)
    let mut i: usize = 0;
    while i < n
        invariant n == ms.len(), i <= n, z as nat == zkl(k as nat, l as nat), z > 0,
            wf_kl(ms@, k as nat, l as nat),
            forall |j: int| 0 <= j < i ==> ms@[j] != z,
        decreases n - i,
    {
        if ms[i] == z {
            let ghost r0 = i as nat;
            let mut out: Vec<u128> = Vec::new();
            let mut j: usize = 0;
            while j < n
                invariant n == ms.len(), j <= n, out.len() == j, z > 0, ms@[r0 as int] == z, r0 < n,
                    wsum_nat(ms@, 0) == z as nat,
                    forall |t: int| 0 <= t < j ==> (#[trigger] out@[t]) as nat == (ms@[t] as nat) / (z as nat)
                        && (out@[t] == 1) == (t == r0),
                decreases n - j,
            {
                proof {
                    if j as nat != r0 {
                        lemma_sum_one_full(ms@, r0, j as nat, 0);
                    } else {
                        lemma_fundamental_div_mod_converse(z as int, z as int, 1, 0);
                    }
                }
                out.push(ms[j] / z);
                j = j + 1;
            }
            proof {
                lemma2_to64();
                lemma_pow2_unfold(1);
                assert(zkl(1, 0) == 1);
                assert forall |t: int| 0 <= t < n implies (#[trigger] out@[t] as nat) * (z as nat) == (ms@[t] as nat) * 1 by {
                    if t != r0 { lemma_sum_one_full(ms@, r0, t as nat, 0); }
                }
                assert forall |t: int| 0 <= t < n implies (#[trigger] out@[t] == 1) == (t == r0) && out@[t] <= 1 by {
                    if t != r0 { lemma_sum_one_full(ms@, r0, t as nat, 0); }
                }
                lemma_sum_unit(out@, r0, 0);
            }
            return (out, 1, 0);
        }
        i = i + 1;
    }
    proof {
        assert forall |r: int| 0 <= r < n implies (#[trigger] ms@[r] as nat) < zkl(k as nat, l as nat) by {
            lemma_w_le_sum(ms@, 0, r as nat);
        }
    }
    if l == 0 {
        return (ms.clone(), k, l);
    }
    // all(M % 2 == 0)
    let mut even = true;
    let mut i: usize = 0;
    while i < n
        invariant n == ms.len(), i <= n, even == forall |j: int| 0 <= j < i ==> ms@[j] % 2 == 0,
        decreases n - i,
    {
        if ms[i] % 2 != 0 { even = false; }
        i = i + 1;
    }
    if even {
        let mut half: Vec<u128> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant n == ms.len(), j <= n, half.len() == j,
                forall |t: int| 0 <= t < n ==> ms@[t] % 2 == 0,
                forall |t: int| 0 <= t < j ==> (#[trigger] half@[t]) as nat * 2 == ms@[t] as nat,
            decreases n - j,
        {
            proof { assert(ms@[j as int] % 2 == 0); }
            half.push(ms[j] / 2);
            j = j + 1;
        }
        proof {
            assert forall |t: int| 0 <= t < n implies (#[trigger] ms@[t]) as nat == 2 * (half@[t] as nat) by {}
            lemma_sum_halve(ms@, half@, 0);
            // k ≥ 2: with k = l = 1, Z = 2 and even weights none equal to 2 cannot sum to 2.
            assert(k >= 2) by {
                if k == 1 {
                    lemma_pow2_unfold(1);
                    lemma2_to64();
                    assert(zkl(1, 1) == 2);
                    assert(wsum_nat(half@, 0) == 1);
                    assert forall |t: int| 0 <= t < n implies (#[trigger] half@[t]) == 0 by {
                        lemma_w_le_sum(half@, 0, t as nat);
                    }
                    lemma_sum_const(half@, 0, 0);
                    assert((n - 0) * 0 == 0) by(nonlinear_arith);
                }
            }
            lemma_zkl((k - 1) as nat, (l - 1) as nat);
            lemma_pow2_unfold(k as nat);
            lemma_pow2_unfold(l as nat);
            assert(zkl(k as nat, l as nat) == 2 * zkl((k - 1) as nat, (l - 1) as nat));
        }
        let (out, k2, l2) = reduce_fractions(&half, k - 1, l - 1);
        proof {
            let z1 = zkl((k - 1) as nat, (l - 1) as nat);
            let z2 = zkl(k2 as nat, l2 as nat);
            assert forall |t: int| 0 <= t < n implies (#[trigger] out@[t] as nat) * zkl(k as nat, l as nat) == (ms@[t] as nat) * z2 by {
                let o = out@[t] as nat;
                let h = half@[t] as nat;
                assert(o * z1 == h * z2);
                assert(o * zkl(k as nat, l as nat) == (ms@[t] as nat) * z2) by(nonlinear_arith)
                    requires o * z1 == h * z2, zkl(k as nat, l as nat) == 2 * z1, ms@[t] as nat == 2 * h;
            }
        }
        return (out, k2, l2);
    }
    // all(M == Ms[0])
    let m0 = ms[0];
    let mut same = true;
    let mut i: usize = 0;
    while i < n
        invariant n == ms.len(), n >= 1, i <= n, m0 == ms@[0], same == forall |j: int| 0 <= j < i ==> ms@[j] == m0,
        decreases n - i,
    {
        if ms[i] != m0 { same = false; }
        i = i + 1;
    }
    if same && m0 > 0 && z % m0 == 0 {
        // remainder = Zkl / Ms[0] (= n); base = log2(remainder), exactly.
        let rem = z / m0;
        let mut b: u64 = 0;
        let mut pb: u128 = 1;
        proof { lemma2_to64(); }
        while pb < rem
            invariant pb as nat == pow2(b as nat), rem <= 0x10000000000000000000000000000000, b <= 124,
                pb <= 0x10000000000000000000000000000000,
            decreases 124 - b,
        {
            proof {
                lemma_pow2_unfold((b + 1) as nat);
                assert(b + 1 <= 124) by {
                    if b + 1 > 124 { lemma_pow2_mono(124, b as nat); lemma_pow2_consts(); }
                }
            }
            proof { lemma_pow2_mono((b + 1) as nat, 124); lemma_pow2_consts(); }
            pb = 2 * pb;
            b = b + 1;
        }
        if pb == rem && b >= 1 {
            let mut out: Vec<u128> = Vec::new();
            let mut j: usize = 0;
            while j < n
                invariant j <= n, out.len() == j, forall |t: int| 0 <= t < j ==> (#[trigger] out@[t]) == 1,
                decreases n - j,
            {
                out.push(1);
                j = j + 1;
            }
            proof {
                lemma_fundamental_div_mod(z as int, m0 as int);
                assert forall |t: int| 0 <= t < n implies (#[trigger] ms@[t]) as nat == m0 as nat by {}
                lemma_sum_const(ms@, m0 as nat, 0);
                lemma_sum_const(out@, 1, 0);
                assert(n * (m0 as nat) == z as nat);
                assert(rem as nat == n) by(nonlinear_arith)
                    requires z as nat == m0 * rem, n * (m0 as nat) == z as nat, m0 > 0;
                assert(zkl(b as nat, b as nat) == pow2(b as nat));
                assert forall |t: int| 0 <= t < n implies (#[trigger] out@[t] as nat) * (z as nat) == (ms@[t] as nat) * pow2(b as nat) by {
                    assert((z as nat) == (m0 as nat) * (pow2(b as nat))) by(nonlinear_arith)
                        requires z as nat == m0 * rem, rem as nat == pow2(b as nat);
                }
                assert(n >= 2) by {
                    if n < 2 {
                        assert(ms@[0] as nat == z as nat) by {
                            lemma_sum_const(ms@, m0 as nat, 0);
                            assert(n == 1);
                            assert((n - 0) * (m0 as nat) == m0 as nat) by(nonlinear_arith) requires n == 1;
                        }
                    }
                }
                assert(b <= k) by {
                    if b > k {
                        lemma_pow2_strictly_increases(k as nat, b as nat);
                        assert(rem as nat <= z as nat) by(nonlinear_arith) requires z as nat == m0 * rem, m0 >= 1;
                    }
                }
                assert((n - 0) * 1 == n) by(nonlinear_arith);
            }
            return (out, b, b);
        }
    }
    (ms.clone(), k, l)
}

proof fn lemma_sum_unit(ms: Seq<u128>, r0: nat, r: nat)
    requires r0 < ms.len(), r <= ms.len(),
        forall |t: int| 0 <= t < ms.len() ==> (#[trigger] ms[t] == 1) == (t == r0) && ms[t] <= 1,
    ensures wsum_nat(ms, r) == if r <= r0 { 1nat } else { 0nat },
    decreases ms.len() - r,
{
    if r < ms.len() { lemma_sum_unit(ms, r0, r + 1); }
}

} // verus!
