//! Build the entropy-optimal sampler of an exact
//! rational distribution p (Section 5). Z is the least common denominator,
//! (k, l) the shape of the binary expansion of 1/Z, so p_i = M_i / Z_kl.
//!
//! `construct_sample_ky_encoding` builds the packed tree through the
//! generic `ddg_walk::{tree, packing}`.

use vstd::prelude::*;

verus! {

use crate::optas::utils::{get_common_denominator, get_binary_expansion_length, get_zkl,
    get_common_numerators};
use crate::optas::matrix::{make_ddg_matrix, make_hamming_vector, make_hamming_matrix};
#[cfg(verus_keep_ghost)]
use crate::optas::utils::{zkl, fval, wf_fracs, wf_kl, normalize_vector, lemma_zkl};
#[cfg(verus_keep_ghost)]
use crate::optas::matrix::{col_pre, is_hamming_matrix, lemma_is_matrix_bits};
#[cfg(verus_keep_ghost)]
use crate::optas::ztype::wsum_nat;
#[cfg(verus_keep_ghost)]
use crate::optas::sample::sampler_input;
use crate::optas::tree::{make_leaf_table, OptasSpec};
use crate::optas::sample::degenerate_label;
#[cfg(verus_keep_ghost)]
use crate::optas::tree::{optas_point, lemma_optas_point};
use crate::ddg_walk::encoding::{construct_encoding, Encoded};
#[cfg(verus_keep_ghost)]
use crate::ddg_walk::walk::DdgWalk;
#[cfg(verus_keep_ghost)]
use crate::ddg_walk::walk::DdgSpec;
#[cfg(verus_keep_ghost)]
use crate::fldr_helper::lemma_nat_mul_real_cast;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse};

/// Σ_{i ∈ [r, n)} p_i.
pub open spec fn frac_sum(p: Seq<(u64, u64)>, r: nat) -> real
    decreases p.len() - r,
{
    if r >= p.len() { 0real } else { fval(p[r as int]) + frac_sum(p, r + 1) }
}

/// The input of `construct_sample_ky_matrix`: a probability vector of
/// fractions (`Fraction`s in the original).
pub open spec fn wf_dist(p: Seq<(u64, u64)>) -> bool {
    &&& wf_fracs(p)
    &&& 1 <= p.len() < 0x4000000000000000
    &&& frac_sum(p, 0) == 1real
}

/// The sampler built from p samples p exactly: M_r / Z_kl = p_r.
pub open spec fn samples_exactly(p: Seq<(u64, u64)>, ms: Seq<u128>, k: nat, l: nat) -> bool {
    &&& ms.len() == p.len()
    &&& forall |r: int| 0 <= r < p.len() ==> #[trigger] normalize_vector(zkl(k, l), ms)(r as nat) == fval(p[r])
}

proof fn lemma_dvd_trans(a: nat, b: nat, c: nat)
    requires a > 0, b > 0, b % a == 0, c % b == 0,
    ensures c % a == 0,
{
    lemma_fundamental_div_mod(b as int, a as int);
    lemma_fundamental_div_mod(c as int, b as int);
    let x = b / a;
    let y = c / b;
    assert(c == (x * y) * a) by(nonlinear_arith) requires b == a * x + 0, c == b * y + 0;
    lemma_fundamental_div_mod_converse(c as int, a as int, (x * y) as int, 0);
}

/// M_r = Z·p_r as reals, and Σ M = Z·Σ p.
proof fn lemma_numerators(p: Seq<(u64, u64)>, z: nat, ms: Seq<u128>, r: nat)
    requires
        wf_fracs(p), z > 0, ms.len() == p.len(), r <= p.len(),
        forall |i: int| 0 <= i < p.len() ==> (#[trigger] ms[i] as nat) * (p[i].1 as nat) == z * (p[i].0 as nat),
    ensures
        (wsum_nat(ms, r) as real) == (z as real) * frac_sum(p, r),
        forall |i: int| r <= i < p.len() ==> (#[trigger] ms[i] as real) / (z as real) == fval(p[i]),
    decreases p.len() - r,
{
    if r < p.len() {
        lemma_numerators(p, z, ms, r + 1);
        let m = ms[r as int] as nat;
        let num = p[r as int].0 as nat;
        let den = p[r as int].1 as nat;
        lemma_nat_mul_real_cast(m, den);
        lemma_nat_mul_real_cast(z, num);
        let zr = z as real;
        assert((m as real) == zr * ((num as real) / (den as real))) by(nonlinear_arith)
            requires (m as real) * (den as real) == zr * (num as real), den > 0;
        assert((m as real) / zr == (num as real) / (den as real)) by(nonlinear_arith)
            requires (m as real) == zr * ((num as real) / (den as real)), zr > 0real;
        assert((m as real) + zr * frac_sum(p, r + 1) == zr * frac_sum(p, r)) by(nonlinear_arith)
            requires (m as real) == zr * fval(p[r as int]), frac_sum(p, r) == fval(p[r as int]) + frac_sum(p, r + 1);
    } else {
        assert((z as real) * 0real == 0real);
    }
}

/// `construct_sample_ky_matrix(p_target)`: (P, k, l) for an exact rational
/// distribution (and the weights M of P, ghost). None if the denominators
/// or the expansion need more than 62 bits.
pub fn construct_sample_ky_matrix(p_target: &Vec<(u64, u64)>) -> (r: Option<(Vec<Vec<u8>>, u64, u64, Ghost<Seq<u128>>)>)
    requires wf_dist(p_target@),
    ensures r matches Some((p, k, l, ms)) ==> sampler_input(p@, ms@, k as nat, l as nat)
        && samples_exactly(p_target@, ms@, k as nat, l as nat),
{
    let z = match get_common_denominator(p_target) { Some(z) => z, None => { return None; } };
    let (k, l) = match get_binary_expansion_length(z) { Some(kl) => kl, None => { return None; } };
    let zkl_v = get_zkl(k, l);
    proof {
        lemma_zkl(k as nat, l as nat);
        assert forall |i: int| 0 <= i < p_target.len() implies (zkl_v as nat) % (#[trigger] p_target@[i].1 as nat) == 0 by {
            lemma_dvd_trans(p_target@[i].1 as nat, z as nat, zkl_v as nat);
        }
    }
    let ms = get_common_numerators(zkl_v, p_target);
    proof {
        lemma_numerators(p_target@, zkl_v as nat, ms@, 0);
        assert((wsum_nat(ms@, 0) as real) == (zkl_v as real));
        assert(wf_kl(ms@, k as nat, l as nat));
    }
    let (p, k2, l2, ms2) = make_ddg_matrix(&ms, k, l);
    proof {
        lemma_zkl(k2 as nat, l2 as nat);
        let z1 = zkl(k as nat, l as nat);
        let z2 = zkl(k2 as nat, l2 as nat);
        assert forall |r: int| 0 <= r < p_target.len() implies
            #[trigger] normalize_vector(z2, ms2@)(r as nat) == fval(p_target@[r]) by {
            let a = ms@[r] as nat;
            let b = ms2@[r] as nat;
            assert(b * z1 == a * z2);
            lemma_nat_mul_real_cast(b, z1);
            lemma_nat_mul_real_cast(a, z2);
            assert((b as real) / (z2 as real) == (a as real) / (z1 as real)) by(nonlinear_arith)
                requires (b as real) * (z1 as real) == (a as real) * (z2 as real), z1 > 0, z2 > 0;
        }
    }
    Some((p, k2, l2, ms2))
}

/// `construct_sample_ky_matrix_cached(p_target)`: (k, l, h, T), plus P and
/// M (ghost).
pub fn construct_sample_ky_matrix_cached(p_target: &Vec<(u64, u64)>)
    -> (r: Option<(u64, u64, Vec<u64>, Vec<Vec<i64>>, Ghost<Seq<Vec<u8>>>, Ghost<Seq<u128>>)>)
    requires wf_dist(p_target@),
    ensures r matches Some((k, l, h, t, p, ms)) ==>
        sampler_input(p@, ms@, k as nat, l as nat)
        && samples_exactly(p_target@, ms@, k as nat, l as nat)
        && h.len() == k
        && (forall |c: int| 0 <= c < k ==> (#[trigger] h@[c]) as nat == col_pre(p@, c as nat, p@.len() as nat))
        && is_hamming_matrix(t@, p@, k as nat),
{
    let (p, k, l, ms) = match construct_sample_ky_matrix(p_target) { Some(x) => x, None => { return None; } };
    proof {
        lemma_is_matrix_bits(p@, ms@, k as nat, l as nat);
        assert(p@[0].len() == k);
    }
    let h = make_hamming_vector(&p, k as usize);
    let t = make_hamming_matrix(&p, k as usize);
    Some((k, l, h, t, Ghost(p@), ms))
}

/// The packed encoding of the sampler of P (any table with an internal
/// root), or the one-slot encoding of the point mass when Z = 1.
pub fn encode_ky_matrix(p: &Vec<Vec<u8>>, k: u64, l: u64, Ghost(ms): Ghost<Seq<u128>>) -> (r: Option<Encoded<OptasSpec>>)
    requires sampler_input(p@, ms, k as nat, l as nat),
    ensures
        r matches Some(enc) ==> enc.wf() && enc.spec@ == (OptasSpec { ms, k: k as nat, l: l as nat }),
        ms.len() < 0x4000000000000 ==> r is Some,
{
    let ghost os = OptasSpec { ms, k: k as nat, l: l as nat };
    let n = p.len();
    if k == 1 && l == 0 {
        // `if k == 1 and l == 0: root.label = 1`: the label with M_r = 1.
        let r = degenerate_label(p, Ghost(ms));
        let mut enc: Vec<i64> = Vec::new();
        enc.push(-(r as i64) - 1);
        let res = Encoded { enc, n: n as u64, exact: false, spec: Ghost(os), node_at: Ghost(Seq::empty()) };
        proof {
            assert(res.enc@ =~= seq![(-(r as int) - 1) as i64]);
            assert(os.point() == Some(r as nat));
        }
        return Some(res);
    }
    if n as u64 >= 0x4000000000000 {
        return None;
    }
    let tab = make_leaf_table(p, k, l, Ghost(ms));
    let (enc, node_at) = construct_encoding(&tab);
    Some(Encoded { enc, n: n as u64, exact: l == k, spec: Ghost(os), node_at })
}

/// `construct_sample_ky_encoding(p_target)`: (enc, n, k). None if the
/// denominators or the expansion need more than 62 bits, or if the
/// encoding does not fit (n ≥ 2⁵⁰).
pub fn construct_sample_ky_encoding(p_target: &Vec<(u64, u64)>) -> (r: Option<(Encoded<OptasSpec>, u64, u64)>)
    requires wf_dist(p_target@),
    ensures r matches Some((enc, n, k)) ==>
        enc.wf() && n as nat == p_target@.len() && k as nat == enc.spec@.k
        && samples_exactly(p_target@, enc.spec@.ms, enc.spec@.k, enc.spec@.l),
{
    let (p, k, l, ms) = match construct_sample_ky_matrix(p_target) { Some(x) => x, None => { return None; } };
    let enc = match encode_ky_matrix(&p, k, l, ms) { Some(x) => x, None => { return None; } };
    let n = enc.n;
    Some((enc, n, k))
}

} // verus!
