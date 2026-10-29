//! The DDG of M / Z_kl: the leaf table (`make_leaf_table`), the
//! level-structured tree [`optas_ddg`] that `ddg_walk` packs, and
//! [`OptasSpec`], M / Z_kl as a `DdgSpec`, whose fuel law comes from
//! `ztype.rs` (`lemma_optas_walk`). Unlike the original, `make_leaf_table`
//! lists each level's leaves in row order rather than in a dict.

use vstd::prelude::*;

verus! {

#[cfg(verus_keep_ghost)]
use crate::ddg_walk::walk::*;
use crate::ddg_walk::tree::*;
use crate::ddg_walk::walk::DdgSpec;
#[cfg(verus_keep_ghost)]
use crate::optas::ztype::*;
#[cfg(verus_keep_ghost)]
use crate::optas::matrix::*;
#[cfg(verus_keep_ghost)]
use crate::optas::sample::*;
#[cfg(verus_keep_ghost)]
use crate::optas::utils::{zkl, wf_kl, proper_kl, lemma_zkl};
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::{pow2, lemma2_to64};
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;

// ── The DDG of M / Z_kl, level-structured ────────────────────────────────────

/// The x-th leaf of level j (in label order).
pub open spec fn optas_lab(ms: Seq<u128>, z: nat, j: nat, x: nat) -> nat {
    choose |r: nat| r < ms.len() && ddg_bit(ms, z, j, r) == 1 && ddg_pre(ms, z, j, r) == x
}

/// The tree of `sample.rs`, cut at depth k: depth j ≤ k is level j of the
/// unrolled tree, and depth k wraps to depth l. In the degenerate case
/// Z = 1 the root is the leaf (any valid shape will do; only `point` is
/// used).
pub open spec fn optas_ddg(ms: Seq<u128>, k: nat, l: nat) -> LDdg {
    let z = zkl(k, l);
    if k == 1 && l == 0 {
        LDdg { n: ms.len(), levels: 1, wrap: 0, h: |j: nat| if j == 1 { 2nat } else { 0nat }, lab: |j: nat, x: nat| 0nat }
    } else {
        LDdg {
            n: ms.len(),
            levels: k,
            wrap: if l < k { l } else { 0 },
            h: |j: nat| if 1 <= j <= k { ddg_h(ms, z, j, 0) } else { 0nat },
            lab: |j: nat, x: nat| optas_lab(ms, z, j, x),
        }
    }
}

/// The residues after j bits and after c bits agree.
pub open spec fn rho_eq(ms: Seq<u128>, z: nat, j: nat, c: nat) -> bool {
    forall |r: nat| r < ms.len() ==> #[trigger] ddg_rho(ms, z, j, r) == ddg_rho(ms, z, c, r)
}

/// Σ_{r' ≥ r} 2^j M_{r'} mod Z.
pub open spec fn rho_sum(ms: Seq<u128>, z: nat, j: nat, r: nat) -> nat
    decreases ms.len() - r,
{
    if r >= ms.len() { 0 } else { ddg_rho(ms, z, j, r) + rho_sum(ms, z, j, r + 1) }
}

proof fn lemma_rho_sum(ms: Seq<u128>, z: nat, j: nat, r: nat)
    requires z > 0, r <= ms.len(),
    ensures z * ddg_fs(ms, z, j, r) + rho_sum(ms, z, j, r) == pow2(j) * wsum_nat(ms, r),
    decreases ms.len() - r,
{
    if r < ms.len() {
        lemma_rho_sum(ms, z, j, r + 1);
        let a = pow2(j) * (ms[r as int] as nat);
        lemma_fundamental_div_mod(a as int, z as int);
        let f1 = ddg_fs(ms, z, j, r + 1);
        let s1 = rho_sum(ms, z, j, r + 1);
        let w1 = wsum_nat(ms, r + 1);
        assert(z * (a / z + f1) == z * (a / z) + z * f1) by(nonlinear_arith);
        assert(pow2(j) * ((ms[r as int] as nat) + w1) == pow2(j) * (ms[r as int] as nat) + pow2(j) * w1) by(nonlinear_arith);
    } else {
        assert(z * 0 == 0 && pow2(j) * 0 == 0);
    }
}

proof fn lemma_rho_sum_eq(ms: Seq<u128>, z: nat, j: nat, c: nat, r: nat)
    requires rho_eq(ms, z, j, c),
    ensures rho_sum(ms, z, j, r) == rho_sum(ms, z, c, r),
    decreases ms.len() - r,
{
    if r < ms.len() { lemma_rho_sum_eq(ms, z, j, c, r + 1); }
}

/// Z·A(j) = Σ_r 2^j M_r mod Z, so A depends only on the residues.
proof fn lemma_internal_eq(ms: Seq<u128>, z: nat, j: nat, c: nat)
    requires z > 0, wsum_nat(ms, 0) == z, rho_eq(ms, z, j, c),
    ensures ddg_num_internal(ms, z, j) == ddg_num_internal(ms, z, c),
{
    lemma_rho_sum(ms, z, j, 0);
    lemma_rho_sum(ms, z, c, 0);
    lemma_rho_sum_eq(ms, z, j, c, 0);
    let aj = ddg_num_internal(ms, z, j);
    let ac = ddg_num_internal(ms, z, c);
    let fj = ddg_fs(ms, z, j, 0) as int;
    let fc = ddg_fs(ms, z, c, 0) as int;
    let s = rho_sum(ms, z, j, 0) as int;
    assert(z * aj == s) by(nonlinear_arith)
        requires aj == pow2(j) as int - fj, z * fj + s == pow2(j) * z;
    assert(z * ac == s) by(nonlinear_arith)
        requires ac == pow2(c) as int - fc, z * fc + s == pow2(c) * z;
    assert(aj == ac) by(nonlinear_arith) requires z * aj == z * ac, z > 0;
}

/// Equal residues give the same leaves one level down.
proof fn lemma_level_eq(ms: Seq<u128>, z: nat, j: nat, c: nat, r: nat)
    requires z > 0, rho_eq(ms, z, j, c), r <= ms.len(),
    ensures
        ddg_h(ms, z, j + 1, r) == ddg_h(ms, z, c + 1, r),
        ddg_pre(ms, z, j + 1, r) == ddg_pre(ms, z, c + 1, r),
        forall |r2: nat| r2 < ms.len() ==> #[trigger] ddg_bit(ms, z, j + 1, r2) == ddg_bit(ms, z, c + 1, r2),
{
    assert forall |r2: nat| r2 < ms.len() implies #[trigger] ddg_bit(ms, z, j + 1, r2) == ddg_bit(ms, z, c + 1, r2) by {
        lemma_ddg_bit_agree(ms, z, j + 1, c + 1, r2);
    }
    lemma_h_eq(ms, z, j, c, r);
    lemma_pre_eq(ms, z, j, c, r);
}

proof fn lemma_h_eq(ms: Seq<u128>, z: nat, j: nat, c: nat, r: nat)
    requires z > 0, forall |r2: nat| r2 < ms.len() ==> #[trigger] ddg_bit(ms, z, j + 1, r2) == ddg_bit(ms, z, c + 1, r2),
    ensures ddg_h(ms, z, j + 1, r) == ddg_h(ms, z, c + 1, r),
    decreases ms.len() - r,
{
    if r < ms.len() { lemma_h_eq(ms, z, j, c, r + 1); }
}

proof fn lemma_pre_eq(ms: Seq<u128>, z: nat, j: nat, c: nat, r: nat)
    requires z > 0, r <= ms.len(), forall |r2: nat| r2 < ms.len() ==> #[trigger] ddg_bit(ms, z, j + 1, r2) == ddg_bit(ms, z, c + 1, r2),
    ensures ddg_pre(ms, z, j + 1, r) == ddg_pre(ms, z, c + 1, r),
    decreases r,
{
    if r > 0 { lemma_pre_eq(ms, z, j, c, (r - 1) as nat); }
}

/// Leaf x of level j (x < h) exists, and is the only label there.
pub proof fn lemma_optas_lab(ms: Seq<u128>, z: nat, j: nat, x: nat)
    requires z > 0, j >= 1, x < ddg_h(ms, z, j, 0),
    ensures ({
        let r = optas_lab(ms, z, j, x);
        r < ms.len() && ddg_bit(ms, z, j, r) == 1 && ddg_pre(ms, z, j, r) == x
    }),
{
    lemma_ddg_pre_h(ms, z, j, ms.len() as nat);
    let w = lemma_pre_witness(ms, z, j, ms.len() as nat, x);
}

pub proof fn lemma_optas_lab_unique(ms: Seq<u128>, z: nat, j: nat, a: nat, b: nat)
    requires z > 0, j >= 1, a < ms.len(), b < ms.len(),
        ddg_bit(ms, z, j, a) == 1, ddg_bit(ms, z, j, b) == 1, ddg_pre(ms, z, j, a) == ddg_pre(ms, z, j, b),
    ensures a == b,
{
    if a < b {
        lemma_ddg_pre_mono(ms, z, j, a, b);
        lemma_ddg_pre_mono(ms, z, j, a + 1, b);
    } else if b < a {
        lemma_ddg_pre_mono(ms, z, j, b, a);
        lemma_ddg_pre_mono(ms, z, j, b + 1, a);
    }
}

/// A(c) of the level structure is the A(c) of `ztype.rs`.
pub proof fn lemma_optas_lnum(ms: Seq<u128>, k: nat, l: nat, c: nat)
    requires wf_kl(ms, k, l), proper_kl(ms, k, l), !(k == 1 && l == 0), c <= k,
    ensures lnum(optas_ddg(ms, k, l), c) == ddg_num_internal(ms, zkl(k, l), c),
    decreases c,
{
    lemma_zkl(k, l);
    let z = zkl(k, l);
    if c == 0 {
        lemma_root_internal(ms, k, l, |i: nat| 0real, 0);
    } else {
        lemma_optas_lnum(ms, k, l, (c - 1) as nat);
        lemma_ddg_shape(ms, z, (c - 1) as nat);
    }
}

/// The level structure is valid, and A(k) ≤ A(wrap).
pub proof fn lemma_optas_valid(ms: Seq<u128>, k: nat, l: nat)
    requires wf_kl(ms, k, l), proper_kl(ms, k, l),
    ensures
        valid_ldd(optas_ddg(ms, k, l)),
        (optas_ddg(ms, k, l).h)(0) == 0,
        !(k == 1 && l == 0) ==> forall |j: nat| j <= k ==> #[trigger] lnum(optas_ddg(ms, k, l), j) == ddg_num_internal(ms, zkl(k, l), j),
        !(k == 1 && l == 0) && l == k ==> lnum(optas_ddg(ms, k, l), k) == 0,
        forall |j: nat, x: nat| x < (optas_ddg(ms, k, l).h)(j) ==> #[trigger] (optas_ddg(ms, k, l).lab)(j, x) < ms.len(),
{
    let t = optas_ddg(ms, k, l);
    lemma_zkl(k, l);
    let z = zkl(k, l);
    if k == 1 && l == 0 {
        assert(lnum(t, 0) == 1);
        assert(lnum(t, 1) == 0);
    } else {
        assert forall |j: nat| j <= k implies #[trigger] lnum(t, j) == ddg_num_internal(ms, z, j) by {
            lemma_optas_lnum(ms, k, l, j);
        }
        assert forall |j: nat| 1 <= j <= t.levels implies (#[trigger] (t.h)(j)) <= 2 * lnum(t, (j - 1) as nat) by {
            lemma_ddg_shape(ms, z, (j - 1) as nat);
            lemma_ddg_shape(ms, z, j);
            assert(lnum(t, (j - 1) as nat) == ddg_num_internal(ms, z, (j - 1) as nat));
        }
        if l < k {
            assert(rho_eq(ms, z, k, l)) by {
                assert forall |r: nat| r < ms.len() implies #[trigger] ddg_rho(ms, z, k, r) == ddg_rho(ms, z, l, r) by {
                    lemma_ddg_wrap(ms, k, l, r);
                }
            }
            lemma_internal_eq(ms, z, k, l);
            assert(lnum(t, k) == ddg_num_internal(ms, z, k));
            assert(lnum(t, l) == ddg_num_internal(ms, z, l));
        } else {
            assert forall |r: nat| r < ms.len() implies #[trigger] ddg_rho(ms, z, k, r) == 0 by {
                lemma_ddg_rho_pow2(ms, k, k, r);
            }
            lemma_ddg_internal_zero(ms, z, k);
            lemma_ddg_shape(ms, z, 0);
            assert(lnum(t, k) == 0);
            assert(lnum(t, 0) == 1);
        }
        assert forall |j: nat, x: nat| x < (t.h)(j) implies #[trigger] (t.lab)(j, x) < ms.len() by {
            lemma_optas_lab(ms, z, j, x);
        }
    }
}

/// The bridge: lwalk_f at depth c is ddg_f at an unrolled level j with the
/// same residues.
pub proof fn lemma_optas_walk(ms: Seq<u128>, k: nat, l: nat, e: spec_fn(nat) -> real, c: nat, d: nat, j: nat, f: nat)
    requires
        wf_kl(ms, k, l), proper_kl(ms, k, l), !(k == 1 && l == 0),
        is_internal(optas_ddg(ms, k, l), c, d),
        rho_eq(ms, zkl(k, l), j, c),
    ensures lwalk_f(optas_ddg(ms, k, l), e, c, d, f) == ddg_f(ms, zkl(k, l), e, j, d, f),
    decreases f, 1nat,
{
    if f > 0 {
        let f1 = (f - 1) as nat;
        lemma_optas_child(ms, k, l, e, c, d, j, 2 * d, f1);
        lemma_optas_child(ms, k, l, e, c, d, j, 2 * d + 1, f1);
    }
}

/// One child of the bridge.
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
proof fn lemma_optas_child(ms: Seq<u128>, k: nat, l: nat, e: spec_fn(nat) -> real, c: nat, d: nat, j: nat, x: nat, f1: nat)
    requires
        wf_kl(ms, k, l), proper_kl(ms, k, l), !(k == 1 && l == 0),
        is_internal(optas_ddg(ms, k, l), c, d),
        rho_eq(ms, zkl(k, l), j, c),
        x == 2 * d || x == 2 * d + 1,
    ensures lwalk_g(optas_ddg(ms, k, l), e, c + 1, x, f1) == ddg_g(ms, zkl(k, l), e, j + 1, x, 0, f1),
    decreases f1, 2nat,
{
    let t = optas_ddg(ms, k, l);
    lemma_zkl(k, l);
    let z = zkl(k, l);
    lemma_optas_valid(ms, k, l);
    lemma_level_eq(ms, z, j, c, 0);
    let h = ddg_h(ms, z, c + 1, 0);
    assert((t.h)(c + 1) == h);
    if x < h {
        let r = optas_lab(ms, z, c + 1, x);
        lemma_optas_lab(ms, z, c + 1, x);
        lemma_level_eq(ms, z, j, c, r);
        assert(ddg_bit(ms, z, j + 1, r) == 1);
        assert(ddg_pre(ms, z, j + 1, 0) == 0);
        lemma_ddg_g_pre(ms, z, e, j + 1, r, 0, f1);
    } else {
        lemma_ddg_g_internal(ms, z, e, j + 1, x, 0, f1);
        let y = (x - h) as nat;
        lemma_child_internal(t, c, d, if x == 2 * d { 0 } else { 1 }, false);
        lemma_next_column(ms, k, l, j, c);
        let c2 = next_depth(t, c + 1);
        if c + 1 == k && l == k {
            assert(lnum(t, c + 1) == 2 * lnum(t, c) - (t.h)(c + 1) as int);
            assert(false);
        }
        assert(rho_eq(ms, z, j + 1, c2));
        lemma_optas_walk(ms, k, l, e, c2, y, j + 1, f1);
    }
}

// ── The spec ──────────────────────────────────────────────────────────────────

/// The label with M_r = 1 when Z = 1.
pub open spec fn optas_point(ms: Seq<u128>) -> nat {
    choose |r: nat| r < ms.len() && ms[r as int] != 0
}

/// The distribution M / Z_kl.
pub struct OptasSpec {
    pub ms: Seq<u128>,
    pub k: nat,
    pub l: nat,
}

/// Z = 1: the label with M_r ≠ 0 is unique, and E[ℰ] = ℰ(r).
pub proof fn lemma_optas_point(ms: Seq<u128>, e: spec_fn(nat) -> real)
    requires wf_kl(ms, 1, 0),
    ensures
        optas_point(ms) < ms.len(), ms[optas_point(ms) as int] == 1,
        forall |i: int| 0 <= i < ms.len() && i != optas_point(ms) ==> #[trigger] ms[i] == 0,
        ddg_exp(ms, zkl(1, 0), e) == e(optas_point(ms)),
{
    lemma2_to64();
    assert(zkl(1, 0) == 1);
    if forall |i: int| 0 <= i < ms.len() ==> #[trigger] ms[i] == 0 {
        lemma_all_zero_sum(ms, 0);
    }
    let i0 = choose |i: int| 0 <= i < ms.len() && !(#[trigger] ms[i] == 0);
    assert(ms[i0 as nat as int] != 0);
    let r = optas_point(ms);
    lemma_unit(ms, r);
    lemma_wsum_unit(ms, e, r, 0);
    assert(wsum(ms, e, 0) / 1real == wsum(ms, e, 0));
}

impl DdgSpec for OptasSpec {
    open spec fn wf(&self) -> bool {
        wf_kl(self.ms, self.k, self.l) && proper_kl(self.ms, self.k, self.l) && self.ms.len() < 0x4000000000000000
    }

    open spec fn ddg(&self) -> LDdg { optas_ddg(self.ms, self.k, self.l) }

    open spec fn target(&self, e: spec_fn(nat) -> real) -> real { ddg_exp(self.ms, zkl(self.k, self.l), e) }

    open spec fn point(&self) -> Option<nat> {
        if self.k == 1 && self.l == 0 { Some(optas_point(self.ms)) } else { None }
    }

    open spec fn exact(&self) -> bool { self.l == self.k }

    proof fn lemma_shape(&self) {
        lemma_optas_valid(self.ms, self.k, self.l);
        lemma_zkl(self.k, self.l);
        assert forall |e: spec_fn(nat) -> real| (forall |i: nat| (#[trigger] e(i)) >= 0real)
            implies #[trigger] self.target(e) >= 0real by {
            lemma_wsum_nonneg(self.ms, e, 0);
            let z = zkl(self.k, self.l) as real;
            assert(wsum(self.ms, e, 0) / z >= 0real) by(nonlinear_arith)
                requires wsum(self.ms, e, 0) >= 0real, z > 0real;
        }
        if self.k == 1 && self.l == 0 {
            assert forall |e: spec_fn(nat) -> real| (forall |i: nat| (#[trigger] e(i)) >= 0real)
                implies #[trigger] self.target(e) >= e(optas_point(self.ms)) by {
                lemma_optas_point(self.ms, e);
            }
            lemma_optas_point(self.ms, |i: nat| 0real);
        }
    }

    proof fn lemma_fuel(&self, e: spec_fn(nat) -> real, s0: real) -> (f: nat) {
        let (ms, k, l) = (self.ms, self.k, self.l);
        lemma_zkl(k, l);
        let z = zkl(k, l);
        let f: nat = if l < k { lemma_ddg_fail_witness(ms.len() as nat, s0) } else { k };
        if l < k {
            lemma_root_bound(ms, k, l, e, ddg_exp(ms, z, e), s0, f);
        } else {
            lemma_root_bound(ms, k, l, e, ddg_exp(ms, z, e), 0real, f);
        }
        lemma_optas_valid(ms, k, l);
        lemma_ddg_shape(ms, z, 0);
        assert(is_internal(optas_ddg(ms, k, l), 0, 0));
        lemma_optas_walk(ms, k, l, e, 0, 0, 0, f);
        f
    }
}

// ── make_leaf_table ───────────────────────────────────────────────────────────

/// The leaves of P, per depth: h[j] and lab[j] for j = 0..k (j = 0 empty).
pub struct LeafTable {
    pub k: u64,
    pub l: u64,
    pub h: Vec<u64>,
    pub lab: Vec<Vec<u64>>,
    pub ms: Ghost<Seq<u128>>,
}

impl Leaves for LeafTable {
    open spec fn lwf(&self) -> bool {
        let ms = self.ms@;
        let (k, l) = (self.k as nat, self.l as nat);
        let z = zkl(k, l);
        &&& wf_kl(ms, k, l) && proper_kl(ms, k, l) && ms.len() < 0x4000000000000
        &&& !(k == 1 && l == 0)
        &&& self.h@.len() == k + 1
        &&& self.lab@.len() == k + 1
        &&& forall |j: int| 1 <= j <= k ==> #[trigger] self.h@[j] as nat == ddg_h(ms, z, j as nat, 0)
        &&& forall |j: int| 1 <= j <= k ==> #[trigger] self.lab@[j]@.len() == self.h@[j]
        &&& forall |j: int, x: int| 1 <= j <= k && 0 <= x < self.h@[j] ==>
            #[trigger] self.lab@[j]@[x] as nat == optas_lab(ms, z, j as nat, x as nat)
    }

    open spec fn ddg(&self) -> LDdg { optas_ddg(self.ms@, self.k as nat, self.l as nat) }

    proof fn lemma_leaves(&self) {
        let (ms, k, l) = (self.ms@, self.k as nat, self.l as nat);
        lemma_optas_valid(ms, k, l);
        lemma_zkl(k, l);
        let t = optas_ddg(ms, k, l);
        assert forall |j: nat| j <= t.levels implies #[trigger] npos(t, j) <= 0x10000000000000 by {
            lemma_ddg_shape(ms, zkl(k, l), j);
            assert(lnum(t, j) == ddg_num_internal(ms, zkl(k, l), j));
        }
    }

    fn levels(&self) -> (r: u64) { self.k }

    fn wrap_level(&self) -> (r: u64) {
        proof { lemma_optas_valid(self.ms@, self.k as nat, self.l as nat); }
        self.l
    }

    fn get_h(&self, j: u64) -> (r: u64) { self.h[j as usize] }

    fn get_lab(&self, j: u64, x: u64) -> (r: u64) {
        proof {
            assert(self.h@[j as int] as nat == ddg_h(self.ms@, zkl(self.k as nat, self.l as nat), j as nat, 0));
            assert(self.lab@[j as int]@[x as int] as nat == optas_lab(self.ms@, zkl(self.k as nat, self.l as nat), j as nat, x as nat));
            assert((self.ddg().lab)(j as nat, x as nat) == optas_lab(self.ms@, zkl(self.k as nat, self.l as nat), j as nat, x as nat));
            assert((j as usize) as int == j as int);
        }
        let row = &self.lab[j as usize];
        let _len = row.len();
        row[x as usize]
    }
}

/// `make_leaf_table(P)`: the labels of the ones in each column c of P are
/// the leaves of depth c + 1.
pub fn make_leaf_table(p: &Vec<Vec<u8>>, k: u64, l: u64, Ghost(ms): Ghost<Seq<u128>>) -> (t: LeafTable)
    requires sampler_input(p@, ms, k as nat, l as nat), !(k == 1 && l == 0), ms.len() < 0x4000000000000,
    ensures t.lwf(), t.ms@ == ms, t.k == k, t.l == l,
{
    let ghost z = zkl(k as nat, l as nat);
    proof { lemma_zkl(k as nat, l as nat); lemma_is_matrix_bits(p@, ms, k as nat, l as nat); }
    let n = p.len();
    let mut h: Vec<u64> = Vec::new();
    let mut lab: Vec<Vec<u64>> = Vec::new();
    h.push(0);
    lab.push(Vec::new());
    let mut c: u64 = 0;
    while c < k
        invariant
            n == p.len() == ms.len(), sampler_input(p@, ms, k as nat, l as nat), !(k == 1 && l == 0), ms.len() < 0x4000000000000,
            z == zkl(k as nat, l as nat), z > 0, is_bits(p@, k as nat),
            c <= k, h@.len() == c + 1, lab@.len() == c + 1,
            forall |j: int| 1 <= j <= c ==> #[trigger] h@[j] as nat == ddg_h(ms, z, j as nat, 0),
            forall |j: int| 1 <= j <= c ==> #[trigger] lab@[j]@.len() == h@[j],
            forall |j: int, x: int| 1 <= j <= c && 0 <= x < h@[j] ==>
                #[trigger] lab@[j]@[x] as nat == optas_lab(ms, z, j as nat, x as nat),
        decreases k - c,
    {
        let mut row: Vec<u64> = Vec::new();
        let mut r: usize = 0;
        while r < n
            invariant
                n == p.len() == ms.len(), sampler_input(p@, ms, k as nat, l as nat), !(k == 1 && l == 0),
                z == zkl(k as nat, l as nat), z > 0, is_bits(p@, k as nat), c < k, r <= n,
                row@.len() == ddg_pre(ms, z, c as nat + 1, r as nat),
                forall |x: int| 0 <= x < row@.len() ==> {
                    let r2 = #[trigger] row@[x] as nat;
                    &&& r2 < n && ddg_bit(ms, z, c as nat + 1, r2) == 1 && ddg_pre(ms, z, c as nat + 1, r2) == x
                },
            decreases n - r,
        {
            proof {
                lemma_col_level(p@, ms, k as nat, l as nat, c as nat, c as nat, r as nat);
                assert(p@[r as int].len() == k);
                lemma_ddg_pre_mono(ms, z, c as nat + 1, r as nat, (r + 1) as nat);
            }
            if p[r][c as usize] == 1 {
                row.push(r as u64);
            }
            r = r + 1;
        }
        proof {
            lemma_ddg_pre_h(ms, z, c as nat + 1, n as nat);
            assert(ddg_h(ms, z, c as nat + 1, n as nat) == 0);
            lemma_ddg_h_le(ms, z, c as nat + 1, 0);
            assert forall |x: int| 0 <= x < row@.len() implies
                #[trigger] row@[x] as nat == optas_lab(ms, z, c as nat + 1, x as nat) by {
                let r2 = row@[x] as nat;
                lemma_optas_lab(ms, z, c as nat + 1, x as nat);
                lemma_optas_lab_unique(ms, z, c as nat + 1, r2, optas_lab(ms, z, c as nat + 1, x as nat));
            }
        }
        h.push(row.len() as u64);
        lab.push(row);
        c = c + 1;
    }
    LeafTable { k, l, h, lab, ms: Ghost(ms) }
}

} // verus!
