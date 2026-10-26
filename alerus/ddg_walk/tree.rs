//! optas's `tree.py`: build the DDG tree as a pointer structure, for any table
//! of leaves ([`Leaves`]). The nodes live in an arena (`Vec<Node>`) and a
//! pointer is an index into it.
//!
//! `make_tree` is a right-first depth-first traversal, as in the original. A
//! node is named by its depth j and its position o among the nodes of that
//! depth, counted from the right; the nodes of depth j+1 are the children
//! 2d, 2d+1 of the internal nodes d of depth j (the original uses the
//! level-order index; the leaves of a level are its rightmost nodes, so
//! `index in L` is o < h(j)). The internal nodes at the
//! wrap depth l are queued as they are visited, and a missing child at
//! depth K takes the next queued node (the back-edge).
//!
//! The proof tracks how many positions of each depth the traversal has
//! visited (`v`). Positions of a depth are visited in order, so the i-th
//! back-edge is to the i-th internal node of depth l, and the queue is never
//! empty when popped: the internal nodes of depth K below the first a
//! internal nodes of depth l number at most a (`lemma_icnt_le`), since the
//! count is star-shaped in a.

use vstd::prelude::*;

verus! {

#[cfg(verus_keep_ghost)]
use crate::ddg_walk::walk::*;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::{pow2, lemma_pow2_unfold, lemma2_to64};

/// An arena node: a leaf (`label` is Some) or an internal node with two
/// children (indices into the arena).
pub struct Node {
    pub label: Option<u64>,
    pub left: usize,
    pub right: usize,
}

/// A table of leaves: h(j) and lab(j, x) for depths 1..K.
pub trait Leaves {
    spec fn lwf(&self) -> bool;

    spec fn lldd(&self) -> LDdg;

    proof fn lemma_leaves(&self)
        requires self.lwf(),
        ensures
            valid_ldd(self.lldd()),
            (self.lldd().h)(0) == 0,
            self.lldd().levels <= 124,
            forall |j: nat| j <= self.lldd().levels ==> #[trigger] npos(self.lldd(), j) <= 0x10000000000000,
            forall |j: nat, x: nat| x < (self.lldd().h)(j) ==> #[trigger] (self.lldd().lab)(j, x) < 0x4000000000000000;

    fn levels(&self) -> (r: u64)
        requires self.lwf(),
        ensures r as nat == self.lldd().levels;

    /// The `l` of the original: the wrap depth, or any depth ≥ K when no
    /// internal node reaches depth K.
    fn wrap_level(&self) -> (r: u64)
        requires self.lwf(),
        ensures
            r as nat == self.lldd().wrap
                || (r as nat >= self.lldd().levels && lnum(self.lldd(), self.lldd().levels) == 0);

    fn get_h(&self, j: u64) -> (r: u64)
        requires self.lwf(), 1 <= j as nat <= self.lldd().levels,
        ensures r as nat == (self.lldd().h)(j as nat);

    fn get_lab(&self, j: u64, x: u64) -> (r: u64)
        requires self.lwf(), 1 <= j as nat <= self.lldd().levels, (x as nat) < (self.lldd().h)(j as nat),
        ensures r as nat == (self.lldd().lab)(j as nat, x as nat);
}

// ── Counting positions ────────────────────────────────────────────────────────

pub open spec fn max0(x: int) -> nat {
    if x > 0 { x as nat } else { 0 }
}

/// The positions at depth j: h(j) leaves and A(j) internal nodes.
pub open spec fn npos(t: LDdg, j: nat) -> nat {
    max0((t.h)(j) as int + lnum(t, j))
}

/// The positions of depth j2 below the first o positions of depth j.
pub open spec fn cover(t: LDdg, j: nat, o: nat, j2: nat) -> nat
    decreases j2,
{
    if j2 <= j { o } else { 2 * max0(cover(t, j, o, (j2 - 1) as nat) as int - (t.h)((j2 - 1) as nat) as int) }
}

/// The internal nodes of depth j2 below the first a internal nodes of depth i.
pub open spec fn icnt(t: LDdg, i: nat, a: nat, j2: nat) -> nat
    decreases j2,
{
    if j2 <= i { a } else { max0(2 * icnt(t, i, a, (j2 - 1) as nat) as int - (t.h)(j2) as int) }
}

pub proof fn lemma_npos(t: LDdg, j: nat)
    requires valid_ldd(t), (t.h)(0) == 0, j <= t.levels,
    ensures
        npos(t, j) as int == (t.h)(j) as int + lnum(t, j),
        j < t.levels ==> npos(t, j + 1) == 2 * lnum(t, j),
        npos(t, j) <= pow2(j),
    decreases j,
{
    lemma_lnum_nonneg(t, j);
    if j < t.levels {
        lemma_lnum_nonneg(t, j + 1);
    }
    if j == 0 {
        lemma2_to64();
    } else {
        lemma_npos(t, (j - 1) as nat);
        lemma_pow2_unfold(j);
        lemma_lnum_nonneg(t, (j - 1) as nat);
    }
}

/// cover(j, o, ·) = cover(j1, cover(j, o, j1), ·) for j ≤ j1.
pub proof fn lemma_cover_compose(t: LDdg, j: nat, o: nat, j1: nat, j2: nat)
    requires j <= j1 <= j2,
    ensures cover(t, j, o, j2) == cover(t, j1, cover(t, j, o, j1), j2),
    decreases j2,
{
    if j2 > j1 {
        lemma_cover_compose(t, j, o, j1, (j2 - 1) as nat);
    }
}

pub proof fn lemma_cover_mono(t: LDdg, j: nat, o: nat, o2: nat, j2: nat)
    requires o <= o2,
    ensures cover(t, j, o, j2) <= cover(t, j, o2, j2),
    decreases j2,
{
    if j2 > j {
        lemma_cover_mono(t, j, o, o2, (j2 - 1) as nat);
    }
}

/// Below the leaves only, nothing.
pub proof fn lemma_cover_leaf(t: LDdg, j: nat, o: nat, j2: nat)
    requires o <= (t.h)(j), j < j2,
    ensures cover(t, j, o, j2) == 0,
    decreases j2,
{
    assert(cover(t, j, o, j) == o);
    if j2 > j + 1 {
        lemma_cover_leaf(t, j, o, (j2 - 1) as nat);
        assert(cover(t, j, o, j2) == 2 * max0(0 - (t.h)((j2 - 1) as nat) as int));
    } else {
        assert(cover(t, j, o, j2) == 2 * max0(o as int - (t.h)(j) as int));
    }
}

/// Past the leaves, cover counts internal nodes as icnt does.
pub proof fn lemma_cover_icnt(t: LDdg, i: nat, a: nat, j2: nat)
    requires i <= j2,
    ensures max0(cover(t, i, (t.h)(i) + a, j2) as int - (t.h)(j2) as int) == icnt(t, i, a, j2),
    decreases j2,
{
    if j2 > i {
        lemma_cover_icnt(t, i, a, (j2 - 1) as nat);
    }
}

pub proof fn lemma_icnt_full(t: LDdg, i: nat, j2: nat)
    requires valid_ldd(t), i <= j2 <= t.levels,
    ensures icnt(t, i, lnum(t, i) as nat, j2) as int == lnum(t, j2),
    decreases j2,
{
    lemma_lnum_nonneg(t, j2);
    lemma_lnum_nonneg(t, i);
    if j2 > i {
        lemma_icnt_full(t, i, (j2 - 1) as nat);
    }
}

/// icnt is monotone and star-shaped: icnt(a)·b ≤ icnt(b)·a for a ≤ b.
pub proof fn lemma_icnt_star(t: LDdg, i: nat, a: nat, b: nat, j2: nat)
    requires a <= b,
    ensures
        icnt(t, i, a, j2) <= icnt(t, i, b, j2),
        icnt(t, i, a, j2) * b <= icnt(t, i, b, j2) * a,
    decreases j2,
{
    if j2 > i {
        let j1 = (j2 - 1) as nat;
        lemma_icnt_star(t, i, a, b, j1);
        let ca = icnt(t, i, a, j1);
        let cb = icnt(t, i, b, j1);
        let h = (t.h)(j2) as int;
        let pa = icnt(t, i, a, j2);
        let pb = icnt(t, i, b, j2);
        assert(pa == max0(2 * ca - h) && pb == max0(2 * cb - h));
        assert(h >= 0);
        if pa > 0 {
            assert(pb == 2 * cb - h);
            // ψ(x) = max(0, 2x − h) is star-shaped: ψ(ca)·cb ≤ ψ(cb)·ca.
            assert(pa * cb <= pb * ca) by(nonlinear_arith)
                requires pa == 2 * ca - h, pb == 2 * cb - h, ca <= cb, pa > 0, h >= 0;
            assert(pa * b * ca <= pa * cb * a) by(nonlinear_arith)
                requires ca * b <= cb * a, pa >= 0;
            assert(pa * cb * a <= pb * ca * a) by(nonlinear_arith)
                requires pa * cb <= pb * ca, a >= 0;
            assert(ca > 0);
            assert(pa * b <= pb * a) by(nonlinear_arith)
                requires pa * b * ca <= pb * ca * a, ca > 0;
        } else {
            assert(0 * b == 0);
            assert(pb * a >= 0) by(nonlinear_arith);
        }
    } else {
        assert(a * b <= b * a) by(nonlinear_arith);
    }
}

/// The back-edges of the first a internal nodes of depth l are at most a.
pub proof fn lemma_icnt_le(t: LDdg, a: nat)
    requires valid_ldd(t), a as int <= lnum(t, t.wrap),
    ensures icnt(t, t.wrap, a, t.levels) <= a,
{
    let l = t.wrap;
    let al = lnum(t, l) as nat;
    lemma_lnum_nonneg(t, l);
    lemma_icnt_full(t, l, t.levels);
    lemma_icnt_star(t, l, a, al, t.levels);
    let c = icnt(t, l, a, t.levels);
    if al > 0 {
        assert(c * al <= al * a) by(nonlinear_arith)
            requires c * al <= icnt(t, l, al, t.levels) * a, icnt(t, l, al, t.levels) <= al;
        assert(c <= a) by(nonlinear_arith) requires c * al <= al * a, al > 0;
    }
}

// ── The arena and what the traversal knows ────────────────────────────────────

/// The traversal state: the arena, the queue of depth-l internal nodes (with
/// the index of its head), and two ghost maps: `pos` (the node each arena
/// entry stands for: (depth, internal index)) and `v` (positions visited per
/// depth).
pub struct Builder {
    pub nodes: Vec<Node>,
    pub ancestors: Vec<usize>,
    pub head: usize,
    pub pos: Ghost<Seq<(nat, nat)>>,
    pub v: Ghost<Seq<nat>>,
}

/// Σ_{j<m} v[j].
pub open spec fn visited_sum(v: Seq<nat>, m: nat) -> nat
    decreases m,
{
    if m == 0 { 0 } else { visited_sum(v, (m - 1) as nat) + v[(m - 1) as int] }
}

/// The arena entry `id` is the node of depth j at position x.
pub open spec fn node_is(t: LDdg, nodes: Seq<Node>, pos: Seq<(nat, nat)>, id: int, j: nat, x: nat) -> bool {
    &&& 0 <= id < nodes.len()
    &&& if x < (t.h)(j) {
        nodes[id].label matches Some(r) && r as nat == (t.lab)(j, x)
    } else {
        nodes[id].label is None && pos[id] == (next_depth(t, j), (x - (t.h)(j)) as nat)
    }
}

/// An internal arena node has the right children (left: flip 0, 2d+1;
/// right: flip 1, 2d).
pub open spec fn complete(t: LDdg, nodes: Seq<Node>, pos: Seq<(nat, nat)>, id: int) -> bool {
    nodes[id].label is None ==> {
        let (j, d) = pos[id];
        &&& node_is(t, nodes, pos, nodes[id].left as int, j + 1, 2 * d + 1)
        &&& node_is(t, nodes, pos, nodes[id].right as int, j + 1, 2 * d)
    }
}

#[verifier::opaque]
pub open spec fn binv(t: LDdg, lw: nat, b: Builder) -> bool {
    let k = t.levels;
    let v = b.v@;
    &&& b.pos@.len() == b.nodes@.len()
    &&& v.len() == k + 1
    &&& forall |j: int| 0 <= j <= k ==> #[trigger] v[j] <= npos(t, j as nat)
    &&& b.nodes@.len() + b.head == visited_sum(v, k + 1)
    &&& b.head == max0(v[k as int] as int - (t.h)(k) as int)
    &&& b.ancestors@.len() == (if lw < k { max0(v[lw as int] as int - (t.h)(lw) as int) } else { 0 })
    &&& forall |s: int| 0 <= s < b.ancestors@.len() ==> {
        let a = #[trigger] b.ancestors@[s] as int;
        &&& 0 <= a < b.nodes@.len()
        &&& b.nodes@[a].label is None
        &&& b.pos@[a] == (lw, s as nat)
    }
    &&& forall |id: int| 0 <= id < b.nodes@.len() && (#[trigger] b.nodes@[id]).label is None ==>
        is_internal(t, b.pos@[id].0, b.pos@[id].1)
    &&& forall |id: int| 0 <= id < b.nodes@.len() ==>
        ((#[trigger] b.nodes@[id]).label matches Some(r) ==> r < 0x4000000000000000)
}

/// The facts about the leaf table the traversal uses.
#[verifier::opaque]
pub open spec fn tree_input(t: LDdg, lw: nat) -> bool {
    &&& valid_ldd(t)
    &&& (t.h)(0) == 0
    &&& t.levels <= 124
    &&& (forall |j: nat| j <= t.levels ==> #[trigger] npos(t, j) <= 0x10000000000000)
    &&& (lw == t.wrap || (lw >= t.levels && lnum(t, t.levels) == 0))
    &&& forall |j: nat, x: nat| x < (t.h)(j) ==> #[trigger] (t.lab)(j, x) < 0x4000000000000000
}

proof fn lemma_vsum_update(v: Seq<nat>, m: nat, j: int, x: nat)
    requires 0 <= j < m <= v.len(),
    ensures visited_sum(v.update(j, x), m) + v[j] == visited_sum(v, m) + x,
    decreases m,
{
    if m - 1 > j {
        lemma_vsum_update(v, (m - 1) as nat, j, x);
    } else {
        lemma_vsum_prefix(v, j, x, (m - 1) as nat);
    }
}

proof fn lemma_vsum_prefix(v: Seq<nat>, j: int, x: nat, m: nat)
    requires 0 <= j < v.len(), m <= j,
    ensures visited_sum(v.update(j, x), m) == visited_sum(v, m),
    decreases m,
{
    if m > 0 { lemma_vsum_prefix(v, j, x, (m - 1) as nat); }
}

/// Σ_{j ≤ K} npos(j) < 2^{K+1}.
pub proof fn lemma_vsum_bound(t: LDdg, v: Seq<nat>, m: nat)
    requires m <= t.levels + 1, v.len() >= m,
        forall |j: int| 0 <= j < m ==> #[trigger] v[j] <= npos(t, j as nat),
        forall |j: nat| j <= t.levels ==> #[trigger] npos(t, j) <= 0x10000000000000,
    ensures visited_sum(v, m) <= m * 0x10000000000000,
    decreases m,
{
    if m > 0 {
        lemma_vsum_bound(t, v, (m - 1) as nat);
        assert(v[(m - 1) as int] <= npos(t, (m - 1) as nat));
        assert(npos(t, (m - 1) as nat) <= 0x10000000000000);
    }
}

// ── Transitions of the traversal state ───────────────────────────────────────

/// What the opaque invariant says.
pub proof fn lemma_binv_facts(t: LDdg, lw: nat, b: Builder)
    requires binv(t, lw, b),
    ensures
        b.pos@.len() == b.nodes@.len(),
        b.v@.len() == t.levels + 1,
        forall |j: int| 0 <= j <= t.levels ==> #[trigger] b.v@[j] <= npos(t, j as nat),
        b.nodes@.len() + b.head == visited_sum(b.v@, t.levels + 1),
        forall |id: int| 0 <= id < b.nodes@.len() && (#[trigger] b.nodes@[id]).label is None ==>
            is_internal(t, b.pos@[id].0, b.pos@[id].1),
        forall |id: int| 0 <= id < b.nodes@.len() ==>
            ((#[trigger] b.nodes@[id]).label matches Some(r) ==> r < 0x4000000000000000),
{
    reveal(binv);
}

/// Pushing the node of depth j at position o.
#[verifier::rlimit(300)]
proof fn lemma_binv_push(t: LDdg, lw: nat, b0: Builder, b1: Builder, j: nat, o: nat, idu: usize)
    requires
        idu as int == b0.nodes@.len(),
        tree_input(t, lw), binv(t, lw, b0),
        j <= t.levels, o < npos(t, j), b0.v@[j as int] == o,
        b1.nodes@.len() == b0.nodes@.len() + 1,
        forall |i: int| 0 <= i < b0.nodes@.len() ==> #[trigger] b1.nodes@[i] == b0.nodes@[i],
        b1.pos@.len() == b1.nodes@.len(),
        forall |i: int| 0 <= i < b0.nodes@.len() ==> #[trigger] b1.pos@[i] == b0.pos@[i],
        b1.v@ == b0.v@.update(j as int, o + 1),
        b1.head == b0.head,
        b1.nodes@[b0.nodes@.len() as int].label is None ==> {
            &&& j < t.levels && o >= (t.h)(j)
            &&& b1.pos@[b0.nodes@.len() as int] == (j, (o - (t.h)(j)) as nat)
            &&& is_internal(t, j, (o - (t.h)(j)) as nat)
            &&& b1.ancestors@ == (if j == lw { b0.ancestors@.push(idu) } else { b0.ancestors@ })
        },
        b1.nodes@[b0.nodes@.len() as int].label is Some ==> {
            &&& 1 <= j && o < (t.h)(j)
            &&& b1.ancestors@ == b0.ancestors@
            &&& b1.nodes@[b0.nodes@.len() as int].label matches Some(r) && r < 0x4000000000000000
        },
    ensures binv(t, lw, b1),
{
    reveal(binv);
    let k = t.levels;
    lemma_vsum_update(b0.v@, k + 1, j as int, o + 1);
    let id = b0.nodes@.len() as int;
    if b1.nodes@[id].label is None && j == lw {
        assert(b0.ancestors@.len() == (o - (t.h)(j)) as nat);
    }
    assert forall |i: int| 0 <= i < b1.nodes@.len() && (#[trigger] b1.nodes@[i]).label is None implies
        is_internal(t, b1.pos@[i].0, b1.pos@[i].1) by {
        if i < id { assert(b1.nodes@[i] == b0.nodes@[i]); }
    }
    assert forall |i: int| 0 <= i < b1.nodes@.len() implies
        ((#[trigger] b1.nodes@[i]).label matches Some(r) ==> r < 0x4000000000000000) by {
        if i < id { assert(b1.nodes@[i] == b0.nodes@[i]); }
    }
    assert forall |s: int| 0 <= s < b1.ancestors@.len() implies {
        let a = #[trigger] b1.ancestors@[s] as int;
        &&& 0 <= a < b1.nodes@.len()
        &&& b1.nodes@[a].label is None
        &&& b1.pos@[a] == (lw, s as nat)
    } by {
        if s < b0.ancestors@.len() {
            let a = b0.ancestors@[s] as int;
            assert(b1.ancestors@[s] == b0.ancestors@[s]);
            assert(b1.nodes@[a] == b0.nodes@[a]);
        } else {
            assert(b1.ancestors@[s] as int == id);
        }
    }
}

/// Taking the back-edge at position x of depth K.
proof fn lemma_binv_pop(t: LDdg, lw: nat, b0: Builder, b1: Builder, x: nat)
    requires
        tree_input(t, lw), binv(t, lw, b0), lw < t.levels,
        b0.v@[t.levels as int] == x, (t.h)(t.levels) <= x < npos(t, t.levels),
        b1.nodes@ == b0.nodes@, b1.pos@ == b0.pos@, b1.ancestors@ == b0.ancestors@,
        b1.head == b0.head + 1,
        b1.v@ == b0.v@.update(t.levels as int, x + 1),
    ensures binv(t, lw, b1),
{
    reveal(tree_input);
    reveal(binv);
    lemma_vsum_update(b0.v@, t.levels + 1, t.levels as int, x + 1);
}

/// Setting the children of an arena node keeps every label.
proof fn lemma_binv_set(t: LDdg, lw: nat, b0: Builder, b1: Builder, id: int)
    requires
        binv(t, lw, b0), 0 <= id < b0.nodes@.len(),
        b1.nodes@.len() == b0.nodes@.len(),
        b1.nodes@[id].label == b0.nodes@[id].label,
        forall |i: int| 0 <= i < b0.nodes@.len() && i != id ==> #[trigger] b1.nodes@[i] == b0.nodes@[i],
        b1.pos@ == b0.pos@, b1.v@ == b0.v@, b1.ancestors@ == b0.ancestors@, b1.head == b0.head,
    ensures
        binv(t, lw, b1),
        forall |i: int| 0 <= i < b0.nodes@.len() ==> #[trigger] b1.nodes@[i].label == b0.nodes@[i].label,
{
    reveal(binv);
    assert forall |i: int| 0 <= i < b0.nodes@.len() implies #[trigger] b1.nodes@[i].label == b0.nodes@[i].label by {
        if i != id { assert(b1.nodes@[i] == b0.nodes@[i]); }
    }
    assert forall |i: int| 0 <= i < b1.nodes@.len() && (#[trigger] b1.nodes@[i]).label is None implies
        is_internal(t, b1.pos@[i].0, b1.pos@[i].1) by {
        assert(b1.nodes@[i].label == b0.nodes@[i].label);
    }
    assert forall |i: int| 0 <= i < b1.nodes@.len() implies
        ((#[trigger] b1.nodes@[i]).label matches Some(r) ==> r < 0x4000000000000000) by {
        assert(b1.nodes@[i].label == b0.nodes@[i].label);
    }
    assert forall |s: int| 0 <= s < b1.ancestors@.len() implies {
        let a = #[trigger] b1.ancestors@[s] as int;
        &&& 0 <= a < b1.nodes@.len()
        &&& b1.nodes@[a].label is None
        &&& b1.pos@[a] == (lw, s as nat)
    } by {
        let a = b1.ancestors@[s] as int;
        assert(b1.nodes@[a].label == b0.nodes@[a].label);
    }
}

/// The queue is not empty at a back-edge, and its head is the right node.
proof fn lemma_pop_ok(t: LDdg, lw: nat, b: Builder, j: nat, x: nat)
    requires
        tree_input(t, lw), binv(t, lw, b),
        j + 1 == t.levels, (t.h)(t.levels) <= x < npos(t, t.levels),
        b.v@[t.levels as int] == x,
        forall |j2: nat| j2 <= j ==> x < cover(t, j2, #[trigger] b.v@[j2 as int], j + 1),
    ensures
        lw == t.wrap, lw < t.levels,
        b.head == x - (t.h)(t.levels),
        b.head < b.ancestors@.len(),
        0 <= b.ancestors@[b.head as int] < b.nodes@.len(),
        b.nodes@[b.ancestors@[b.head as int] as int].label is None,
        b.pos@[b.ancestors@[b.head as int] as int] == (t.wrap, (x - (t.h)(t.levels)) as nat),
{
    reveal(tree_input);
    reveal(binv);
    let k = t.levels;
    lemma_npos(t, k);
    assert(lw == t.wrap);
    let vl = b.v@[lw as int];
    assert(x < cover(t, lw, vl, k));
    if vl <= (t.h)(lw) {
        lemma_cover_leaf(t, lw, vl, k);
    }
    let a = (vl - (t.h)(lw)) as nat;
    assert(vl == (t.h)(lw) + a);
    lemma_cover_icnt(t, lw, a, k);
    lemma_npos(t, lw);
    lemma_icnt_le(t, a);
    let s = b.head as int;
    assert(0 <= s < b.ancestors@.len());
    let an = b.ancestors@[s] as int;
    assert(0 <= an < b.nodes@.len() && b.nodes@[an].label is None && b.pos@[an] == (lw, s as nat));
}

/// cover after one level.
proof fn lemma_cover_step(t: LDdg, j: nat, o: nat)
    ensures cover(t, j, o, j + 1) == 2 * max0(o as int - (t.h)(j) as int),
{
    assert(cover(t, j, o, j) == o);
}

/// Entering the children of internal node (j, o).
proof fn lemma_child_setup(t: LDdg, j: nat, o: nat, v: Seq<nat>)
    requires
        j < t.levels, o >= (t.h)(j), v.len() == t.levels + 1,
        v[j as int] == o + 1,
        forall |j2: nat| j < j2 <= t.levels ==> #[trigger] v[j2 as int] == cover(t, j, o, j2),
        forall |j2: nat| j2 < j ==> o < cover(t, j2, #[trigger] v[j2 as int], j),
    ensures ({
        let d = (o - (t.h)(j)) as nat;
        &&& v[(j + 1) as int] == 2 * d
        &&& forall |j2: nat| j + 1 < j2 <= t.levels ==> #[trigger] v[j2 as int] == cover(t, j + 1, 2 * d, j2)
        &&& forall |j2: nat| j2 <= j ==> 2 * d + 1 < cover(t, j2, #[trigger] v[j2 as int], j + 1)
    }),
{
    let d = (o - (t.h)(j)) as nat;
    lemma_cover_step(t, j, o);
    lemma_cover_step(t, j, o + 1);
    assert forall |j2: nat| j + 1 < j2 <= t.levels implies #[trigger] v[j2 as int] == cover(t, j + 1, 2 * d, j2) by {
        lemma_cover_compose(t, j, o, j + 1, j2);
    }
    assert forall |j2: nat| j2 <= j implies 2 * d + 1 < cover(t, j2, #[trigger] v[j2 as int], j + 1) by {
        if j2 < j {
            lemma_cover_compose(t, j2, v[j2 as int], j, j + 1);
            lemma_cover_mono(t, j, o + 1, cover(t, j2, v[j2 as int], j), j + 1);
        }
    }
}

/// Leaving internal node (j, o).
proof fn lemma_child_finish(t: LDdg, j: nat, o: nat, v: Seq<nat>)
    requires
        o >= (t.h)(j), v.len() == t.levels + 1,
        v[(j + 1) as int] == 2 * (o - (t.h)(j)) + 2,
        forall |j2: nat| j + 1 < j2 <= t.levels ==> #[trigger] v[j2 as int] == cover(t, j + 1, 2 * (o - (t.h)(j)) as nat + 2, j2),
    ensures
        forall |j2: nat| j < j2 <= t.levels ==> #[trigger] v[j2 as int] == cover(t, j, o + 1, j2),
{
    lemma_cover_step(t, j, o + 1);
    assert forall |j2: nat| j < j2 <= t.levels implies #[trigger] v[j2 as int] == cover(t, j, o + 1, j2) by {
        lemma_cover_compose(t, j, o + 1, j + 1, j2);
    }
}

/// Leaving leaf (j, o): nothing below it.
proof fn lemma_leaf_finish(t: LDdg, j: nat, o: nat, v: Seq<nat>)
    requires
        o < (t.h)(j),
        forall |j2: nat| j < j2 <= t.levels ==> #[trigger] v[j2 as int] == cover(t, j, o, j2),
    ensures
        forall |j2: nat| j < j2 <= t.levels ==> #[trigger] v[j2 as int] == cover(t, j, o + 1, j2),
{
    assert forall |j2: nat| j < j2 <= t.levels implies #[trigger] v[j2 as int] == cover(t, j, o + 1, j2) by {
        lemma_cover_leaf(t, j, o, j2);
        lemma_cover_leaf(t, j, o + 1, j2);
    }
}

/// node_is and complete only read labels and positions.
proof fn lemma_labels_keep(t: LDdg, n0: Seq<Node>, n1: Seq<Node>, pos: Seq<(nat, nat)>)
    requires
        n1.len() >= n0.len(),
        forall |i: int| 0 <= i < n0.len() ==> #[trigger] n1[i].label == n0[i].label,
    ensures
        forall |i: int, j: nat, x: nat| #[trigger] node_is(t, n0, pos, i, j, x) ==> node_is(t, n1, pos, i, j, x),
{
}

/// A node the traversal enters: a leaf, or an internal node above depth K.
proof fn lemma_tree_node(t: LDdg, lw: nat, j: nat, o: nat)
    requires
        tree_input(t, lw), j <= t.levels, o < npos(t, j),
        j == 0 ==> o == 0,
        j == t.levels ==> o < (t.h)(j),
    ensures
        (t.h)(0) == 0,
        o < 0x1000000000000000,
        o < (t.h)(j) ==> (t.lab)(j, o) < 0x4000000000000000,
        o >= (t.h)(j) ==> j < t.levels && is_internal(t, j, (o - (t.h)(j)) as nat) && next_depth(t, j) == j,
{
    reveal(tree_input);
    lemma_npos(t, j);
    lemma_lnum_nonneg(t, j);
    assert(npos(t, j) <= 0x10000000000000);
}

/// The children of an internal node are positions of the next depth.
proof fn lemma_child_pos(t: LDdg, lw: nat, j: nat, o: nat, x: nat)
    requires
        tree_input(t, lw), j < t.levels, o >= (t.h)(j), is_internal(t, j, (o - (t.h)(j)) as nat),
        x == 2 * (o - (t.h)(j)) || x == 2 * (o - (t.h)(j)) + 1,
    ensures x < npos(t, j + 1), next_depth(t, t.levels) == t.wrap,
{
    reveal(tree_input);
    lemma_npos(t, j + 1);
}

/// What the traversal needs from the table, once.
proof fn lemma_tree_input(t: LDdg, lw: nat)
    requires valid_ldd(t), (t.h)(0) == 0, t.levels <= 124,
        forall |j: nat| j <= t.levels ==> #[trigger] npos(t, j) <= 0x10000000000000,
        lw == t.wrap || (lw >= t.levels && lnum(t, t.levels) == 0),
        forall |j: nat, x: nat| x < (t.h)(j) ==> #[trigger] (t.lab)(j, x) < 0x4000000000000000,
    ensures tree_input(t, lw),
{
    reveal(tree_input);
}

// ── make_tree ─────────────────────────────────────────────────────────────────

/// `make_tree(index, k, l, ancestors, L)`: build the node of depth j at
/// position o and its subtree, returning its arena index.
#[verifier::spinoff_prover]
pub fn make_tree<L: Leaves>(tab: &L, j: u64, o: u64, lw: u64, b: &mut Builder) -> (id: usize)
    requires
        tab.lwf(),
        tree_input(tab.lldd(), lw as nat),
        binv(tab.lldd(), lw as nat, *old(b)),
        j as nat <= tab.lldd().levels,
        (o as nat) < npos(tab.lldd(), j as nat),
        j == 0 ==> o == 0,
        j as nat == tab.lldd().levels ==> (o as nat) < (tab.lldd().h)(j as nat),
        old(b).v@[j as int] == o as nat,
        forall |j2: nat| j < j2 <= tab.lldd().levels ==> #[trigger] old(b).v@[j2 as int] == cover(tab.lldd(), j as nat, o as nat, j2),
        forall |j2: nat| j2 < j ==> (o as nat) < cover(tab.lldd(), j2, #[trigger] old(b).v@[j2 as int], j as nat),
    ensures
        binv(tab.lldd(), lw as nat, *final(b)),
        old(b).nodes@.len() <= final(b).nodes@.len(),
        forall |i: int| 0 <= i < old(b).nodes@.len() ==>
            #[trigger] final(b).nodes@[i] == old(b).nodes@[i] && final(b).pos@[i] == old(b).pos@[i],
        forall |i: int| old(b).nodes@.len() <= i < final(b).nodes@.len() ==> #[trigger] complete(tab.lldd(), final(b).nodes@, final(b).pos@, i),
        node_is(tab.lldd(), final(b).nodes@, final(b).pos@, id as int, j as nat, o as nat),
        id == old(b).nodes@.len(),
        final(b).v@[j as int] == o as nat + 1,
        forall |j2: nat| j2 < j ==> #[trigger] final(b).v@[j2 as int] == old(b).v@[j2 as int],
        forall |j2: nat| j < j2 <= tab.lldd().levels ==> #[trigger] final(b).v@[j2 as int] == cover(tab.lldd(), j as nat, (o + 1) as nat, j2),
    decreases tab.lldd().levels - j, 1nat,
{
    let ghost t = tab.lldd();
    proof { lemma_tree_node(t, lw as nat, j as nat, o as nat); lemma_binv_facts(t, lw as nat, *b); }
    let hj: u64 = if j == 0 { 0 } else { tab.get_h(j) };
    let id = b.nodes.len();
    let ghost b0 = *b;
    if j >= 1 && o < hj {
        // A leaf: `node.label = L[index]`.
        let r = tab.get_lab(j, o);
        b.nodes.push(Node { label: Some(r), left: 0, right: 0 });
        b.pos = Ghost(b.pos@.push((0nat, 0nat)));
        b.v = Ghost(b.v@.update(j as int, o as nat + 1));
        proof {
            lemma_binv_push(t, lw as nat, b0, *b, j as nat, o as nat, id);
            lemma_leaf_finish(t, j as nat, o as nat, b0.v@);
            assert(complete(t, b.nodes@, b.pos@, id as int));
        }
        return id;
    }
    // An internal node, number d of depth j.
    let d = o - hj;
    b.nodes.push(Node { label: None, left: 0, right: 0 });
    b.pos = Ghost(b.pos@.push((j as nat, d as nat)));
    b.v = Ghost(b.v@.update(j as int, o as nat + 1));
    // Internal nodes at level l are ancestors.
    if j == lw {
        b.ancestors.push(id);
    }
    proof {
        lemma_binv_push(t, lw as nat, b0, *b, j as nat, o as nat, id);
        lemma_child_setup(t, j as nat, o as nat, b.v@);
    }
    // Build the right child (flip 1, position 2d), then the left (2d + 1).
    let ghost b1 = *b;
    let right = make_child(tab, j, 2 * d, lw, b, Ghost(o as nat));
    let ghost b2 = *b;
    proof {
        assert forall |j2: nat| j2 <= j implies ((2 * d + 1) as nat) < cover(t, j2, #[trigger] b.v@[j2 as int], j as nat + 1) by {
            assert(b.v@[j2 as int] == b1.v@[j2 as int]);
        }
    }
    let left = make_child(tab, j, 2 * d + 1, lw, b, Ghost(o as nat));
    let ghost b3 = *b;
    b.nodes.set(id, Node { label: None, left, right });
    proof {
        lemma_binv_set(t, lw as nat, b3, *b, id as int);
        lemma_labels_keep(t, b3.nodes@, b.nodes@, b.pos@);
        lemma_labels_keep(t, b2.nodes@, b3.nodes@, b.pos@);
        assert forall |i: int| 0 <= i < b2.nodes@.len() implies #[trigger] b3.nodes@[i].label == b2.nodes@[i].label by {
            assert(b3.nodes@[i] == b2.nodes@[i]);
        }
        assert(node_is(t, b3.nodes@, b.pos@, right as int, j as nat + 1, 2 * d as nat));
        assert forall |i: int| old(b).nodes@.len() <= i < b.nodes@.len() implies #[trigger] complete(t, b.nodes@, b.pos@, i) by {
            if i != id as int {
                if i < b2.nodes@.len() {
                    assert(complete(t, b2.nodes@, b2.pos@, i));
                    assert(b3.nodes@[i] == b2.nodes@[i] && b3.pos@[i] == b2.pos@[i]);
                    if b2.nodes@[i].label is None {
                        let (j1, d1) = b2.pos@[i];
                        assert(node_is(t, b3.nodes@, b.pos@, b2.nodes@[i].left as int, j1 + 1, 2 * d1 + 1));
                        assert(node_is(t, b3.nodes@, b.pos@, b2.nodes@[i].right as int, j1 + 1, 2 * d1));
                    }
                } else {
                    assert(complete(t, b3.nodes@, b3.pos@, i));
                }
                assert(b.nodes@[i] == b3.nodes@[i]);
                if b3.nodes@[i].label is None {
                    let (j1, d1) = b.pos@[i];
                    assert(node_is(t, b3.nodes@, b.pos@, b3.nodes@[i].left as int, j1 + 1, 2 * d1 + 1));
                    assert(node_is(t, b3.nodes@, b.pos@, b3.nodes@[i].right as int, j1 + 1, 2 * d1));
                }
            } else {
                assert(b.pos@[i] == (j as nat, d as nat));
            }
        }
        assert forall |i: int| 0 <= i < old(b).nodes@.len() implies
            #[trigger] b.nodes@[i] == old(b).nodes@[i] && b.pos@[i] == old(b).pos@[i] by {
            assert(b0.nodes@ == old(b).nodes@ && b0.pos@ == old(b).pos@);
            assert(b.pos@ == b3.pos@);
            assert(i != id as int);
            assert(b.nodes@[i] == b3.nodes@[i]);
            assert(i < b1.nodes@.len() && i < b2.nodes@.len());
            assert(b3.nodes@[i] == b2.nodes@[i] && b3.pos@[i] == b2.pos@[i]);
            assert(b2.nodes@[i] == b1.nodes@[i] && b2.pos@[i] == b1.pos@[i]);
            assert(b1.nodes@[i] == b0.nodes@[i] && b1.pos@[i] == b0.pos@[i]);
        }
        lemma_binv_facts(t, lw as nat, *b);
        lemma_child_finish(t, j as nat, o as nat, b.v@);
        assert(b.v@[j as int] == o as nat + 1);
        assert forall |i: int| 0 <= i < old(b).nodes@.len() implies #[trigger] b.nodes@[i] == old(b).nodes@[i] by {
            assert(b.nodes@[i] == old(b).nodes@[i] && b.pos@[i] == old(b).pos@[i]);
        }
        assert forall |i: int| 0 <= i < old(b).nodes@.len() implies #[trigger] b.pos@[i] == old(b).pos@[i] by {
            assert(b.nodes@[i] == old(b).nodes@[i] && b.pos@[i] == old(b).pos@[i]);
        }
    }
    id
}

/// The child of internal node (j, o) at position x of depth j+1: a new
/// subtree, or at depth K a back-edge to the next queued ancestor.
#[verifier::spinoff_prover]
fn make_child<L: Leaves>(tab: &L, j: u64, x: u64, lw: u64, b: &mut Builder, Ghost(o): Ghost<nat>) -> (id: usize)
    requires
        tab.lwf(),
        tree_input(tab.lldd(), lw as nat),
        binv(tab.lldd(), lw as nat, *old(b)),
        (j as nat) < tab.lldd().levels,
        is_internal(tab.lldd(), j as nat, (o - (tab.lldd().h)(j as nat)) as nat),
        o >= (tab.lldd().h)(j as nat),
        x == 2 * (o - (tab.lldd().h)(j as nat)) || x == 2 * (o - (tab.lldd().h)(j as nat)) + 1,
        old(b).v@[j + 1] == x as nat,
        forall |j2: nat| j + 1 < j2 <= tab.lldd().levels ==> #[trigger] old(b).v@[j2 as int] == cover(tab.lldd(), j as nat + 1, x as nat, j2),
        forall |j2: nat| j2 <= j ==> (x as nat) < cover(tab.lldd(), j2, #[trigger] old(b).v@[j2 as int], j as nat + 1),
    ensures
        binv(tab.lldd(), lw as nat, *final(b)),
        old(b).nodes@.len() <= final(b).nodes@.len(),
        forall |i: int| 0 <= i < old(b).nodes@.len() ==>
            #[trigger] final(b).nodes@[i] == old(b).nodes@[i] && final(b).pos@[i] == old(b).pos@[i],
        forall |i: int| old(b).nodes@.len() <= i < final(b).nodes@.len() ==> #[trigger] complete(tab.lldd(), final(b).nodes@, final(b).pos@, i),
        node_is(tab.lldd(), final(b).nodes@, final(b).pos@, id as int, j as nat + 1, x as nat),
        final(b).v@[j + 1] == x as nat + 1,
        forall |j2: nat| j2 <= j ==> #[trigger] final(b).v@[j2 as int] == old(b).v@[j2 as int],
        forall |j2: nat| j + 1 < j2 <= tab.lldd().levels ==> #[trigger] final(b).v@[j2 as int] == cover(tab.lldd(), j as nat + 1, (x + 1) as nat, j2),
    decreases tab.lldd().levels - j, 0nat,
{
    let ghost t = tab.lldd();
    let ghost k = t.levels;
    proof { lemma_child_pos(t, lw as nat, j as nat, o, x as nat); }
    let k_e = tab.levels();
    let h1 = tab.get_h(j + 1);
    if j + 1 == k_e && x >= h1 {
        // `node.right = ancestors.pop(0)` (or `node.left`): the back-edge.
        proof {
            lemma_pop_ok(t, lw as nat, *b, j as nat, x as nat);
            assert(b.head < b.ancestors@.len());
            assert(k == j + 1);
        }
        let id = b.ancestors[b.head];
        let _alen = b.ancestors.len();
        let ghost b0 = *b;
        proof { lemma_binv_facts(t, lw as nat, b0); }
        b.head = b.head + 1;
        b.v = Ghost(b.v@.update(k as int, x as nat + 1));
        proof {
            lemma_binv_pop(t, lw as nat, b0, *b, x as nat);
            assert(b.v@[(j + 1) as int] == x as nat + 1);
        }
        id
    } else {
        make_tree(tab, j + 1, x, lw, b)
    }
}

/// `make_ddg_tree(P, k, l)` for a table with an internal root: the arena,
/// with the root at index 0.
pub fn make_ddg_tree<L: Leaves>(tab: &L) -> (b: Builder)
    requires tab.lwf(),
    ensures
        b.nodes@.len() >= 1,
        b.nodes@.len() < 0x800000000000000,
        b.pos@.len() == b.nodes@.len(),
        node_is(tab.lldd(), b.nodes@, b.pos@, 0, 0, 0),
        forall |i: int| 0 <= i < b.nodes@.len() ==> #[trigger] complete(tab.lldd(), b.nodes@, b.pos@, i),
        forall |i: int| 0 <= i < b.nodes@.len() && (#[trigger] b.nodes@[i]).label is None ==>
            is_internal(tab.lldd(), b.pos@[i].0, b.pos@[i].1),
        forall |i: int| 0 <= i < b.nodes@.len() ==>
            ((#[trigger] b.nodes@[i]).label matches Some(r) ==> r < 0x4000000000000000),
{
    let ghost t = tab.lldd();
    proof { tab.lemma_leaves(); }
    let lw = tab.wrap_level();
    proof { lemma_tree_input(t, lw as nat); }
    let mut b = Builder {
        nodes: Vec::new(),
        ancestors: Vec::new(),
        head: 0,
        pos: Ghost(Seq::empty()),
        v: Ghost(Seq::new(t.levels + 1, |j: int| 0nat)),
    };
    proof {
        reveal(binv);
        reveal(tree_input);
        lemma_vsum_zero(b.v@, t.levels + 1);
        assert forall |j2: nat| 0 < j2 <= t.levels implies #[trigger] b.v@[j2 as int] == cover(t, 0, 0, j2) by {
            lemma_cover_zero(t, 0, j2);
        }
        lemma_npos(t, 0);
        lemma_lnum_nonneg(t, 0);
        assert forall |j: int| 0 <= j <= t.levels implies #[trigger] b.v@[j] <= npos(t, j as nat) by {}
        assert(binv(t, lw as nat, b));
    }
    let _root = make_tree(tab, 0, 0, lw, &mut b);
    proof {
        lemma_binv_facts(t, lw as nat, b);
        reveal(tree_input);
        lemma_vsum_bound(t, b.v@, t.levels + 1);
        assert((t.levels + 1) * 0x10000000000000 < 0x800000000000000) by(nonlinear_arith) requires t.levels <= 124;
    }
    b
}

proof fn lemma_vsum_zero(v: Seq<nat>, m: nat)
    requires m <= v.len(), forall |j: int| 0 <= j < v.len() ==> v[j] == 0,
    ensures visited_sum(v, m) == 0,
    decreases m,
{
    if m > 0 { lemma_vsum_zero(v, (m - 1) as nat); }
}

proof fn lemma_cover_zero(t: LDdg, j: nat, j2: nat)
    ensures cover(t, j, 0, j2) == 0,
    decreases j2,
{
    if j2 > j { lemma_cover_zero(t, j, (j2 - 1) as nat); }
}

} // verus!
