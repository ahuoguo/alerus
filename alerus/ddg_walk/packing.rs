//! optas's `packing.py`: pack the arena of `tree.rs` into one array. The
//! array as a sampler (`sample_ky_encoding`) is `Encoded` in `encoding.rs`.
//!
//! An internal node takes two slots, the offsets of its left child (flip 0)
//! and right child (flip 1); a leaf takes one slot, −(label + 1). The
//! original stores −label with 1-based labels; ours are 0-based, hence the
//! + 1. `pack_tree` is the original's memoized depth-first pass: a node is
//! packed once, and a pointer to an already packed node (a back-edge) is
//! its offset.
//!
//! `pack_tree` recurses through `pack_children` and `pack_child`, as the
//! original does. A back-edge to a depth-l node not yet packed packs it
//! there, so the recursion depth is not bounded by K; the proof says nothing
//! about stack depth.
//!
//! `Encoded` (in `encoding.rs`) is the packed array as a `DdgWalk`. Which
//! distribution it samples is given by a `DdgSpec` (FLDR's `Ddg`, or the
//! M / Z_kl of `optas`), so the one sampler `walk::sample` covers every
//! encoding.

use vstd::prelude::*;

verus! {

#[cfg(verus_keep_ghost)]
use crate::ddg_walk::walk::*;
use crate::ddg_walk::tree::*;

// ── The packed array ──────────────────────────────────────────────────────────

/// The child pointer q of an internal node leads to node x of depth j1.
pub open spec fn enc_child_ok(t: LDdg, enc: Seq<i64>, node_at: Seq<Option<(nat, nat)>>, q: i64, j1: nat, x: nat) -> bool {
    &&& 0 <= q < enc.len()
    &&& if x < (t.h)(j1) {
        enc[q as int] == -((t.lab)(j1, x) as int) - 1
    } else {
        enc[q as int] >= 0 && node_at[q as int] == Some((next_depth(t, j1), (x - (t.h)(j1)) as nat))
    }
}

/// The internal node at offset o.
pub open spec fn enc_node_ok(t: LDdg, enc: Seq<i64>, node_at: Seq<Option<(nat, nat)>>, o: int) -> bool {
    let (j, d) = node_at[o]->Some_0;
    &&& is_internal(t, j, d)
    &&& o + 1 < enc.len()
    &&& enc_child_ok(t, enc, node_at, enc[o], j + 1, 2 * d + 1)
    &&& enc_child_ok(t, enc, node_at, enc[o + 1], j + 1, 2 * d)
}

/// `enc` encodes the DDG t: `node_at[o]` is the internal node at offset o (if
/// one starts there), and the root is at offset 0.
pub open spec fn enc_wf(t: LDdg, enc: Seq<i64>, node_at: Seq<Option<(nat, nat)>>) -> bool {
    &&& node_at.len() == enc.len()
    &&& enc.len() >= 2
    &&& enc.len() < 0x4000000000000000
    &&& node_at[0] == Some((0nat, 0nat))
    &&& forall |o: int| 0 <= o < enc.len() && (#[trigger] node_at[o]) is Some ==> enc_node_ok(t, enc, node_at, o)
}

/// The packing state: the array, the offset of each packed arena node, and
/// two ghost maps: the internal node starting at each offset, and its arena
/// index.
pub struct Packer {
    pub enc: Vec<i64>,
    pub loc: Vec<Option<usize>>,
    pub node_at: Ghost<Seq<Option<(nat, nat)>>>,
    pub owner: Ghost<Seq<int>>,
}

/// #{ i < m : loc[i] is Some }.
pub open spec fn cnt_some(loc: Seq<Option<usize>>, m: nat) -> nat
    decreases m,
{
    if m == 0 { 0 } else { cnt_some(loc, (m - 1) as nat) + (if loc[(m - 1) as int] is Some { 1nat } else { 0nat }) }
}

proof fn lemma_cnt_some_set(loc: Seq<Option<usize>>, m: nat, i: int, x: usize)
    requires 0 <= i < m <= loc.len(), loc[i] is None,
    ensures cnt_some(loc.update(i, Some(x)), m) == cnt_some(loc, m) + 1,
    decreases m,
{
    if m - 1 > i {
        lemma_cnt_some_set(loc, (m - 1) as nat, i, x);
    } else {
        lemma_cnt_some_prefix(loc, i, Some(x), (m - 1) as nat);
    }
}

proof fn lemma_cnt_some_prefix(loc: Seq<Option<usize>>, i: int, x: Option<usize>, m: nat)
    requires 0 <= i < loc.len(), m <= i,
    ensures cnt_some(loc.update(i, x), m) == cnt_some(loc, m),
    decreases m,
{
    if m > 0 { lemma_cnt_some_prefix(loc, i, x, (m - 1) as nat); }
}

proof fn lemma_cnt_some_le(loc: Seq<Option<usize>>, m: nat)
    ensures cnt_some(loc, m) <= m,
    decreases m,
{
    if m > 0 { lemma_cnt_some_le(loc, (m - 1) as nat); }
}

/// The arena is closed: child pointers are in range and labels fit.
pub open spec fn arena_ok(nodes: Seq<Node>, pos: Seq<(nat, nat)>) -> bool {
    &&& pos.len() == nodes.len()
    &&& nodes.len() < 0x2000000000000000
    &&& forall |i: int| 0 <= i < nodes.len() && (#[trigger] nodes[i]).label is None ==>
        nodes[i].left < nodes.len() && nodes[i].right < nodes.len()
    &&& forall |i: int| 0 <= i < nodes.len() ==>
        ((#[trigger] nodes[i]).label matches Some(r) ==> r < 0x4000000000000000)
}

#[verifier::opaque]
pub open spec fn pinv(nodes: Seq<Node>, pos: Seq<(nat, nat)>, pk: Packer) -> bool {
    let enc = pk.enc@;
    let loc = pk.loc@;
    &&& loc.len() == nodes.len()
    &&& pk.node_at@.len() == enc.len()
    &&& pk.owner@.len() == enc.len()
    &&& enc.len() <= 2 * cnt_some(loc, loc.len())
    &&& forall |i: int| 0 <= i < nodes.len() && (#[trigger] loc[i]) is Some ==> {
        let o = loc[i]->Some_0 as int;
        &&& o < enc.len()
        &&& (nodes[i].label matches Some(r) ==> enc[o] == -(r as int) - 1)
        &&& (nodes[i].label is None ==> pk.node_at@[o] == Some(pos[i]))
    }
    &&& forall |o: int| 0 <= o < enc.len() && (#[trigger] pk.node_at@[o]) is Some ==> {
        let i = pk.owner@[o];
        &&& 0 <= i < nodes.len()
        &&& loc[i] == Some(o as usize)
        &&& nodes[i].label is None
        &&& pos[i] == pk.node_at@[o]->Some_0
        &&& o + 1 < enc.len()
        &&& enc[o] >= 0 && enc[o + 1] >= 0
    }
}

/// The two child slots of a packed internal node hold its children's offsets.
#[verifier::opaque]
pub open spec fn packed(nodes: Seq<Node>, pk: Packer, i: int) -> bool {
    nodes[i].label is None ==> {
        let o = pk.loc@[i]->Some_0 as int;
        &&& pk.loc@[nodes[i].left as int] is Some
        &&& pk.loc@[nodes[i].right as int] is Some
        &&& pk.enc@[o] == pk.loc@[nodes[i].left as int]->Some_0 as int
        &&& pk.enc@[o + 1] == pk.loc@[nodes[i].right as int]->Some_0 as int
    }
}

// ── Transitions of the packing state ────────────────────────────────────────

pub proof fn lemma_pinv_facts(nodes: Seq<Node>, pos: Seq<(nat, nat)>, pk: Packer)
    requires pinv(nodes, pos, pk), arena_ok(nodes, pos),
    ensures
        pk.loc@.len() == nodes.len(),
        pk.node_at@.len() == pk.enc@.len(),
        pk.owner@.len() == pk.enc@.len(),
        pk.enc@.len() <= 2 * nodes.len(),
        pk.enc@.len() < 0x4000000000000000,
        forall |i: int| 0 <= i < nodes.len() && (#[trigger] pk.loc@[i]) is Some ==> {
            let o = pk.loc@[i]->Some_0 as int;
            &&& o < pk.enc@.len()
            &&& (nodes[i].label matches Some(r) ==> pk.enc@[o] == -(r as int) - 1)
            &&& (nodes[i].label is None ==> pk.node_at@[o] == Some(pos[i]))
        },
        forall |o: int| 0 <= o < pk.enc@.len() && (#[trigger] pk.node_at@[o]) is Some ==> {
            let i = pk.owner@[o];
            &&& 0 <= i < nodes.len()
            &&& pk.loc@[i] == Some(o as usize)
            &&& nodes[i].label is None
            &&& pos[i] == pk.node_at@[o]->Some_0
            &&& o + 1 < pk.enc@.len()
            &&& pk.enc@[o] >= 0 && pk.enc@[o + 1] >= 0
        },
{
    reveal(pinv);
    lemma_cnt_some_le(pk.loc@, pk.loc@.len() as nat);
}

/// Packing a leaf at the end.
proof fn lemma_pinv_leaf(nodes: Seq<Node>, pos: Seq<(nat, nat)>, pk0: Packer, pk1: Packer, id: int, r: u64)
    requires
        pinv(nodes, pos, pk0), arena_ok(nodes, pos), 0 <= id < nodes.len(), pk0.loc@[id] is None,
        nodes[id].label == Some(r),
        pk1.loc@ == pk0.loc@.update(id, Some(pk0.enc@.len() as usize)),
        pk0.enc@.len() as usize as int == pk0.enc@.len(),
        pk1.enc@ == pk0.enc@.push((-(r as int) - 1) as i64),
        pk1.node_at@ == pk0.node_at@.push(None),
        pk1.owner@ == pk0.owner@.push(0),
    ensures pinv(nodes, pos, pk1),
{
    reveal(pinv);
    lemma_cnt_some_set(pk0.loc@, nodes.len() as nat, id, pk0.enc@.len() as usize);
    assert forall |i: int| 0 <= i < nodes.len() && (#[trigger] pk1.loc@[i]) is Some implies {
        let o = pk1.loc@[i]->Some_0 as int;
        &&& o < pk1.enc@.len()
        &&& (nodes[i].label matches Some(r) ==> pk1.enc@[o] == -(r as int) - 1)
        &&& (nodes[i].label is None ==> pk1.node_at@[o] == Some(pos[i]))
    } by {
        if i != id { assert(pk0.loc@[i] is Some); }
    }
    assert forall |o: int| 0 <= o < pk1.enc@.len() && (#[trigger] pk1.node_at@[o]) is Some implies {
        let i = pk1.owner@[o];
        &&& 0 <= i < nodes.len()
        &&& pk1.loc@[i] == Some(o as usize)
        &&& nodes[i].label is None
        &&& pos[i] == pk1.node_at@[o]->Some_0
        &&& o + 1 < pk1.enc@.len()
        &&& pk1.enc@[o] >= 0 && pk1.enc@[o + 1] >= 0
    } by {
        assert(o < pk0.enc@.len());
        assert(pk0.node_at@[o] is Some);
        assert(pk0.owner@[o] != id);
    }
}

/// Reserving the two slots of an internal node at the end.
proof fn lemma_pinv_internal(nodes: Seq<Node>, pos: Seq<(nat, nat)>, pk0: Packer, pk1: Packer, id: int)
    requires
        pinv(nodes, pos, pk0), arena_ok(nodes, pos), 0 <= id < nodes.len(), pk0.loc@[id] is None,
        nodes[id].label is None,
        pk1.loc@ == pk0.loc@.update(id, Some(pk0.enc@.len() as usize)),
        pk0.enc@.len() as usize as int == pk0.enc@.len(),
        pk1.enc@ == pk0.enc@.push(0).push(0),
        pk1.node_at@ == pk0.node_at@.push(Some(pos[id])).push(None),
        pk1.owner@ == pk0.owner@.push(id).push(0),
    ensures pinv(nodes, pos, pk1),
{
    reveal(pinv);
    lemma_cnt_some_set(pk0.loc@, nodes.len() as nat, id, pk0.enc@.len() as usize);
    let off = pk0.enc@.len() as int;
    assert forall |i: int| 0 <= i < nodes.len() && (#[trigger] pk1.loc@[i]) is Some implies {
        let o = pk1.loc@[i]->Some_0 as int;
        &&& o < pk1.enc@.len()
        &&& (nodes[i].label matches Some(r) ==> pk1.enc@[o] == -(r as int) - 1)
        &&& (nodes[i].label is None ==> pk1.node_at@[o] == Some(pos[i]))
    } by {
        if i != id { assert(pk0.loc@[i] is Some); }
    }
    assert forall |o: int| 0 <= o < pk1.enc@.len() && (#[trigger] pk1.node_at@[o]) is Some implies {
        let i = pk1.owner@[o];
        &&& 0 <= i < nodes.len()
        &&& pk1.loc@[i] == Some(o as usize)
        &&& nodes[i].label is None
        &&& pos[i] == pk1.node_at@[o]->Some_0
        &&& o + 1 < pk1.enc@.len()
        &&& pk1.enc@[o] >= 0 && pk1.enc@[o + 1] >= 0
    } by {
        if o < off {
            assert(pk0.node_at@[o] is Some);
            assert(pk0.owner@[o] != id);
        } else {
            assert(o == off);
        }
    }
}

/// Overwriting a nonnegative slot with a nonnegative offset (only the child
/// slots of internal nodes are nonnegative).
proof fn lemma_pinv_set(nodes: Seq<Node>, pos: Seq<(nat, nat)>, pk0: Packer, pk1: Packer, o: int, val: i64)
    requires
        pinv(nodes, pos, pk0), 0 <= o < pk0.enc@.len(), pk0.enc@[o] >= 0, val >= 0,
        pk1.enc@ == pk0.enc@.update(o, val), pk1.loc@ == pk0.loc@, pk1.node_at@ == pk0.node_at@, pk1.owner@ == pk0.owner@,
    ensures pinv(nodes, pos, pk1),
{
    reveal(pinv);
    assert forall |i: int| 0 <= i < nodes.len() && (#[trigger] pk1.loc@[i]) is Some implies {
        let o2 = pk1.loc@[i]->Some_0 as int;
        &&& o2 < pk1.enc@.len()
        &&& (nodes[i].label matches Some(r) ==> pk1.enc@[o2] == -(r as int) - 1)
        &&& (nodes[i].label is None ==> pk1.node_at@[o2] == Some(pos[i]))
    } by {
        assert(pk0.loc@[i] is Some);
    }
    assert forall |o2: int| 0 <= o2 < pk1.enc@.len() && (#[trigger] pk1.node_at@[o2]) is Some implies {
        let i = pk1.owner@[o2];
        &&& 0 <= i < nodes.len()
        &&& pk1.loc@[i] == Some(o2 as usize)
        &&& nodes[i].label is None
        &&& pos[i] == pk1.node_at@[o2]->Some_0
        &&& o2 + 1 < pk1.enc@.len()
        &&& pk1.enc@[o2] >= 0 && pk1.enc@[o2 + 1] >= 0
    } by {
        assert(pk0.node_at@[o2] is Some);
    }
}

/// The measure of the packing recursion.
pub open spec fn unpacked(nodes: Seq<Node>, pk: Packer) -> nat {
    (nodes.len() - cnt_some(pk.loc@, nodes.len() as nat)) as nat
}

pub proof fn lemma_packed_unfold(nodes: Seq<Node>, pk: Packer, i: int)
    requires packed(nodes, pk, i),
    ensures nodes[i].label is None ==> {
        let o = pk.loc@[i]->Some_0 as int;
        &&& pk.loc@[nodes[i].left as int] is Some
        &&& pk.loc@[nodes[i].right as int] is Some
        &&& pk.enc@[o] == pk.loc@[nodes[i].left as int]->Some_0 as int
        &&& pk.enc@[o + 1] == pk.loc@[nodes[i].right as int]->Some_0 as int
    },
{
    reveal(packed);
}

// ── Frames ────────────────────────────────────────────────────────────────────

/// From a to b: packed nodes stay, the array only grows (and changes only at
/// `keep`), and nothing gets unpacked.
#[verifier::opaque]
pub open spec fn pk_frame(nodes: Seq<Node>, a: Packer, b: Packer, keep: int) -> bool {
    &&& forall |i: int| 0 <= i < nodes.len() && (#[trigger] a.loc@[i]) is Some ==> b.loc@[i] == a.loc@[i]
    &&& forall |o: int| 0 <= o < a.enc@.len() && o != keep ==> #[trigger] b.enc@[o] == a.enc@[o]
    &&& forall |o: int| 0 <= o < a.enc@.len() ==> #[trigger] b.node_at@[o] == a.node_at@[o] && b.owner@[o] == a.owner@[o]
    &&& b.enc@.len() >= a.enc@.len()
    &&& unpacked(nodes, b) <= unpacked(nodes, a)
}

/// Every node packed between a and b sits at an offset ≥ lo and is packed.
#[verifier::opaque]
pub open spec fn new_packed(nodes: Seq<Node>, a: Packer, b: Packer, lo: int) -> bool {
    forall |i: int| 0 <= i < nodes.len() && a.loc@[i] is None && (#[trigger] b.loc@[i]) is Some ==>
        lo <= b.loc@[i]->Some_0 < b.enc@.len() && packed(nodes, b, i)
}

proof fn lemma_frame_trans(nodes: Seq<Node>, a: Packer, b: Packer, c: Packer, k1: int, k2: int, k: int)
    requires
        pk_frame(nodes, a, b, k1), pk_frame(nodes, b, c, k2),
        k1 == k || k1 < 0 || k1 >= a.enc@.len(),
        k2 == k || k2 < 0 || k2 >= a.enc@.len(),
    ensures pk_frame(nodes, a, c, k),
{
    reveal(pk_frame);
    assert forall |o: int| 0 <= o < a.enc@.len() && o != k implies #[trigger] c.enc@[o] == a.enc@[o] by {
        assert(c.enc@[o] == b.enc@[o]);
    }
    assert forall |o: int| 0 <= o < a.enc@.len() implies #[trigger] c.node_at@[o] == a.node_at@[o] && c.owner@[o] == a.owner@[o] by {
        assert(c.node_at@[o] == b.node_at@[o]);
    }
    assert forall |i: int| 0 <= i < nodes.len() && (#[trigger] a.loc@[i]) is Some implies c.loc@[i] == a.loc@[i] by {
        assert(b.loc@[i] == a.loc@[i]);
    }
}

/// The two children of the internal node `id` packed at `offset`.
proof fn lemma_internal_done(nodes: Seq<Node>, pos: Seq<(nat, nat)>, pk0: Packer, pk1: Packer, pk2: Packer, pk3: Packer,
    id: int, offset: int, w1: int)
    requires
        arena_ok(nodes, pos), pinv(nodes, pos, pk2),
        0 <= id < nodes.len(), nodes[id].label is None, 0 <= offset <= usize::MAX,
        pk0.loc@[id] is None, pk0.enc@.len() == offset, pk0.loc@.len() == nodes.len(),
        pk1.loc@ == pk0.loc@.update(id, Some(offset as usize)), pk1.enc@.len() == offset + 2,
        pk_frame(nodes, pk1, pk2, offset), new_packed(nodes, pk1, pk2, offset + 2),
        pk2.loc@[nodes[id].left as int] is Some, pk2.enc@[offset] == pk2.loc@[nodes[id].left as int]->Some_0 as int,
        pk2.enc@.len() == w1, offset + 2 <= w1,
        pk_frame(nodes, pk2, pk3, offset + 1), new_packed(nodes, pk2, pk3, w1),
        pk3.loc@[nodes[id].right as int] is Some, pk3.enc@[offset + 1] == pk3.loc@[nodes[id].right as int]->Some_0 as int,
    ensures new_packed(nodes, pk0, pk3, offset),
{
    reveal(pk_frame);
    reveal(new_packed);
    reveal(packed);
    lemma_pinv_facts(nodes, pos, pk2);
    assert forall |i: int| 0 <= i < nodes.len() && pk0.loc@[i] is None && (#[trigger] pk3.loc@[i]) is Some implies
        offset <= pk3.loc@[i]->Some_0 < pk3.enc@.len() && packed(nodes, pk3, i) by {
        assert(pk2.enc@.len() >= pk1.enc@.len());
        assert(pk3.enc@.len() >= pk2.enc@.len());
        if i == id {
            assert(pk1.loc@[i] is Some);
            assert(pk2.loc@[i] == pk1.loc@[i]);
            assert(pk3.loc@[i] == Some(offset as usize));
            assert(pk3.enc@[offset] == pk2.enc@[offset]);
            assert(pk3.loc@[nodes[id].left as int] == pk2.loc@[nodes[id].left as int]);
            assert(packed(nodes, pk3, i));
            assert(offset <= pk3.loc@[i]->Some_0 < pk3.enc@.len());
        } else if pk2.loc@[i] is Some {
            assert(pk1.loc@[i] is None);
            assert(packed(nodes, pk2, i));
            let oi = pk2.loc@[i]->Some_0 as int;
            assert(pk3.loc@[i] == pk2.loc@[i]);
            if nodes[i].label is None {
                assert(pk2.node_at@[oi] == Some(pos[i]));
                assert(oi + 1 < pk2.enc@.len());
                assert(pk3.enc@[oi] == pk2.enc@[oi]);
                assert(pk3.enc@[oi + 1] == pk2.enc@[oi + 1]);
                assert(pk3.loc@[nodes[i].left as int] == pk2.loc@[nodes[i].left as int]);
                assert(pk3.loc@[nodes[i].right as int] == pk2.loc@[nodes[i].right as int]);
            }
            assert(packed(nodes, pk3, i));
            assert(offset + 2 <= pk3.loc@[i]->Some_0 < pk3.enc@.len());
        } else {
            assert(pk1.loc@[i] is None);
            assert(pk2.loc@[i] is None);
            assert(w1 <= pk3.loc@[i]->Some_0 < pk3.enc@.len() && packed(nodes, pk3, i));
        }
    }
}

// ── pack_tree ─────────────────────────────────────────────────────────────────

/// `pack_tree(enc, node, offset)`: pack the arena node `id` at `offset`
/// (= the current length) and everything below it not packed yet; return
/// the next free offset.
pub fn pack_tree(nodes: &Vec<Node>, Ghost(pos): Ghost<Seq<(nat, nat)>>, id: usize, offset: usize, pk: &mut Packer) -> (w: usize)
    requires
        arena_ok(nodes@, pos),
        pinv(nodes@, pos, *old(pk)),
        id < nodes@.len(),
        old(pk).loc@[id as int] is None,
        offset == old(pk).enc@.len(),
    ensures
        pinv(nodes@, pos, *final(pk)),
        w == final(pk).enc@.len(),
        final(pk).loc@[id as int] == Some(offset),
        pk_frame(nodes@, *old(pk), *final(pk), -1),
        new_packed(nodes@, *old(pk), *final(pk), offset as int),
    decreases unpacked(nodes@, *old(pk)), 0nat,
{
    let ghost pk0 = *pk;
    proof {
        lemma_pinv_facts(nodes@, pos, pk0);
        lemma_cnt_some_set(pk.loc@, nodes@.len() as nat, id as int, offset);
        lemma_cnt_some_le(pk.loc@.update(id as int, Some(offset)), nodes@.len() as nat);
    }
    pk.loc.set(id, Some(offset));
    match nodes[id].label {
        Some(r) => {
            // Encode a leaf.
            pk.enc.push(-(r as i64) - 1);
            pk.node_at = Ghost(pk.node_at@.push(None));
            pk.owner = Ghost(pk.owner@.push(0));
            proof {
                lemma_pinv_leaf(nodes@, pos, pk0, *pk, id as int, r);
                reveal(pk_frame);
                reveal(new_packed);
                reveal(packed);
                assert forall |i: int| 0 <= i < nodes@.len() && (#[trigger] pk0.loc@[i]) is Some implies pk.loc@[i] == pk0.loc@[i] by {
                    assert(i != id as int);
                }
            }
            pk.enc.len()   // offset + 1
        }
        None => {
            // Encode an internal node: two slots, filled below.
            pk.enc.push(0);
            pk.enc.push(0);
            pk.node_at = Ghost(pk.node_at@.push(Some(pos[id as int])).push(None));
            pk.owner = Ghost(pk.owner@.push(id as int).push(0));
            proof {
                lemma_pinv_internal(nodes@, pos, pk0, *pk, id as int);
                reveal(pk_frame);
                assert forall |i: int| 0 <= i < nodes@.len() && (#[trigger] pk0.loc@[i]) is Some implies pk.loc@[i] == pk0.loc@[i] by {
                    assert(i != id as int);
                }
                assert(pk_frame(nodes@, pk0, *pk, -1));
            }
            pack_children(nodes, Ghost(pos), id, offset, pk, Ghost(pk0))
        }
    }
}

/// The two child slots of the internal node `id` packed at `offset`.
fn pack_children(nodes: &Vec<Node>, Ghost(pos): Ghost<Seq<(nat, nat)>>, id: usize, offset: usize, pk: &mut Packer,
    Ghost(pk0): Ghost<Packer>) -> (w: usize)
    requires
        arena_ok(nodes@, pos),
        pinv(nodes@, pos, *old(pk)),
        id < nodes@.len(), nodes@[id as int].label is None,
        pk0.loc@[id as int] is None, pk0.enc@.len() == offset,
        old(pk).loc@ == pk0.loc@.update(id as int, Some(offset)),
        old(pk).enc@.len() == offset + 2,
        old(pk).enc@[offset as int] >= 0, old(pk).enc@[offset + 1] >= 0,
        pk_frame(nodes@, pk0, *old(pk), -1),
    ensures
        pinv(nodes@, pos, *final(pk)),
        w == final(pk).enc@.len(),
        pk_frame(nodes@, pk0, *final(pk), -1),
        new_packed(nodes@, pk0, *final(pk), offset as int),
        final(pk).loc@[id as int] == Some(offset),
    decreases unpacked(nodes@, *old(pk)), 2nat,
{
    let ghost pk1 = *pk;
    let left = nodes[id].left;
    let right = nodes[id].right;
    // Encode left child, then right child.
    let w0 = pk.enc.len();   // offset + 2
    let w1 = pack_child(nodes, Ghost(pos), left, offset, w0, pk);
    let ghost pk2 = *pk;
    proof {
        reveal(pk_frame);
        assert(pk.enc@[offset + 1] == pk1.enc@[offset + 1]);
    }
    let w2 = pack_child(nodes, Ghost(pos), right, offset + 1, w1, pk);
    proof {
        lemma_pinv_facts(nodes@, pos, pk1);
        lemma_internal_done(nodes@, pos, pk0, pk1, pk2, *pk, id as int, offset as int, w1 as int);
        lemma_frame_trans(nodes@, pk0, pk1, pk2, -1, offset as int, -1);
        lemma_frame_trans(nodes@, pk0, pk2, *pk, -1, offset + 1, -1);
        reveal(pk_frame);
        assert(pk2.loc@[id as int] == pk1.loc@[id as int]);
    }
    w2
}

/// Fill `slot` with the offset of arena node c, packing c at w first if it
/// is not packed yet.
fn pack_child(nodes: &Vec<Node>, Ghost(pos): Ghost<Seq<(nat, nat)>>, c: usize, slot: usize, w: usize, pk: &mut Packer) -> (w2: usize)
    requires
        arena_ok(nodes@, pos),
        pinv(nodes@, pos, *old(pk)),
        c < nodes@.len(),
        slot < w, w == old(pk).enc@.len(),
        old(pk).enc@[slot as int] >= 0,
    ensures
        pinv(nodes@, pos, *final(pk)),
        w2 == final(pk).enc@.len(),
        final(pk).loc@[c as int] is Some,
        final(pk).enc@[slot as int] == final(pk).loc@[c as int]->Some_0 as int,
        pk_frame(nodes@, *old(pk), *final(pk), slot as int),
        new_packed(nodes@, *old(pk), *final(pk), w as int),
    decreases unpacked(nodes@, *old(pk)), 1nat,
{
    let ghost pk0 = *pk;
    proof { lemma_pinv_facts(nodes@, pos, pk0); }
    match pk.loc[c] {
        Some(oc) => {
            proof { assert(pk.loc@[c as int] is Some); }
            pk.enc.set(slot, oc as i64);
            proof {
                lemma_pinv_set(nodes@, pos, pk0, *pk, slot as int, oc as i64);
                reveal(pk_frame);
                reveal(new_packed);
            }
            w
        }
        None => {
            pk.enc.set(slot, w as i64);
            proof {
                lemma_pinv_set(nodes@, pos, pk0, *pk, slot as int, w as i64);
                reveal(pk_frame);
                assert(pk_frame(nodes@, pk0, *pk, slot as int));
            }
            let ghost pk1 = *pk;
            let w2 = pack_tree(nodes, Ghost(pos), c, w, pk);
            proof {
                reveal(pk_frame);
                reveal(new_packed);
                assert(pk.enc@[slot as int] == pk1.enc@[slot as int]);
                lemma_frame_trans(nodes@, pk0, pk1, *pk, slot as int, -1, slot as int);
            }
            w2
        }
    }
}

} // verus!
