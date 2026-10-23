//! The packed encoding as a sampler: `construct_encoding` (the arena of
//! `tree.rs`, packed by `packing.rs`) yields an array satisfying `enc_wf`,
//! and [`Encoded`] walks it (`sample_ky_encoding` of the original).

use vstd::prelude::*;

verus! {

use crate::ddg_walk::walk::*;
use crate::ddg_walk::tree::*;
use crate::ddg_walk::packing::*;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::pow2;

/// Build the DDG tree of a leaf table and pack it.
pub fn construct_encoding<L: Leaves>(tab: &L) -> (r: (Vec<i64>, Ghost<Seq<Option<(nat, nat)>>>))
    requires tab.lwf(),
    ensures enc_wf(tab.lldd(), r.0@, r.1@),
{
    let ghost t = tab.lldd();
    proof { tab.lemma_leaves(); }
    let b = make_ddg_tree(tab);
    let ghost pos = b.pos@;
    let nodes = b.nodes;
    proof {
        assert forall |i: int| 0 <= i < nodes@.len() && (#[trigger] nodes@[i]).label is None implies
            nodes@[i].left < nodes@.len() && nodes@[i].right < nodes@.len() by {
            assert(complete(t, nodes@, pos, i));
        }
        assert(arena_ok(nodes@, pos));
    }
    let n = nodes.len();
    let mut loc: Vec<Option<usize>> = Vec::new();
    while loc.len() < n
        invariant loc.len() <= n, forall |i: int| 0 <= i < loc.len() ==> #[trigger] loc@[i] is None,
        decreases n - loc.len(),
    {
        loc.push(None);
    }
    let mut pk = Packer { enc: Vec::new(), loc, ipos: Ghost(Seq::empty()), owner: Ghost(Seq::empty()) };
    proof {
        reveal(pinv);
        assert forall |m: nat| m <= n implies cnt_some(pk.loc@, m) == 0 by {
            lemma_cnt_none(pk.loc@, m);
        }
    }
    let ghost pk_init = pk;
    proof {
        assert(pk.loc@[0] is None);
    }
    let _w = pack_tree(&nodes, Ghost(pos), 0, 0, &mut pk);
    let _elen = pk.enc.len();
    proof {
        reveal(new_packed);
        assert forall |i: int| 0 <= i < nodes@.len() && (#[trigger] pk.loc@[i]) is Some implies packed(nodes@, pk, i) by {
            assert(pk_init.loc@[i] is None);
        }
        lemma_enc_wf(t, nodes@, pos, pk);
    }
    (pk.enc, pk.ipos)
}

/// The packed arena encodes the DDG.
proof fn lemma_enc_wf(t: LDdg, nodes: Seq<Node>, pos: Seq<(nat, nat)>, pk: Packer)
    requires
        arena_ok(nodes, pos), pinv(nodes, pos, pk), pk.enc@.len() <= usize::MAX,
        nodes.len() >= 1,
        node_is(t, nodes, pos, 0, 0, 0), (t.h)(0) == 0, t.levels >= 1,
        pk.loc@[0] == Some(0usize),
        forall |i: int| 0 <= i < nodes.len() ==> #[trigger] complete(t, nodes, pos, i),
        forall |i: int| 0 <= i < nodes.len() && (#[trigger] nodes[i]).label is None ==> is_internal(t, pos[i].0, pos[i].1),
        forall |i: int| 0 <= i < nodes.len() && (#[trigger] pk.loc@[i]) is Some ==> packed(nodes, pk, i),
    ensures enc_wf(t, pk.enc@, pk.ipos@),
{
    lemma_pinv_facts(nodes, pos, pk);
    let enc = pk.enc@;
    let ipos = pk.ipos@;
    assert forall |o: int| 0 <= o < enc.len() && (#[trigger] ipos[o]) is Some implies enc_node_ok(t, enc, ipos, o) by {
        lemma_enc_node(t, nodes, pos, pk, o);
    }
    assert(nodes[0].label is None);
    assert(next_depth(t, 0) == 0);
    assert(ipos[0] == Some(pos[0]));
}

/// One internal node of the packed array.
proof fn lemma_enc_node(t: LDdg, nodes: Seq<Node>, pos: Seq<(nat, nat)>, pk: Packer, o: int)
    requires
        arena_ok(nodes, pos), pinv(nodes, pos, pk),
        0 <= o < pk.enc@.len(), pk.ipos@[o] is Some, pk.enc@.len() <= usize::MAX,
        forall |i: int| 0 <= i < nodes.len() ==> #[trigger] complete(t, nodes, pos, i),
        forall |i: int| 0 <= i < nodes.len() && (#[trigger] nodes[i]).label is None ==> is_internal(t, pos[i].0, pos[i].1),
        forall |i: int| 0 <= i < nodes.len() && (#[trigger] pk.loc@[i]) is Some ==> packed(nodes, pk, i),
    ensures enc_node_ok(t, pk.enc@, pk.ipos@, o),
{
    lemma_pinv_facts(nodes, pos, pk);
    let enc = pk.enc@;
    let ipos = pk.ipos@;
        let i = pk.owner@[o];
        let (j, d) = ipos[o]->Some_0;
        assert(pk.loc@[i] is Some);
        assert(packed(nodes, pk, i));
        lemma_packed_unfold(nodes, pk, i);
        assert(pk.loc@[i] == Some(o as usize));
        assert((o as usize) as int == o);
        assert(complete(t, nodes, pos, i));
        assert(pos[i] == (j, d));
        let l = nodes[i].left as int;
        let r = nodes[i].right as int;
        assert(nodes[i].label is None);
        assert(is_internal(t, j, d));
        assert(node_is(t, nodes, pos, l, j + 1, 2 * d + 1));
        assert(node_is(t, nodes, pos, r, j + 1, 2 * d));
        assert(pk.loc@[l] is Some && pk.loc@[r] is Some);
        assert(enc[o] == pk.loc@[l]->Some_0 as int);
        assert(enc[o + 1] == pk.loc@[r]->Some_0 as int);
        lemma_child_slot(t, nodes, pos, pk, l, j + 1, 2 * d + 1);
        lemma_child_slot(t, nodes, pos, pk, r, j + 1, 2 * d);
    }

/// The offset of a packed child holds the right thing.
proof fn lemma_child_slot(t: LDdg, nodes: Seq<Node>, pos: Seq<(nat, nat)>, pk: Packer, c: int, j1: nat, x: nat)
    requires
        arena_ok(nodes, pos), pinv(nodes, pos, pk),
        node_is(t, nodes, pos, c, j1, x), pk.loc@[c] is Some,
    ensures enc_child_ok(t, pk.enc@, pk.ipos@, pk.loc@[c]->Some_0 as i64, j1, x),
{
    lemma_pinv_facts(nodes, pos, pk);
    let q = pk.loc@[c]->Some_0 as int;
    assert(q < pk.enc@.len());
    assert((q as i64) as int == q);
    if x < (t.h)(j1) {
        assert(nodes[c].label is Some);
    } else {
        assert(nodes[c].label is None);
        assert(pk.ipos@[q] == Some(pos[c]));
        assert(pk.ipos@[q] is Some);
    }
}

proof fn lemma_cnt_none(loc: Seq<Option<usize>>, m: nat)
    requires m <= loc.len(), forall |i: int| 0 <= i < loc.len() ==> #[trigger] loc[i] is None,
    ensures cnt_some(loc, m) == 0,
    decreases m,
{
    if m > 0 { lemma_cnt_none(loc, (m - 1) as nat); }
}

/// A packed DDG of the family F. `enc` is `[−(r+1)]` when F is the point
/// mass at r (the original's `len(enc) == 1` case).
pub struct Encoded<F: Family> {
    pub enc: Vec<i64>,
    pub n: u64,
    pub exact: bool,
    pub fam: Ghost<F>,
    pub ipos: Ghost<Seq<Option<(nat, nat)>>>,
}

impl<F: Family> DdgWalk for Encoded<F> {
    type Pos = usize;

    open spec fn wf(&self) -> bool {
        &&& self.fam@.fwf()
        &&& self.n as nat == self.fam@.fldd().n
        &&& self.exact == self.fam@.fexact()
        &&& match self.fam@.fpoint() {
            Some(r) => self.enc@ == seq![(-(r as int) - 1) as i64] && r < 0x4000000000000000,
            None => enc_wf(self.fam@.fldd(), self.enc@, self.ipos@),
        }
    }

    open spec fn ldd(&self) -> LDdg { self.fam@.fldd() }

    open spec fn target(&self, e: spec_fn(nat) -> real) -> real { self.fam@.ftarget(e) }

    open spec fn pos(&self, p: usize) -> (nat, nat) { self.ipos@[p as int]->Some_0 }

    open spec fn valid_pos(&self, p: usize) -> bool { p < self.ipos@.len() && self.ipos@[p as int] is Some }

    open spec fn swap(&self) -> bool { true }

    open spec fn point(&self) -> Option<nat> { self.fam@.fpoint() }

    open spec fn exact(&self) -> bool { self.fam@.fexact() }

    proof fn lemma_shape(&self) { self.fam@.lemma_fshape(); }

    proof fn lemma_fuel(&self, e: spec_fn(nat) -> real, s0: real) -> (f: nat) { self.fam@.lemma_ffuel(e, s0) }

    fn is_exact(&self) -> (r: bool) { self.exact }

    fn root(&self) -> (r: Step<usize>) {
        if self.enc.len() == 1 {
            // `if len(enc) == 1: return 1` (here: the label stored there).
            let v = self.enc[0];
            Step::Done((-(v + 1)) as u64)
        } else {
            Step::Next(0)
        }
    }

    /// `c = enc[c + b]; if enc[c] < 0: return -enc[c]`.
    fn step(&self, p: usize, b: u64) -> (r: Step<usize>) {
        let ghost t = self.fam@.fldd();
        let _len = self.enc.len();
        proof {
            assert(enc_node_ok(t, self.enc@, self.ipos@, p as int));
        }
        let q = self.enc[p + b as usize];
        proof {
            let (j, d) = self.ipos@[p as int]->Some_0;
            if b == 0 {
                assert(enc_child_ok(t, self.enc@, self.ipos@, q, j + 1, child(d, b as nat, true)));
            } else {
                assert(enc_child_ok(t, self.enc@, self.ipos@, q, j + 1, child(d, b as nat, true)));
            }
        }
        let c = q as usize;
        let v = self.enc[c];
        if v < 0 {
            let r = (-(v + 1)) as u64;
            if r < self.n { Step::Done(r) } else { Step::Restart }
        } else {
            Step::Next(c)
        }
    }
}

} // verus!
