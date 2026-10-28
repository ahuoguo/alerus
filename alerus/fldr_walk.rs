//! FLDR on the generic walk of `ddg_walk/`.
//!
//! - **`ByLevel<T: DdgTable>`** walks any FLDR table level by level as a
//!   `DdgWalk`; `sample_fldr` is `walk::sample` on it. The bridge is
//!   `lemma_fldr_walk`: the generic credit `lwalk_f` equals FLDR's value
//!   plus failure credit, fldr_f + fldr_fail_f.
//! - **`impl DdgSpec for Ddg`** states FLDR's laws once (`lemma_fldr_fuel`);
//!   `ByLevel` and the packed encoding both use it.
//! - **The packed encoding.** `construct_fldr_encoding` builds `optas`'s
//!   packed array (`tree.py` + `packing.py`, here `ddg_walk/{tree,
//!   packing}.rs`) from any `DdgTable`. A reject label n is a leaf that
//!   restarts the walk. `sample_fldr_encoding` samples it with the spec of
//!   `sample_fldr`. The encoding needs levels ≤ 52, so that the array's
//!   offsets (at most 2^52 nodes per depth) fit, and n < 2⁶², so that a leaf
//!   entry −(label + 1) fits an `i64`.
//!
//! `sample_748_encoding` runs the (7, 4, 8) example on the encoding of the
//! AISTATS layout.

use vstd::prelude::*;

verus! {

use crate::ec::*;
#[cfg(verus_keep_ghost)]
use crate::ec::ErrorCreditCarrier::Value;
use crate::fldr::*;
use crate::ddg_walk::walk;
use crate::ddg_walk::walk::*;
use crate::ddg_walk::tree::*;
use crate::ddg_walk::encoding::*;
#[cfg(verus_keep_ghost)]
use crate::fldr_helper::*;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::lemma_pow2_strictly_increases;

/// The FLDR tree as a level-structured DDG: no wrap-around (A(K) = 0), and
/// the reject label n restarts at the root.
pub open spec fn fldr_ddg(t: Ddg) -> LDdg {
    LDdg { n: t.n, levels: t.levels, wrap: 0, h: t.h, lab: t.lab }
}

/// A(j) = N(j) − h(j): the internal nodes are the nodes that are not leaves.
pub proof fn lemma_fldr_lnum(t: Ddg, j: nat)
    requires valid_ddg(t), j <= t.levels,
    ensures lnum(fldr_ddg(t), j) == num_nodes(t, j) as int - (t.h)(j) as int,
    decreases j,
{
    if j > 0 {
        lemma_fldr_lnum(t, (j - 1) as nat);
        let j1 = (j - 1) as nat;
        if j1 >= 1 {
            assert((t.h)(j1) <= num_nodes(t, j1));
        }
        assert(num_nodes(t, j) == 2 * ((num_nodes(t, j1) - (t.h)(j1)) as nat));
    }
}

pub proof fn lemma_fldr_valid_ldd(t: Ddg)
    requires valid_ddg(t), t.levels >= 1,
    ensures
        valid_ldd(fldr_ddg(t)),
        lnum(fldr_ddg(t), t.levels) == 0,
        forall |j: nat| j <= t.levels ==> #[trigger] lnum(fldr_ddg(t), j) == num_nodes(t, j) as int - (t.h)(j) as int,
{
    let l = fldr_ddg(t);
    assert forall |j: nat| j <= t.levels implies #[trigger] lnum(l, j) == num_nodes(t, j) as int - (t.h)(j) as int by {
        lemma_fldr_lnum(t, j);
    }
    assert forall |j: nat| 1 <= j <= l.levels implies (#[trigger] (l.h)(j)) <= 2 * lnum(l, (j - 1) as nat) by {
        let j1 = (j - 1) as nat;
        lemma_fldr_lnum(t, j1);
        if j1 >= 1 { assert((t.h)(j1) <= num_nodes(t, j1)); }
        assert(num_nodes(t, j) == 2 * ((num_nodes(t, j1) - (t.h)(j1)) as nat));
        assert((t.h)(j) <= num_nodes(t, j));
    }
    lemma_ddg_close(t);
    lemma_fldr_lnum(t, t.levels);
    assert(lnum(l, 0) == 1);
}

/// The generic credit of an internal node is fldr_f + fldr_fail_f.
pub proof fn lemma_fldr_walk(t: Ddg, e: spec_fn(nat) -> real, f: nat)
    requires valid_ddg(t), t.levels >= 1,
    ensures
        forall |j: nat, d: nat| is_internal(fldr_ddg(t), j, d) ==>
            #[trigger] lwalk_f(fldr_ddg(t), e, j, d, f) == fldr_f(t, e, j, d, f) + fldr_fail_f(t, j, d, f),
    decreases f,
{
    let l = fldr_ddg(t);
    lemma_fldr_valid_ldd(t);
    if f > 0 {
        let f1 = (f - 1) as nat;
        lemma_fldr_walk(t, e, f1);
        assert forall |j: nat, d: nat| is_internal(l, j, d) implies
            #[trigger] lwalk_f(l, e, j, d, f) == fldr_f(t, e, j, d, f) + fldr_fail_f(t, j, d, f) by {
            assert forall |x: nat| x < 2 * d + 2 implies
                #[trigger] lwalk_g(l, e, j + 1, x, f1) == fldr_g(t, e, j + 1, x, f1) + fldr_fail_g(t, j + 1, x, f1) by {
                assert(lnum(l, j + 1) == 2 * lnum(l, j) - (t.h)(j + 1) as int);
                if x < (t.h)(j + 1) {
                    if (t.lab)(j + 1, x) >= t.n {
                        assert(is_internal(l, 0, 0));
                        assert(lwalk_f(l, e, 0, 0, f1) == fldr_f(t, e, 0, 0, f1) + fldr_fail_f(t, 0, 0, f1));
                        assert(lwalk_g(l, e, j + 1, x, f1) == lwalk_f(l, e, 0, 0, f1));
                    } else {
                        assert(lwalk_g(l, e, j + 1, x, f1) == e((t.lab)(j + 1, x)));
                        assert(fldr_fail_g(t, j + 1, x, f1) == 0real);
                    }
                } else {
                    let y = (x - (t.h)(j + 1)) as nat;
                    assert(j + 1 < t.levels);
                    assert(is_internal(l, j + 1, y));
                    assert(next_depth(l, j + 1) == j + 1);
                    assert(lwalk_f(l, e, j + 1, y, f1) == fldr_f(t, e, j + 1, y, f1) + fldr_fail_f(t, j + 1, y, f1));
                    assert(lwalk_g(l, e, j + 1, x, f1) == lwalk_f(l, e, j + 1, y, f1));
                }
            }
            assert(lwalk_g(l, e, j + 1, 2 * d, f1) == fldr_g(t, e, j + 1, 2 * d, f1) + fldr_fail_g(t, j + 1, 2 * d, f1));
            assert(lwalk_g(l, e, j + 1, 2 * d + 1, f1)
                == fldr_g(t, e, j + 1, 2 * d + 1, f1) + fldr_fail_g(t, j + 1, 2 * d + 1, f1));
        }
    }
}

/// The fuel law of FLDR, shared by every layout.
pub proof fn lemma_fldr_fuel(t: Ddg, e: spec_fn(nat) -> real, s0: real) -> (f: nat)
    requires valid_ddg(t), t.levels >= 1, forall |i: nat| (#[trigger] e(i)) >= 0real, s0 > 0real,
    ensures lwalk_f(fldr_ddg(t), e, 0, 0, f) <= fldr_exp(t, e) + s0,
{
    lemma_fldr_valid_ldd(t);
    lemma_fldr_fail_witness(t, s0);
    let f = choose |k: nat| fldr_fail_f(t, 0, 0, k) < s0;
    lemma_fldr_val_le_target(t, e, f);
    lemma_fldr_walk(t, e, f);
    assert(is_internal(fldr_ddg(t), 0, 0));
    f
}

/// FLDR's distribution: Σ (aᵢ/m)·ℰ(i), for any table with view t.
impl DdgSpec for Ddg {
    open spec fn wf(&self) -> bool { valid_ddg(*self) && self.levels >= 1 }

    open spec fn ddg(&self) -> LDdg { fldr_ddg(*self) }

    open spec fn target(&self, e: spec_fn(nat) -> real) -> real { fldr_exp(*self, e) }

    open spec fn point(&self) -> Option<nat> { None }

    open spec fn exact(&self) -> bool { false }

    proof fn lemma_shape(&self) {
        lemma_fldr_valid_ldd(*self);
        assert forall |e: spec_fn(nat) -> real| (forall |i: nat| (#[trigger] e(i)) >= 0real)
            implies #[trigger] self.target(e) >= 0real by {
            lemma_fldr_exp_nonneg(*self, e);
        }
    }

    proof fn lemma_fuel(&self, e: spec_fn(nat) -> real, s0: real) -> (f: nat) {
        lemma_fldr_fuel(*self, e, s0)
    }
}

/// Any FLDR table, walked level by level: the position is (c, d).
pub struct ByLevel<'a, T: DdgTable> {
    pub tab: &'a T,
}

impl<'a, T: DdgTable> DdgWalk for ByLevel<'a, T> {
    type Spec = Ddg;
    type Pos = (u64, u64);

    open spec fn wf(&self) -> bool { self.tab.wf() }

    open spec fn spec(&self) -> Ddg { self.tab@ }

    proof fn lemma_wf(&self) { self.tab.wf_props(); }

    open spec fn pos(&self, p: (u64, u64)) -> (nat, nat) { (p.0 as nat, p.1 as nat) }

    open spec fn valid_pos(&self, p: (u64, u64)) -> bool { true }

    open spec fn swap(&self) -> bool { false }

    fn is_exact(&self) -> (r: bool) { false }

    fn root(&self) -> (r: Step<(u64, u64)>) { Step::Next((0, 0)) }

    fn step(&self, p: (u64, u64), b: u64) -> (r: Step<(u64, u64)>) {
        let ghost t = self.tab@;
        let (c, d) = p;
        proof {
            self.tab.wf_props();
            lemma_fldr_valid_ldd(t);
            // d < A(c) ≤ N(c) ≤ 2^c ≤ 2^levels ≤ 2^62, and c < levels ≤ 62.
            lemma_num_nodes_le_pow2(t, c as nat);
            lemma_pow2_mono(c as nat, t.levels);
            lemma_pow2_62();
            if t.levels > 62 { lemma_pow2_strictly_increases(62nat, t.levels); }
        }
        let c1 = c + 1;
        let x = 2 * d + b;
        let hc = self.tab.get_h(c1);
        if x < hc {
            let lab = self.tab.get_lab(c1, x);
            if lab < self.tab.n() { Step::Done(lab) } else { Step::Restart }
        } else {
            proof {
                let l = fldr_ddg(t);
                assert(lnum(l, c1 as nat) == 2 * lnum(l, c as nat) - (t.h)(c1 as nat) as int);
                assert(c1 < t.levels);
            }
            Step::Next((c1, x - hc))
        }
    }
}

/// The leaves of an FLDR table, for `make_ddg_tree`. No internal node
/// reaches depth K, so the wrap depth passed is K itself (no back-edges).
impl<'a, T: DdgTable> Leaves for ByLevel<'a, T> {
    open spec fn lwf(&self) -> bool {
        self.tab.wf() && self.tab@.n < 0x4000000000000000 && self.tab@.levels <= 52
    }

    open spec fn ddg(&self) -> LDdg { fldr_ddg(self.tab@) }

    proof fn lemma_leaves(&self) {
        self.tab.wf_props();
        lemma_fldr_valid_ldd(self.tab@);
        let t = fldr_ddg(self.tab@);
        assert forall |j: nat| j <= t.levels implies #[trigger] npos(t, j) <= 0x10000000000000 by {
            lemma_npos(t, j);
            lemma_pow2_mono(j, 52);
            vstd::arithmetic::power2::lemma2_to64();
            vstd::arithmetic::power2::lemma2_to64_rest();
        }
    }

    fn levels(&self) -> (r: u64) { self.tab.levels() }

    fn wrap_level(&self) -> (r: u64) {
        proof { self.tab.wf_props(); lemma_fldr_valid_ldd(self.tab@); }
        self.tab.levels()
    }

    fn get_h(&self, j: u64) -> (r: u64) { self.tab.get_h(j) }

    fn get_lab(&self, j: u64, x: u64) -> (r: u64) { self.tab.get_lab(j, x) }
}

/// The packed encoding of an FLDR table.
pub fn construct_fldr_encoding<T: DdgTable>(tab: &T) -> (r: Encoded<Ddg>)
    requires tab.wf(), tab@.n < 0x4000000000000000, tab@.levels <= 52,
    ensures r.wf(), r.spec@ == tab@,
{
    proof { tab.wf_props(); }
    let w = ByLevel { tab };
    let (enc, node_at) = construct_encoding(&w);
    Encoded { enc, n: tab.n(), exact: false, spec: Ghost(tab@), node_at }
}

/// FLDR on its packed encoding: the spec of `sample_fldr`.
pub fn sample_fldr_encoding(
    enc: &Encoded<Ddg>,
    Ghost(e): Ghost<spec_fn(nat) -> real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(eps): Ghost<real>,
) -> ((value, out_credit): (u64, Tracked<ErrorCreditResource>))
    requires
        enc.wf(),
        forall |x: nat| (#[trigger] e(x)) >= 0real,
        eps >= fldr_exp(enc.spec@, e),
        input_credit@ =~= (Value { car: eps }),
    ensures
        (value as nat) < enc.spec@.n,
        out_credit@@ =~= (Value { car: e(value as nat) }),
{
    walk::sample(enc, Ghost(e), Tracked(input_credit), Ghost(eps))
}

/// The running example (7, 4, 8), packed from the AISTATS layout.
pub fn sample_748_encoding(
    Ghost(e): Ghost<spec_fn(nat) -> real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(eps): Ghost<real>,
) -> ((value, out_credit): (u64, Tracked<ErrorCreditResource>))
    requires
        forall |x: nat| (#[trigger] e(x)) >= 0real,
        eps >= (7real * e(0nat) + 4real * e(1nat) + 8real * e(2nat)) / 19real,
        input_credit@ =~= (Value { car: eps }),
    ensures
        value < 3,
        out_credit@@ =~= (Value { car: e(value as nat) }),
{
    let mut w: Vec<u64> = Vec::new();
    w.push(7);
    w.push(4);
    w.push(8);
    proof { reveal_with_fuel(crate::fldr::vsum, 4); reveal_with_fuel(fldr_wsum, 4); vstd::arithmetic::power2::lemma2_to64(); }
    let tab = crate::fldr_layouts::fldr_preprocess_h(w, 19, 5);
    let enc = construct_fldr_encoding(&tab);
    sample_fldr_encoding(&enc, Ghost(e), Tracked(input_credit), Ghost(eps))
}

} // verus!
