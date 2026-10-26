//! The random walk on a level-structured DDG, proved once for every table
//! layout that implements [`DdgWalk`].
//!
//! A level-structured DDG ([`LDdg`]) has its leaves at depths 1..K. At each
//! depth the h(j) leaves come first (positions 0..h(j)−1) and the internal
//! nodes follow. Internal node d of depth j has the children 2d and 2d+1 at
//! depth j+1. Two kinds of back-edge are allowed:
//!   - a leaf labeled ≥ n restarts the walk at the root (FLDR's reject label);
//!   - an internal node at depth K continues as the internal node of the same
//!     index at depth `wrap` (the back-edges of OPTAS, l < k).
//!
//! FLDR (`fldr.rs`) uses only the first kind and the Z_kl-type samplers
//! (`optas`) only the second. A [`DdgSpec`] gives the DDG and the
//! distribution and proves their laws ([`DdgSpec::lemma_fuel`]); a
//! [`DdgWalk`] is a table layout of a spec that says how to take one step
//! ([`DdgWalk::step`]). [`sample`] then has the spec
//!
//! ```text
//!   ε ≥ E_p[ℰ]        ℰ ≥ 0
//!   ---------------------------------------------
//!   [{ ↯(ε) }] sample(w) [{ r. ↯(ℰ(r)) }]
//! ```
//!
//! The credit is fuel-indexed as in `fldr.rs`: `lwalk_f(j, d, f)` is the
//! value of internal node d at depth j with f flips left, and a node with no
//! fuel is worth 1.

use vstd::prelude::*;

verus! {

use crate::ec::*;
#[cfg(verus_keep_ghost)]
use crate::ec::ErrorCreditCarrier::Value;
use crate::rand_primitives::{rand_2_u64_fast, thin_air};

/// A level-structured DDG: labels < n are outcomes, leaves at depths 1..K.
pub struct LDdg {
    pub n: nat,
    pub levels: nat,
    pub wrap: nat,
    pub h: spec_fn(nat) -> nat,
    pub lab: spec_fn(nat, nat) -> nat,
}

/// A(j): the internal nodes at depth j. A(0) = 1 (the root) and
/// A(j+1) = 2A(j) − h(j+1).
pub open spec fn lnum(t: LDdg, j: nat) -> int
    decreases j,
{
    if j == 0 { 1 } else { 2 * lnum(t, (j - 1) as nat) - (t.h)(j) as int }
}

/// The shape is consistent: every depth has enough nodes for its leaves, and
/// the internal nodes at depth K fit into depth `wrap`.
pub open spec fn valid_ldd(t: LDdg) -> bool {
    &&& t.levels >= 1
    &&& t.wrap < t.levels
    &&& forall |j: nat| 1 <= j <= t.levels ==> (#[trigger] (t.h)(j)) <= 2 * lnum(t, (j - 1) as nat)
    &&& lnum(t, t.levels) <= lnum(t, t.wrap)
}

/// The depth an internal node of depth j continues at.
pub open spec fn next_depth(t: LDdg, j: nat) -> nat {
    if j >= t.levels { t.wrap } else { j }
}

/// Value of internal node d at depth j with f flips left.
pub open spec fn lwalk_f(t: LDdg, e: spec_fn(nat) -> real, j: nat, d: nat, f: nat) -> real
    decreases f, 0nat,
{
    if f == 0 {
        1real
    } else {
        (lwalk_g(t, e, j + 1, 2 * d, (f - 1) as nat) + lwalk_g(t, e, j + 1, 2 * d + 1, (f - 1) as nat)) / 2real
    }
}

/// Value of node x at depth j, just reached, with f flips left.
pub open spec fn lwalk_g(t: LDdg, e: spec_fn(nat) -> real, j: nat, x: nat, f: nat) -> real
    decreases f, 1nat,
{
    if x < (t.h)(j) {
        if (t.lab)(j, x) < t.n { e((t.lab)(j, x)) } else { lwalk_f(t, e, 0, 0, f) }
    } else {
        lwalk_f(t, e, next_depth(t, j), (x - (t.h)(j)) as nat, f)
    }
}

/// The child reached by flip b: 2d + b, or 2d + (1 − b) for layouts that
/// send flip 0 to the odd child (the packed encoding of `encoding.rs`).
pub open spec fn child(d: nat, b: nat, swap: bool) -> nat {
    if swap { 2 * d + (1 - b) as nat } else { 2 * d + b }
}

/// A valid internal node.
pub open spec fn is_internal(t: LDdg, j: nat, d: nat) -> bool {
    j < t.levels && (d as int) < lnum(t, j)
}

pub proof fn lemma_lnum_nonneg(t: LDdg, j: nat)
    requires valid_ldd(t), j <= t.levels,
    ensures lnum(t, j) >= 0,
    decreases j,
{
    if j > 0 {
        lemma_lnum_nonneg(t, (j - 1) as nat);
        assert((t.h)(j) <= 2 * lnum(t, (j - 1) as nat));
    }
}

/// The node reached from an internal node is a leaf or an internal node.
pub proof fn lemma_child_internal(t: LDdg, j: nat, d: nat, b: nat, swap: bool)
    requires valid_ldd(t), is_internal(t, j, d), b <= 1,
    ensures
        child(d, b, swap) >= (t.h)(j + 1) ==>
            is_internal(t, next_depth(t, j + 1), (child(d, b, swap) - (t.h)(j + 1)) as nat),
{
    let x = child(d, b, swap);
    assert(x < 2 * d + 2);
    assert(lnum(t, j + 1) == 2 * lnum(t, j) - (t.h)(j + 1) as int);
    if x >= (t.h)(j + 1) && j + 1 >= t.levels {
        assert(j + 1 == t.levels);
    }
}

pub proof fn lemma_lwalk_nonneg(t: LDdg, e: spec_fn(nat) -> real, f: nat)
    requires forall |i: nat| (#[trigger] e(i)) >= 0real,
    ensures
        forall |j: nat, d: nat| #[trigger] lwalk_f(t, e, j, d, f) >= 0real,
        forall |j: nat, x: nat| #[trigger] lwalk_g(t, e, j, x, f) >= 0real,
    decreases f,
{
    if f > 0 {
        lemma_lwalk_nonneg(t, e, (f - 1) as nat);
    }
    assert forall |j: nat, d: nat| #[trigger] lwalk_f(t, e, j, d, f) >= 0real by {
        if f > 0 {
            let f1 = (f - 1) as nat;
            assert(lwalk_g(t, e, j + 1, 2 * d, f1) >= 0real);
            assert(lwalk_g(t, e, j + 1, 2 * d + 1, f1) >= 0real);
        }
    }
    assert forall |j: nat, x: nat| #[trigger] lwalk_g(t, e, j, x, f) >= 0real by {
        if x < (t.h)(j) {
            if (t.lab)(j, x) < t.n {
            } else {
                assert(lwalk_f(t, e, 0, 0, f) >= 0real);
            }
        } else {
            assert(lwalk_f(t, e, next_depth(t, j), (x - (t.h)(j)) as nat, f) >= 0real);
        }
    }
}

/// The result of one step.
pub enum Step<P> {
    /// A leaf with an outcome.
    Done(u64),
    /// A leaf with the reject label: start again from the root.
    Restart,
    /// An internal node.
    Next(P),
}

/// The spec side of a DDG sampler: the tree it walks (`ddg`), the
/// distribution it samples (`target`), and the laws `DdgWalk` needs about
/// them, proved once and shared by every layout of the same DDG.
pub trait DdgSpec {
    spec fn wf(&self) -> bool;

    /// The DDG.
    spec fn ddg(&self) -> LDdg;

    /// E_p[ℰ] for the distribution p the DDG samples.
    spec fn target(&self, e: spec_fn(nat) -> real) -> real;

    /// Some(r) if p is the point mass at r; then the root is a leaf.
    spec fn point(&self) -> Option<nat>;

    /// The fuel law holds with no slack (no `thin_air` needed).
    spec fn exact(&self) -> bool;

    proof fn lemma_shape(&self)
        requires self.wf(),
        ensures
            valid_ldd(self.ddg()),
            forall |e: spec_fn(nat) -> real| (forall |i: nat| (#[trigger] e(i)) >= 0real) ==> #[trigger] self.target(e) >= 0real,
            self.point() matches Some(r) ==> (r < self.ddg().n
                && forall |e: spec_fn(nat) -> real| (forall |i: nat| (#[trigger] e(i)) >= 0real) ==> #[trigger] self.target(e) >= e(r));

    /// With enough fuel the root is worth at most E_p[ℰ] + s₀.
    proof fn lemma_fuel(&self, e: spec_fn(nat) -> real, s0: real) -> (f: nat)
        requires
            self.wf(), self.point() is None,
            forall |i: nat| (#[trigger] e(i)) >= 0real,
            s0 > 0real || (self.exact() && s0 == 0real),
        ensures lwalk_f(self.ddg(), e, 0, 0, f) <= self.target(e) + s0;
}


/// A table layout that can be walked: a way to take one step through the
/// DDG of its spec. The sampler only uses `is_exact`, `root` and `step`;
/// every fact about the distribution comes from the laws of [`DdgSpec`].
pub trait DdgWalk {
    /// The distribution and its DDG.
    type Spec: DdgSpec;

    /// A position in the table (an internal node).
    type Pos;

    spec fn wf(&self) -> bool;

    spec fn spec(&self) -> Self::Spec;

    proof fn lemma_wf(&self)
        requires self.wf(),
        ensures self.spec().wf();

    /// The node a position stands for: (depth, index among the internal nodes).
    spec fn pos(&self, p: Self::Pos) -> (nat, nat);

    /// p is a position of the table (an internal node).
    spec fn valid_pos(&self, p: Self::Pos) -> bool;

    /// Flip b leads to child 2d + (1 − b) instead of 2d + b.
    spec fn swap(&self) -> bool;

    fn is_exact(&self) -> (r: bool)
        requires self.wf(),
        ensures r == self.spec().exact();

    fn root(&self) -> (r: Step<Self::Pos>)
        requires self.wf(),
        ensures
            self.spec().point() matches Some(v) ==> (r matches Step::Done(x) && x as nat == v),
            self.spec().point() is None ==> (r matches Step::Next(p) && self.valid_pos(p) && self.pos(p) == (0nat, 0nat));

    /// One flip b from the internal node at p.
    fn step(&self, p: Self::Pos, b: u64) -> (r: Step<Self::Pos>)
        requires
            self.wf(), self.spec().point() is None, b <= 1, self.valid_pos(p),
            is_internal(self.spec().ddg(), self.pos(p).0, self.pos(p).1),
        ensures
            r matches Step::Next(q) ==> self.valid_pos(q),
            ({
            let t = self.spec().ddg();
            let j1 = self.pos(p).0 + 1;
            let x = child(self.pos(p).1, b as nat, self.swap());
            &&& x < (t.h)(j1) && (t.lab)(j1, x) < t.n ==> (r matches Step::Done(v) && v as nat == (t.lab)(j1, x))
            &&& x < (t.h)(j1) && (t.lab)(j1, x) >= t.n ==>
                r is Restart || (r matches Step::Next(q) && self.pos(q) == (0nat, 0nat))
            &&& x >= (t.h)(j1) ==>
                (r matches Step::Next(q) && self.pos(q) == (next_depth(t, j1), (x - (t.h)(j1)) as nat))
        });
}

/// The sampler, for any layout:
///
/// ```text
///   ε ≥ E_p[ℰ]        ℰ ≥ 0
///   ---------------------------------------------
///   [{ ↯(ε) }] sample(w) [{ r. ↯(ℰ(r)) }]
/// ```
pub fn sample<W: DdgWalk>(
    w: &W,
    Ghost(e): Ghost<spec_fn(nat) -> real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(eps): Ghost<real>,
) -> ((value, out_credit): (u64, Tracked<ErrorCreditResource>))
    requires
        w.wf(),
        forall |i: nat| (#[trigger] e(i)) >= 0real,
        eps >= w.spec().target(e),
        input_credit@ =~= (Value { car: eps }),
    ensures
        (value as nat) < w.spec().ddg().n,
        out_credit@@ =~= (Value { car: e(value as nat) }),
{
    let ghost s = w.spec();
    let ghost t = s.ddg();
    proof { w.lemma_wf(); s.lemma_shape(); }
    let r0 = w.root();
    let mut p = match r0 {
        Step::Done(v) => {
            let tracked c;
            proof {
                let tracked (c1, _rest) = ec_split(input_credit, e(v as nat), eps - e(v as nat));
                c = c1;
            }
            return (v, Tracked(c));
        }
        Step::Restart => {
            proof { assert(false); }
            return (0, Tracked(input_credit));
        }
        Step::Next(p0) => p0,
    };
    // ↯(ε + s₀), with s₀ = 0 for an exact layout.
    let ghost mut s0: real = 0real;
    let tracked mut work = input_credit;
    if !w.is_exact() {
        let Tracked(slack) = thin_air();
        proof {
            s0 = choose |sv: real| sv > 0real && (slack@ =~= (Value { car: sv }));
            let tracked w2 = ec_combine(work, slack, eps, s0);
            work = w2;
        }
    }
    let ghost mut f: nat = s.lemma_fuel(e, s0);
    let tracked mut credit;
    proof {
        lemma_lwalk_nonneg(t, e, f);
        let v = lwalk_f(t, e, 0, 0, f);
        let tracked (c1, _rest) = ec_split(work, v, eps + s0 - v);
        credit = c1;
        lemma_lnum_nonneg(t, 0);
    }
    loop
        invariant
            s == w.spec(), t == s.ddg(), w.wf(), s.point() is None, valid_ldd(t),
            forall |i: nat| (#[trigger] e(i)) >= 0real,
            w.valid_pos(p),
            is_internal(t, w.pos(p).0, w.pos(p).1),
            credit@ =~= (Value { car: lwalk_f(t, e, w.pos(p).0, w.pos(p).1, f) }),
        decreases f,
    {
        let ghost j = w.pos(p).0;
        let ghost d = w.pos(p).1;
        let ghost sw = w.swap();
        proof {
            if f == 0 {
                ec_contradict(&credit);
            }
        }
        let ghost f1 = (f - 1) as nat;
        let ghost alloc = |i: nat|
            if i == 1 { lwalk_g(t, e, j + 1, child(d, 1, sw), f1) } else { lwalk_g(t, e, j + 1, child(d, 0, sw), f1) };
        proof {
            lemma_lwalk_nonneg(t, e, f1);
            assert(alloc(0) >= 0real && alloc(1) >= 0real);
            assert(lwalk_f(t, e, j, d, f) == (alloc(0) + alloc(1)) / 2real);
        }
        let (b, Tracked(out)) = rand_2_u64_fast(Tracked(credit), Ghost(alloc));
        proof {
            credit = out;
            f = f1;
            lemma_child_internal(t, j, d, b as nat, sw);
            lemma_lnum_nonneg(t, 0);
        }
        match w.step(p, b) {
            Step::Done(v) => {
                return (v, Tracked(credit));
            }
            Step::Restart => {
                p = match w.root() {
                    Step::Next(q) => q,
                    _ => {
                        proof { assert(false); }
                        return (0, Tracked(credit));
                    }
                };
            }
            Step::Next(q) => {
                p = q;
            }
        }
    }
}

} // verus!
