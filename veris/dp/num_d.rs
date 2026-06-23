// NumD — a concrete integer value with a ghost "distance" annotation,
// encoding LightDP's `num(d)` type.
//
// Intuition: we imagine two adjacent worlds (adjacent databases).
// `val()` is the value in world 1; `val() + dist()` is the value in
// world 2. `dist()` is ghost.
//
// the `d` field is PRIVATE to this module, so external code cannot 
// fabricate a NumD with a chosen distance. Distances are only
// produced by:
//   • `lit`, `from_ibig`  — always distance 0 (safe)
//   • `add`, `clone`       — derived from existing NumD distances
//   • `laplace`            — #[verus::trusted] Laplace-shift axiom
//                            paired with a credit payment
//
// Distance rules (LightDP T-OPLUS):   ^(e1 + e2) = ^e1 + ^e2
// Comparison  (LightDP T-ODOT)    :   (e1 < e2) == (e1+d1 < e2+d2)

use vstd::prelude::*;
use random::{IBig, ibig_from_i64, ibig_add, ibig_ge, ibig_lt, ibig_clone};

verus! {

use crate::dp::mult_credit::*;
#[cfg(verus_keep_ghost)]
use crate::extern_spec::ExIBig;
#[cfg(verus_keep_ghost)]
use crate::extern_spec::ibig_view;

pub open spec fn abs_int(x: int) -> int {
    if x >= 0 { x } else { -x }
}

pub open spec fn abs_real(x: real) -> real {
    if x >= 0real { x } else { -x }
}

/// A numeric value with a ghost distance annotation.
pub struct NumD {
    v: IBig,
    d: Ghost<int>,
}

impl NumD {
    /// Ghost projection of the distance. Opaque.
    pub closed spec fn dist(&self) -> int { self.d@ }

    /// World-1 value. Opaque projection through `ibig_view`.
    pub closed spec fn val(&self) -> int { ibig_view(&self.v) }

    /// World-2 value.
    pub open spec fn shifted(&self) -> int { self.val() + self.dist() }

    /// Integer literal — distance 0.
    #[inline]
    pub fn lit(x: i64) -> (r: NumD)
        ensures r.val() == x as int, r.dist() == 0int,
    {
        NumD { v: ibig_from_i64(x), d: Ghost(0int) }
    }

    /// Wrap an existing IBig with distance 0.
    #[inline]
    pub fn from_ibig(v: IBig) -> (r: NumD)
        ensures r.val() == ibig_view(&v), r.dist() == 0int,
    {
        NumD { v, d: Ghost(0int) }
    }

    /// T-OPLUS
    #[inline]
    pub fn add(&self, other: &NumD) -> (r: NumD)
        ensures
            r.val() == self.val() + other.val(),
            r.dist() == self.dist() + other.dist(),
    {
        NumD {
            v: ibig_add(&self.v, &other.v),
            d: Ghost(self.d@ + other.d@),
        }
    }

    #[inline]
    pub fn clone(&self) -> (r: NumD)
        ensures r.val() == self.val(), r.dist() == self.dist(),
    {
        NumD { v: ibig_clone(&self.v), d: self.d }
    }

    /// T-ODOT aligned ≥. Caller proves the boolean agrees across worlds;
    /// the returned bool is therefore identical in both worlds.
    #[inline]
    pub fn ge_aligned(&self, other: &NumD) -> (r: bool)
        requires
            (self.val() >= other.val()) == (self.shifted() >= other.shifted()),
        ensures
            r == (self.val() >= other.val()),
            r == (self.shifted() >= other.shifted()),
    {
        ibig_ge(&self.v, &other.v)
    }

    /// T-ODOT aligned <.
    #[inline]
    pub fn lt_aligned(&self, other: &NumD) -> (r: bool)
        requires
            (self.val() < other.val()) == (self.shifted() < other.shifted()),
        ensures
            r == (self.val() < other.val()),
            r == (self.shifted() < other.shifted()),
    {
        ibig_lt(&self.v, &other.v)
    }

    /// Laplace-shift axiom — T-LAPLACE.
    ///
    ///   {↯× ε}  η := Lap r  {η : num(d(v)),  ↯× (ε − |d(v)|/r)}
    ///
    /// Operationally this samples η from the verified discrete Laplace
    /// at scale `r = scale_num / scale_den`, then attributes a ghost
    /// "distance" equal to `d_chooser(v)` — the imagined world-2 value
    /// will be `v + d_chooser(v)`. The distance commitment is the
    /// Clutch-DP Laplace coupling: for any ghost `d` we can choose,
    /// we pay `|d|/r` credits and the shifted distribution is
    /// statistically indistinguishable from the original.
    ///
    /// Since the caller cannot know the drawn value `v` before the call, 
    /// so we can't charge `|d_chooser(v)|/r`, we need to introduce a `d_bound`
    /// that upper-bounds `d_chooser(v)` for any `v``. You can get back the credit
    /// 
    /// The refund is what lets SparseVector stay tight: η₂ has
    /// `d_bound = 2` (so every iteration reserves ε/(2N)), but on the
    /// False branch the chooser returns 0 and the residual charge is 0.
    /// Only the True branches actually spend, capped at N of them.
    ///
    /// For fixed-distance callers (SmartSum) `d_chooser` is the constant
    /// `|_| d`, so `d_bound = |d|` and there's no gap between reservation
    /// and actual charge.
    ///
    /// TRUSTED AXIOM
    #[verus::trusted]
    #[verifier::external_body]
    pub fn laplace(
        scale_num: u64,
        scale_den: u64,
        Ghost(d_chooser): Ghost<spec_fn(int) -> int>,
        Ghost(d_bound): Ghost<int>,
        Ghost(eps_in): Ghost<real>,
        Tracked(input_credit): Tracked<MultCreditResource>,
    ) -> ((value, out_credit): (NumD, Tracked<MultCreditResource>))
        requires
            scale_num > 0,
            scale_den > 0,
            d_bound >= 0,
            forall |v: int| abs_int(#[trigger] d_chooser(v)) <= d_bound,
            input_credit.view() =~= (MultCreditCarrier::Value { car: eps_in }),
            eps_in >= (d_bound as real) * (scale_den as real) / (scale_num as real),
        ensures
            value.dist() == d_chooser(value.val()),
            out_credit@.view() =~= (MultCreditCarrier::Value {
                car: eps_in
                    - (abs_int(d_chooser(value.val())) as real)
                        * (scale_den as real) / (scale_num as real),
            }),
    {
        let v = crate::cks::discrete_laplace::sample_discrete_laplace_entry(
            scale_num,
            scale_den,
        );
        let ghost d = d_chooser(ibig_view(&v));
        (NumD { v, d: Ghost(d) }, Tracked::assume_new())
    }

    // /// LightDP T-LAPLACE-LIST (joint coupling for `n` independent Laplaces).
    // ///
    // /// Samples `n` i.i.d. discrete-Laplace draws at scale `scale_den/scale_num`,
    // /// then assigns each draw a ghost distance via a JOINT chooser
    // /// `d_chooser : Seq<int> → Seq<int>` that depends on the full sample.
    // /// The Clutch-DP coupling for a list pays
    // ///
    // ///     max_i |d_chooser(v)[i]|  ·  scale_den / scale_num
    // ///
    // /// in credits — i.e. cost is governed by the *largest* per-index
    // /// distance, NOT their sum. This is the key amplification used by
    // /// Report Noisy Max (a single coupling event over the joint sample
    // /// allows a constant max-distance regardless of `n`).
    // ///
    // /// Caller supplies a uniform upper bound `d_bound` on |d_chooser(v)[i]|
    // /// for the pre-call reservation; any unused slack is refunded post-sample.
    // ///
    // /// TRUSTED AXIOM.
    // #[verus::trusted]
    // #[verifier::external_body]
    // pub fn laplace_list(
    //     n: u64,
    //     scale_num: u64,
    //     scale_den: u64,
    //     Ghost(d_chooser): Ghost<spec_fn(Seq<int>) -> Seq<int>>,
    //     Ghost(d_bound): Ghost<int>,
    //     Ghost(eps_in): Ghost<real>,
    //     Tracked(input_credit): Tracked<MultCreditResource>,
    // ) -> ((value, out_credit): (Vec<NumD>, Tracked<MultCreditResource>))
    //     requires
    //         scale_num > 0,
    //         scale_den > 0,
    //         d_bound >= 0,
    //         forall |xs: Seq<int>| xs.len() == n as int ==> {
    //             let ds = #[trigger] d_chooser(xs);
    //             ds.len() == n as int
    //             && (forall |i: int| 0 <= i < n as int ==>
    //                    abs_int(ds[i]) <= d_bound)
    //         },
    //         input_credit.view() =~= (MultCreditCarrier::Value { car: eps_in }),
    //         eps_in >= (d_bound as real) * (scale_den as real) / (scale_num as real),
    //     ensures
    //         value.len() == n as int,
    //         // The dist of the i-th NumD equals d_chooser(world-1 vals)[i].
    //         ({
    //             let vs = Seq::<int>::new(n as nat,
    //                 |i: int| if 0 <= i < n as int { value@[i].val() } else { 0int });
    //             let ds = d_chooser(vs);
    //             forall |i: int| 0 <= i < n as int ==>
    //                 (#[trigger] value@[i]).dist() == ds[i]
    //         }),
    //         // Credit residual: pre − cost, where cost ≤ d_bound·rate.
    //         // We don't try to expose the precise refund (only the worst-case
    //         // reservation deduction) — that's enough for RNM, which uses a
    //         // tight |d|=d_bound = 2 anyway.
    //         out_credit@.view() =~= (MultCreditCarrier::Value {
    //             car: eps_in - (d_bound as real)
    //                           * (scale_den as real) / (scale_num as real),
    //         }),
    // {
    //     // Untrusted body: sample n laplaces, build vector. Distances are
    //     // ghost-assigned by the spec.
    //     let mut out: Vec<NumD> = Vec::new();
    //     let mut i: u64 = 0;
    //     while i < n
    //         invariant out.len() == i as int, i <= n,
    //         decreases n - i,
    //     {
    //         let v = crate::cks::discrete_laplace::sample_discrete_laplace_entry(
    //             scale_num,
    //             scale_den,
    //         );
    //         out.push(NumD { v, d: Ghost(0int) });
    //         i = i + 1;
    //     }
    //     (out, Tracked::assume_new())
    // }

    // /// World-1 strict less-than comparison. Returns the ordering in world 1.
    // ///
    // /// SOUNDNESS NOTE. By itself this is privacy-leaking (it exposes
    // /// raw world-1 numeric values rather than a coupled-aligned bool).
    // /// Its safe use sits *inside* a privacy proof that has already
    // /// chosen distances aligning the comparison's outcome — e.g. the
    // /// argmax loop in Report Noisy Max, where the laplace_list distances
    // /// guarantee the same argmax in both worlds. This method is
    // /// trusted for that purpose.
    // #[verus::trusted]
    // pub fn lt_world1(&self, other: &NumD) -> (r: bool)
    //     ensures r == (self.val() < other.val()),
    // {
    //     ibig_lt(&self.v, &other.v)
    // }
}

} // verus!
