//! Attempt to replicate the prophecy/error-credit paradox using Verus's
//! prophecy-based encoding of mutable borrows. Concretely, `*final(x)` for
//! `x: &mut T` is a prophesied value — the analogue of `Prophecy::view`.
//!
//! Crucially, `*final(_)` (like `ProphecyGhost::value`) is marked
//! `verifier::prophetic`, so Verus tracks its dependencies and refuses to
//! let it flow into tracked/ghost positions that could break soundness. We
//! therefore expect this attempt to fail to verify, and that is the point:
//! the very tracking that the new mutable-references encoding inherits is
//! what rules out the Eris-style paradox — whereas plain `vstd::proph::Prophecy`
//! (whose `view` is not marked prophetic) does not enforce it, which is why
//! `proph_paradox.rs` goes through.
//!
//! We include the attempt here for completeness; it is gated behind a
//! `cfg(any())` so the rest of the crate keeps verifying. To see Verus
//! actually emit the rejection, remove the `#[cfg(any())]` line below
//! (or run `bash demo_mutref_rejection.sh` from this directory).

#![allow(unused)]

use vstd::resource::pcm::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::prelude::*;

use crate::ec::*;
use crate::rand_primitives::rand_2_u64;
#[cfg(verus_keep_ghost)]
use crate::proph_paradox::{credit_alloc_proph, credit_alloc_proph_sum};
use crate::proph_paradox::havoc;

verus! {

/// Attempted analogue of `proph_paradox::safe_with_half_credit`, using
/// `*final(x)` (the prophesied final value of a mutable reference) in place
/// of `Prophecy::view`. We mirror the same six steps; the credit allocation
/// is now `|y| credit_alloc_proph(*final(x), y)`.
///
/// Verus rejects this with a prophecy-dependence error (confirmed against
/// the in-tree build):
///
///     error: prophetic value not allowed for 'Ghost' wrapper
///       --> proph_paradox_mutref.rs:58:15
///        |
///     58 |         Ghost(|y: real| credit_alloc_proph(*final(x), y));
///        |               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^---------^^^^
///        |               |                            |
///        |               |                            the `final` builtin is prophetic
///        |               operand of this wrapper is expected to be non-prophetic
///
/// which is exactly the tracking that makes `&mut`-style prophecy sound
/// against this Eris-style attack.
#[cfg(any())]
pub fn safe_with_half_credit_mutref(
    x: &mut u64,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
)
    requires
        input_credit.view() =~= (ErrorCreditCarrier::Value { car: 1real / 2real }),
    ensures
        true
{
    // The "prophecy" here is `*final(x)`: the value `*x` will take when
    // this function returns. We attempt to use it in a tracked credit
    // allocation — Verus's dependence tracker should refuse.
    let credit_alloc: Ghost<spec_fn(real) -> real> =
        Ghost(|y: real| credit_alloc_proph(*final(x), y));

    proof {
        assert(forall |i: nat| #[trigger] (credit_alloc@)(i as real) >= 0real);
        if *final(x) == 0 || *final(x) == 1 {
            credit_alloc_proph_sum(*final(x));
        }
    }

    let (val, Tracked(outcome_credit)) =
        rand_2_u64(Tracked(input_credit), credit_alloc);

    // "Resolve" the prophecy by writing val into the mutable location.
    *x = val;

    proof {
        assert(*final(x) == val);
        assert(val as real == *final(x) as real);
        assert((credit_alloc@)(val as real) == 1real);
        assert(outcome_credit.view() =~= (ErrorCreditCarrier::Value { car: 1real }));
        ec_contradict(&outcome_credit);
    }

    havoc();
}

} // verus!
