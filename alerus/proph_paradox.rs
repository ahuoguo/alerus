//! example showing that combining Eris-style error credits with 
//! prophecy variables is unsound.
//!
//! The informal example:
//!
//!     let p = new proph
//!     let x = rand 1 in
//!     resolve p to x;;
//!     () ()
//!

// This file intentionally uses the banned `vstd::proph::Prophecy` to exhibit
// the unsoundness
#![allow(clippy::disallowed_types)]

#[cfg(verus_keep_ghost)]
use vstd::resource::pcm::*;
#[cfg(verus_keep_ghost)]
use vstd::resource::algebra::ResourceAlgebra;
use vstd::prelude::*;
use vstd::proph::Prophecy;

use crate::ec::*;
use crate::rand_primitives::rand_2_u64;

verus! {

/// Credit allocation that depends on the prophesied value `pv`.
///
/// For `x in {0, 1}`:
///   credit_alloc_proph(pv, x) = 1  if x == pv
///                             = 0  otherwise
///
/// The point is that the average over `x in {0, 1}` is `1/2` whenever
/// `pv in {0, 1}`, but after resolving the prophecy to the sampled `val`,
/// the per-outcome credit on the "taken" branch collapses to exactly 1.
pub open spec fn credit_alloc_proph(pv: u64, x: real) -> real {
    if x == pv as real { 1real } else { 0real }
}

pub proof fn credit_alloc_proph_sum(pv: u64)
    requires
        pv == 0 || pv == 1,
    ensures
        credit_alloc_proph(pv, 0real) + credit_alloc_proph(pv, 1real) == 1real,
{
}

/// The havoc / crash primitive -- analogue of `() ()`.
#[verifier::external_body]
pub fn havoc()
    requires
        false,
{
    panic!("havoc")
}

/// The paradoxical program. Verus verifies it under 1/2 error credit,
/// even though it always terminates in `havoc()`.
pub fn safe_with_half_credit(Tracked(input_credit): Tracked<ErrorCreditResource>)
    requires
        input_credit@ =~= (ErrorCreditCarrier::Value { car: 1real / 2real }),
    ensures
        true
{
    // allocate a fresh prophecy variable over `u64`. Its `view()`
    // is the prophesied value `p@`, which becomes whatever we resolve to
    // later (in this case, the result of `rand 1`).
    let p: Prophecy<u64> = Prophecy::<u64>::new();

    let credit_alloc: Ghost<spec_fn(real) -> real> =
        Ghost(|x: real| credit_alloc_proph(p@, x));

    proof {
        assert(forall |i: nat| #[trigger] (credit_alloc@)(i as real) >= 0real);
        if p@ == 0 || p@ == 1 {
            credit_alloc_proph_sum(p@);
        }
    }

    let (val, Tracked(outcome_credit)) =
        rand_2_u64(Tracked(input_credit), credit_alloc);

    // resolve the prophecy to the sampled value. Now `p@ == val`.
    p.resolve(&val);

    // After the resolve, `credit_alloc(val) = credit_alloc_proph(p@, val) = 1`
    // because `p@ == val`.
    proof {
        assert(p@ == val);
        assert(val as real == p@ as real);
        assert((credit_alloc@)(val as real) == 1real);
        assert(outcome_credit@ =~= (ErrorCreditCarrier::Value { car: 1real }));
        ec_contradict(&outcome_credit);
    }

    havoc();
}

} // verus!
