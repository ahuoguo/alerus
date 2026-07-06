//! # Error credits
//!
//! The core Eris resource a
//! separation-logic resource [`ErrorCreditResource`] tracking an upper bound
//! `↯(ε)` on a program's probability of error. It is backed by the
//! [`ErrorCreditCarrier`] PCM at a single global ghost location, and exposes the
//! credit algebra used throughout the proofs:
//!
//! - [`ec_combine`] — `↯(ε₁) ∗ ↯(ε₂) ⊢ ↯(ε₁ + ε₂)`
//! - [`ec_split`] — `↯(ε₁ + ε₂) ⊢ ↯(ε₁) ∗ ↯(ε₂)`
//! - [`ec_contradict`] — owning `↯(ε)` with `ε ≥ 1` derives `False`
//! - [`ec_zero`] — obtain `↯(0)` for free

use vstd::resource::pcm::*;
#[cfg(verus_keep_ghost)]
use vstd::resource::algebra::ResourceAlgebra;
#[cfg(verus_keep_ghost)]
use vstd::resource::Loc;
#[cfg(verus_keep_ghost)]
use vstd::resource::relations::frame_preserving_update;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use crate::ec::ErrorCreditCarrier::Value;


verus! {

// Ghost name for the single global error-credit resource location.
#[allow(non_snake_case)]
pub uninterp spec fn EC_GLOBAL_LOC() -> Loc;

/// wrapper around ec, namely `↯`
/// A error credit represents a resource with a non zero value
/// https://logsem.github.io/clutch/clutch.base_logic.error_credits.html
/// the reason we have `Empty` separately is becuase we Value{0} can't be a unit since
/// ↯(-1) · ↯(0) = Invalid
/// this is because we don't have a subset type for non-negative reals, 
/// so we have to bake the non-negativity into the algebra itself. 
pub enum ErrorCreditCarrier {
    Value { car: real },
    Empty,
    Invalid,
}

impl ErrorCreditCarrier {
    pub closed spec fn zero() -> Self {
        Value { car: 0real }
    }

    pub open spec fn value(self) -> Option<real> {
        match self {
            Value { car } => Some(car),
            _ => None,
        }
    }
}

impl vstd::resource::algebra::ResourceAlgebra for ErrorCreditCarrier {
    closed spec fn valid(self) -> bool {
        match self {
            Value { car } => 0real <= car < 1real,
            ErrorCreditCarrier::Empty => true,
            ErrorCreditCarrier::Invalid => false,
        }
    }

    closed spec fn op(a: Self, b: Self) -> Self {
        match (a, b) {
            (Value { car: c1 }, Value { car: c2 }) => {
                // REVIEW: we have to bake in the `nonnegreal` part in the op
                // I guess verus doesn't have a good way to express subset types like Dafny...
                if c1 < 0real || c2 < 0real {
                    ErrorCreditCarrier::Invalid
                } else {
                    Value { car: c1 + c2 }
                }

            },
            (ErrorCreditCarrier::Empty, ec) | (ec, ErrorCreditCarrier::Empty) => ec,
            _ => ErrorCreditCarrier::Invalid,
        }
    }

    proof fn valid_op(a: Self, b: Self) {
    }

    proof fn commutative(a: Self, b: Self) {
    }

    proof fn associative(a: Self, b: Self, c: Self) {
    }
}

impl PCM for ErrorCreditCarrier {
    closed spec fn unit() -> Self {
        ErrorCreditCarrier::Empty
    }

    proof fn op_unit(self) {
    }

    proof fn unit_valid() {
    }
}

#[allow(dead_code)]
pub struct ErrorCreditResource {
    r: Resource<ErrorCreditCarrier>,
}

impl ErrorCreditResource {
    // All error credits live at the single global location.
    #[verifier::type_invariant]
    closed spec fn wf(self) -> bool {
        self.r.loc() == EC_GLOBAL_LOC()
    }

    pub closed spec fn view(self) -> ErrorCreditCarrier {
        self.r.value()
    }

    pub proof fn explode(tracked &self, c: real)
        requires
            self@ =~= (Value { car: c }),
            c >= 1real,
        ensures
            !self@.valid(),
    {
    }

    pub proof fn valid(tracked &self)
        ensures
            self@.valid(),
    {
        self.r.validate();
    }
}

pub proof fn ec_contradict(tracked e: &ErrorCreditResource)
    requires
        exists |car: real| {
            &&& car >= 1real
            &&& e@ =~= (Value { car })
        }
    ensures
        false,
{
    let car = choose|v: real| e@ == (Value { car: v });
    e.explode(car);
    e.valid();
    assert(!e@.valid());
}

/// Combine two error credits into one with summed value.
pub proof fn ec_combine(
    tracked c1: ErrorCreditResource,
    tracked c2: ErrorCreditResource,
    v1: real,
    v2: real,
) -> (tracked out: ErrorCreditResource)
    requires
        c1@ =~= (Value { car: v1 }),
        c2@ =~= (Value { car: v2 }),
        v1 >= 0real,
        v2 >= 0real,
    ensures
        out@ =~= (Value { car: v1 + v2 }),
{
    use_type_invariant(&c1);
    use_type_invariant(&c2);
    let tracked joined = c1.r.join(c2.r);
    ErrorCreditResource { r: joined }
}

/// Split one error credit into two with specified values.
pub proof fn ec_split(
    tracked c: ErrorCreditResource,
    v1: real,
    v2: real,
) -> (tracked (c1, c2): (ErrorCreditResource, ErrorCreditResource))
    requires
        c@ =~= (Value { car: v1 + v2 }),
        v1 >= 0real,
        v2 >= 0real,
    ensures
        c1@ =~= (Value { car: v1 }),
        c2@ =~= (Value { car: v2 }),
{
    use_type_invariant(&c);
    let tracked (r1, r2) = c.r.split(
        Value { car: v1 },
        Value { car: v2 },
    );
    (ErrorCreditResource { r: r1 }, ErrorCreditResource { r: r2 })
}

/// ⊢ ↯(0)
/// The PCM unit `Empty` via `create_unit`, then frame-preserving update to `Value{0}`
/// by "uniqueness" of unit
pub proof fn ec_zero() -> (tracked out: ErrorCreditResource)
    ensures
        out@ =~= (Value { car: 0real }),
{
    let tracked u = Resource::<ErrorCreditCarrier>::create_unit(EC_GLOBAL_LOC());
    assert(frame_preserving_update(
        ErrorCreditCarrier::Empty,
        Value { car: 0real },
    )) by {
        assert forall |c: ErrorCreditCarrier|
            #![trigger ErrorCreditCarrier::op(ErrorCreditCarrier::Empty, c)]
            ErrorCreditCarrier::op(ErrorCreditCarrier::Empty, c).valid()
            implies ErrorCreditCarrier::op(Value { car: 0real }, c).valid() by {
            match c {
                Value { car } => {},
                ErrorCreditCarrier::Empty => {},
                ErrorCreditCarrier::Invalid => {},
            }
        }
    };
    let tracked r = u.update(Value { car: 0real });
    ErrorCreditResource { r }
}

} // verus!
