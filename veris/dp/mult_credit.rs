use vstd::resource::pcm::*;
#[cfg(verus_keep_ghost)]
use vstd::resource::algebra::ResourceAlgebra;
#[cfg(verus_keep_ghost)]
use vstd::resource::Loc;
use vstd::prelude::*;

verus! {

#[allow(non_snake_case)]
pub uninterp spec fn MULT_EC_GLOBAL_LOC() -> Loc;

pub enum MultCreditCarrier {
    Value { car: real },
    Empty,
    Invalid,
}

impl MultCreditCarrier {
    pub closed spec fn zero() -> Self {
        MultCreditCarrier::Value { car: 0real }
    }

    pub open spec fn value(self) -> Option<real> {
        match self {
            MultCreditCarrier::Value { car } => Some(car),
            _ => None,
        }
    }
}

impl vstd::resource::algebra::ResourceAlgebra for MultCreditCarrier {
    closed spec fn valid(self) -> bool {
        match self {
            MultCreditCarrier::Value { car } => 0real <= car,
            MultCreditCarrier::Empty => true,
            MultCreditCarrier::Invalid => false,
        }
    }

    closed spec fn op(a: Self, b: Self) -> Self {
        match (a, b) {
            (MultCreditCarrier::Value { car: c1 }, MultCreditCarrier::Value { car: c2 }) => {
                if c1 < 0real || c2 < 0real {
                    MultCreditCarrier::Invalid
                } else {
                    MultCreditCarrier::Value { car: c1 + c2 }
                }
            },
            (MultCreditCarrier::Empty, x) | (x, MultCreditCarrier::Empty) => x,
            _ => MultCreditCarrier::Invalid,
        }
    }

    proof fn valid_op(a: Self, b: Self) {
    }

    proof fn commutative(a: Self, b: Self) {
    }

    proof fn associative(a: Self, b: Self, c: Self) {
    }
}

impl PCM for MultCreditCarrier {
    closed spec fn unit() -> Self {
        MultCreditCarrier::Empty
    }

    proof fn op_unit(self) {
    }

    proof fn unit_valid() {
    }
}

#[allow(dead_code)]
pub struct MultCreditResource {
    r: Resource<MultCreditCarrier>,
}

impl MultCreditResource {
    #[verifier::type_invariant]
    closed spec fn wf(self) -> bool {
        self.r.loc() == MULT_EC_GLOBAL_LOC()
    }

    pub closed spec fn view(self) -> MultCreditCarrier {
        self.r.value()
    }

    pub proof fn valid(tracked &self)
        ensures
            self.view().valid(),
    {
        self.r.validate();
    }
}

/// Combine two multiplicative credits additively
pub proof fn mc_combine(
    tracked c1: MultCreditResource,
    tracked c2: MultCreditResource,
    v1: real,
    v2: real,
) -> (tracked out: MultCreditResource)
    requires
        c1.view() =~= (MultCreditCarrier::Value { car: v1 }),
        c2.view() =~= (MultCreditCarrier::Value { car: v2 }),
        v1 >= 0real,
        v2 >= 0real,
    ensures
        out.view() =~= (MultCreditCarrier::Value { car: v1 + v2 }),
{
    use_type_invariant(&c1);
    use_type_invariant(&c2);
    let tracked joined = c1.r.join(c2.r);
    MultCreditResource { r: joined }
}

/// Split one credit into two.
pub proof fn mc_split(
    tracked c: MultCreditResource,
    v1: real,
    v2: real,
) -> (tracked out: (MultCreditResource, MultCreditResource))
    requires
        c.view() =~= (MultCreditCarrier::Value { car: v1 + v2 }),
        v1 >= 0real,
        v2 >= 0real,
    ensures
        out.0.view() =~= (MultCreditCarrier::Value { car: v1 }),
        out.1.view() =~= (MultCreditCarrier::Value { car: v2 }),
{
    use_type_invariant(&c);
    let tracked (r1, r2) = c.r.split(
        MultCreditCarrier::Value { car: v1 },
        MultCreditCarrier::Value { car: v2 },
    );
    (MultCreditResource { r: r1 }, MultCreditResource { r: r2 })
}

} // verus!
