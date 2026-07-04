//! Geometric Distribution Sampler — samples from a geometric distribution by repeatedly
//! flipping a fair coin. Each flip either terminates (outcome 0) or recurses with doubled
//! error credit (outcome 1).
//!
//! TODO: might remove this file, since it only reasons about termination — but maybe it's
//! also a nice intro to using error credits for almost-sure termination (AST)?
//!
//! The amplification factor is 2 (coin flip), and the error credit invariant is:
//!   eps * 2^depth >= 1

use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::calc_macro::*;

verus! {

use crate::ec::*;
use crate::rand_primitives::{rand_2_u64, thin_air};
#[cfg(verus_keep_ghost)]
use crate::math::pow::{pow, archimedean_exp_growth};
#[cfg(verus_keep_ghost)]
use crate::math::real::real_assoc_mult;

spec fn geo_credit_alloc(outcome: real, eps: real) -> real {
    if outcome == 0real { 0real } else { 2real * eps }
}

/// Geometric distribution sampler (unbounded).
/// Creates thin-air error credit and delegates to the bounded version.
pub fn geometric() -> (ret: u64)
{
    let Tracked(input_credit) = thin_air();

    let ghost depth: nat;
    let ghost eps: real;

    proof {
        if input_credit.view().value() =~= None { } // OBSERVE
    }
    assert(exists |v: real| input_credit.view().value() == Some(v));

    proof {
        eps = choose |v: real| input_credit.view().value() == Some(v);
        archimedean_exp_growth(eps, 2real);
        depth = choose |k: nat| eps * pow(2real, k) >= 1real;
    }

    bounded_geometric(Tracked(input_credit), Ghost(depth))
}

pub fn bounded_geometric(
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(depth): Ghost<nat>,
) -> (ret: u64)
    requires
        exists |eps: real| {
            &&& eps > 0real
            &&& input_credit.view() =~= (ErrorCreditCarrier::Value { car: eps })
            &&& eps * pow(2real, depth) >= 1real
        },
    ensures
        ret >= 0,
    decreases depth,
{
    let ghost eps: real;

    proof {
        eps = choose |v: real| {
            &&& v > 0real
            &&& input_credit.view() =~= (ErrorCreditCarrier::Value { car: v })
            &&& v * pow(2real, depth) >= 1real
        };

        // Base case: depth == 0 implies eps >= 1, contradiction
        if depth == 0nat {
            assert(pow(2real, 0nat) == 1real);
            assert(eps >= 1real);
            ec_contradict(&input_credit);
        }
    }

    let (val, Tracked(outcome_credit)) = rand_2_u64(
        Tracked(input_credit),
        Ghost(|x: real| geo_credit_alloc(x, eps)),
    );

    if val == 0 {
        0
    } else {
        let ghost new_eps = 2real * eps;
        assert(geo_credit_alloc(val as real, eps) == new_eps);

        proof {
            // Show: new_eps * 2^(depth-1) >= 1
            // (2 * eps) * 2^(depth-1) = eps * (2 * 2^(depth-1)) = eps * 2^depth >= 1
            calc! {
                (==)
                new_eps * pow(2real, (depth - 1) as nat); {}
                (eps * 2real) * pow(2real, (depth - 1) as nat); {
                    real_assoc_mult(eps, 2real, pow(2real, (depth - 1) as nat));
                }
                eps * (2real * pow(2real, (depth - 1) as nat)); {}
                eps * pow(2real, depth);
            }
            assert(new_eps * pow(2real, (depth - 1) as nat) >= 1real);
        }

        let rest = bounded_geometric(Tracked(outcome_credit), Ghost((depth - 1) as nat));
        rest.wrapping_add(1u64)
    }
}

} // verus!
