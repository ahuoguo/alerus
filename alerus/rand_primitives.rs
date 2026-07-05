//! # Axiomtized Primitives for Randomness
//!
//! Trusted interface to the randomness source, exposing the Eris sampling rules
//! over [error credits](crate::ec).
//!
//! - [`rand_ubig`]
//! - [`thin_air`] 

#[cfg(verus_keep_ghost)]
use vstd::calc_macro::*;
#[cfg(verus_keep_ghost)]
use vstd::resource::pcm::*;
#[cfg(verus_keep_ghost)]
use vstd::resource::algebra::ResourceAlgebra;
use vstd::prelude::*;

use random::UBig;

verus! {

use crate::ec::*;
#[cfg(verus_keep_ghost)]
use crate::math::pow::pow;
#[cfg(verus_keep_ghost)]
use crate::extern_spec::ExUBig;
#[cfg(verus_keep_ghost)]
use crate::extern_spec::ubig_view;

/// Recursive sum of credit_alloc over [0, n)
/// credit_alloc(i) is the error credit allocated to outcome i
/// Defining this using `fold_left` was not that pleasant to work with
pub open spec fn sum_credit(credit_alloc: spec_fn(real) -> real, n: nat) -> real
    decreases n,
{
    if n == 0 { 0real }
    else { sum_credit(credit_alloc, (n - 1) as nat) + credit_alloc((n - 1) as real) }
}

/// Average of credit_alloc over [0, bound)
/// This is the expected error credit when sampling uniformly from [0, bound)
pub open spec fn average(bound: u64, credit_alloc: spec_fn(real) -> real) -> real {
    sum_credit(credit_alloc, bound as nat) / bound as real
}

/// Average over [0, bound) with nat bound.
pub open spec fn average_nat(bound: nat, credit_alloc: spec_fn(real) -> real) -> real {
    sum_credit(credit_alloc, bound) / bound as real
}

//// Wrappers
pub fn rand_u64(
    bound: u64,
    Tracked(e1): Tracked<ErrorCreditResource>,
    Ghost(e2): Ghost<spec_fn(real) -> real>,
) -> ((n, out_credit): (u64, Tracked<ErrorCreditResource>))
    requires
      // ε₁ ≥ 𝔼(ℰ₂)
      bound > 0,
      forall |i: nat| (#[trigger] e2(i as real)) >= 0real,
      exists |eps: real| (ErrorCreditCarrier::Value { car: eps } =~= e1.view()) && eps >= average(bound, e2),
    ensures
      // Result is in range [0, bound)
      n < bound,
      // owns ↯(ℰ₂(n))
      (ErrorCreditCarrier::Value { car: e2(n as real) }) =~= out_credit.view().view(),
{
    let bound_ubig = random::ubig_from_u64(bound);
    let (n_ubig, out_credit) = rand_ubig(&bound_ubig, Tracked(e1), Ghost(e2));
    let n = random::ubig_to_u64(&n_ubig);
    (n, out_credit)
}

/// Uniform sampler with UBig bound: sample u ~ Uniform([0, bound)).
/// See opendp: `sample_uniform_ubig_below` in opendp/rust/src/traits/samplers/uniform/mod.rs.
#[verus::trusted]
#[verifier::external_body]
#[inline(always)]
pub fn rand_ubig(
    bound: &UBig,
    Tracked(e1): Tracked<ErrorCreditResource>,
    Ghost(e2): Ghost<spec_fn(real) -> real>,
) -> ((n, out_credit): (UBig, Tracked<ErrorCreditResource>))
    requires
        ubig_view(bound) > 0,
        forall |i: nat| (#[trigger] e2(i as real)) >= 0real,
        exists |eps: real| (ErrorCreditCarrier::Value { car: eps } =~= e1.view())
            && eps >= average_nat(ubig_view(bound), e2),
    ensures
        ubig_view(&n) < ubig_view(bound),
        (ErrorCreditCarrier::Value { car: e2(ubig_view(&n) as real) }) =~= out_credit.view().view(),
{
    let val = random::rand_ubig(bound.clone());
    (val, Tracked::assume_new())
}

// REVIEW:
// In Eris, you can only invoke a thin air rule if your postcondition is a WP or is wrapped in some modality
// you can't not invoke thin air rule in any lemma (this might(?) be unsound)
// TODO: can you write it as a `proof fn` returning some value?
#[inline(always)]
#[verus::trusted]
#[verifier::external_body]
pub fn thin_air() -> (ret: Tracked<ErrorCreditResource>)
    ensures
        // owns ↯(ε) for ε > 0
        exists |eps: real| eps > 0.0 && (ErrorCreditCarrier::Value { car: eps } =~= ret.view().view()),
{
    Tracked::assume_new()
}


pub open spec fn flip_credit_alloc(x: real) -> real {
    if x == 1real {
        0real
    } else {
        1real
    }
}

/// A wrapper around `rand_u64(2)` for coin flip scenarios.
/// Simplifies the average calculation to (credit_alloc(0) + credit_alloc(1)) / 2.
#[inline(always)]
pub fn rand_2_u64(
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(credit_alloc): Ghost<spec_fn(real) -> real>,
) -> ((n, out_credit): (u64, Tracked<ErrorCreditResource>))
    requires
        forall |i: nat| (#[trigger] credit_alloc(i as real)) >= 0real,
        exists |eps: real| (ErrorCreditCarrier::Value { car: eps } =~= input_credit.view()) &&
            eps >= (credit_alloc(0real) + credit_alloc(1real)) / 2real,
    ensures
        n == 0 || n == 1,
        (ErrorCreditCarrier::Value { car: credit_alloc(n as real) }) =~= out_credit.view().view(),
{
    // Prove that average(2, credit_alloc) == (credit_alloc(0) + credit_alloc(1)) / 2
    // by unfolding sum_credit using asserts
    assert(average(2u64, credit_alloc) == (credit_alloc(0real) + credit_alloc(1real)) / 2real) by {
        // assert(sum_credit(credit_alloc, 2) == sum_credit(credit_alloc, 1) + credit_alloc(1real));
        assert(sum_credit(credit_alloc, 1) == sum_credit(credit_alloc, 0) + credit_alloc(0real)); // OBSERVE
        // assert(sum_credit(credit_alloc, 0) == 0real);
    };
    let (val, output_credit) = rand_u64(2u64, Tracked(input_credit), Ghost(credit_alloc));
    (val, output_credit)
}

// {1/2} 
//   flip()
// {v. v == true }
pub fn flip(Tracked(input_credit): Tracked<ErrorCreditResource>) -> (ret: u64)
    requires
        (ErrorCreditCarrier::Value { car: 0.5real }) == input_credit.view(),
    ensures
        ret == 1,
{
    assert(flip_credit_alloc(0real) + flip_credit_alloc(1real) == 1real);
    let (val, Tracked(outcome_credit)) = rand_2_u64(Tracked(input_credit), Ghost(|x: real| flip_credit_alloc(x)));

    proof {
        if (val != 1) {
            ec_contradict(&outcome_credit);
        }
    }
    assert(val == 1);
    val
}

// Example: fliping two coins, the probability they are both heads is 1/4
// {1/4} 
//   let b1 = flip() in
//   let b2 = flip() in
//   b1 && b2
// {v. v == false }
pub fn flip_and(Tracked(credit): Tracked<ErrorCreditResource>) -> (ret: bool)
    requires
        credit.view() =~= (ErrorCreditCarrier::Value { car: 1real / 4real }),
    ensures
        ret == false,
{
    let (b1, Tracked(c1)) = rand_2_u64(
        Tracked(credit),
        Ghost(|x: real| if x == 1real { 1real / 2real } else { 0real }),
    );

    let (b2, Tracked(c2)) = rand_2_u64(
        Tracked(c1),
        Ghost(|x: real| if b1 == 1 && x == 1real { 1real } else { 0real }),
    );

    proof {
        if b1 == 1 && b2 == 1 {
            ec_contradict(&c2);
        }
    }

    (b1 == 1) && (b2 == 1)
}

} // verus!
