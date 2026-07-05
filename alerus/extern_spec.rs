//! External type specifications and assumed specifications for third-party libraries.
//!
//! All external_type_specification, assume_specification, and external_body
//! wrappers for types/functions from bignum crate

use vstd::prelude::*;

use random::{UBig, IBig, RBig};

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)]
pub struct ExUBig(UBig);

/// Ghost interpretation of a UBig as a nat.
pub uninterp spec fn ubig_view(n: &UBig) -> nat;

pub assume_specification[ random::ubig_zero ]() -> (ret: UBig)
    ensures ubig_view(&ret) == 0nat;

pub assume_specification[ random::ubig_succ ](n: &UBig) -> (ret: UBig)
    ensures ubig_view(&ret) == ubig_view(n) + 1;

pub assume_specification[ <UBig as Clone>::clone ](n: &UBig) -> (ret: UBig)
    ensures ubig_view(&ret) == ubig_view(n);

pub assume_specification[ random::ubig_pred ](n: &UBig) -> (ret: UBig)
    requires ubig_view(n) > 0,
    ensures ubig_view(&ret) == ubig_view(n) - 1;

pub assume_specification[ random::ubig_is_zero ](n: &UBig) -> (ret: bool)
    ensures ret == (ubig_view(n) == 0);

pub assume_specification[ random::ubig_add ](a: &UBig, b: &UBig) -> (ret: UBig)
    ensures ubig_view(&ret) == ubig_view(a) + ubig_view(b);

pub assume_specification[ random::ubig_mul ](a: &UBig, b: &UBig) -> (ret: UBig)
    ensures ubig_view(&ret) == ubig_view(a) * ubig_view(b);

pub assume_specification[ random::ubig_sub ](a: &UBig, b: &UBig) -> (ret: UBig)
    requires ubig_view(a) >= ubig_view(b),
    ensures ubig_view(&ret) == ubig_view(a) - ubig_view(b);

pub assume_specification[ random::ubig_mul_u64 ](a: &UBig, b: u64) -> (ret: UBig)
    ensures ubig_view(&ret) == ubig_view(a) * b as nat;

pub assume_specification[ random::ubig_from_u64 ](n: u64) -> (ret: UBig)
    ensures ubig_view(&ret) == n as nat;

pub assume_specification[ random::ubig_to_u64 ](n: &UBig) -> (ret: u64)
    requires ubig_view(n) <= u64::MAX,
    ensures ret as nat == ubig_view(n);

pub assume_specification[ random::ubig_is_odd ](n: &UBig) -> (ret: bool)
    ensures ret == (ubig_view(n) % 2 == 1);

pub assume_specification[ random::ubig_div ](a: &UBig, b: &UBig) -> (ret: UBig)
    requires ubig_view(b) > 0,
    ensures ubig_view(&ret) == ubig_view(a) / ubig_view(b);

#[verifier::external_body]
pub fn ubig_lt(a: &UBig, b: &UBig) -> (ret: bool)
    ensures ret == (ubig_view(a) < ubig_view(b)),
{
    a < b
}

// ============================================================================
// IBig (signed big integer)
// ============================================================================

#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)]
pub struct ExIBig(IBig);

/// Ghost interpretation of an IBig as an int.
pub uninterp spec fn ibig_view(n: &IBig) -> int;

pub assume_specification[ random::ibig_from_ubig ](n: &UBig) -> (ret: IBig)
    ensures ibig_view(&ret) == ubig_view(n) as int;

pub assume_specification[ random::ibig_neg ](n: &IBig) -> (ret: IBig)
    ensures ibig_view(&ret) == -ibig_view(n);

pub assume_specification[ random::ibig_is_zero ](n: &IBig) -> (ret: bool)
    ensures ret == (ibig_view(n) == 0int);

pub assume_specification[ random::ibig_from_i64 ](n: i64) -> (ret: IBig)
    ensures ibig_view(&ret) == n as int;

pub assume_specification[ random::ibig_add ](a: &IBig, b: &IBig) -> (ret: IBig)
    ensures ibig_view(&ret) == ibig_view(a) + ibig_view(b);

pub assume_specification[ random::ibig_sub ](a: &IBig, b: &IBig) -> (ret: IBig)
    ensures ibig_view(&ret) == ibig_view(a) - ibig_view(b);

pub assume_specification[ random::ibig_ge ](a: &IBig, b: &IBig) -> (ret: bool)
    ensures ret == (ibig_view(a) >= ibig_view(b));

pub assume_specification[ random::ibig_lt ](a: &IBig, b: &IBig) -> (ret: bool)
    ensures ret == (ibig_view(a) < ibig_view(b));

pub assume_specification[ random::ibig_clone ](n: &IBig) -> (ret: IBig)
    ensures ibig_view(&ret) == ibig_view(n);

pub assume_specification[ random::ibig_mul ](a: &IBig, b: &IBig) -> (ret: IBig)
    ensures ibig_view(&ret) == ibig_view(a) * ibig_view(b);

/// |n| as a UBig:  ubig_view(result) == |ibig_view(n)|.
pub assume_specification[ random::ibig_abs ](n: &IBig) -> (ret: UBig)
    ensures ubig_view(&ret) as int == (if ibig_view(n) >= 0 { ibig_view(n) } else { -ibig_view(n) });

#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)]
pub struct ExRBig(RBig);

pub uninterp spec fn rbig_view(r: &RBig) -> real;

/// Reduced parts:  rbig_view(r) = numer / denom,  denom > 0.
pub assume_specification[ random::rbig_into_parts ](r: &RBig) -> ((numer, denom): (IBig, UBig))
    ensures
        ubig_view(&denom) > 0,
        rbig_view(r) == ibig_view(&numer) as real / ubig_view(&denom) as real;

pub assume_specification[ random::rbig_from_parts ](numer: &IBig, denom: &UBig) -> (ret: RBig)
    requires ubig_view(denom) > 0,
    ensures rbig_view(&ret) == ibig_view(numer) as real / ubig_view(denom) as real;

/// ⌊r⌋:  ibig_view(ret) == ⌊rbig_view(r)⌋,  and the defining bracketing.
pub assume_specification[ random::rbig_floor ](r: &RBig) -> (ret: IBig)
    ensures
        ibig_view(&ret) == rbig_view(r).floor(),
        ibig_view(&ret) as real <= rbig_view(r),
        rbig_view(r) < (ibig_view(&ret) + 1) as real;

} // verus!
