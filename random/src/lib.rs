// interface for external functions
// mostly randomized sampling functions, and wrappers for bignum types

#[inline(always)]
pub fn rand_u64(bound: u64) -> u64 {
  // TODO: unwarp is probably very bad
  opendp::traits::samplers::sample_uniform_uint_below(bound).unwrap()
}

#[inline(always)]
pub fn rand_ubig(bound: UBig) -> UBig {
    // TODO: unwarp is probably very bad
    opendp::traits::samplers::sample_uniform_ubig_below(bound).unwrap()
}

pub use dashu::integer::UBig;
pub use dashu::integer::IBig;

#[inline(always)]
pub fn ubig_zero() -> UBig {
    UBig::ZERO
}

#[inline(always)]
pub fn ubig_succ(n: &UBig) -> UBig {
    n.clone() + UBig::ONE
}

#[inline(always)]
pub fn ubig_add(a: &UBig, b: &UBig) -> UBig {
    a.clone() + b.clone()
}

#[inline(always)]
pub fn ubig_mul(a: &UBig, b: &UBig) -> UBig {
    a.clone() * b.clone()
}

#[inline(always)]
pub fn ubig_sub(a: &UBig, b: &UBig) -> UBig {
    a.clone() - b.clone()
}

#[inline(always)]
pub fn ubig_from_u64(n: u64) -> UBig {
    UBig::from(n)
}

#[inline(always)]
pub fn ubig_to_u64(n: &UBig) -> u64 {
    u64::try_from(n.clone()).unwrap()
}

#[inline(always)]
pub fn ubig_mul_u64(a: &UBig, b: u64) -> UBig {
    a * UBig::from(b)
}

#[inline(always)]
pub fn ubig_pred(n: &UBig) -> UBig {
    n.clone() - UBig::ONE
}

#[inline(always)]
pub fn ubig_is_zero(n: &UBig) -> bool {
    *n == UBig::ZERO
}

#[inline(always)]
pub fn ubig_is_odd(n: &UBig) -> bool {
    n % 2u8 == 1u8
}

#[inline(always)]
pub fn ubig_div(a: &UBig, b: &UBig) -> UBig {
    a.clone() / b.clone()
}

#[inline(always)]
pub fn ubig_lt(a: &UBig, b: &UBig) -> bool {
    a < b
}

#[inline(always)]
pub fn ibig_from_ubig(n: &UBig) -> IBig {
    IBig::from(n.clone())
}

#[inline(always)]
pub fn ibig_neg(n: &IBig) -> IBig {
    -n.clone()
}

#[inline(always)]
pub fn ibig_is_zero(n: &IBig) -> bool {
    *n == IBig::ZERO
}

#[inline(always)]
pub fn ibig_from_i64(n: i64) -> IBig {
    IBig::from(n)
}

#[inline(always)]
pub fn ibig_add(a: &IBig, b: &IBig) -> IBig {
    a.clone() + b.clone()
}

#[inline(always)]
pub fn ibig_sub(a: &IBig, b: &IBig) -> IBig {
    a.clone() - b.clone()
}

#[inline(always)]
pub fn ibig_ge(a: &IBig, b: &IBig) -> bool {
    a >= b
}

#[inline(always)]
pub fn ibig_lt(a: &IBig, b: &IBig) -> bool {
    a < b
}

#[inline(always)]
pub fn ibig_clone(n: &IBig) -> IBig {
    n.clone()
}

#[inline(always)]
pub fn ibig_mul(a: &IBig, b: &IBig) -> IBig {
    a.clone() * b.clone()
}

/// Absolute value of an IBig as a UBig.
#[inline(always)]
pub fn ibig_abs(n: &IBig) -> UBig {
    use dashu::base::Abs;
    n.clone().abs().into_parts().1
}

pub use dashu::rational::RBig;

/// Reduced numerator (signed) and denominator (positive) of r.
#[inline(always)]
pub fn rbig_into_parts(r: &RBig) -> (IBig, UBig) {
    r.clone().into_parts()
}

/// Construct numer/denom as an RBig (denom must be nonzero).
#[inline(always)]
pub fn rbig_from_parts(numer: &IBig, denom: &UBig) -> RBig {
    RBig::from_parts(numer.clone(), denom.clone())
}

/// ⌊r⌋ as an IBig.
#[inline(always)]
pub fn rbig_floor(r: &RBig) -> IBig {
    r.clone().floor()
}
