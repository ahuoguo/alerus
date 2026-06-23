pub fn rand_u64(bound: u64) -> u64 {
  // TODO: unwarp is probably very bad
  opendp::traits::samplers::sample_uniform_uint_below(bound).unwrap()
}

pub fn rand_ubig(bound: UBig) -> UBig {
    // TODO: unwarp is probably very bad
    opendp::traits::samplers::sample_uniform_ubig_below(bound).unwrap()
}

pub use dashu::integer::UBig;
pub use dashu::integer::IBig;

pub fn ubig_zero() -> UBig {
    UBig::ZERO
}

pub fn ubig_succ(n: UBig) -> UBig {
    n + UBig::ONE
}

pub fn ubig_add(a: UBig, b: UBig) -> UBig {
    a + b
}

pub fn ubig_mul(a: UBig, b: UBig) -> UBig {
    a * b
}

pub fn ubig_sub(a: &UBig, b: &UBig) -> UBig {
    a.clone() - b.clone()
}

pub fn ubig_from_u64(n: u64) -> UBig {
    UBig::from(n)
}

pub fn ubig_mul_u64(a: &UBig, b: u64) -> UBig {
    a * UBig::from(b)
}

pub fn ubig_pred(n: UBig) -> UBig {
    n - UBig::ONE
}

pub fn ubig_is_zero(n: &UBig) -> bool {
    *n == UBig::ZERO
}

pub fn ubig_is_odd(n: &UBig) -> bool {
    n % 2u8 == 1u8
}

pub fn ubig_div(a: UBig, b: UBig) -> UBig {
    a / b
}

pub fn ubig_lt(a: &UBig, b: &UBig) -> bool {
    a < b
}

pub fn ibig_from_ubig(n: UBig) -> IBig {
    IBig::from(n)
}

pub fn ibig_neg(n: IBig) -> IBig {
    -n
}

pub fn ibig_is_zero(n: &IBig) -> bool {
    *n == IBig::ZERO
}

pub fn ibig_from_i64(n: i64) -> IBig {
    IBig::from(n)
}

pub fn ibig_add(a: &IBig, b: &IBig) -> IBig {
    a.clone() + b.clone()
}

pub fn ibig_sub(a: &IBig, b: &IBig) -> IBig {
    a.clone() - b.clone()
}

pub fn ibig_ge(a: &IBig, b: &IBig) -> bool {
    a >= b
}

pub fn ibig_lt(a: &IBig, b: &IBig) -> bool {
    a < b
}

pub fn ibig_clone(n: &IBig) -> IBig {
    n.clone()
}

pub fn ibig_mul(a: &IBig, b: &IBig) -> IBig {
    a.clone() * b.clone()
}

/// Absolute value of an IBig as a UBig.
pub fn ibig_abs(n: &IBig) -> UBig {
    use dashu::base::Abs;
    n.clone().abs().into_parts().1
}

pub use dashu::rational::RBig;

/// Reduced numerator (signed) and denominator (positive) of r.
pub fn rbig_into_parts(r: &RBig) -> (IBig, UBig) {
    r.clone().into_parts()
}

/// Construct numer/denom as an RBig (denom must be nonzero).
pub fn rbig_from_parts(numer: IBig, denom: UBig) -> RBig {
    RBig::from_parts(numer, denom)
}

/// ⌊r⌋ as an IBig.
pub fn rbig_floor(r: &RBig) -> IBig {
    r.clone().floor()
}
