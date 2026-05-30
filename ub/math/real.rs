// Small shared lemmas about real arithmetic.

use vstd::prelude::*;

verus! {

/// Associativity of real multiplication:  a·(b·c) = (a·b)·c.
/// (A `nonlinear` lemma so callers can reassociate a product without invoking
/// the nonlinear solver at the use site.)
#[verifier::nonlinear]
pub proof fn real_assoc_mult(a: real, b: real, c: real)
    ensures a * (b * c) == (a * b) * c,
{}

} // verus!
