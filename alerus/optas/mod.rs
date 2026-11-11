//! Optimal approximate sampling (Saad et al., POPL 2020), following the
//! structure of the reference library `optas`.

// Z_kl, the binary expansion of M / Z_kl (`frac_to_bits`),
// gcd/lcm, `orderm2` and `reduce_fractions`.
pub mod utils;
// The unrolled DDG tree of M / Z, its credits and their bounds. The proofs
// of the samplers rest on it.
pub mod ztype;
// The matrix P (Algorithm 4) and the hamming tables h, T of
// the cached sampler.
pub mod matrix;
// `sample_ky_matrix`, `sample_ky_matrix_cached` and
// `sample_ky_encoding`, each `walk::sample` on a layout.
pub mod sample;
// `make_leaf_table`, and M / Z_kl as a `DdgSpec` (`OptasSpec`) with its
// fuel law.
pub mod tree;
// The TV divergence, exact.
pub mod divergences;
// Algorithm 3 for TV, and its optimality.
pub mod opt;
// The approximate specs (Theorem 4.17): sampling M / Z samples p up to
// TV(p, M / Z), paid as error credit.
pub mod approx;
// The samplers of an exact rational p: matrix, cached, or packed array.
pub mod construct;
// Algorithm 3 followed by a sampler, and the discrete Gaussian.
pub mod examples;
