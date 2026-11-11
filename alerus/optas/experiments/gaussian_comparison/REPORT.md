# Discrete Gaussian benchmark

**Goal.** Compare the verified samplers for N_ℤ(0, σ²) with the unverified
original, at an accuracy cryptography would accept: TV(output, N_ℤ(0, σ²)) ≤ 2⁻⁹⁰.

**Samplers.**

- **CKS exact**: the Canonne–Kamath–Steinke sampler
  (`cks::discrete_gaussian`, verified). It samples N_ℤ(0, σ²) exactly.
- **Saad Rust**: the verified OPTAS pipeline (`optas::examples::gaussian`):
  Taylor bounds, integer weights, Algorithm 3, then the packed encoding.
- **Saad C**: the artifact's C encoding sampler (`senc.c`), sampling a table built by upstream
  optas in Python. The paper benchmarks the same way.

**Parameters.** The σ values are our choice. They span the variance range of
the paper's discrete Gaussian grid (0.5 to 50, `accuracy.py`), plus σ = 3.33
from Roy et al. (SAC 2013). B and k are the smallest values that keep each
error term below 2⁻⁹²:

| σ | 0.75 | 1 | 2.5 | 3.33 | 5 | 7 |
|---|---|---|---|---|---|---|
| B (support [−B, B]) | 10 | 13 | 30 | 39 | 58 | 81 |
| k (Z = 2^k) | 96 | 96 | 97 | 98 | 98 | 99 |

## Results

The data are in `results90.csv`. Samples: 10⁶ for CKS, 10⁷ for Saad Rust and
C. Times are wall-clock on one Apple-silicon core.

| σ | log₂ TV (Saad) | bits/sample (Saad) | Saad C | Saad Rust | CKS exact (bits) |
|---|---|---|---|---|---|
| 0.75 | −95.2 | 2.59 | 9 ns | 25 ns | 4.0 µs (22) |
| 1 | −94.5 | 3.62 | 11 ns | 32 ns | 5.2 µs (23) |
| 2.5 | −94.1 | 4.50 | 13 ns | 40 ns | 3.9 µs (30) |
| 3.33 | −94.8 | 5.17 | 13 ns | 45 ns | 3.9 µs (65) |
| 5 | −94.1 | 5.35 | 14 ns | 47 ns | 4.0 µs (35) |
| 7 | −94.6 | 6.09 | 16 ns | 54 ns | 3.8 µs (41) |

- **The two Saad implementations are the same sampler.** Rust and C give the
  same M (hence the same TV, computed exactly from M) and use the same number
  of bits per sample. The bits stay within the paper's entropy bound H + 2.
- **The verified sampler is about 3× slower than C.** Most of the gap is the
  random source. C reads bits from `rand()`, a non-cryptographic generator;
  Rust reads them from OpenSSL. Run on the same bits, the verified walk is
  within about 20% of the C sampler (`gcmp bench`).
- **CKS is exact, but costs about 100× more.** It needs no table, but it draws
  6–13× more random bits and takes microseconds per sample.
- **Accuracy is nearly free per sample.** Reaching 2⁻⁹⁰ instead of the
  paper's 2⁻³¹ (k = 32) makes the tree three times deeper, but the extra
  levels are almost never reached, so the time per sample barely changes.

## Upstream optas needs exact arithmetic

Upstream optas computes the target and M/Z in floats. `saad_py.py` with
`EXACT=1` (what `run.sh` uses) computes the target exactly and patches
`get_delta_error` to use `Fraction(M, Z)`; the rest of Algorithm 3 and the C
encoding sampler are unchanged. Without it, at σ = 1 (B = 13):

| k | 32 | 48 | 56 | 64 | 72 | 80 | 88 | 96 |
|---|---|---|---|---|---|---|---|---|
| log₂ TV, floats | −31.3 | −46.9 | −54.3 | −55.2 | −55.2 | −55.2 | not run (≈ 2 min) | not run (≈ 9 h) |
| log₂ TV, exact | −31.3 | −46.9 | −55.3 | −62.8 | −70.4 | −78.5 | −86.4 | −94.5 |

- **Floats plateau at about 2⁻⁵⁵**, the precision of a double, from k ≈ 56 on.
- **The float time doubles with each bit of k.** The float p_i sum to
  1 + 2⁻⁶¹, so the initial M_i = ⌊Z·p_i⌋ overshoot Z by 2^{k−61}, and
  `fix_shortfall` removes the excess one unit per iteration: 0.4 s at k = 80,
  about 2 minutes at k = 88, and about 9 hours at k = 96 (estimated at
  ~1 µs per iteration).

So the paper's code, as shipped, cannot reach 2⁻⁹⁰; the verified Rust
pipeline is exact by construction.

