# Discrete Gaussian comparison

Samples N_ℤ(0, σ²) with three samplers and measures accuracy and cost:

- **CKS exact** (`cks::discrete_gaussian`, verified)
- **Saad Rust** (`optas::examples::gaussian`, verified)
- **Saad C**: the artifact's C encoding sampler (`senc.c`) on a table built by upstream
  [optas](https://github.com/probsys/optimal-approximate-sampling) (Python),
  as in the paper's own benchmarks

Saad's parameters are set so that TV(output, N_ℤ(0, σ²)) ≤ 2⁻⁹⁰. The σ values
cover the paper's discrete Gaussian sweep (variance 0.5 to 50), plus 3.33
(Roy et al., SAC 2013). Results are in `results90.csv`.

| File | What |
|---|---|
| `main.rs`, `Cargo.toml.example` | Rust harness (`cks`, `saad`, `bench` modes) |
| `saad_py.py` | builds the C sampler's table with optas; with `EXACT=1`, an exact target and `Fraction(M, Z)` in Algorithm 3 |
| `gsenc.c` | the artifact's C encoding sampler (`senc.c`), with a histogram |
| `analyze.py` | exact TV and empirical checks, as CSV rows |
| `random_counter.patch` | counts RNG calls and bits in a copy of `random` |
| `run.sh` | the grid |

## Running

1. Make `$WORK`. Copy `alerus/` and `random/` into `$WORK/cnt/`, then
   `patch $WORK/cnt/random/src/lib.rs random_counter.patch`.
2. Copy `main.rs` to `$WORK/gcmp/src/` and `Cargo.toml.example` to
   `$WORK/gcmp/Cargo.toml` (fill in `${WORK}`), then `cargo build --release`.
3. Copy the `.py` and `.c` files to `$WORK/py/`, and `cc -O3 -o gsenc gsenc.c` there.
4. Make a venv in `$WORK/venv` with `numpy` and `mpmath`.
5. `WORK=$WORK OPTAS=<optas checkout> ./run.sh` writes `$WORK/results90.csv`
   (about a minute).
