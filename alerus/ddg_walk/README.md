# DDG samplers behind one trait

The fast loaded dice roller (`fldr.rs`) and OPTAS, the Z_kl-type samplers
of Saad et al. (POPL 2020; `approx_ddg/`), both walk a discrete distribution generating
(DDG) tree, one coin flip per level. They differ in how the tree is stored
(per-level label lists, matrices, a packed array) and in their back-edges.
This directory proves the walk once for every storage layout.

## The abstraction

- **`LDdg`** (`walk.rs`) is a level-structured DDG. Its leaves are at
  depths 1..K. At each depth the h(j) leaves come first, then the internal
  nodes, and internal node d has the children 2d and 2d+1. There are two
  kinds of back-edge: a leaf labeled ≥ n restarts at the root (FLDR's
  reject label), and an internal node at depth K continues at depth `wrap`.
- **`DdgWalk`** is a table layout. It says how to take one step (`root`,
  `step`: node → leaf, restart, or next node) and gives two laws: the shape
  is valid (`lemma_shape`), and with enough flips the root's credit is at
  most E_p[ℰ] + s₀ (`lemma_fuel`).
- **`sample_walk<W: DdgWalk>`** is the sampler, proved once:

  ```text
    ε ≥ E_p[ℰ]        ℰ ≥ 0
    ---------------------------------------------
    [{ ↯(ε) }] sample_walk(w) [{ r. ↯(ℰ(r)) }]
  ```

- **`Family`** (`packing.rs`) is the distribution side of the laws, stated
  once per distribution and shared by all its layouts. FLDR's family is its
  spec `Ddg`; the OPTAS family is `approx_ddg::tree::ApproxFam`.
- **`make_ddg_tree`** (`tree.rs`, `optas/tree.py`) and **`pack_tree`**
  (`packing.rs`, `optas/packing.py`) build the packed array from any
  `Leaves` table (`h(j)`, `lab(j, x)`). **`Encoded<F>`** (`encoding.rs`)
  is that array as a `DdgWalk` for the family F.

## Instances

| Layout | Family | Where | Sampler |
|---|---|---|---|
| `FldrTable` (lab[c][d], per level) | FLDR | `fldr.rs` | `sample_fldr` (the paper's), or `sample_fldr_walk` |
| `FldrH` (h[k] and a flat (n+1)×k H, Saad et al. AISTATS'20 and its C code) | FLDR | `fldr_layouts.rs` | `sample_fldr` (a `DdgTable`) |
| `FldrFlat` (one row of n+2 entries per level, ryco117's `level_label_matrix`, issue #18) | FLDR | `fldr_layouts.rs` | `sample_fldr` (a `DdgTable`) |
| packed array built from any `DdgTable` (levels ≤ 52) | FLDR | `fldr_walk.rs` | `sample_fldr_encoding` |
| matrix P, cached (h, T) | OPTAS | `approx_ddg/sample.rs` | `sample_ky_matrix[_cached]` |
| packed array (`tree.py` + `packing.py`; n < 2⁵⁰, k ≤ 124) | OPTAS | `approx_ddg/construct.rs` | `sample_ky_encoding` |

The two FLDR tables are `DdgTable` impls, so the existing `sample_fldr`
samples them unchanged; only their preprocessing (`fldr_preprocess_h`,
`fldr_preprocess_flat`) is new. `ByLevel<T: DdgTable>` turns any
`DdgTable` into a `DdgWalk`, so it can also be packed.

The matrix samplers of `approx_ddg` keep their own loops (they follow
`sample.py` line by line). Their proof is the one `ApproxFam` reuses through
`lemma_approx_walk`.

## Proof outline

- **The walk.** The credit of internal node (j, d) with f flips left is
  `lwalk_f`: ½ of its children's, a leaf pays ℰ(label), a reject leaf is
  the root, and no fuel is worth 1. `sample_walk` splits it with
  `rand_2_u64_fast` (the buffered fair bit, same spec as `rand_2_u64`);
  the fuel law closes the loop.
- **FLDR's fuel law.** `lwalk_f` = `fldr_f` + `fldr_fail_f`
  (`lemma_fldr_walk`), so the bounds of `fldr_helper.rs` apply.
- **OPTAS's fuel law.** `lwalk_f` at depth c = `ddg_f` at any unrolled
  level with the same residues (`lemma_approx_walk`), so
  `lemma_ddg_val_le_target` applies. For l = k it needs no `thin_air`.
- **The tree.** `make_tree` is right-first, so each depth's positions are
  visited in order (`cover` counts them, `binv` holds the state). The i-th
  back-edge therefore takes the i-th internal node of depth l. The queue
  is never empty: below the first a internal nodes of depth l there are at
  most a internal nodes of depth K (`lemma_icnt_le`; the count is
  star-shaped in a).
- **The packing.** `pack_tree` keeps, for every packed node, its offset
  and the contents of its slots (`pinv`, `packed`). With `complete` from
  the tree this gives `enc_wf`: the two slots of every internal node point
  at its children (`construct_encoding`).

## Checked by running

- **FLDR tables.** For (7,4,8), (1,1,1), (5,0,3) and (2,9,1,13), `FldrH`
  and `FldrFlat` match the C code's `fldr_preprocess_int` and ryco117's
  `Generator::new` entry for entry.
- **Encodings.** `construct_sample_ky_encoding` matches `optas` on 8
  distributions.
- **Sampling.** Over 3·10^5 samples, `sample_fldr` on all three tables,
  `sample_fldr_walk`, `sample_fldr_encoding` and `sample_ky_encoding` all
  have frequencies within 0.003 of p.
