# DDG samplers behind one trait

The fast loaded dice roller (`fldr.rs`) and OPTAS, the Z_kl-type samplers
of Saad et al. (POPL 2020; `optas/`), both walk a discrete distribution generating
(DDG) tree, one coin flip per level. They differ in how the tree is stored
(per-level label lists, matrices, a packed array) and in their back-edges.
This directory proves the walk once for every storage layout.

## The abstraction

- **`LDdg`** (`walk.rs`) is a level-structured DDG. Its leaves are at
  depths 1..K. At each depth the h(j) leaves come first, then the internal
  nodes, and internal node d has the children 2d and 2d+1. There are two
  kinds of back-edge: a leaf labeled ≥ n restarts at the root (FLDR's
  reject label), and an internal node at depth K continues at depth `wrap`.
- **`DdgSpec`** (`walk.rs`) is the spec side of a sampler: the tree it
  walks (`ddg`), the distribution it samples, and two laws, proved once and
  shared by all layouts of that tree: the shape is valid (`lemma_shape`),
  and with enough flips the root's credit is at most E_p[ℰ] + s₀
  (`lemma_fuel`). FLDR's spec is its `Ddg` (`fldr_walk.rs`); OPTAS's is
  `optas::tree::OptasSpec`.
- **`DdgWalk`** (`walk.rs`) is a table layout of a spec (`type Spec`,
  `spec()`). It says how to take one step: `root`, and `step` from a node
  to a leaf, a restart, or the next node.
- **`sample<W: DdgWalk>`** (`walk.rs`) is the sampler, proved once:

  ```text
    ε ≥ E_p[ℰ]        ℰ ≥ 0
    ---------------------------------------------
    [{ ↯(ε) }] sample(w) [{ r. ↯(ℰ(r)) }]
  ```

- **`make_ddg_tree`** (`tree.rs`, optas's `tree.py`) and **`pack_tree`**
  (`packing.rs`, optas's `packing.py`) build the packed array from any
  `Leaves` table (`h(j)`, `lab(j, x)`). **`Encoded<S>`** (`encoding.rs`)
  is that array as a `DdgWalk` for the spec S.

## Instances

| Layout | Spec | Where | Sampler |
|---|---|---|---|
| `FldrTable` (lab[c][d], per level) | FLDR | `fldr.rs` | `sample_fldr` (`walk::sample` on `ByLevel`) |
| `FldrH` (h[k] and a flat (n+1)×k H, Saad et al. AISTATS'20 and its C code) | FLDR | `fldr_layouts.rs` | `sample_fldr` (a `DdgTable`) |
| `FldrFlat` (one row of n+2 entries per level, ryco117's `level_label_matrix`, issue #18) | FLDR | `fldr_layouts.rs` | `sample_fldr` (a `DdgTable`) |
| packed array built from any `DdgTable` (levels ≤ 52, n < 2⁶²) | FLDR | `fldr_walk.rs` | `sample_fldr_encoding` |
| matrix P, cached (h, T) | OPTAS | `optas/sample.rs` | `sample_ky_matrix[_cached]` |
| packed array (`tree.py` + `packing.py`; n < 2⁵⁰, k ≤ 124) | OPTAS | built in `optas/construct.rs` | `sample_ky_encoding` (`optas/sample.rs`) |

The two FLDR tables are `DdgTable` impls, so the existing `sample_fldr`
samples them unchanged; only their preprocessing (`fldr_preprocess_h`,
`fldr_preprocess_flat`) is new. `ByLevel<T: DdgTable>` turns any
`DdgTable` into a `DdgWalk` and (via `Leaves`) into a table that can be
packed.

The matrix samplers of `optas` are layouts too (`MatrixWalk`,
`CachedWalk` in `optas/sample.rs`), so every sampler in the crate is
`walk::sample` on some `DdgWalk`, and each `DdgWalk` names its `DdgSpec`.

## Proof outline

- **The walk.** The credit of internal node (j, d) with f flips left is
  `lwalk_f`: ½ of its children's, a leaf pays ℰ(label), a reject leaf is
  the root, and no fuel is worth 1. `walk::sample` splits it with
  `rand_2_u64_fast` (the buffered fair bit, same spec as `rand_2_u64`);
  the fuel law closes the loop.
- **FLDR's fuel law.** `lwalk_f` = `fldr_f` + `fldr_fail_f`
  (`lemma_fldr_walk`), so the bounds of `fldr_helper.rs` apply.
- **OPTAS's fuel law.** `lwalk_f` at depth c = `ddg_f` at any unrolled
  level with the same residues (`lemma_optas_walk`), so
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

These were one-off runs during development; the harnesses are not in the
repository.

- **FLDR tables.** For (7,4,8), (1,1,1), (5,0,3) and (2,9,1,13), `FldrH`
  and `FldrFlat` match the C code's `fldr_preprocess_int` and ryco117's
  `Generator::new` entry for entry.
- **Encodings.** `construct_sample_ky_encoding` matches `optas` on 8
  distributions.
- **Sampling.** Over 3·10^5 samples, `sample_fldr` on all three tables,
  `sample_fldr_encoding` and `sample_ky_encoding` all
  have frequencies within 0.003 of p.
