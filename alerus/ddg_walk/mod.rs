//! Table layouts for DDG samplers, behind one trait.
//!
//! - `walk.rs`: the level-structured DDG (`LDdg`), the `DdgSpec` and
//!   `DdgWalk` traits, and `sample`, the walk proved once for every layout.
//! - `tree.rs`: optas's `tree.py`. Builds the DDG of any `Leaves` table as
//!   an arena of nodes (`make_ddg_tree`), back-edges included.
//! - `packing.rs`: optas's `packing.py`. Packs that arena into one `i64`
//!   array (`pack_tree`) and states what a well-formed array is (`enc_wf`).
//! - `encoding.rs`: `construct_encoding` (tree, then packing) and
//!   `Encoded`, the packed array as a `DdgWalk`.
pub mod walk;
pub mod tree;
pub mod packing;
pub mod encoding;
