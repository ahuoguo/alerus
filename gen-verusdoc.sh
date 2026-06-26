#!/bin/bash
# Generate Verusdoc (rustdoc + Verus spec annotations) for the `alerus` crate.
#
# Mirrors verus-lang/verus's source/tools/docs.sh, adapted for this project:
#   - documents the `alerus` crate (lib.rs) instead of vstd
#   - pulls in the `random` workspace dependency and its transitive rlibs
#
# The same script runs locally and in CI; the locations of the Verus artifacts
# are overridable via environment variables:
#
#   VERUS_BIN_DIR  dir containing libverus_builtin.rlib, libverus_builtin_macros.<dyn>,
#                  libverus_state_machines_macros.<dyn> and libvstd.rlib.
#                  Both a local `target-verus/release` build and an unzipped
#                  Verus release share these exact file names.
#   VERUSDOC_BIN   path to the `verusdoc` HTML post-processor binary.
#   RUSTDOC        rustdoc to invoke (defaults to the 1.95.0 toolchain's rustdoc).
#
# Output: ./doc/alerus/index.html
set -e

VERIS="$(cd "$(dirname "$0")" && pwd)"
DEPS="$VERIS/target/debug/deps"

# Local defaults (a Verus source checkout next to this repo). CI overrides these.
VERUS="${VERUS:-/Users/byc/Desktop/mpi/verus}"
VERUS_BIN_DIR="${VERUS_BIN_DIR:-$VERUS/source/target-verus/release}"
VERUSDOC_BIN="${VERUSDOC_BIN:-$VERUS/source/target/debug/verusdoc}"
RUSTDOC="${RUSTDOC:-$(rustup which --toolchain 1.95.0 rustdoc)}"

case "$(uname)" in
  Darwin) DYN=dylib ;;
  Linux)  DYN=so ;;
  *) echo "unsupported OS" >&2; exit 1 ;;
esac

cd "$VERIS"

# The `veris` crate depends on `random` (which re-exports dashu's UBig/IBig/RBig).
# Build it so rustdoc has the rlib plus its transitive deps in target/debug/deps.
echo "Building the random dependency..."
cargo +1.95.0 build -p random

RANDOM_RLIB="$(ls -t "$DEPS"/librandom-*.rlib | head -1)"

echo "Running rustdoc on the alerus crate..."
RUSTC_BOOTSTRAP=1 VERUSDOC=1 "$RUSTDOC" \
  --crate-name alerus \
  --edition=2021 \
  --crate-type=lib \
  --extern verus_builtin="$VERUS_BIN_DIR/libverus_builtin.rlib" \
  --extern verus_builtin_macros="$VERUS_BIN_DIR/libverus_builtin_macros.$DYN" \
  --extern verus_state_machines_macros="$VERUS_BIN_DIR/libverus_state_machines_macros.$DYN" \
  --extern vstd="$VERUS_BIN_DIR/libvstd.rlib" \
  --extern random="$RANDOM_RLIB" \
  -L dependency="$VERUS_BIN_DIR" \
  -L dependency="$DEPS" \
  --cfg verus_keep_ghost \
  --cfg verus_keep_ghost_body \
  --cfg 'feature="std"' \
  --cfg 'feature="alloc"' \
  -Zcrate-attr=feature\(stmt_expr_attributes\) \
  -Zcrate-attr=feature\(negative_impls\) \
  -Zcrate-attr=feature\(register_tool\) \
  -Zcrate-attr=feature\(rustc_attrs\) \
  -Zcrate-attr=feature\(unboxed_closures\) \
  -Zcrate-attr=feature\(custom_inner_attributes\) \
  -Zcrate-attr=register_tool\(verus\) \
  -Zcrate-attr=register_tool\(verifier\) \
  -Zcrate-attr=register_tool\(verusfmt\) \
  -Zcrate-attr=allow\(internal_features\) \
  -Zcrate-attr=allow\(unused_braces\) \
  -Zproc-macro-backtrace \
  veris/lib.rs

echo "Running verusdoc post-processor..."
"$VERUSDOC_BIN"

echo "Documentation generated at $VERIS/doc/alerus/index.html"
