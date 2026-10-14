#!/usr/bin/env bash
# Point every Verus pin in the repo at the latest stable Verus release:
#   - VERUS_VER / VERUS_TAG in .github/workflows/{main,pages}.yml
#   - the Rust toolchain (taken from that release's rust-toolchain.toml), in
#     those workflows and in opendp.sh / gen-verusdoc.sh, which pin `cargo
#     +<version>` and run inside the Verusdoc job
#   - vstd in alerus/Cargo.toml (newest crates.io build published on or before
#     the release date; vstd is not published for every release)
#
# Usage: .github/scripts/bump-verus.sh [release/0.YYYY.MM.DD.sha]
# Prints `version=<VERUS_VER>` on stdout for CI. Needs curl, python3, perl.
set -euo pipefail
cd "$(dirname "$0")/../.."

gh_api() {
  curl -fsSL -H "Accept: application/vnd.github+json" \
    ${GITHUB_TOKEN:+-H "Authorization: Bearer $GITHUB_TOKEN"} "$1"
}

# `releases/latest` skips prereleases, i.e. the release/rolling/* builds.
tag="${1:-$(gh_api https://api.github.com/repos/verus-lang/verus/releases/latest |
  python3 -c 'import json,sys; print(json.load(sys.stdin)["tag_name"])')}"
ver="${tag#release/}"
date="$(echo "$ver" | cut -d. -f2-4 | tr . -)"   # 0.2026.09.27.sha -> 2026-09-27

rust="$(curl -fsSL "https://raw.githubusercontent.com/verus-lang/verus/$tag/rust-toolchain.toml" |
  python3 -c 'import sys,tomllib; print(tomllib.load(sys.stdin.buffer)["toolchain"]["channel"])')"

vstd="$(curl -fsSL -A "veris-verus-bump (github.com/ahuoguo/veris)" \
  https://crates.io/api/v1/crates/vstd/versions | DATE="$date" python3 -c '
import json, os, sys
cutoff = os.environ["DATE"]
vs = [v["num"] for v in json.load(sys.stdin)["versions"]
      if not v["yanked"] and v["num"].startswith("0.0.0-")
      and v["num"][6:16] <= cutoff]
print(max(vs, key=lambda n: n[6:]))')"

echo "Verus $ver, Rust $rust, vstd $vstd" >&2

for f in .github/workflows/main.yml .github/workflows/pages.yml opendp.sh gen-verusdoc.sh; do
  perl -pi -e "
    s/^(\s*VERUS_VER:\s*).*/\${1}$ver/;
    s/^(\s*VERUS_TAG:\s*).*/\${1}release\/$ver/;
    s/^(\s*RUST_VER:\s*).*/\${1}$rust/;
    s/\b1\.\d+\.\d+\b/$rust/g if /toolchain|Install Rust|cargo \+|rustup (which|default)/;
  " "$f"
done
perl -pi -e "s/^vstd = \"=[^\"]*\"/vstd = \"=$vstd\"/" alerus/Cargo.toml

echo "version=$ver"
echo "rust=$rust"
echo "vstd=$vstd"
