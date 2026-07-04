#!/bin/bash

set -e

BASEDIR=$(realpath $(dirname "$0"))

cd $BASEDIR
mkdir -p build

cd random
# cargo clean --release
cargo +1.96.0 build --release
cd ..
OPENDP_RLIB_NAME=$(find ./random/target/release/deps/ -name 'libopendp-*.rlib')
