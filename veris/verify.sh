#!/bin/bash
exec cargo verus verify -p alerus "$@" --manifest-path "$(dirname "$0")/../Cargo.toml"
