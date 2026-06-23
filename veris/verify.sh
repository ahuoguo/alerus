#!/bin/bash
exec cargo verus verify -p veris "$@" --manifest-path "$(dirname "$0")/../Cargo.toml"
