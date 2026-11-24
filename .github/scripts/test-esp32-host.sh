#!/usr/bin/env bash
# Check one ESP32 firmware crate on the host: inkbot-esp32 or esp32-ble.
# `cargo fmt` and Clippy cover the library and each tool crate under tools/,
# and `make test` runs the host tests. Device builds need the espup Xtensa
# toolchain; test.yml cross-builds them in a separate job.
#
# The crate's rust-toolchain.toml pins the host toolchain, which this script
# installs. Every build goes to APP/target, the directory the Makefile builds
# the tools in, so the crate and its tools share their dependencies and
# test.yml caches one directory.
#
# Usage:
#   test-esp32-host.sh APP
set -euo pipefail

app="${1:?usage: test-esp32-host.sh APP}"
repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
cd "$repo_root/$app"
export CARGO_TARGET_DIR="$PWD/target"

rustup toolchain install --no-self-update

cargo fmt --check
cargo clippy --lib --locked -- -D warnings
for manifest in tools/*/Cargo.toml; do
  [ -f "$manifest" ] || continue
  cargo fmt --check --manifest-path "$manifest"
  cargo clippy --manifest-path "$manifest" --locked -- -D warnings
done
make test
