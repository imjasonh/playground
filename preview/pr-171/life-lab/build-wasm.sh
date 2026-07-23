#!/usr/bin/env bash
# Rebuild vendor/life_stl from the ../life-stl crate.
#
# Requires: rustup target add wasm32-unknown-unknown
#           cargo install wasm-bindgen-cli --version <wasm-bindgen version in ../life-stl/Cargo.lock>
set -euo pipefail
cd "$(dirname "$0")"

CRATE=../life-stl
WANT="$(grep -A1 'name = "wasm-bindgen"' "$CRATE/Cargo.lock" | grep version | head -1 | cut -d'"' -f2)"
HAVE="$(wasm-bindgen --version | awk '{print $2}')"
if [[ "$WANT" != "$HAVE" ]]; then
  echo "error: wasm-bindgen-cli $HAVE != crate's wasm-bindgen $WANT" >&2
  echo "run: cargo install wasm-bindgen-cli --version $WANT --locked" >&2
  exit 1
fi

cargo build --manifest-path "$CRATE/Cargo.toml" --lib \
  --profile wasm-release --target wasm32-unknown-unknown \
  --no-default-features --features wasm

wasm-bindgen --target web --no-typescript \
  --out-dir vendor/life_stl \
  "$CRATE/target/wasm32-unknown-unknown/wasm-release/life_stl.wasm"

ls -go vendor/life_stl/
