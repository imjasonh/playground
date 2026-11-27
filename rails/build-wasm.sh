#!/usr/bin/env bash
# Rebuild vendor/rails_engine from the ../rails-server crate.
#
# Requires: rustup target add wasm32-unknown-unknown
#           cargo install wasm-bindgen-cli --version <wasm-bindgen version in ../rails-server/Cargo.lock>
set -euo pipefail
cd "$(dirname "$0")"

CRATE=../rails-server
WANT="$(grep -A1 'name = "wasm-bindgen"' "$CRATE/Cargo.lock" | grep version | head -1 | cut -d'"' -f2)"
HAVE="$(wasm-bindgen --version | awk '{print $2}')"
if [[ "$WANT" != "$HAVE" ]]; then
  echo "error: wasm-bindgen-cli $HAVE != crate's wasm-bindgen $WANT" >&2
  echo "run: cargo install wasm-bindgen-cli --version $WANT --locked" >&2
  exit 1
fi

cargo build --manifest-path "$CRATE/Cargo.toml" --lib \
  --profile wasm-release --target wasm32-unknown-unknown \
  --no-default-features --features browser-wasm

wasm-bindgen --target web --no-typescript \
  --out-dir vendor/rails_engine \
  "$CRATE/target/wasm32-unknown-unknown/wasm-release/rails_server.wasm"

ls -go vendor/rails_engine/
