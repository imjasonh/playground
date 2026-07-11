#!/usr/bin/env bash
# Build the Cloudflare Worker wasm artifact (`worker-build --release`).
#
# wrangler-action (and local `npm i wrangler`) creates a package.json in this
# directory *before* the build runs. Any `#[wasm_bindgen]` in *this* crate
# makes the wasm-bindgen macro embed that package.json path into the wasm; the
# CLI then copies `dependencies` into build/package.json as a nested object.
# worker-build 0.1.x tries to parse that whole file as HashMap<String, String>
# and fails with: `invalid type: map, expected a string`.
#
# Hide npm manifests for the compile + bindgen step so they are not embedded.
# See: https://github.com/cloudflare/workers-rs/issues/998
set -euo pipefail

cd "$(dirname "$0")/.."

stash_dir=$(mktemp -d)
cleanup() {
  if [[ -f "$stash_dir/package.json" ]]; then
    mv -f "$stash_dir/package.json" package.json
  fi
  if [[ -f "$stash_dir/package-lock.json" ]]; then
    mv -f "$stash_dir/package-lock.json" package-lock.json
  fi
  rm -rf "$stash_dir"
}
trap cleanup EXIT

[[ -f package.json ]] && mv package.json "$stash_dir/"
[[ -f package-lock.json ]] && mv package-lock.json "$stash_dir/"

# Macros observe package.json at rustc time. If a prior compile embedded it,
# incremental cargo would reuse that tainted wasm — bump the crate so it
# rebuilds without the path.
touch src/lib.rs

# Install the tool with stable (its own deps want a recent Cargo); it then
# compiles this crate with rust-toolchain.toml (rustup honors it per-dir).
cargo +stable install -q worker-build@0.1.14
worker-build --release
