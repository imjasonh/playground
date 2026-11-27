#!/usr/bin/env bash
# Build the Cloudflare Worker wasm artifact (`worker-build --release`).
# See git-server/scripts/worker-build.sh for details on stashing package.json.
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

touch src/lib.rs

cargo +stable install -q "worker-build@$(cargo pkgid worker | cut -d@ -f2)"
worker-build --release
