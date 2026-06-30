#!/usr/bin/env bash
# Build the gitdb Go/WASM worker into a static app directory.
set -euo pipefail

if [ "$#" -ne 1 ]; then
  echo "usage: $0 OUTPUT_DIR" >&2
  exit 2
fi

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
output=$1
if [[ "$output" != /* ]]; then
  output="$PWD/$output"
fi
mkdir -p "$output"

(
  cd "$repo_root/gitdb"
  GOOS=js GOARCH=wasm go build \
    -trimpath \
    -ldflags="-s -w" \
    -o "$output/gitdb.wasm" \
    ./cmd/wasm
)

wasm_exec="$(go env GOROOT)/lib/wasm/wasm_exec.js"
if [ ! -f "$wasm_exec" ]; then
  wasm_exec="$(go env GOROOT)/misc/wasm/wasm_exec.js"
fi
cp "$wasm_exec" "$output/wasm_exec.js"

echo "Built gitdb browser worker in $output"
