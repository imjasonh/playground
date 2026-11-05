#!/bin/bash
# Rebuild wasm/palette.wasm and the matching wasm_exec.js glue.
set -euo pipefail

root=$(cd "$(dirname "$0")" && pwd)
cd "$root"

goroot=$(go env GOROOT)
mkdir -p wasm
cp "${goroot}/lib/wasm/wasm_exec.js" wasm/wasm_exec.js

export GOOS=js
export GOARCH=wasm
export GOEXPERIMENT=simd
go build -o wasm/palette.wasm ./cmd/wasm
