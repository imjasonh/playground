#!/usr/bin/env bash
# Compile bin/detect and bin/build for linux targets so `pack` can package
# this directory as a buildpack (see package.toml / builder.toml).
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

targets=("linux/amd64" "linux/arm64")
if [[ "${1:-}" == "--host" ]]; then
  targets=("${GOOS:-$(go env GOOS)}/${GOARCH:-$(go env GOARCH)}")
fi

mkdir -p bin
# Default layout for local pack create: host-arch linux binaries in bin/.
os=linux
arch="$(go env GOARCH)"
echo "→ building detect/build for ${os}/${arch}"
CGO_ENABLED=0 GOOS="$os" GOARCH="$arch" go build -trimpath -ldflags='-s -w' -o bin/detect ./cmd/detect
CGO_ENABLED=0 GOOS="$os" GOARCH="$arch" go build -trimpath -ldflags='-s -w' -o bin/build ./cmd/build
chmod +x bin/detect bin/build
echo "→ wrote bin/detect bin/build"
