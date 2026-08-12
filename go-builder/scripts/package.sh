#!/usr/bin/env bash
# Compile arch-specific detect/build binaries and install multi-arch trampolines
# at bin/detect and bin/build so `pack builder create --target …` can embed the
# same directory into every platform image.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

targets=(amd64 arm64)
if [[ "${1:-}" == "--host" ]]; then
  targets=("$(go env GOARCH)")
fi

mkdir -p bin
cp scripts/bin-trampoline.sh bin/detect
cp scripts/bin-trampoline.sh bin/build
chmod +x bin/detect bin/build

for arch in "${targets[@]}"; do
  mkdir -p "bin/${arch}"
  echo "→ building detect/build for linux/${arch}"
  CGO_ENABLED=0 GOOS=linux GOARCH="$arch" go build -trimpath -ldflags='-s -w' \
    -o "bin/${arch}/detect" ./cmd/detect
  CGO_ENABLED=0 GOOS=linux GOARCH="$arch" go build -trimpath -ldflags='-s -w' \
    -o "bin/${arch}/build" ./cmd/build
  chmod +x "bin/${arch}/detect" "bin/${arch}/build"
done

echo "→ wrote bin/{detect,build} trampolines + bin/{$(IFS=,; echo "${targets[*]}")}/{detect,build}"
