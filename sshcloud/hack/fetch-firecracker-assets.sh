#!/usr/bin/env bash
# Download Firecracker binary + recommended kernel into ./_assets/
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
OUT="${OUT:-$ROOT/_assets}"
mkdir -p "$OUT"

FC_VERSION="${FC_VERSION:-v1.10.1}"
ARCH="$(uname -m)"
case "$ARCH" in
  x86_64|amd64) ARCH=x86_64 ;;
  aarch64|arm64) ARCH=aarch64 ;;
  *) echo "unsupported arch: $ARCH" >&2; exit 1 ;;
esac

FC_TGZ="firecracker-${FC_VERSION}-${ARCH}.tgz"
FC_URL="https://github.com/firecracker-microvm/firecracker/releases/download/${FC_VERSION}/${FC_TGZ}"

echo "fetching $FC_URL"
curl -fsSL "$FC_URL" -o "$OUT/$FC_TGZ"
tar -xzf "$OUT/$FC_TGZ" -C "$OUT"
# release tarball layout: release-${VERSION}-${ARCH}/firecracker-${VERSION}-${ARCH}
FC_BIN="$(find "$OUT" -type f -name "firecracker-${FC_VERSION#v}-${ARCH}" -o -name "firecracker" | head -n1)"
if [[ -z "${FC_BIN}" ]]; then
  FC_BIN="$(find "$OUT" -type f -name 'firecracker*' ! -name '*.tgz' | head -n1)"
fi
cp -f "$FC_BIN" "$OUT/firecracker"
chmod +x "$OUT/firecracker"
echo "firecracker -> $OUT/firecracker"

# Kernel: use Firecracker's CI artifact naming from the same release when present,
# otherwise document manual placement.
KERNEL_URL="${KERNEL_URL:-https://s3.amazonaws.com/spec.ccfc.min/firecracker-ci/v1.10/x86_64/vmlinux-5.10.223}"
if [[ "$ARCH" != "x86_64" ]]; then
  echo "set KERNEL_URL for $ARCH and re-run" >&2
else
  echo "fetching kernel $KERNEL_URL"
  curl -fsSL "$KERNEL_URL" -o "$OUT/vmlinux"
  echo "kernel -> $OUT/vmlinux"
fi

echo "done. build rootfs next:"
echo "  go build -o $OUT/fortune ./cmd/fortune"
echo "  go run ./cmd/mkrootfs -fortune $OUT/fortune -ca-pub ssh_user_ca.pub -out $OUT/fortune-rootfs.ext4"
