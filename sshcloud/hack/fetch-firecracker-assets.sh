#!/usr/bin/env bash
# Download Firecracker binary + recommended kernel into ./_assets/
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
OUT="${OUT:-$ROOT/_assets}"
mkdir -p "$OUT"

FC_VERSION="${FC_VERSION:-v1.10.1}"
ARCH="${TARGET_ARCH:-x86_64}"
case "$ARCH" in
  x86_64|amd64) ARCH=x86_64 ;;
  *) echo "unsupported target architecture: $ARCH (Terraform agents are x86_64)" >&2; exit 1 ;;
esac
HOST_OS="$(uname -s)"
HOST_ARCH="$(uname -m)"

download() {
  local url="$1" dest="$2"
  curl --retry 5 --retry-all-errors --connect-timeout 15 -fsSL "$url" -o "$dest"
}

sha256_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  else
    shasum -a 256 "$1" | awk '{print $1}'
  fi
}

FC_TGZ="firecracker-${FC_VERSION}-${ARCH}.tgz"
FC_URL="https://github.com/firecracker-microvm/firecracker/releases/download/${FC_VERSION}/${FC_TGZ}"
FC_SHA_URL="${FC_URL}.sha256.txt"

echo "fetching $FC_URL"
download "$FC_URL" "$OUT/$FC_TGZ"
download "$FC_SHA_URL" "$OUT/$FC_TGZ.sha256"
FC_EXPECTED="$(awk 'NR == 1 {print $1}' "$OUT/$FC_TGZ.sha256")"
FC_ACTUAL="$(sha256_file "$OUT/$FC_TGZ")"
if [[ "$FC_ACTUAL" != "$FC_EXPECTED" ]]; then
  echo "Firecracker checksum mismatch: got $FC_ACTUAL want $FC_EXPECTED" >&2
  exit 1
fi
echo "$FC_ACTUAL  $FC_TGZ"
tar -xzf "$OUT/$FC_TGZ" -C "$OUT"

# Release layout: release-<ver>-<arch>/firecracker-<ver>-<arch>
# Do NOT pick *.debug (dynamically linked; segfaults if executed).
FC_BIN="$OUT/release-${FC_VERSION}-${ARCH}/firecracker-${FC_VERSION}-${ARCH}"
if [[ ! -x "$FC_BIN" ]]; then
  FC_BIN="$(find "$OUT" -type f -name "firecracker-${FC_VERSION}-${ARCH}" ! -name '*.debug' | head -n1 || true)"
fi
if [[ -z "${FC_BIN}" || ! -f "${FC_BIN}" ]]; then
  echo "could not find firecracker binary in tarball" >&2
  find "$OUT" -type f -name 'firecracker*' -print >&2 || true
  exit 1
fi
cp -f "$FC_BIN" "$OUT/firecracker"
chmod +x "$OUT/firecracker"
echo "firecracker -> $OUT/firecracker (from $FC_BIN)"
if [[ "$HOST_OS" == "Linux" && "$HOST_ARCH" =~ ^(x86_64|amd64)$ ]] && ! "$OUT/firecracker" --version; then
  echo "ERROR: firecracker --version failed (wrong binary?)" >&2
  file "$OUT/firecracker" >&2 || true
  exit 1
fi

# Kernel: Firecracker CI artifact for this release line. Use the regional form
# of the same S3 bucket so restrictive egress proxies do not reset the legacy
# global endpoint.
KERNEL_URL="${KERNEL_URL:-https://s3.us-east-1.amazonaws.com/spec.ccfc.min/firecracker-ci/v1.10/x86_64/vmlinux-5.10.223}"
KERNEL_SHA256="${KERNEL_SHA256:-22847375721aceea63d934c28f2dfce4670b6f52ec904fae19f5145a970c1e65}"
echo "fetching kernel $KERNEL_URL"
download "$KERNEL_URL" "$OUT/vmlinux"
KERNEL_ACTUAL="$(sha256_file "$OUT/vmlinux")"
if [[ "$KERNEL_ACTUAL" != "$KERNEL_SHA256" ]]; then
  echo "kernel checksum mismatch: got $KERNEL_ACTUAL want $KERNEL_SHA256" >&2
  exit 1
fi
echo "$KERNEL_ACTUAL  vmlinux" | tee "$OUT/vmlinux.sha256"
echo "kernel -> $OUT/vmlinux"

echo "done. Platform assets are firecracker + vmlinux."
echo "Apps (including fortune) are digest-pinned OCI images — deploy via the gateway."
