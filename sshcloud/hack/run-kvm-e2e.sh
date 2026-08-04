#!/usr/bin/env bash
# Prepare Firecracker assets and run real KVM e2e tests (sleep/wake + migrate).
#
# Requires: /dev/kvm, root (or CAP_NET_ADMIN) for TAP, curl, e2fsprogs, iproute2, Go.
# On GitHub Actions ubuntu-latest, enable KVM first:
#   echo 'KERNEL=="kvm", GROUP="kvm", MODE="0666", OPTIONS+="static_node=kvm"' \
#     | sudo tee /etc/udev/rules.d/99-kvm4all.rules
#   sudo udevadm control --reload-rules && sudo udevadm trigger --name-match=kvm
#   sudo bash hack/run-kvm-e2e.sh
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

if [[ ! -e /dev/kvm ]]; then
  echo "ERROR: /dev/kvm missing — nested virtualization not available on this host" >&2
  exit 1
fi
if [[ ! -r /dev/kvm || ! -w /dev/kvm ]]; then
  echo "ERROR: /dev/kvm not read/writable by $(id -u) (fix udev MODE=0666 or run as root)" >&2
  ls -l /dev/kvm >&2 || true
  exit 1
fi
if [[ "$(id -u)" -ne 0 ]]; then
  echo "ERROR: must run as root for TAP (CAP_NET_ADMIN). Example: sudo -E bash $0" >&2
  exit 1
fi

ASSETS="${SSHCLOUD_ASSETS:-$ROOT/_assets}"
mkdir -p "$ASSETS"

echo "::group::Fetch Firecracker + kernel"
OUT="$ASSETS" bash "$ROOT/hack/fetch-firecracker-assets.sh"
echo "::endgroup::"

echo "::group::Build fortune guest + rootfs"
# Guest binary must be linux; CGO off for a portable static-ish binary.
CGO_ENABLED=0 go build -o "$ASSETS/fortune" ./cmd/fortune
CA_KEY="$ASSETS/ssh_user_ca"
CA_PUB="$ASSETS/ssh_user_ca.pub"
if [[ ! -f "$CA_PUB" ]]; then
  # Mint a CA via a tiny Go helper (userca.LoadOrGenerate).
  go run ./hack/genuca -out "$CA_KEY"
fi
go run ./cmd/mkrootfs \
  -fortune "$ASSETS/fortune" \
  -ca-pub "$CA_PUB" \
  -out "$ASSETS/fortune-rootfs.ext4" \
  -size-mb 64
echo "::endgroup::"

export SSHCLOUD_FIRECRACKER="$ASSETS/firecracker"
export SSHCLOUD_KERNEL="$ASSETS/vmlinux"
export SSHCLOUD_ROOTFS="$ASSETS/fortune-rootfs.ext4"
export SSHCLOUD_CA_PUB="$CA_PUB"

echo "::group::KVM e2e tests"
# Preserve GOPATH/GOCACHE when invoked via sudo -E from CI.
go test -tags=kvm -count=1 -timeout 10m -v ./internal/agent/ -run 'TestKVM'
echo "::endgroup::"

echo "KVM e2e passed."
