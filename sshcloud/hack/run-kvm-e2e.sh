#!/usr/bin/env bash
# Prepare Firecracker assets and run real KVM e2e tests (sleep/wake + migrate).
#
# Requires: /dev/kvm (rw), passwordless sudo for `ip` (TAP), curl, e2fsprogs, Go.
# Firecracker itself runs as the invoking user (not root).
#
# On GitHub Actions ubuntu-latest:
#   # udev rule for /dev/kvm (see test.yml)
#   bash hack/run-kvm-e2e.sh
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

if [[ ! -e /dev/kvm ]]; then
  echo "ERROR: /dev/kvm missing — nested virtualization not available on this host" >&2
  exit 1
fi
if [[ ! -r /dev/kvm || ! -w /dev/kvm ]]; then
  echo "ERROR: /dev/kvm not read/writable by $(id -un) (fix udev MODE=0666)" >&2
  ls -l /dev/kvm >&2 || true
  exit 1
fi
if [[ "$(id -u)" -eq 0 ]]; then
  echo "ERROR: do not run this script as root — Firecracker should run unprivileged." >&2
  echo "Use sudo only for the udev/apt setup; then: bash $0" >&2
  exit 1
fi
if ! sudo -n ip link show >/dev/null 2>&1; then
  echo "ERROR: need passwordless sudo for \`ip\` (TAP setup). On GHA runners this is available." >&2
  exit 1
fi

ASSETS="${SSHCLOUD_ASSETS:-$ROOT/_assets}"
mkdir -p "$ASSETS"

# Short work root — Firecracker unix socket paths are capped (~108 bytes).
export TMPDIR="${TMPDIR:-/tmp}"
export SSHCLOUD_WORK_ROOT="${SSHCLOUD_WORK_ROOT:-/tmp/sshcloud-kvm}"
mkdir -p "$SSHCLOUD_WORK_ROOT"
chmod 755 "$SSHCLOUD_WORK_ROOT"

echo "::group::Fetch Firecracker + kernel"
OUT="$ASSETS" bash "$ROOT/hack/fetch-firecracker-assets.sh"
echo "::endgroup::"

echo "::group::Build fortune guest + rootfs + guestinit"
CGO_ENABLED=0 go build -o "$ASSETS/fortune" ./cmd/fortune
CGO_ENABLED=0 GOOS=linux GOARCH=amd64 go build -o "$ASSETS/guestinit" ./cmd/guestinit
CA_KEY="$ASSETS/ssh_user_ca"
CA_PUB="$ASSETS/ssh_user_ca.pub"
if [[ ! -f "$CA_PUB" ]]; then
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
export SSHCLOUD_BOOT_SPEC="$ASSETS/fortune-rootfs.boot.json"
export SSHCLOUD_GUESTINIT="$ASSETS/guestinit"
export SSHCLOUD_CA_PUB="$CA_PUB"

echo "::group::KVM e2e tests"
LOG="$(mktemp)"
set +e
go test -tags=kvm -count=1 -timeout 10m -v ./internal/agent/ -run 'TestKVM' 2>&1 | tee "$LOG"
rc=${PIPESTATUS[0]}
set -e
if grep -E '^--- SKIP:' "$LOG"; then
  echo "ERROR: KVM tests must not be skipped" >&2
  exit 1
fi
for name in TestKVMSleepWake TestKVMCrossHostMigrate; do
  if ! grep -q "^--- PASS: ${name}" "$LOG"; then
    echo "ERROR: ${name} did not PASS" >&2
    exit 1
  fi
done
if [[ "$rc" -ne 0 ]]; then
  exit "$rc"
fi
echo "::endgroup::"

echo "KVM e2e passed (no skips)."
