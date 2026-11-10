#!/usr/bin/env bash
# Checks that the bootloader image builds reproducibly to the digest pinned
# in dev-image.sha256. The proofs cover one exact image, so a change to the
# bootloader, c3-verify, c3-crypto, a dependency, or the toolchain changes
# this digest on purpose and must update the file.
#
# The pinned image is the default test build: the public development genesis
# keys and no eFuse burns.
#
# Usage: bootloader/check-digest.sh [--update]

set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
pinned="${root}/bootloader/dev-image.sha256"
work="$(mktemp -d)"
trap 'rm -rf "${work}"' EXIT

cd "${root}"
cargo build -q --locked -p c3-ota
C3_GENESIS=dev C3_EFUSE_BURN=off cargo build -q --locked --release \
  --target riscv32imc-unknown-none-elf -p c3-bootloader
target/debug/c3-ota bootloader-image \
  --elf target/riscv32imc-unknown-none-elf/release/c3-bootloader --out "${work}/bootloader.bin"
digest="$(sha256sum "${work}/bootloader.bin" | cut -d' ' -f1)"

if [[ "${1:-}" == "--update" ]]; then
  echo "${digest}" >"${pinned}"
  echo "pinned ${digest}"
  exit 0
fi
if [[ "${digest}" != "$(cat "${pinned}")" ]]; then
  echo "bootloader image digest ${digest} doesn't match ${pinned}." >&2
  echo "If the change is intended, run bootloader/check-digest.sh --update." >&2
  exit 1
fi
echo "bootloader image digest matches: ${digest}"
