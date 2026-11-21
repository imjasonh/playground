#!/usr/bin/env bash
# Checks a signed release the way a device would: converts the Sigstore
# bundle to the bootloader's container, builds a trust-root blob that pins
# the signer's identity, assembles a slot, runs the device's checks on the
# host, and boots the slot in Espressif's QEMU.
#
# The trust-root blob is signed by the public development genesis keys, and
# the bootloader is built with them, so the slot this writes is for tests
# only. A production blob is signed offline by the genesis or rotated keys.
#
# Usage: release/check.sh IMAGE BUNDLE TRUSTED_ROOT WORK_DIR
#
# The signer's identity comes from these environment variables, which must
# match the Fulcio certificate exactly:
#   C3_ISSUER, C3_BUILD_SIGNER_URI, C3_REPOSITORY_ID, C3_OWNER_ID, C3_TRIGGER
# Set QEMU to the qemu-system-riscv32 binary if it isn't on PATH.

set -euo pipefail

if (($# != 4)); then
  echo "usage: $0 IMAGE BUNDLE TRUSTED_ROOT WORK_DIR" >&2
  exit 2
fi
image="$1"
bundle="$2"
trusted_root="$3"
work="$4"
root="$(cd "$(dirname "$0")/.." && pwd)"
keys="${root}/testdata/keys"
mkdir -p "${work}"

: "${C3_ISSUER:?}" "${C3_BUILD_SIGNER_URI:?}" "${C3_REPOSITORY_ID:?}"
: "${C3_OWNER_ID:?}" "${C3_TRIGGER:?}"

(cd "${root}" && cargo build -q --locked -p c3-ota)
(cd "${root}" && C3_GENESIS=dev cargo build -q --locked --release \
  --target riscv32imc-unknown-none-elf -p c3-bootloader)
ota() {
  "${root}/target/debug/c3-ota" "$@"
}

ota container --bundle "${bundle}" --image "${image}" --out "${work}/container.bin"
ota chain --out "${work}/chain.bin"
ota blob --trusted-root "${trusted_root}" --level 0 \
  --issuer "${C3_ISSUER}" --build-signer-uri "${C3_BUILD_SIGNER_URI}" \
  --repository-id "${C3_REPOSITORY_ID}" --owner-id "${C3_OWNER_ID}" \
  --trigger "${C3_TRIGGER}" \
  --signers "0=${keys}/genesis-dev-1.seed,1=${keys}/genesis-dev-2.seed" \
  --out "${work}/blob.bin"
ota slot --image "${image}" --bundle "${work}/container.bin" \
  --chain "${work}/chain.bin" --blob "${work}/blob.bin" --out "${work}/slot.bin"
ota verify --slot "${work}/slot.bin" --genesis "${keys}/genesis-dev.pub"

ota bootloader-image \
  --elf "${root}/target/riscv32imc-unknown-none-elf/release/c3-bootloader" \
  --out "${work}/bootloader.bin"
ota flash --bootloader "${work}/bootloader.bin" --slot-a "${work}/slot.bin" \
  --out "${work}/flash.bin"
dd if=/dev/zero of="${work}/efuse.bin" bs=1024 count=1 status=none
bash "${root}/qemu/boot.sh" "${work}/flash.bin" "${work}/efuse.bin" "${work}/boot.log"
if ! grep -q '^c3-demo: running from slot 0' "${work}/boot.log"; then
  echo "the bootloader didn't boot the signed slot" >&2
  exit 1
fi
echo "release checked: ${work}/slot.bin"
