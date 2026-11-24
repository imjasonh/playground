#!/usr/bin/env bash
# Checks a signed release the way a device would: converts the Sigstore
# bundle to the bootloader's container, assembles a slot with the TUF part,
# runs the device's checks on the host, and boots the slot in Espressif's
# QEMU with a bootloader that pins the same root and the signer's identity.
#
# The bootloader pins C3_TUF_ROOT, which defaults to Sigstore's root in
# release/pinned-root.json. Set C3_TUF_ROOT=dev to check an image that
# fakestore signed, with a TUF part from the development repository.
#
# Usage: release/check.sh IMAGE BUNDLE TUF WORK_DIR
#
# TUF is the slot's TUF part, as release/package-tuf.sh or c3-ota
# tuf-package writes it. The signer's identity comes from these environment
# variables, which must match the Fulcio certificate exactly:
#   C3_ISSUER, C3_BUILD_SIGNER_URI, C3_REPOSITORY_ID, C3_OWNER_ID, C3_TRIGGER
# Set QEMU to the qemu-system-riscv32 binary if it isn't on PATH.

set -euo pipefail

if (($# != 4)); then
  echo "usage: $0 IMAGE BUNDLE TUF WORK_DIR" >&2
  exit 2
fi
image="$1"
bundle="$2"
tuf="$3"
mkdir -p "$4"
work="$(cd "$4" && pwd)"
root="$(cd "$(dirname "$0")/.." && pwd)"

: "${C3_ISSUER:?}" "${C3_BUILD_SIGNER_URI:?}" "${C3_REPOSITORY_ID:?}"
: "${C3_OWNER_ID:?}" "${C3_TRIGGER:?}"
tuf_root="${C3_TUF_ROOT:-release/pinned-root.json}"
if [[ "${tuf_root}" == dev ]]; then
  pinned="${root}/testdata/keys/tuf-dev-root.json"
else
  pinned="$(cd "${root}" && realpath "${tuf_root}")"
fi
cat >"${work}/policy" <<EOF
issuer=${C3_ISSUER}
build-signer-uri=${C3_BUILD_SIGNER_URI}
repository-id=${C3_REPOSITORY_ID}
owner-id=${C3_OWNER_ID}
trigger=${C3_TRIGGER}
EOF

# QEMU's eFuse file is disposable, and a production root requires burns.
(cd "${root}" && cargo build -q --locked -p c3-ota)
(cd "${root}" && C3_TUF_ROOT="${tuf_root}" C3_POLICY="${work}/policy" C3_EFUSE_BURN=on \
  cargo build -q --locked --release --target riscv32imc-unknown-none-elf -p c3-bootloader)
ota() {
  "${root}/target/debug/c3-ota" "$@"
}

ota container --bundle "${bundle}" --image "${image}" --out "${work}/container.bin"
ota slot --image "${image}" --bundle "${work}/container.bin" --tuf "${tuf}" \
  --out "${work}/slot.bin"
ota verify --slot "${work}/slot.bin" --pinned "${pinned}" --policy "${work}/policy"

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
