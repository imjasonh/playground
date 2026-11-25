#!/usr/bin/env bash
# Checks that the bootloader image builds reproducibly to the digest pinned
# in dev-image.sha256. The proofs cover one exact image, so a change to the
# bootloader, c3-verify, c3-crypto, a dependency, or the toolchain changes
# this digest on purpose and must update the file.
#
# The pinned image is the production build: Sigstore's root from
# release/pinned-root.json, the identity policy in release/policy, and eFuse
# burns on. --update also regenerates the function bytes that
# c3-boot-proofs' machine-code proofs are about (it needs the llvm-tools
# component) and the facts the proofs state about those bytes; a proof whose
# function's code changed shape then needs redoing.
#
# Usage: bootloader/check-digest.sh [--update]

set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
pinned="${root}/bootloader/dev-image.sha256"
work="$(mktemp -d)"
trap 'rm -rf "${work}"' EXIT

cd "${root}"
cargo build -q --locked -p c3-ota
C3_TUF_ROOT=release/pinned-root.json C3_EFUSE_BURN=on cargo build -q --locked --release \
  --target riscv32imc-unknown-none-elf -p c3-bootloader
target/debug/c3-ota bootloader-image \
  --elf target/riscv32imc-unknown-none-elf/release/c3-bootloader --out "${work}/bootloader.bin"
digest="$(sha256sum "${work}/bootloader.bin" | cut -d' ' -f1)"

if [[ "${1:-}" == "--update" ]]; then
  echo "${digest}" >"${pinned}"
  echo "pinned ${digest}"
  # The machine-code proofs are about function bytes from this image.
  nm="$(rustc --print sysroot)/lib/rustlib/x86_64-unknown-linux-gnu/bin/llvm-nm"
  proofs="${root}/../c3-boot-proofs"
  python3 "${proofs}/scripts/extract-functions.py" "${work}/bootloader.bin" \
    target/riscv32imc-unknown-none-elf/release/c3-bootloader "${nm}" \
    "${proofs}/C3BootProofs/Image/Bootloader.lean" \
    "${proofs}"/C3BootProofs/Image/BootloaderData{,2,3,4,5,6,7,8}.lean
  echo "regenerated c3-boot-proofs/C3BootProofs/Image/Bootloader.lean and BootloaderData*.lean"
  # The proofs' decode lemmas, code chunks, and straight-line blocks follow
  # from those bytes.
  (cd "${proofs}" && python3 scripts/image-facts.py)
  echo "regenerated the image facts in c3-boot-proofs/C3BootProofs/Proofs"
  exit 0
fi
if [[ "${digest}" != "$(cat "${pinned}")" ]]; then
  echo "bootloader image digest ${digest} doesn't match ${pinned}." >&2
  echo "If the change is intended, run bootloader/check-digest.sh --update." >&2
  exit 1
fi
echo "bootloader image digest matches: ${digest}"
