#!/usr/bin/env bash
# Boots the burns-off bootloader image on the Lean RV32 model
# (c3-boot-proofs' boot-sim) and in Espressif's QEMU (qemu/rsp-trace.py),
# and checks that both make the same ROM calls with the same arguments,
# end the same way, and leave the same flash. The model runs the whole
# image: SHA-256, ECDSA, Ed25519, and the parsers, as compiled.
#
# It uses the slots that qemu/scenarios.sh built, for four boots: an image
# signed by another workflow and one with a stale timestamp, which both
# halt, and a trial boot of version 2 that rewrites the boot state and
# jumps to it, at eFuse level 0 and at level 1. Each boot must also end the
# way the scenario expects.
#
# Usage: qemu/boot-lockstep.sh SCENARIO_WORK_DIR [OUT_DIR]
# Environment: QEMU (qemu-system-riscv32), BOOT_SIM (the boot-sim binary,
# default ../c3-boot-proofs/.lake/build/bin/boot-sim).

set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
scen="$1"
out="${2:-$(mktemp -d)}"
qemu="${QEMU:-qemu-system-riscv32}"
sim="${BOOT_SIM:-${root}/../c3-boot-proofs/.lake/build/bin/boot-sim}"
mkdir -p "${out}"

# The ELF behind the scenarios' burns-off image, for the halt address.
cd "${root}"
cargo build -q --locked -p c3-ota
C3_GENESIS=dev C3_EFUSE_BURN=off cargo build -q --locked --release \
  --target riscv32imc-unknown-none-elf -p c3-bootloader
elf="${root}/target/riscv32imc-unknown-none-elf/release/c3-bootloader"
ota() {
  "${root}/target/debug/c3-ota" "$@"
}
ota bootloader-image --elf "${elf}" --out "${out}/bootloader.bin"
if ! cmp -s "${out}/bootloader.bin" "${scen}/bootloader-burn-off.bin"; then
  echo "the rebuilt bootloader doesn't match ${scen}/bootloader-burn-off.bin" >&2
  exit 1
fi
nm="$(rustc --print sysroot)/lib/rustlib/x86_64-unknown-linux-gnu/bin/llvm-nm"
[[ -x "${nm}" ]] || nm=nm
halt="$("${nm}" -C "${elf}" | awk '$3 == "c3_bootloader::halt" { print $1 }')"
[[ -n "${halt}" ]] || {
  echo "no c3_bootloader::halt symbol in ${elf}" >&2
  exit 1
}

ota record --preferred b --trial b --boots 3 --confirmed a --out "${out}/trial.record"
ota flash --bootloader "${scen}/bootloader-burn-off.bin" --slot-a "${scen}/slot-v1-wrong-identity" \
  --out "${out}/wrong-identity.flash"
ota flash --bootloader "${scen}/bootloader-burn-off.bin" --slot-a "${scen}/slot-v1-stale" \
  --out "${out}/stale.flash"
ota flash --bootloader "${scen}/bootloader-burn-off.bin" --record "${out}/trial.record" \
  --slot-a "${scen}/slot-v1" --slot-b "${scen}/slot-v2" --out "${out}/trial.flash"

cp "${out}/trial.flash" "${out}/trial-level1.flash"

declare -A expect=(
  [wrong-identity]="halt e5"
  [stale]="halt e5"
  [trial]="jump 40380000 1"
  [trial-level1]="jump 40380000 1"
)
for name in wrong-identity stale trial trial-level1; do
  dd if=/dev/zero of="${out}/${name}.efuse" bs=1024 count=1 status=none
  if [[ "${name}" == trial-level1 ]]; then
    # SECURE_VERSION bit 0: block 0 bit 142.
    printf '\x40' | dd of="${out}/${name}.efuse" bs=1 seek=17 conv=notrunc status=none
  fi
  cp "${out}/${name}.flash" "${out}/${name}.qemu.flash"
  cp "${out}/${name}.efuse" "${out}/${name}.qemu.efuse"
  python3 "${root}/qemu/rsp-trace.py" "${qemu}" "${out}/${name}.qemu.flash" \
    "${out}/${name}.qemu.efuse" "${halt}" >"${out}/${name}.qemu.txt"
  "${sim}" "${out}/${name}.flash" "${out}/${name}.efuse" "${halt}" "${out}/${name}.lean.flash" \
    >"${out}/${name}.lean.txt" 2>"${out}/${name}.lean.err"
  if ! diff -q "${out}/${name}.qemu.txt" "${out}/${name}.lean.txt" >/dev/null; then
    echo "${name}: the Lean model and QEMU make different ROM calls:" >&2
    diff "${out}/${name}.qemu.txt" "${out}/${name}.lean.txt" | head -8 >&2
    exit 1
  fi
  if ! cmp -s "${out}/${name}.qemu.flash" "${out}/${name}.lean.flash"; then
    echo "${name}: the Lean model and QEMU leave different flash" >&2
    exit 1
  fi
  if [[ "$(tail -1 "${out}/${name}.lean.txt")" != "${expect[${name}]}" ]]; then
    echo "${name}: ended with '$(tail -1 "${out}/${name}.lean.txt")', not '${expect[${name}]}'" >&2
    exit 1
  fi
  if (($(wc -l <"${out}/${name}.lean.txt") < 100)); then
    echo "${name}: only $(wc -l <"${out}/${name}.lean.txt") ROM calls" >&2
    exit 1
  fi
  echo "${name}: $(wc -l <"${out}/${name}.lean.txt") events agree, ending" \
    "'$(tail -1 "${out}/${name}.lean.txt")'; $(cat "${out}/${name}.lean.err")"
done
echo "all boots agree (${out})"
