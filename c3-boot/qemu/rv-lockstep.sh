#!/usr/bin/env bash
# Runs the lockstep test of the Lean RV32 model against Espressif's QEMU.
# For each batch, it generates random RV32IMC sequences (c3-ota's rv_cases
# example), builds the c3-rvtest firmware around them, runs it in QEMU,
# and checks that c3-boot-proofs' rv-check gets the same registers and
# memory from the same starting state.
#
# Usage: qemu/rv-lockstep.sh [WORK_DIR]
# Environment: QEMU (qemu-system-riscv32), RV_CHECK (the rv-check binary,
# default ../c3-boot-proofs/.lake/build/bin/rv-check), RV_BATCHES (default
# 20), RV_CASES (cases per batch, default 150).

set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
work="${1:-$(mktemp -d)}"
check="${RV_CHECK:-${root}/../c3-boot-proofs/.lake/build/bin/rv-check}"
batches="${RV_BATCHES:-20}"
cases="${RV_CASES:-150}"
mkdir -p "${work}"

(cd "${root}" && cargo build -q --locked -p c3-ota)
total=0
for batch in $(seq 1 "${batches}"); do
  dir="${work}/batch-${batch}"
  mkdir -p "${dir}"
  (cd "${root}" && cargo run -q --locked -p c3-ota --example rv_cases -- "${dir}" "${batch}" "${cases}")
  (cd "${root}" && C3_RVTEST_CASES="${dir}" cargo build -q --locked --release \
    --target riscv32imc-unknown-none-elf -p c3-rvtest)
  "${root}/target/debug/c3-ota" bootloader-image \
    --elf "${root}/target/riscv32imc-unknown-none-elf/release/c3-rvtest" --out "${dir}/firmware.bin"
  "${root}/target/debug/c3-ota" flash --bootloader "${dir}/firmware.bin" --out "${dir}/flash.bin"
  dd if=/dev/zero of="${dir}/efuse.bin" bs=1024 count=1 status=none
  BOOT_DONE='rvtest: done' BOOT_TIMEOUT=1200 \
    bash "${root}/qemu/boot.sh" "${dir}/flash.bin" "${dir}/efuse.bin" "${dir}/serial.log"
  python3 - "${dir}" "${cases}" <<'PY'
import re
import sys

d, want = sys.argv[1], int(sys.argv[2])
cases = {}
for line in open(f"{d}/cases.txt"):
    _, n, code, regs, mem = line.split()
    cases[n] = (code, regs, mem)
out = []
pattern = re.compile(r"^rv (\d+) SEQ=([0-9a-f]{8}) R=([0-9a-f]{248}) M=([0-9a-f]{512})$")
for line in open(f"{d}/serial.log", errors="replace"):
    m = pattern.match(line.strip())
    if m:
        n, seq, regs_out, mem_out = m.groups()
        code, regs, mem = cases[n]
        out.append(f"rv {seq} {code} {regs} {mem} | {regs_out} {mem_out}")
if len(out) != want:
    sys.exit(f"QEMU reported {len(out)} of {want} cases")
with open(f"{d}/qemu.txt", "w") as f:
    f.write("\n".join(out) + "\n")
PY
  "${check}" <"${dir}/qemu.txt" >"${dir}/lean.txt"
  if ! diff -q "${dir}/qemu.txt" "${dir}/lean.txt" >/dev/null; then
    echo "batch ${batch}: the Lean model and QEMU disagree:" >&2
    diff "${dir}/qemu.txt" "${dir}/lean.txt" | head -4 | cut -c1-300 >&2
    exit 1
  fi
  total=$((total + cases))
  echo "batch ${batch}: ${cases} cases agree"
done
echo "all ${total} cases agree (${work})"
