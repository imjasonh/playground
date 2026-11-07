#!/usr/bin/env bash
# Checks the emitted images against tools outside the proof:
#   1. GNU objdump decodes the encoder's test vectors to the expected text.
#   2. QEMU runs the counter image and its UART prints what the source
#      semantics says it should.
# Run `lake exe emit out` first.
set -euo pipefail

out="${1:-out}"
objdump="${OBJDUMP:-riscv64-unknown-elf-objdump}"

for tool in "${objdump}" qemu-system-riscv32; do
  if ! command -v "${tool}" >/dev/null; then
    echo "missing ${tool}" >&2
    exit 1
  fi
done

"${objdump}" -D -b binary -m riscv:rv32 -M no-aliases "${out}/encode-vectors.bin" \
  | grep -P '^\s+[0-9a-f]+:' \
  | awk -F'\t' '{print $3"\t"$4}' \
  | sed 's/\s*$//' > "${out}/encode-vectors.objdump"
diff -u "${out}/encode-vectors.txt" "${out}/encode-vectors.objdump"
echo "encoder matches ${objdump}"

timeout 20 qemu-system-riscv32 -machine virt -bios none -nographic -monitor none \
  -serial stdio -device "loader,file=${out}/qemu-counter.bin,addr=0x80000000" \
  > "${out}/qemu-counter.uart"
cmp "${out}/qemu-counter.expected" "${out}/qemu-counter.uart"
echo "QEMU UART output matches the source semantics: $(cat "${out}/qemu-counter.uart")"
