#!/usr/bin/env bash
# Boots a c3-boot flash image once in Espressif's QEMU and saves the serial
# log. It stops QEMU when the demo application goes idle or the bootloader
# halts, or when a line matches BOOT_DONE if that's set, then prints the
# c3-boot and c3-demo lines of the log.
#
# Usage: qemu/boot.sh FLASH EFUSE LOG
# Set QEMU to the qemu-system-riscv32 binary if it isn't on PATH. FLASH and
# EFUSE are changed in place, as a device's flash and eFuses would be.

set -euo pipefail

if (($# != 3)); then
  echo "usage: $0 FLASH EFUSE LOG" >&2
  exit 2
fi
flash="$1"
efuse="$2"
log="$3"
qemu="${QEMU:-qemu-system-riscv32}"
done="${BOOT_DONE:-c3-demo: idle|c3-boot: halt}"

: >"${log}"
"${qemu}" -machine esp32c3 -display none -monitor none \
  -serial "file:${log}" \
  -drive "file=${flash},if=mtd,format=raw" \
  -drive "file=${efuse},if=none,format=raw,id=efuse" \
  -global driver=nvram.esp32c3.efuse,property=drive,value=efuse \
  >/dev/null 2>&1 &
pid=$!

waited=0
until grep -qE "${done}" "${log}"; do
  if ! kill -0 "${pid}" 2>/dev/null; then
    echo "QEMU exited before the boot finished" >&2
    exit 1
  fi
  if ((waited >= ${BOOT_TIMEOUT:-300})); then
    kill "${pid}" 2>/dev/null || true
    echo "no result after $((${BOOT_TIMEOUT:-300} / 10)) seconds" >&2
    exit 1
  fi
  sleep 0.1
  waited=$((waited + 1))
done
kill "${pid}" 2>/dev/null || true
wait "${pid}" 2>/dev/null || true
grep -E '^c3-' "${log}" || true
