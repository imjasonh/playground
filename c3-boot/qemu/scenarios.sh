#!/usr/bin/env bash
# Boots c3-boot in Espressif's QEMU through an update's life: first boot,
# a tampered image, a trial update, the security-level raise, a rollback
# attempt, a failed trial, a stale key set, a key rotation, and power cuts
# during a trial and during a security-level raise.
#
# Every boot after the first reuses the same flash and eFuse files, so the
# boot-state writes and eFuse burns carry over, as on a device. Images are
# signed by fakestore and the trust roots by the public development genesis
# keys, so nothing here is fit for a real device.
#
# Usage: qemu/scenarios.sh [WORK_DIR]
# Set QEMU to the qemu-system-riscv32 binary if it isn't on PATH.

set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
work="${1:-$(mktemp -d)}"
qemu="${QEMU:-qemu-system-riscv32}"
keys="${root}/testdata/keys"
target="${root}/target/riscv32imc-unknown-none-elf/release"
mkdir -p "${work}"

ota() {
  "${root}/target/debug/c3-ota" "$@"
}

fail() {
  echo "FAIL: $*" >&2
  exit 1
}

# patch FILE OFFSET SOURCE writes SOURCE into FILE at OFFSET.
patch() {
  dd if="$3" of="$1" bs=1 seek="$(($2))" conv=notrunc status=none
}

# flip FILE OFFSET inverts one byte of FILE.
flip() {
  python3 - "$1" "$(($2))" <<'EOF'
import sys
path, at = sys.argv[1], int(sys.argv[2])
with open(path, "r+b") as f:
    f.seek(at)
    b = f.read(1)[0]
    f.seek(at)
    f.write(bytes([b ^ 0xFF]))
EOF
}

# boot NAME [FLASH [EFUSE]] runs one boot and saves its serial log as
# NAME.log.
boot() {
  local name="$1" flash="${2:-${work}/flash.bin}" efuse="${3:-${work}/efuse.bin}"
  current="${work}/${name}.log"
  echo "--- ${name}"
  QEMU="${qemu}" bash "${root}/qemu/boot.sh" "${flash}" "${efuse}" "${current}" ||
    fail "${name}: boot didn't finish"
}

expect() {
  grep -qF "$1" "${current}" || fail "$(basename "${current}" .log): missing '$1'"
}

expect_not() {
  if grep -qF "$1" "${current}"; then
    fail "$(basename "${current}" .log): unexpected '$1'"
  fi
}

# The bootloader logs a rejection as the c3_verify::Error variant's index
# in hexadecimal.
error_code() {
  awk '/^pub enum Error/,/^}/' "${root}/verify/src/error.rs" |
    grep -E '^    [A-Z][A-Za-z]*,' | grep -n "^    $1," | cut -d: -f1 |
    { read -r n; printf '%x' "$((n - 1))"; }
}
bad_signature="$(error_code BadSignature)"
bad_level="$(error_code BadLevel)"

# cut NAME DELAY_MS starts a boot and kills QEMU after DELAY_MS
# milliseconds, as a power cut would stop the chip.
cut() {
  local log="${work}/$1.log"
  : >"${log}"
  "${qemu}" -machine esp32c3 -display none -monitor none \
    -serial "file:${log}" \
    -drive "file=${work}/flash.bin,if=mtd,format=raw" \
    -drive "file=${work}/efuse.bin,if=none,format=raw,id=efuse" \
    -global driver=nvram.esp32c3.efuse,property=drive,value=efuse \
    >/dev/null 2>&1 &
  local pid=$!
  sleep "$(printf '0.%03d' "$2")"
  # The demo application never exits, so QEMU must still be running.
  kill -9 "${pid}" 2>/dev/null || fail "$1: QEMU exited before the cut"
  wait "${pid}" 2>/dev/null || true
}

# set_secure_version EFUSE BITS... sets SECURE_VERSION bits (0 through 15)
# in a QEMU eFuse file, which holds block 0 from byte 0. SECURE_VERSION is
# block 0 bits 142 through 157.
set_secure_version() {
  python3 - "$@" <<'EOF'
import sys

path, bits = sys.argv[1], [int(b) for b in sys.argv[2:]]
with open(path, "r+b") as f:
    data = bytearray(f.read())
    for b in bits:
        at = 142 + b
        data[at // 8] |= 1 << (at % 8)
    f.seek(0)
    f.write(data)
EOF
}

# secure_version_bits EFUSE prints the SECURE_VERSION bits that are set.
secure_version_bits() {
  python3 - "$1" <<'EOF'
import sys

data = open(sys.argv[1], "rb").read()
print(" ".join(str(b) for b in range(16) if data[(142 + b) // 8] >> ((142 + b) % 8) & 1))
EOF
}

# levels LOG... prints every security level the bootloader read, in order.
levels() {
  cat "$@" | tr -d '\r' | sed -n 's/^c3-boot: security level \([0-9a-f]*\)$/\1/p'
}

# expect_monotone LOG... fails if the security level ever went down, or if
# the logs show no level at all.
expect_monotone() {
  local previous=0 level seen=0
  for level in $(levels "$@"); do
    seen=$((seen + 1))
    if ((16#${level} < previous)); then
      fail "security level went from ${previous} to $((16#${level}))"
    fi
    previous=$((16#${level}))
  done
  ((seen > 0)) || fail "no security level in the logs"
}

# record ARGS... writes the same boot-state record to both copies.
record() {
  ota record "$@" --out "${work}/record"
  patch "${work}/flash.bin" 0x28000 "${work}/record"
  patch "${work}/flash.bin" 0x29000 "${work}/record"
}

# Build.
(cd "${root}" && cargo build -q --locked -p c3-ota)
# The QEMU eFuse file is disposable, so these scenarios burn eFuses. A second
# bootloader, built the default way, never does.
for burn in off on; do
  (cd "${root}" && C3_GENESIS=dev C3_EFUSE_BURN="${burn}" cargo build -q --locked --release \
    --target riscv32imc-unknown-none-elf -p c3-bootloader)
  ota bootloader-image --elf "${target}/c3-bootloader" --out "${work}/bootloader-burn-${burn}.bin"
done
cp "${work}/bootloader-burn-on.bin" "${work}/bootloader.bin"
# Version 5 jumps from level 3 to 6, so its raise burns three bits.
# Version 6 never confirms itself, so its trial expires.
security_versions=(0 0 1 2 3 6 6)
for v in 1 2 3 4 5 6; do
  no_confirm=()
  if ((v == 6)); then
    no_confirm=(C3_DEMO_NO_CONFIRM=1)
  fi
  (cd "${root}" && env "${no_confirm[@]}" C3_DEMO_VERSION="${v}" cargo build -q --locked \
    --release --target riscv32imc-unknown-none-elf -p c3-demo-app)
  ota pack --elf "${target}/c3-demo-app" --security-version "${security_versions[v]}" \
    --out "${work}/app${v}.img"
done

# Sign each image with fakestore.
(cd "${root}/fakestore" && go run . init -dir "${work}/fakestore" >/dev/null)
for v in 1 2 3 4 5 6; do
  (cd "${root}/fakestore" && go run . sign -dir "${work}/fakestore" \
    -artifact "${work}/app${v}.img" -out "${work}/app${v}.json")
  ota container --bundle "${work}/app${v}.json" --image "${work}/app${v}.img" \
    --out "${work}/app${v}.bundle"
done

# Trust roots. Level 0 and 1 use the genesis keys. Level 2 rotates to a new
# key set, authorized by two genesis keys.
genesis="0=${keys}/genesis-dev-1.seed,1=${keys}/genesis-dev-2.seed"
rotated_hex=()
for i in 1 2 3 4; do
  printf '%064x\n' "$((0x5100 + i))" >"${work}/rotated-${i}.seed"
  rotated_hex+=("$(ota pubkey --seed "${work}/rotated-${i}.seed")")
done
rotated="0=${work}/rotated-1.seed,1=${work}/rotated-2.seed"
policy=(
  --trusted-root "${work}/fakestore/trusted_root.json"
  --issuer https://token.actions.githubusercontent.com
  --build-signer-uri https://github.com/imjasonh/playground/.github/workflows/c3-release.yml@refs/heads/main
  --repository-id 1234 --owner-id 5678 --trigger push
)
ota chain --out "${work}/chain0"
ota link --level 2 --keys "$(IFS=,; echo "${rotated_hex[*]}")" --signers "${genesis}" \
  --out "${work}/link2"
ota chain --links "${work}/link2" --out "${work}/chain2"
ota blob "${policy[@]}" --level 0 --signers "${genesis}" --out "${work}/blob0"
ota blob "${policy[@]}" --level 1 --signers "${genesis}" --out "${work}/blob1"
ota blob "${policy[@]}" --level 2 --signers "${rotated}" --out "${work}/blob2"
ota blob "${policy[@]}" --level 2 --signers "${genesis}" --out "${work}/blob2-stale"
ota blob "${policy[@]}" --level 3 --signers "${rotated}" --out "${work}/blob3"
ota blob "${policy[@]}" --level 6 --signers "${rotated}" --out "${work}/blob6"

slot() {
  ota slot --image "${work}/app$1.img" --bundle "${work}/app$1.bundle" \
    --chain "${work}/$2" --blob "${work}/$3" --out "${work}/$4"
}
slot 1 chain0 blob0 slot-v1
slot 2 chain0 blob1 slot-v2
slot 3 chain2 blob2 slot-v3
slot 3 chain2 blob2-stale slot-v3-stale
slot 4 chain2 blob3 slot-v4
slot 5 chain2 blob6 slot-v5
slot 6 chain2 blob6 slot-v6
cp "${work}/slot-v3" "${work}/slot-v3-tampered"
flip "${work}/slot-v3-tampered" 0x10100

# A blank eFuse block and a flash with only version 1 in slot A.
dd if=/dev/zero of="${work}/efuse.bin" bs=1024 count=1 status=none
ota flash --bootloader "${work}/bootloader.bin" --slot-a "${work}/slot-v1" \
  --out "${work}/flash.bin"

boot first-boot
expect "c3-boot: security level 0"
expect "c3-demo: running from slot 0, version 1"
expect "c3-demo: flash mapping ok"
expect "c3-demo: confirmed slot 0"

cp "${work}/flash.bin" "${work}/flash-tampered.bin"
flip "${work}/flash-tampered.bin" "$((0x30000 + 0x10100))"
boot tampered "${work}/flash-tampered.bin"
expect "c3-boot: slot rejected ${bad_signature}"
expect "c3-boot: halt e5"
expect_not "c3-demo:"

patch "${work}/flash.bin" 0x210000 "${work}/slot-v2"
record --preferred b --trial b --boots 3 --confirmed a --generation 10
boot trial-update
expect "c3-demo: running from slot 1, version 2"
expect "c3-demo: confirmed slot 1"
expect_not "raising security level"

boot level-raise
expect "c3-boot: security level 0"
expect "c3-boot: raising security level to 1"
expect "c3-demo: running from slot 1, version 2"

boot after-raise
expect "c3-boot: security level 1"
expect_not "raising security level"
expect "c3-demo: running from slot 1, version 2"

record --preferred a --confirmed a,b --generation 20
boot rollback
expect "c3-boot: slot rejected ${bad_level}"
expect "c3-demo: running from slot 1, version 2"

patch "${work}/flash.bin" 0x30000 "${work}/slot-v3-tampered"
record --preferred a --trial a --boots 3 --confirmed b --generation 30
boot failed-trial
expect "c3-boot: slot rejected ${bad_signature}"
expect "c3-demo: running from slot 1, version 2"

patch "${work}/flash.bin" 0x30000 "${work}/slot-v3-stale"
record --preferred a --trial a --boots 3 --confirmed b --generation 40
boot stale-keys
expect "c3-boot: slot rejected ${bad_signature}"
expect "c3-demo: running from slot 1, version 2"

patch "${work}/flash.bin" 0x30000 "${work}/slot-v3"
record --preferred a --trial a --boots 3 --confirmed b --generation 50
boot rotation-trial
expect "c3-demo: running from slot 0, version 3"
expect "c3-demo: confirmed slot 0"
expect_not "raising security level"

boot rotation-raise
expect "c3-boot: raising security level to 2"
expect "c3-demo: running from slot 0, version 3"

boot after-rotation
expect "c3-boot: security level 2"
expect "c3-demo: running from slot 0, version 3"

# Power cuts at seeded random points: first during trial boots of version 4
# at level 3, then during boots that raise the level from 3 to 6. The cuts in
# each phase run one after another on the same flash and eFuse files, as
# repeated cuts would on a device. Every boot after the cuts must still
# succeed, and the level must never go down.
RANDOM=3164
patch "${work}/flash.bin" 0x210000 "${work}/slot-v4"
record --preferred a --trial b --boots 3 --confirmed a --generation 60
cut_logs=()
for i in $(seq 1 12); do
  cut "cut-trial-${i}" "$((RANDOM % 300))"
  cut_logs+=("${work}/cut-trial-${i}.log")
done
boot after-trial-cuts
expect_not "c3-boot: halt"
expect "c3-demo: idle"
if ! grep -qE '^c3-demo: running from slot (0, version 3|1, version 4)\b' "${current}"; then
  fail "after-trial-cuts: booted neither version 3 from A nor version 4 from B"
fi
expect_monotone "${cut_logs[@]}" "${current}"

# Version 5 in slot A, already confirmed, so the next boot raises the level
# from 3 to 6 before it jumps, and the cuts land before, between, and after
# the three burns.
patch "${work}/flash.bin" 0x30000 "${work}/slot-v5"
record --preferred a --confirmed a,b --generation 70
cp "${work}/flash.bin" "${work}/flash-before-raise.bin"
cp "${work}/efuse.bin" "${work}/efuse-before-raise.bin"
raise_logs=()
for i in $(seq 1 16); do
  cut "cut-raise-${i}" "$((RANDOM % 300))"
  raise_logs+=("${work}/cut-raise-${i}.log")
done
boot after-raise-cuts
expect_not "c3-boot: halt"
expect "c3-demo: running from slot 0, version 5"
boot after-raise-cuts-2
expect "c3-boot: security level 6"
expect "c3-demo: running from slot 0, version 5"
expect_monotone "${cut_logs[@]}" "${work}/after-trial-cuts.log" "${raise_logs[@]}" \
  "${work}/after-raise-cuts.log" "${current}"
echo "levels read across the cut boots: $(levels "${raise_logs[@]}" | tr '\n' ' ')"

# A raise from 3 to 6 that a cut stopped after one bit, and one that left a
# gap in the bits. Both finish at 6.
for partial in "0 1 2 3" "0 1 2 5"; do
  name="partial-raise-${partial// /}"
  cp "${work}/flash-before-raise.bin" "${work}/${name}.flash"
  cp "${work}/efuse-before-raise.bin" "${work}/${name}.efuse"
  # shellcheck disable=SC2086 # the bit list is meant to split
  set_secure_version "${work}/${name}.efuse" ${partial}
  boot "${name}" "${work}/${name}.flash" "${work}/${name}.efuse"
  expect "c3-boot: security level 4"
  expect "c3-boot: raising security level to 6"
  expect "c3-demo: running from slot 0, version 5"
  [[ "$(secure_version_bits "${work}/${name}.efuse" | wc -w)" == 6 ]] ||
    fail "${name}: SECURE_VERSION bits $(secure_version_bits "${work}/${name}.efuse")"
done

# A trial that the application never confirms boots three times, then the
# bootloader ends it and boots the preferred slot.
patch "${work}/flash.bin" 0x210000 "${work}/slot-v6"
record --preferred a --trial b --boots 3 --confirmed a --generation 80
for i in 1 2 3; do
  boot "unconfirmed-trial-${i}"
  expect "c3-demo: running from slot 1, version 6"
  expect_not "c3-demo: confirmed"
done
boot trial-expired
expect "c3-demo: running from slot 0, version 5"
boot after-trial-expired
expect "c3-demo: running from slot 0, version 5"

# A bootloader built without C3_EFUSE_BURN=on boots a confirmed level 6
# slot on a level 3 board without burning anything.
cp "${work}/flash-before-raise.bin" "${work}/burn-off.flash"
cp "${work}/efuse-before-raise.bin" "${work}/burn-off.efuse"
patch "${work}/burn-off.flash" 0 "${work}/bootloader-burn-off.bin"
boot burn-off "${work}/burn-off.flash" "${work}/burn-off.efuse"
expect "c3-boot: security level 3"
expect "c3-boot: eFuse burns off; not raising security level to 6"
expect "c3-demo: running from slot 0, version 5"
cmp -s "${work}/efuse-before-raise.bin" "${work}/burn-off.efuse" ||
  fail "burn-off: the eFuse file changed"

# With SECURE_VERSION write-disabled (block 0 bit 18), a raise fails. A
# development build boots the accepted slot anyway, so a test board that an
# application damaged this way stays updatable.
cp "${work}/flash-before-raise.bin" "${work}/write-disabled.flash"
cp "${work}/efuse-before-raise.bin" "${work}/write-disabled.efuse"
python3 - "${work}/write-disabled.efuse" <<'EOF'
import sys

with open(sys.argv[1], "r+b") as f:
    data = bytearray(f.read())
    data[18 // 8] |= 1 << (18 % 8)
    f.seek(0)
    f.write(data)
EOF
boot write-disabled "${work}/write-disabled.flash" "${work}/write-disabled.efuse"
expect "c3-boot: raising security level to 6"
expect "c3-boot: raise failed; booting without it"
expect "c3-demo: running from slot 0, version 5"
[[ "$(secure_version_bits "${work}/write-disabled.efuse")" == "0 1 2" ]] ||
  fail "write-disabled: SECURE_VERSION bits $(secure_version_bits "${work}/write-disabled.efuse")"

echo "all scenarios passed (${work})"
