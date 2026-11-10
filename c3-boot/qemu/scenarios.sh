#!/usr/bin/env bash
# Boots c3-boot in Espressif's QEMU through an update's life: first boot,
# a tampered image, a trial update, the security-level raise, a rollback
# attempt, a failed trial, a stale key set, and a key rotation.
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

# boot NAME [FLASH] runs one boot and saves its serial log as NAME.log.
boot() {
  local name="$1" flash="${2:-${work}/flash.bin}"
  local log="${work}/${name}.log"
  : >"${log}"
  "${qemu}" -machine esp32c3 -display none -monitor none \
    -serial "file:${log}" \
    -drive "file=${flash},if=mtd,format=raw" \
    -drive "file=${work}/efuse.bin,if=none,format=raw,id=efuse" \
    -global driver=nvram.esp32c3.efuse,property=drive,value=efuse &
  local pid=$!
  local waited=0
  until grep -qE 'c3-demo: idle|c3-boot: halt' "${log}"; do
    if ((waited >= 300)); then
      kill "${pid}" 2>/dev/null || true
      fail "${name}: no result after 30 seconds"
    fi
    sleep 0.1
    waited=$((waited + 1))
  done
  kill "${pid}" 2>/dev/null || true
  wait "${pid}" 2>/dev/null || true
  current="${log}"
  echo "--- ${name}"
  grep -E '^c3-' "${log}"
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

# record ARGS... writes the same boot-state record to both copies.
record() {
  ota record "$@" --out "${work}/record"
  patch "${work}/flash.bin" 0x28000 "${work}/record"
  patch "${work}/flash.bin" 0x29000 "${work}/record"
}

# Build.
(cd "${root}" && cargo build -q --locked -p c3-ota)
(cd "${root}" && C3_GENESIS=dev cargo build -q --locked --release \
  --target riscv32imc-unknown-none-elf -p c3-bootloader)
ota bootloader-image --elf "${target}/c3-bootloader" --out "${work}/bootloader.bin"
for v in 1 2 3; do
  (cd "${root}" && C3_DEMO_VERSION="${v}" cargo build -q --locked --release \
    --target riscv32imc-unknown-none-elf -p c3-demo-app)
  ota pack --elf "${target}/c3-demo-app" --security-version "$((v - 1))" \
    --out "${work}/app${v}.img"
done

# Sign each image with fakestore.
(cd "${root}/fakestore" && go run . init -dir "${work}/fakestore" >/dev/null)
for v in 1 2 3; do
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

slot() {
  ota slot --image "${work}/app$1.img" --bundle "${work}/app$1.bundle" \
    --chain "${work}/$2" --blob "${work}/$3" --out "${work}/$4"
}
slot 1 chain0 blob0 slot-v1
slot 2 chain0 blob1 slot-v2
slot 3 chain2 blob2 slot-v3
slot 3 chain2 blob2-stale slot-v3-stale
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

echo "all scenarios passed (${work})"
