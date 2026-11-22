#!/usr/bin/env bash
# Tests for check-no-binaries.sh, plus a check of the real repository.
# Run: bash .github/scripts/check-no-binaries_test.sh
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
check="$repo_root/.github/scripts/check-no-binaries.sh"

failures=0
expect() {
  local label="$1" want="$2" got="$3"
  if [[ "$got" != "$want" ]]; then
    echo "FAIL: $label (got $got, want $want)" >&2
    failures=$((failures + 1))
  fi
}

passes() {
  if bash "$check" "$1" >/dev/null 2>&1; then echo pass; else echo fail; fi
}

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

git -C "$tmp" init -q
git -C "$tmp" config user.email test@example.com
git -C "$tmp" config user.name test

# Allowed files: plain text, shell script, Wasm binary, symlink.
printf 'hello world\n' >"$tmp/readme.txt"
printf '#!/bin/sh\necho hi\n' >"$tmp/script.sh"
printf '\x00asm\x01\x00\x00\x00' >"$tmp/mod.wasm"
ln -s readme.txt "$tmp/link.txt"
git -C "$tmp" add readme.txt script.sh mod.wasm link.txt

expect "clean repo with text, script, wasm, and symlink passes" pass "$(passes "$tmp")"

# Untracked binary is ignored (only git-tracked files are checked).
printf '\x7fELF\x02\x01\x01\x00' >"$tmp/untracked-bin"
expect "untracked ELF binary passes" pass "$(passes "$tmp")"
rm "$tmp/untracked-bin"

# Tracked ELF binary fails.
printf '\x7fELF\x02\x01\x01\x00' >"$tmp/elf-bin"
git -C "$tmp" add elf-bin
expect "tracked ELF binary fails" fail "$(passes "$tmp")"
git -C "$tmp" rm -qf elf-bin

# Tracked Mach-O 64-bit binary fails.
printf '\xcf\xfa\xed\xfe\x07\x00\x00\x01' >"$tmp/macho-bin"
git -C "$tmp" add macho-bin
expect "tracked Mach-O binary fails" fail "$(passes "$tmp")"
git -C "$tmp" rm -qf macho-bin

# Tracked Mach-O universal binary fails.
printf '\xca\xfe\xba\xbe\x00\x00\x00\x02' >"$tmp/fat-bin"
git -C "$tmp" add fat-bin
expect "tracked Mach-O universal binary fails" fail "$(passes "$tmp")"
git -C "$tmp" rm -qf fat-bin

# Tracked PE/COFF binary fails.
python3 -c '
import struct, sys
buf = bytearray(128)
buf[0:2] = b"MZ"
struct.pack_into("<I", buf, 60, 64)
buf[64:68] = b"PE\x00\x00"
sys.stdout.buffer.write(buf)
' >"$tmp/win.exe"
git -C "$tmp" add win.exe
expect "tracked PE/COFF binary fails" fail "$(passes "$tmp")"
git -C "$tmp" rm -qf win.exe

# Tracked ar archive fails.
printf '!<arch>\n/               0           0     0     0       0         `\n' >"$tmp/libfoo.a"
git -C "$tmp" add libfoo.a
expect "tracked ar archive fails" fail "$(passes "$tmp")"
git -C "$tmp" rm -qf libfoo.a

# Real repository check.
expect "the real repository has no tracked compiled binaries" pass "$(passes "$repo_root")"

if ((failures > 0)); then
  echo "$failures test(s) failed" >&2
  exit 1
fi
echo "ok - check-no-binaries.sh"
