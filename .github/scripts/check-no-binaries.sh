#!/usr/bin/env bash
# Check that no compiled native binaries or static archives are tracked in git.
#
# Scans every file listed by `git ls-files` for ELF, Mach-O (single-arch and
# universal), PE/COFF, and `ar` archive headers. Intentionally committed
# non-native artifacts (such as .wasm modules, images, and test fixtures) are
# allowed.
#
# Usage:
#   check-no-binaries.sh [ROOT]
#     ROOT is the git repository root. Default: the checkout this script is in.
set -euo pipefail

root=${1:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)}

python3 - "$root" <<'PY'
import os
import struct
import subprocess
import sys

root = sys.argv[1]
files = subprocess.check_output(["git", "-C", root, "ls-files", "-z"]).split(b"\0")

MACHO_MAGICS = {
    b"\xfe\xed\xfa\xce",
    b"\xce\xfa\xed\xfe",
    b"\xfe\xed\xfa\xcf",
    b"\xcf\xfa\xed\xfe",
}
MACHO_FAT_MAGICS = {
    b"\xca\xfe\xba\xbe",
    b"\xbe\xba\xfe\xca",
    b"\xca\xfe\xba\xbf",
    b"\xbf\xba\xfe\xca",
}


def classify(path: str):
    try:
        with open(path, "rb") as fp:
            hdr = fp.read(64)
            if len(hdr) < 4:
                return None
            m4 = hdr[:4]
            if m4 == b"\x7fELF":
                return "ELF binary"
            if m4 in MACHO_MAGICS:
                return "Mach-O binary"
            if m4 in MACHO_FAT_MAGICS and len(hdr) >= 8:
                nfat = struct.unpack(">I" if m4[0] == 0xCA else "<I", hdr[4:8])[0]
                if 1 <= nfat <= 32:
                    return "Mach-O universal binary"
            if hdr[:2] == b"MZ" and len(hdr) >= 64:
                pe_off = struct.unpack("<I", hdr[60:64])[0]
                fp.seek(pe_off)
                if fp.read(4) == b"PE\x00\x00":
                    return "PE/COFF binary"
            if hdr[:8] == b"!<arch>\n":
                return "ar archive"
    except OSError:
        return None
    return None


failures = 0
for raw in files:
    if not raw:
        continue
    rel = os.fsdecode(raw)
    full = os.path.join(root, rel)
    if os.path.islink(full) or not os.path.isfile(full):
        continue
    kind = classify(full)
    if kind is not None:
        print(f"FAIL: {rel}: {kind}", file=sys.stderr)
        failures += 1

if failures > 0:
    print(
        f"{failures} compiled binary file(s) tracked in git. "
        "Remove them with `git rm` and add them to `.gitignore`.",
        file=sys.stderr,
    )
    sys.exit(1)

print("ok - no compiled binaries tracked")
PY
