#!/usr/bin/env python3
"""Reports how much of the bootloader image the machine-code proofs cover.

It counts two things:

- Image coverage: the instructions in proved functions, out of every
  instruction in the image's code.
- Boot coverage: the instructions a boot runs at addresses in proved
  functions, out of every instruction the boot runs, from a boot-sim
  profile (`BOOT_SIM_PROFILE`).

A function counts as proved when it is in PROVED below, which names the
functions in `C3BootProofs/Image/Bootloader.lean` that a correctness
theorem covers. Add a function when its theorem lands. Helpers that two
functions share are counted once.

A proved function's theorem has hypotheses, such as a stack layout or
operands below a modulus, that its callers' proofs must still discharge.
So boot coverage counts instructions in proved code, not instructions whose
every call is proved.

Usage: coverage.py PROFILE ELF NM OBJDUMP [TOP]
"""

import bisect
import os
import re
import subprocess
import sys

PROVED = [
    "crc32", "readerBytes", "readerArray4", "readerU32", "manifestPart", "partSave", "partRestore",
    "manifestParse", "parseSave", "parseRestore", "readerMagic", "magicLoad", "readerU16",
    "readerVersion1", "readerReserved", "readerU8", "segmentPhysical", "imageParse", "imageRestore",
    "memcpyStub", "memcpyBody", "memset", "borrowingSub", "subInner", "subInnerSave",
    "subInnerRestore", "wideMul", "wideMulSave", "wideMulRestore", "fieldMul", "fieldAdd", "fieldSub",
    "fieldDouble", "pointAdd", "sha256Compress", "shaIndex", "shaSigma1Part", "shaUpdate",
    "shaUpdateSave", "shaUpdateRestore", "shaUpdateBlocks", "shaFinalize", "shaFinalizeSave",
    "shaZero32", "shaFinalizeBlock", "shaStoreBe", "shaFinalizeRestore", "sha256Fn", "shaInit",
    "mulMont12", "mulMont12Save", "mulMont12Setup", "mulMont12Restore", "uintSelect12", "uintSelect12Step",
]

IMAGE = os.path.join(os.path.dirname(__file__), "..", "C3BootProofs", "Image", "Bootloader.lean")


def extracted():
    """Returns {name: (address, bytes)} for the code in Bootloader.lean."""
    text = open(IMAGE).read()
    addrs = {m.group(1): int(m.group(2), 16)
             for m in re.finditer(r"def (\w+)Address : Nat := (0x[0-9a-fA-F]+)", text)}
    codes = {}
    for m in re.finditer(r"def (\w+)Code : List Nat :=\s*\[([^\]]*)\]", text):
        codes[m.group(1)] = [int(b, 16) for b in m.group(2).replace("\n", " ").split(",") if b.strip()]
    return {n: (addrs[n], codes[n]) for n in codes if n in addrs}


def starts(addr, code):
    """The addresses where instructions start in `code` at `addr`."""
    out, i = [], 0
    while i < len(code):
        out.append(addr + i)
        i += 4 if code[i] & 3 == 3 else 2
    return out


def symbols(elf, nm):
    funcs = []
    for line in subprocess.run([nm, "-C", "-S", elf], check=True, capture_output=True,
                               text=True).stdout.splitlines():
        parts = line.split(None, 3)
        if len(parts) == 4 and parts[2] in ("t", "T") and int(parts[1], 16) > 0:
            funcs.append((int(parts[0], 16), int(parts[1], 16), parts[3]))
    funcs.sort()
    return funcs


def image_instructions(elf, objdump):
    out = subprocess.run([objdump, "-d", "--no-show-raw-insn", elf], check=True,
                         capture_output=True, text=True).stdout
    return sum(1 for line in out.splitlines() if re.match(r"\s*[0-9a-f]+:\s", line))


def main():
    profile, elf, nm, objdump = sys.argv[1:5]
    top = int(sys.argv[5]) if len(sys.argv) > 5 else 15
    funcs = extracted()
    missing = [n for n in PROVED if n not in funcs]
    if missing:
        sys.exit(f"not in Bootloader.lean: {missing}")
    proved = set()
    for n in PROVED:
        proved.update(starts(*funcs[n]))
    total_image = image_instructions(elf, objdump)

    syms = symbols(elf, nm)
    sym_starts = [s[0] for s in syms]
    boot_total = boot_proved = 0
    unproved = {}
    for line in open(profile):
        a, c = line.split()
        a, c = int(a, 16), int(c)
        boot_total += c
        if a in proved:
            boot_proved += c
            continue
        i = bisect.bisect_right(sym_starts, a) - 1
        name = syms[i][2] if i >= 0 and a < syms[i][0] + syms[i][1] else f"0x{a:08x}"
        unproved[name] = unproved.get(name, 0) + c

    print("| Measure | Proved | Total | Share |")
    print("| --- | --- | --- | --- |")
    print(f"| Instructions in the image | {len(proved):,} | {total_image:,} | "
          f"{100 * len(proved) / total_image:.1f}% |")
    print(f"| Instructions one boot runs | {boot_proved:,} | {boot_total:,} | "
          f"{100 * boot_proved / boot_total:.1f}% |")
    print()
    print("| Unproved function | Instructions run | Share of the boot |")
    print("| --- | --- | --- |")
    for name, c in sorted(unproved.items(), key=lambda kv: -kv[1])[:top]:
        short = name if len(name) <= 90 else name[:87] + "..."
        print(f"| `{short}` | {c:,} | {100 * c / boot_total:.1f}% |")


if __name__ == "__main__":
    main()
