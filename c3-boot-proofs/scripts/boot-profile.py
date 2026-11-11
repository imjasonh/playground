#!/usr/bin/env python3
"""Summarizes a boot-sim instruction profile by crate and by function.

boot-sim writes the profile when `BOOT_SIM_PROFILE` names a file: one
`ADDRESS COUNT` line, in hex and decimal, for each code address that ran.
This script assigns each address to the function whose symbol covers it
and prints two Markdown tables: code size and instructions by crate, and
the functions that ran the most instructions. A function's count excludes the functions
it calls.

At the ESP32-C3's 160 MHz, a million instructions take at least 6.25 ms;
the estimate in the crate table assumes one cycle per instruction, which a
board has to confirm.

Usage: boot-profile.py PROFILE ELF NM [TOP]
"""

import bisect
import subprocess
import sys

# A function belongs to the first crate named in its demangled symbol, so
# `<p256::... as primeorder::...>::add_assign` counts as `p256`.
CRATES = [
    "sha2", "p384", "p256", "primeorder", "curve25519_dalek", "ed25519_dalek",
    "crypto_bigint", "elliptic_curve", "ecdsa", "primefield", "c3_crypto",
    "c3_verify", "c3_bootloader", "core", "compiler_builtins",
]
MHZ = 160


def crate_of(symbol):
    best = None
    for crate in CRATES:
        i = symbol.find(crate + "::")
        if i >= 0 and (best is None or i < best[0]):
            best = (i, crate)
    if best:
        return best[1]
    if symbol in ("memcpy", "memset", "memmove", "memcmp"):
        return "compiler_builtins"
    if symbol.startswith("OUTLINED_FUNCTION_"):
        return "outlined helpers"
    return "other"


def main():
    profile, elf, nm = sys.argv[1:4]
    top = int(sys.argv[4]) if len(sys.argv) > 4 else 25
    funcs = []
    for line in subprocess.run(
        [nm, "-C", "-S", elf], check=True, capture_output=True, text=True
    ).stdout.splitlines():
        parts = line.split(None, 3)
        if len(parts) == 4 and parts[2] in ("t", "T") and int(parts[1], 16) > 0:
            funcs.append((int(parts[0], 16), int(parts[1], 16), parts[3]))
    funcs.sort()
    starts = [f[0] for f in funcs]
    by_func = {}
    total = 0
    for line in open(profile):
        addr_hex, count = line.split()
        addr, count = int(addr_hex, 16), int(count)
        total += count
        i = bisect.bisect_right(starts, addr) - 1
        if i >= 0 and addr < funcs[i][0] + funcs[i][1]:
            name = funcs[i][2]
        else:
            name = f"unknown code at {addr:#x}"
        by_func[name] = by_func.get(name, 0) + count
    size_by_crate = {}
    for _, size, name in funcs:
        crate = crate_of(name)
        size_by_crate[crate] = size_by_crate.get(crate, 0) + size
    by_crate = {}
    for name, count in by_func.items():
        crate = crate_of(name)
        by_crate[crate] = by_crate.get(crate, 0) + count

    print(f"{total:,} instructions, at least {total / MHZ / 1e6 * 1e3:,.0f} ms at {MHZ} MHz.")
    print()
    print(f"{sum(size_by_crate.values()):,} bytes of code.")
    print()
    print("| Crate | Code (bytes) | Instructions run | Share | Time at one cycle each (ms) |")
    print("| --- | --- | --- | --- | --- |")
    for crate in sorted(size_by_crate, key=lambda c: (-by_crate.get(c, 0), -size_by_crate[c])):
        count = by_crate.get(crate, 0)
        print(f"| `{crate}` | {size_by_crate[crate]:,} | {count:,} | {100 * count / total:.1f}% "
              f"| {count / MHZ / 1e3:,.0f} |")
    print()
    print("| Function | Instructions | Share |")
    print("| --- | --- | --- |")
    for name, count in sorted(by_func.items(), key=lambda kv: -kv[1])[:top]:
        shown = name if len(name) <= 100 else name[:97] + "..."
        print(f"| `{shown}` | {count:,} | {100 * count / total:.1f}% |")


if __name__ == "__main__":
    main()
