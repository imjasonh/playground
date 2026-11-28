#!/usr/bin/env python3
"""Writes the fetch lemmas of one long function from `Image/Bootloader.lean`.

The bytes are split into 0x100-byte chunks, each with the next 4 bytes so an
instruction that starts in a chunk ends in it. Each lemma decodes from its
chunk through `fetchRel_chunk`, so `decide` walks a short list.

Usage: gen-fetch-lemmas.py NAME PREFIX ABBREV NAMESPACE TITLE [MODULE...] > OUT.lean

NAME is the function's name in `Image/Bootloader.lean` (`NAMEAddress` and
`NAMECode`), PREFIX names the chunks and lemmas (`PREFIX_c0`, `PREFIX_at_4`),
ABBREV is the abbreviation for the function's address, and TITLE is the
function's Rust path for the module comment. Each MODULE is imported too,
for example `C3BootProofs.Proofs.ReaderArray` for the register names `sp`
and `s0`.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rv32dec  # noqa: E402

CHUNK = 0x100


def main():
    name, prefix, abbrev, ns, title = sys.argv[1:6]
    src = open("C3BootProofs/Image/Bootloader.lean").read()
    code = rv32dec.code_of(src, name + "Code")
    out = [
        "import C3BootProofs.Proof.FetchChunk",
        "import C3BootProofs.Image.Bootloader",
    ] + [f"import {m}" for m in sys.argv[6:]] + [
        "",
        f"/-! Fetch lemmas for `{title}` (`{name}Code`). -/",
        "",
        f"namespace {ns}",
        "",
        "open C3.Image",
        "",
        f"/-- Where `{title}` is in the image. -/",
        f"abbrev {abbrev} : Word := BitVec.ofNat 32 {name}Address",
        "",
        "set_option maxRecDepth 20000",
        "",
    ]
    nchunks = (len(code) + CHUNK - 1) // CHUNK
    lens = []
    for i in range(nchunks):
        lo = i * CHUNK
        hi = min(lo + CHUNK + 4, len(code))
        lens.append(hi - lo)
        body = [f"0x{b:02x}" for b in code[lo:hi]]
        rows = [", ".join(body[j:j + 12]) for j in range(0, len(body), 12)]
        out.append(f"/-- Bytes 0x{lo:X} to 0x{hi:X} of `{name}Code`. -/")
        out.append(f"def {prefix}_c{i} : List Nat :=")
        out.append("  [" + ",\n    ".join(rows) + "]")
        out.append(f"theorem {prefix}_c{i}_ok : {prefix}_c{i} <+: List.drop {lo} {name}Code := by decide")
        out.append("")
    off = 0
    while off < len(code):
        ins = rv32dec.decode(code, off)
        ln = ins[-1]
        i = off // CHUNK
        side = ".inl" if off - i * CHUNK + 4 <= lens[i] else ".inr"
        out.append(f"theorem {prefix}_at_{off:x} : fetchRel {name}Code 0x{off:X} = "
                   f"some ({rv32dec.lean(ins)}, {ln}) :=")
        out.append(f"  (fetchRel_chunk {prefix}_c{i}_ok (by decide) ({side} (by decide))).trans (by decide)")
        off += ln
    out += ["", f"end {ns}", ""]
    sys.stdout.write("\n".join(out))


main()
