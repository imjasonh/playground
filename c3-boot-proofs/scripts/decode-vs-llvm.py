#!/usr/bin/env python3
"""Compares the Lean RV32 decoder with LLVM's RISC-V disassembler.

Checks every 16-bit encoding and a sample of 32-bit encodings, weighted
toward the opcodes and function fields the model decodes. Each encoding goes
in its own executable section of an ELF file, so llvm-objdump decodes each
one from its first byte. An encoding the Lean decoder accepts and LLVM
rejects fails the check: the model would run an instruction the hardware
traps on. An encoding LLVM accepts and the Lean decoder rejects fails too,
unless it's one the model leaves out on purpose: the SYSTEM opcode (ecall,
ebreak, CSR instructions, mret, wfi), fence.i, and c.ebreak.

Usage: decode-vs-llvm.py RV_DECODE LLVM_BIN_DIR
"""

import random
import re
import struct
import subprocess
import sys
import tempfile

SAMPLES_32 = 200_000
CHUNK = 50_000
MATTR = "+m,+c"


def elf(words, size):
    """An ELF32 RISC-V relocatable file with one section per encoding."""
    shstr = b"\0.text\0.shstrtab\0"
    data = b"".join(struct.pack("<H" if size == 2 else "<I", w) for w in words)
    n = len(words)
    header_len = 52
    data_off = header_len
    shstr_off = data_off + len(data)
    sh_off = (shstr_off + len(shstr) + 3) & ~3
    sections = [struct.pack("<10I", 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)]
    for i in range(n):
        sections.append(
            struct.pack("<10I", 1, 1, 6, i * 4, data_off + i * size, size, 0, 0, 2, 0)
        )
    sections.append(
        struct.pack("<10I", 7, 3, 0, 0, shstr_off, len(shstr), 0, 0, 1, 0)
    )
    count = len(sections)
    shnum = 0 if count >= 0xFF00 else count
    shstrndx = count - 1
    if count >= 0xFF00:
        sections[0] = struct.pack("<10I", 0, 0, 0, 0, 0, 0, count, shstrndx, 0, 0)
        shstrndx = 0xFFFF
    ident = b"\x7fELF\x01\x01\x01" + b"\0" * 9
    header = ident + struct.pack(
        "<HHIIIIIHHHHHH", 1, 243, 1, 0, 0, sh_off, 0x4, 52, 0, 0, 40, shnum, shstrndx
    )
    body = header + data + shstr
    body += b"\0" * (sh_off - len(body))
    return body + b"".join(sections)


def llvm_verdicts(words, size, objdump):
    """LLVM's mnemonic for each encoding, or None if it's invalid."""
    out = {}
    for start in range(0, len(words), CHUNK):
        chunk = words[start : start + CHUNK]
        with tempfile.NamedTemporaryFile(suffix=".o") as f:
            f.write(elf(chunk, size))
            f.flush()
            text = subprocess.run(
                [objdump, "-d", f"--mattr={MATTR}", "--no-show-raw-insn", f.name],
                check=True,
                capture_output=True,
                text=True,
            ).stdout
        line = re.compile(r"^\s*([0-9a-f]+):\s+(\S.*)$")
        for raw in text.splitlines():
            m = line.match(raw)
            if not m:
                continue
            addr = int(m.group(1), 16)
            if addr % 4 or addr // 4 >= len(chunk):
                continue
            index = start + addr // 4
            if index in out:
                continue
            mnemonic = m.group(2).split()[0]
            out[index] = None if mnemonic in ("<unknown>", "unimp") else mnemonic
    missing = [i for i in range(len(words)) if i not in out]
    if missing:
        sys.exit(f"llvm-objdump printed nothing for {len(missing)} encodings")
    return out


def lean_verdicts(words, size, rv_decode):
    width = 4 if size == 2 else 8
    lines = "".join(f"{w:0{width}x}\n" for w in words)
    text = subprocess.run(
        [rv_decode], input=lines, check=True, capture_output=True, text=True
    ).stdout.split("\n")
    return [t.split()[1] == "valid" for t in text if t]


def sample_32(rng):
    """32-bit encodings, mostly in the opcodes the model decodes."""
    opcodes = [0x37, 0x17, 0x6F, 0x67, 0x63, 0x03, 0x23, 0x13, 0x33, 0x0F]
    words = [0x0000000F, 0x0FF0000F, 0x8330000F, 0x8FF0000F, 0x0FF0008F, 0x0FF0800F]
    while len(words) < SAMPLES_32:
        w = rng.getrandbits(32) | 3
        if rng.random() < 0.85:
            w = (w & ~0x7F) | rng.choice(opcodes)
            if rng.random() < 0.5:
                w = (w & ~(0x7F << 25)) | (rng.choice([0, 1, 0x20]) << 25)
        if w & 0x7F == 0x73 or (w & 0x707F) == 0x100F:
            continue
        words.append(w)
    return words


def main():
    rv_decode, bin_dir = sys.argv[1], sys.argv[2]
    objdump = f"{bin_dir}/llvm-objdump"
    rng = random.Random(0xC3DEC0DE)
    failures = 0
    for size, words in (
        (2, [h for h in range(0x10000) if h & 3 != 3]),
        (4, sample_32(rng)),
    ):
        llvm = llvm_verdicts(words, size, objdump)
        lean = lean_verdicts(words, size, rv_decode)
        accepted = 0
        for i, w in enumerate(words):
            ok_llvm = llvm[i] is not None
            accepted += lean[i]
            if lean[i] == ok_llvm:
                continue
            if size == 2 and w == 0x9002 and not lean[i]:
                continue
            failures += 1
            if failures <= 20:
                side = "Lean accepts" if lean[i] else f"LLVM accepts ({llvm[i]})"
                print(f"{w:0{size * 2}x}: {side}, the other rejects")
        print(f"{size * 8}-bit: {len(words)} encodings, {accepted} valid")
    if failures:
        sys.exit(f"{failures} encodings disagree")
    print("the Lean decoder agrees with LLVM")


if __name__ == "__main__":
    main()
