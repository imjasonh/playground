#!/usr/bin/env python3
"""Writes C3BootProofs/Image/Bootloader.lean: the bytes of the bootloader
functions that have machine-code proofs, taken from the bootloader image.

The bytes come from the ESP image's segments, which are what the ROM loads,
at the addresses and sizes that the ELF's symbol table gives. LLVM's machine
outliner numbers its helpers (OUTLINED_FUNCTION_N) differently on each
rebuild, so a helper is named by the call that reaches it: the
`auipc t0; jalr t0` pair at an offset of an extracted function, decoded the
way the CPU decodes it. The module
also records the image's SHA-256, which must equal
c3-boot/bootloader/dev-image.sha256. CI regenerates the module and fails if
it differs from the committed one, so the proofs are about the pinned image.

Usage: extract-functions.py ESP_IMAGE ELF NM OUT
"""

import hashlib
import struct
import subprocess
import sys

# Lean name, then the demangled symbol, or the Lean name of an earlier
# function and the offset of a call in it.
FUNCTIONS = [
    ("crc32", "c3_verify::bootstate::crc32"),
    ("readerBytes", "<c3_verify::reader::Reader>::bytes"),
    ("readerArray4", "<c3_verify::reader::Reader>::array::<4>"),
    ("readerU32", "<c3_verify::reader::Reader>::u32"),
    ("manifestPart", "c3_verify::manifest::part"),
    ("partSave", ("manifestPart", 0x02)),
    ("partRestore", ("manifestPart", 0x46)),
    ("manifestParse", "c3_verify::manifest::parse"),
    ("parseSave", ("manifestParse", 0x02)),
    ("parseRestore", ("manifestParse", 0xDC)),
    ("readerMagic", "<c3_verify::reader::Reader>::magic"),
    ("magicLoad", ("readerMagic", 0x22)),
    ("readerU16", "<c3_verify::reader::Reader>::u16"),
    ("readerVersion1", "<c3_verify::reader::Reader>::version_1"),
    ("readerReserved", "<c3_verify::reader::Reader>::reserved"),
    ("readerU8", "<c3_verify::reader::Reader>::u8"),
    ("segmentPhysical", "<c3_verify::image::Segment>::physical"),
    ("imageParse", "c3_verify::image::parse"),
    ("imageRestore", ("imageParse", 0xC2)),
    ("memcpyStub", "memcpy"),
    ("memcpyBody", ("memcpyStub", 0x00)),
    ("memset", "memset"),
    ("borrowingSub", "crypto_bigint::primitives::borrowing_sub"),
    ("subInner", "p256::arithmetic::field::field_impl::sub_inner"),
    ("subInnerSave", ("subInner", 0x02)),
    ("subInnerRestore", ("subInner", 0x12C)),
    ("wideMul", "crypto_bigint::uint::mul::karatsuba::widening_mul_fixed::<8, 8>"),
    ("wideMulSave", ("wideMul", 0x02)),
    ("wideMulRestore", ("wideMul", 0xD2)),
    ("fieldMul", "<p256::arithmetic::field::FieldElement>::multiply"),
    ("fieldAdd", "p256::arithmetic::field::field_impl::add"),
    ("fieldSub", "p256::arithmetic::field::field_impl::sub"),
    ("fieldDouble", "<p256::arithmetic::field::FieldElement as ff::Field>::double"),
    ("pointAdd", "<primeorder::point_arithmetic::EquationAIsMinusThree as "
     "primeorder::point_arithmetic::sealed::PointArithmetic<p256::NistP256>>::add_assign"),
]

# Lean name, then the Lean name of an extracted function, the offset of a
# `lui; addi` pair in it that forms the data's address, and the data's size.
DATA = [
    ("regionEnds", "imageParse", 0x23C, 16),
    ("regionStarts", "imageParse", 0x25E, 16),
]


def call_target(code, addr, off):
    """The target of the auipc/jalr pair at `off` of `code`, loaded at `addr`."""
    if off + 8 > len(code):
        sys.exit(f"offset {off:#x} is past the end of the function at {addr:#x}")
    auipc = int.from_bytes(code[off : off + 4], "little")
    jalr = int.from_bytes(code[off + 4 : off + 8], "little")
    rd = (auipc >> 7) & 31
    if auipc & 0x7F != 0x17 or jalr & 0x707F != 0x67 or (jalr >> 15) & 31 != rd:
        sys.exit(f"no auipc/jalr call at offset {off:#x} of the function at {addr:#x}")
    imm = jalr >> 20
    if imm & 0x800:
        imm -= 0x1000
    return (addr + off + (auipc & 0xFFFFF000) + imm) & 0xFFFFFFFE


def lui_addi(code, addr, off):
    """The address that the `lui rd; addi rd, rd` pair at `off` of `code` forms."""
    if off + 8 > len(code):
        sys.exit(f"offset {off:#x} is past the end of the function at {addr:#x}")
    lui = int.from_bytes(code[off : off + 4], "little")
    addi = int.from_bytes(code[off + 4 : off + 8], "little")
    rd = (lui >> 7) & 31
    if (
        lui & 0x7F != 0x37
        or addi & 0x707F != 0x13
        or (addi >> 7) & 31 != rd
        or (addi >> 15) & 31 != rd
    ):
        sys.exit(f"no lui/addi pair at offset {off:#x} of the function at {addr:#x}")
    imm = addi >> 20
    if imm & 0x800:
        imm -= 0x1000
    return ((lui & 0xFFFFF000) + imm) & 0xFFFFFFFF


def segments(image):
    count = image[1]
    pos = 24
    out = []
    for _ in range(count):
        addr, length = struct.unpack_from("<II", image, pos)
        out.append((addr, image[pos + 8 : pos + 8 + length]))
        pos += 8 + length
    return out


def bytes_at(segs, addr, size):
    for base, data in segs:
        if base <= addr and addr + size <= base + len(data):
            return data[addr - base : addr - base + size]
    sys.exit(f"no segment holds {size} bytes at {addr:#x}")


def main():
    image_path, elf, nm, out = sys.argv[1:]
    image = open(image_path, "rb").read()
    digest = hashlib.sha256(image).hexdigest()
    symbols = {}
    at = {}
    for line in subprocess.run(
        [nm, "-C", "-S", elf], check=True, capture_output=True, text=True
    ).stdout.splitlines():
        parts = line.split(None, 3)
        if len(parts) == 4 and parts[2] in ("t", "T"):
            entry = (int(parts[0], 16), int(parts[1], 16))
            symbols.setdefault(parts[3], []).append(entry)
            at.setdefault(entry[0], []).append((parts[3], entry[1]))
    segs = segments(image)
    lines = [
        "/-!",
        "# Bootloader functions",
        "",
        "Generated by `scripts/extract-functions.py` from the bootloader image with",
        f"SHA-256 `{digest}`",
        "(`c3-boot/bootloader/dev-image.sha256`). Do not edit. Each function's bytes",
        "are what the ROM loads at its address.",
        "-/",
        "",
        "namespace C3.Image",
        "",
        f'def imageSha256 : String := "{digest}"',
    ]
    extracted = {}
    for name, source in FUNCTIONS:
        if isinstance(source, tuple):
            caller, off = source
            caddr, ccode = extracted[caller]
            addr = call_target(ccode, caddr, off)
            found = [s for s in at.get(addr, []) if s[1] > 0]
            if len(found) != 1:
                sys.exit(f"the call at {caller}+{off:#x} reaches {addr:#x}, which starts {found}")
            symbol, size = found[0]
            what = f"`{symbol}`, which `{caller}` calls at offset {off:#x},"
        else:
            symbol = source
            if symbol not in symbols:
                sys.exit(f"no symbol {symbol}")
            if len(set(symbols[symbol])) != 1:
                sys.exit(f"{symbol} names more than one function: {symbols[symbol]}")
            addr, size = symbols[symbol][0]
            what = f"`{symbol}`,"
        code = bytes_at(segs, addr, size)
        extracted[name] = (addr, code)
        rows = [
            "    " + ", ".join(f"0x{b:02x}" for b in code[i : i + 12])
            for i in range(0, len(code), 12)
        ]
        lines += [
            "",
            f"/-- {what} at `{addr:#x}` in the image. -/",
            f"def {name}Address : Nat := {addr:#x}",
            "",
            f"def {name}Code : List Nat :=",
            "  [" + ",\n".join(rows).lstrip() + "]",
        ]
    for name, func, off, size in DATA:
        faddr, fcode = extracted[func]
        addr = lui_addi(fcode, faddr, off)
        data = bytes_at(segs, addr, size)
        lines += [
            "",
            f"/-- The {size} bytes at `{addr:#x}` in the image, whose address `{func}` forms at",
            f"offset {off:#x}. -/",
            f"def {name}Address : Nat := {addr:#x}",
            "",
            f"def {name}Data : List Nat :=",
            "  [" + ", ".join(f"0x{b:02x}" for b in data) + "]",
        ]
    lines += ["", "end C3.Image", ""]
    with open(out, "w") as f:
        f.write("\n".join(lines))


if __name__ == "__main__":
    main()
