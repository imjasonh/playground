#!/usr/bin/env python3
"""Reject loadable ELF segments outside an allowed flash interval."""

from __future__ import annotations

import argparse
import struct
from pathlib import Path

PT_LOAD = 1
ELF32 = 1
LITTLE_ENDIAN = 1


def integer(value: str) -> int:
    """Parse a decimal or `0x`-prefixed integer."""
    return int(value, 0)


def load_segments(path: Path) -> tuple[int, list[tuple[int, int, int]]]:
    """Return the entry point and nonempty loadable segments in an ELF32 file."""
    data = path.read_bytes()
    if len(data) < 52 or data[:4] != b"\x7fELF":
        raise ValueError(f"{path} is not an ELF file")
    if data[4] != ELF32 or data[5] != LITTLE_ENDIAN:
        raise ValueError(f"{path} must be a little-endian ELF32 file")

    header = struct.unpack_from("<16sHHIIIIIHHHHHH", data)
    entry = header[4]
    program_offset = header[5]
    program_entry_size = header[9]
    program_entry_count = header[10]
    if program_entry_size < 32:
        raise ValueError(f"{path} has an invalid program-header size")

    segments = []
    for index in range(program_entry_count):
        offset = program_offset + index * program_entry_size
        if offset + 32 > len(data):
            raise ValueError(f"{path} has a truncated program-header table")
        (
            segment_type,
            _file_offset,
            virtual_address,
            physical_address,
            file_size,
            _memory_size,
            _flags,
            _alignment,
        ) = struct.unpack_from("<IIIIIIII", data, offset)
        if segment_type == PT_LOAD and file_size:
            segments.append((virtual_address, physical_address, file_size))
    return entry, segments


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--flash-start", type=integer, required=True)
    parser.add_argument("--flash-end", type=integer, required=True)
    args = parser.parse_args()

    if args.flash_start >= args.flash_end:
        parser.error("--flash-start must be lower than --flash-end")

    entry, segments = load_segments(args.elf)
    failures = []
    if not args.flash_start <= entry < args.flash_end:
        failures.append(
            f"entry 0x{entry:08x} is outside "
            f"0x{args.flash_start:08x}..0x{args.flash_end:08x}"
        )
    for _virtual, physical, size in segments:
        if physical < args.flash_start or physical + size > args.flash_end:
            failures.append(
                f"physical PT_LOAD 0x{physical:08x}.."
                f"0x{physical + size:08x} is outside the allowed flash interval"
            )

    if not segments:
        failures.append("ELF has no nonempty PT_LOAD segments")
    if failures:
        for failure in failures:
            print(f"ERROR: {failure}")
        return 1

    print(
        f"{args.elf}: {len(segments)} PT_LOAD segments and entry "
        f"0x{entry:08x} fit 0x{args.flash_start:08x}..0x{args.flash_end:08x}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
