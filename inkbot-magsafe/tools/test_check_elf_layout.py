#!/usr/bin/env python3
"""Tests for target ELF flash and RAM placement checks."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_elf_layout

FLASH_START = 0x0001_C000
FLASH_END = 0x0005_C000
RAM_START = 0x2000_8000
RAM_END = 0x2004_0000


class ElfLayoutTest(unittest.TestCase):
    def validate(self, segments):
        return check_elf_layout.validate_layout(
            FLASH_START,
            segments,
            FLASH_START,
            FLASH_END,
            RAM_START,
            RAM_END,
        )

    def test_accepts_text_initialized_data_and_bss(self):
        self.assertEqual(
            self.validate(
                [
                    (FLASH_START, FLASH_START, 0x1000, 0x1000),
                    (RAM_START, FLASH_START + 0x1000, 0x400, 0x400),
                    (RAM_START + 0x400, RAM_START + 0x400, 0, 0x800),
                ]
            ),
            [],
        )

    def test_rejects_flash_load_overflow(self):
        failures = self.validate(
            [(FLASH_START, FLASH_END - 0x100, 0x200, 0x200)]
        )
        self.assertTrue(any("physical PT_LOAD" in failure for failure in failures))

    def test_rejects_ram_and_bss_overflow(self):
        for file_size in (0, 0x100):
            failures = self.validate(
                [(RAM_END - 0x100, FLASH_START, file_size, 0x200)]
            )
            self.assertTrue(any("virtual PT_LOAD" in failure for failure in failures))

    def test_rejects_segment_outside_flash_and_ram(self):
        failures = self.validate([(0x1000_0000, FLASH_START, 0x20, 0x20)])
        self.assertTrue(any("virtual PT_LOAD" in failure for failure in failures))

    def test_rejects_file_size_larger_than_memory_size(self):
        failures = self.validate([(FLASH_START, FLASH_START, 0x200, 0x100)])
        self.assertTrue(any("larger than memory size" in failure for failure in failures))


if __name__ == "__main__":
    unittest.main()
