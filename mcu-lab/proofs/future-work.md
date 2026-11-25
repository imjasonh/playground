# Future Work: Full RV32IMC Machine-Code & No-UB Verification

## Current Status

All 13 `.asm` dumps in `mcu-lab/proofs/rom_asm/` have Lean 4.14.0 specifications and algorithmic proofs (`lake build` passes with 0 errors and 0 `sorry`s):

- `Crc32Rom.lean` (`crc32_le.asm`): proves table-driven `crc32_le` equals bitwise IEEE 802.3 CRC32 for all byte lists, plus `crc32LeBytes_valid_rv32imc` verifying the 52-byte stream decodes as 18 valid RV32IMC instructions.
- `AesRom.lean` (`r_aes_xor_128.asm`, `r_aes_shift_left_128.asm`, `r_aes_ccm_xor_128_lsb.asm`, `r_aes_ccm_xor_128_msb.asm`): proves algebraic properties and 128-bit `<<< 1` equivalence.
- `MemRom.lean` (`memcpy.asm`, `memset.asm`): proves range preservation and idempotence.
- `MzCrc32Rom.lean` (`mz_crc32.asm`): proves equivalence to IEEE 802.3 CRC32.
- `CryptoRom.lean` (`ets_rsa_pss_verify.asm`, `r_ecc_is_valid_point.asm`, `r_ecc_point_multiplication_win_256.asm`): proves curve equation, RSA-PSS soundness, and group scalar-mul identities.
- `MinizRom.lean` (`tdefl_compress.asm`, `tinfl_decompress.asm`): proves stored-block (`BTYPE=00`) DEFLATE round-trip.

## What Remains for Full No-UB / Machine-Code Verification

1. **Full RV32IMC Instruction Semantics & Step Simulation** (`Rv32imc.lean`):
   - Extend `Rv32imc.Instr` and add a `State.step` semantics for every RV32I + RVC instruction used in the ROM dumps.
   - Prove that executing the decoded bytes of each routine from initial register/memory state terminates and matches the Lean specification, with no unaligned accesses, out-of-bounds reads/writes, or illegal instructions.
2. **External ROM Data & Callee Subroutines**:
   - `crc32_le` reads `crc32_le_table` at `0x3ff1c9c8` (1 KiB). We need the actual 256 `UInt32` entries from the ROM dump to prove `romMem[0x3ff1c9c8 + 4*i] == crc32LeTable i`.
   - `ets_rsa_pss_verify`, `r_ecc_is_valid_point`, and `r_ecc_point_multiplication_win_256` call ROM helper subroutines and read curve/RSA constants not present in `rom_asm/*.asm`.
3. **Full `tdefl_compress` / `tinfl_decompress` Equivalence**:
   - Extend `MinizRom.lean` beyond stored blocks (`BTYPE=00`) to fixed/dynamic Huffman trees and LZ77 back-references (RFC 1951), and prove memory safety of the 1,457-line / 719-line loops.

## Dumping the Complete ESP32-C3 ROM over USB-C

To extract the full mask ROM code (`IROM`, `0x40000000`–`0x40060000`, 384 KiB) and ROM data (`DROM`, `0x3ff00000`–`0x3ff20000`, 128 KiB — which includes `crc32_le_table` at `0x3ff1c9c8`) from an ESP32-C3 board connected over USB-C:

1. **Connect the ESP32-C3 via USB-C** (native USB-Serial/JTAG or USB-UART bridge) and put it in bootloader mode if needed (hold `BOOT`, press `RESET`, release `BOOT`).
2. **Install `esptool`** (if not already installed):
   ```bash
   pip install esptool
   ```
3. **Identify the serial port**:
   - Linux: `/dev/ttyACM0` or `/dev/ttyUSB0`
   - macOS: `/dev/cu.usbmodem*` or `/dev/cu.usbserial*`
4. **Dump IROM (384 KiB) and DROM (128 KiB)**:
   ```bash
   PORT=/dev/ttyACM0  # adjust for your OS/port

   # Mask ROM executable code (0x40000000..0x40060000)
   esptool.py --chip esp32c3 --port "$PORT" dump_mem 0x40000000 0x60000 esp32c3_irom.bin

   # Mask ROM read-only data & lookup tables (0x3ff00000..0x3ff20000)
   esptool.py --chip esp32c3 --port "$PORT" dump_mem 0x3ff00000 0x20000 esp32c3_drom.bin
   ```
5. **Extract `crc32_le_table` (`0x3ff1c9c8`, 256 × 4 = 1024 bytes, offset `0x1c9c8` in `esp32c3_drom.bin`)**:
   ```bash
   dd if=esp32c3_drom.bin of=crc32_le_table.bin bs=1 skip=$((0x1c9c8)) count=1024
   ```
