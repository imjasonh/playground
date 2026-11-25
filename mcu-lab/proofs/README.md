# ESP32-C3 ROM Formal Verification (`mcu-lab/proofs`)

Machine-checked Lean 4 proofs for critical routines in the ESP32-C3 silicon mask ROM (`esp32c3_rev3_rom.elf` / `esp32c3_rom.bin`), starting with `crc32_le` (`0x4004a29a–0x4004a2cc`).

## Building & Checking Proofs

```bash
cd mcu-lab/proofs
lake build
```

## Layout & Roadmap

- **`Crc32Rom.lean`**: Models the 18-instruction `rv32imc` `crc32_le` routine (`52` bytes) and `crc32_le_table` (`0x3ff1c9c8`), proving functional equivalence to IEEE 802.3 CRC32 (`0xEDB88320`) for all byte lists `buf : List UInt8`.
  - Next step for a cloud-hosted Lean 4 agent: discharge `romLoopStep_eq_crcByteBitwise` using `bv_decide` (or `Std.Tactic.BVDecide`) and add a byte-level `rv32imc` decoder check against `crc32LeBytes`.
- **Planned targets** (extractable from `esp32c3_rev3_rom.elf` via `riscv32-esp-elf-objdump -d`):
  - `ets_sha256_init` / `ets_sha256_update` / `ets_sha256_finish`
  - `ets_rsa_pss_verify` / `esp_secure_boot_verify_signature`
