# Future Work: Full RV32IMC Machine-Code & No-UB Verification

## Current Status

All `.asm` dumps, ROM tables (`crc32_le_table.txt`, `ecc_tables.txt`), MMIO register definitions (`hwcrypto_reg.h`), and silicon-verified BigInt vectors (`bigint_vectors.txt`) in `mcu-lab/proofs/rom_asm/` have Lean 4.14.0 specifications and proofs (`lake build` passes with 0 errors and 0 `sorry`s):

- `Rv32imc.lean`: RV32IMC (32-bit + compressed RVC) instruction decoder (`decodeRVC`, `decodeRV32`, `decodeAll`) and `State.stepInstr` operational semantics.
- `Crc32Rom.lean` (`crc32_le.asm`) & `Crc32Table.lean` (`crc32_le_table.txt`): proves table-driven `crc32_le` equals bitwise IEEE 802.3 CRC32 for all byte lists, `crc32LeBytes_valid_rv32imc` verifies the 52-byte stream decodes as 18 valid RV32IMC instructions, `crc32Le_init_step`/`crc32Le_exit_step` verify `State.stepInstr` execution, and `romCrc32LeTableData_eq_crc32LeTable` verifies all 256 ROM table entries.
- `AesRom.lean` (`r_aes_xor_128.asm`, `r_aes_shift_left_128.asm`, `r_aes_ccm_xor_128_lsb.asm`, `r_aes_ccm_xor_128_msb.asm`): proves algebraic properties and 128-bit `<<< 1` equivalence.
- `MemRom.lean` (`memcpy.asm`, `memset.asm`, `memcmp.asm`): proves range preservation, idempotence, and `memcmp = 0 ↔ ∀ k < n, a k = b k`.
- `MzCrc32Rom.lean` (`mz_crc32.asm`): proves equivalence to IEEE 802.3 CRC32.
- `CryptoRom.lean` (`ets_rsa_pss_verify.asm`, `ets_emsa_pss_verify.asm`, `ets_bigint_*.asm`, `hwcrypto_reg.h`, `bigint_vectors.txt`, `r_ecc_is_valid_point.asm`, `r_ecc_point_multiplication_win_256.asm`): proves RSA-PSS soundness, EMSA-PSS `0xBC` trailer/length checks, Weierstrass curve equation, group scalar-mul identities, RSA MMIO state transitions, and all 3 silicon-verified 64/128/256-bit `bigint_vectors.txt` vectors (`m < 2^(32*words - 1)` precondition, `m_dash` inverse, and `modPowFast x y m = z`).
- `MinizRom.lean` (`tdefl_compress.asm`, `tinfl_decompress.asm`): proves stored-block (`BTYPE=00`) DEFLATE round-trip.

## What Remains for Full No-UB / Machine-Code Verification

1. **Per-routine `State.stepInstr` Loop-Invariant Proofs**:
   - Prove that executing the decoded bytes of each remaining routine (`r_aes_*`, `mem*`, `ets_rsa_pss_verify`, `r_ecc_*`) under `State.stepInstr` terminates and matches its Lean specification, with no unaligned accesses, out-of-bounds reads/writes, or illegal instructions.
2. **Full `tdefl_compress` / `tinfl_decompress` Equivalence**:
   - Extend `MinizRom.lean` beyond stored blocks (`BTYPE=00`) to fixed/dynamic Huffman trees and LZ77 back-references (RFC 1951), and prove memory safety of the 1,457-line / 719-line loops.
