# Future Work: Full RV32IMC Machine-Code & No-UB Verification

1. **Full Loop-Invariant & End-to-End `State.runInstrs` Proofs**:
   - Extend the `MachineCodeEquiv` step proofs in `Crc32Rom.lean`, `AesRom.lean`, `MemRom.lean`, and `CryptoRom.lean` into full inductive loop-invariant proofs over arbitrary-length inputs, proving termination, memory safety (no unaligned accesses or out-of-bounds reads/writes), and end-to-end equivalence to the Lean specifications.
   - Add `State.runInstrs` proofs for `r_aes_shift_left_128`, `r_aes_ccm_xor_128_lsb`, `r_aes_ccm_xor_128_msb`, `mz_crc32`, `ets_emsa_pss_verify`, `r_ecc_is_valid_point`, and `r_ecc_point_multiplication_win_256`.
2. **Full `tdefl_compress` / `tinfl_decompress` Equivalence**:
   - Extend `MinizRom.lean` beyond stored blocks (`BTYPE=00`) to fixed/dynamic Huffman trees and LZ77 back-references (RFC 1951), and prove memory safety of the 1,457-line / 719-line loops.
