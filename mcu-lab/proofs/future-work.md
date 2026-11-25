# Future Work: Full RV32IMC Machine-Code & No-UB Verification

1. **Full Function-Level Machine-Code Equivalence (`ets_rsa_pss_verify.asm`, `ets_emsa_pss_verify.asm`, `r_ecc_*.asm`)**:
   - Extend `Rv32imc.lean` with all remaining RV32IMC instruction encodings used in these dumps (`auipc`, `sw`, `sltiu`, `bltu`, `bgeu`, `beqz`/`bnez`, etc.).
   - Extract the exact raw machine-code bytes from each `.asm` file and prove via symbolic execution / Hoare-logic invariants over `State.stepInstr` that every path from entry to `ret` (including all branches, stack frames, callees, and error paths) implements the Lean specification.
2. **Full `tdefl_compress` / `tinfl_decompress` Equivalence**:
   - Extend `MinizRom.lean` beyond stored blocks (`BTYPE=00`) to fixed/dynamic Huffman trees and LZ77 back-references (RFC 1951), and prove memory safety of the 1,457-line / 719-line loops.
