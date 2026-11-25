# Future Work: Full RV32IMC Machine-Code & No-UB Verification

1. **Full `tdefl_compress` / `tinfl_decompress` Equivalence**:
   - Extend `MinizRom.lean` beyond stored blocks (`BTYPE=00`) to fixed/dynamic Huffman trees and LZ77 back-references (RFC 1951), and prove memory safety of the 1,457-line / 719-line loops.
