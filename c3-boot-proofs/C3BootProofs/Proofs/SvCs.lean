import C3BootProofs.Proofs.SvEd

/-!
# `sigstore::verify`: the checkpoint's signature lines

Byte tests for the signature lines' name and base64 scans.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

/-- A byte minus `' '` is zero exactly when the byte is `' '`. -/
theorem space_iff : ∀ b : BitVec 8, b.zeroExtend 32 + 0xFFFFFFE0 = 0 ↔ b = 0x20 := by decide

/-- A byte minus `'='` is zero exactly when the byte is `'='`. -/
theorem pad_iff : ∀ b : BitVec 8, b.zeroExtend 32 + 0xFFFFFFC3 = 0 ↔ b = 0x3D := by decide

end C3.RV32.Sv
