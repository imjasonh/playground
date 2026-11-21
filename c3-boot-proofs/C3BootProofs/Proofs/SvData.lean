import C3BootProofs.Proofs.SvDer5
import C3BootProofs.Image.BootloaderData3

/-!
# `sigstore::verify`: its constants

The OIDs, the two tables of OIDs, and the strings `sigstore::verify` reads,
304 bytes from 0x3FCC4818. No step writes them: they are outside the stack.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 20000

abbrev SVK : Word := BitVec.ofNat 32 svConstAddress

/-- The constants `sigstore::verify` reads are the image's. -/
structure SvData (M : Word → BitVec 8) : Prop where
  c : CodeIn M SVK svConstData

theorem SvData.sv {M M0 : Word → BitVec 8} {B : Word} (F : Fr B 0x3830) (D : SvData M0)
    (fR : ∀ x, SvR B x → M x = M0 x) : SvData M :=
  ⟨fun i hi => by
    rw [fR _ (dataR (q := SVK) (ql := svConstData.length) F (by decide) (by decide) i hi)]; exact D.c i hi⟩

/-- `n` constant bytes at offset `i`. -/
theorem SvData.mb {M : Word → BitVec 8} (D : SvData M) {i n : Nat} (h : i + n ≤ svConstData.length) :
    memBytes M (SVK + BitVec.ofNat 32 i) n = (List.range n).map fun j => svConstData.getD (i + j) 0 := by
  unfold memBytes
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  rw [add_ofNat_assoc, D.c _ (by omega)]
  unfold byteAt
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by
    have : ∀ k, k < svConstData.length → svConstData.getD k 0 < 256 := by decide
    exact this _ (by omega))

/-- A constant word at offset `i`. -/
theorem SvData.w32 {M : Word → BitVec 8} (D : SvData M) {i : Nat} {v : Word} (h : i + 4 ≤ svConstData.length)
    (hv : byteAt svConstData (i + 3) ++ byteAt svConstData (i + 2) ++ byteAt svConstData (i + 1) ++
      byteAt svConstData i = v) : memLoad32 M (SVK + BitVec.ofNat 32 i) = v := by
  unfold memLoad32
  have b0 : M (SVK + BitVec.ofNat 32 i) = byteAt svConstData i := D.c _ (by omega)
  have b1 : M (SVK + BitVec.ofNat 32 i + 1) = byteAt svConstData (i + 1) := by
    rw [show SVK + BitVec.ofNat 32 i + 1 = SVK + BitVec.ofNat 32 (i + 1) from add_ofNat_assoc _ i 1]
    exact D.c _ (by omega)
  have b2 : M (SVK + BitVec.ofNat 32 i + 2) = byteAt svConstData (i + 2) := by
    rw [show SVK + BitVec.ofNat 32 i + 2 = SVK + BitVec.ofNat 32 (i + 2) from add_ofNat_assoc _ i 2]
    exact D.c _ (by omega)
  have b3 : M (SVK + BitVec.ofNat 32 i + 3) = byteAt svConstData (i + 3) := by
    rw [show SVK + BitVec.ofNat 32 i + 3 = SVK + BitVec.ofNat 32 (i + 3) from add_ofNat_assoc _ i 3]
    exact D.c _ (by omega)
  rw [b0, b1, b2, b3, hv]

end C3.RV32.Sv
