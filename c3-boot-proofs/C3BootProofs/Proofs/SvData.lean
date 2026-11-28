import C3BootProofs.Proofs.SvDer5
import C3BootProofs.Image.BootloaderData3

/-!
# `sigstore::verify`: its constants

The OIDs, the tables of OIDs, and the strings `sigstore::verify` reads by
value. No step writes them: they are outside the stack.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 20000

/-- The constants `sigstore::verify` reads by value are the image's. -/
structure SvData (M : Word → BitVec 8) : Prop where
  c : CodeIn M (BitVec.ofNat 32 svConstAddress) svConstData
  cms : CodeIn M (BitVec.ofNat 32 svConstCmsAddress) svConstCmsData
  ext : CodeIn M (BitVec.ofNat 32 svConstExtAddress) svConstExtData

/-- Constant bytes in the data window read the same in two memories that
agree outside the stack. -/
theorem CodeIn.svData {M M0 : Word → BitVec 8} {B q : Word} {d : List Nat} (FW : Fr (B + 0xFFFFEC10) 0x3A50)
    (h1 : (img% dataWindowAddress) ≤ q.toNat) (h2 : q.toNat + d.length ≤ (img% dataWindowAddress + dataWindowSize))
    (hc : CodeIn M0 q d) (fR : ∀ x, SvR B x → M x = M0 x) : CodeIn M q d :=
  fun i hi => by rw [fR _ (dataR FW h1 h2 i hi)]; exact hc i hi

theorem SvData.sv {M M0 : Word → BitVec 8} {B : Word} (FW : Fr (B + 0xFFFFEC10) 0x3A50) (D : SvData M0)
    (fR : ∀ x, SvR B x → M x = M0 x) : SvData M :=
  ⟨CodeIn.svData FW (by decide) (by decide) D.c fR, CodeIn.svData FW (by decide) (by decide) D.cms fR,
    CodeIn.svData FW (by decide) (by decide) D.ext fR⟩

/-- `n` constant bytes at offset `i`. -/
theorem CodeIn.mbc {M : Word → BitVec 8} {q : Word} {d : List Nat} (D : CodeIn M q d) (hd : ∀ k, k < d.length → d.getD k 0 < 256)
    {i n : Nat} (h : i + n ≤ d.length) :
    memBytes M (q + BitVec.ofNat 32 i) n = (List.range n).map fun j => d.getD (i + j) 0 := by
  unfold memBytes
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  rw [add_ofNat_assoc, D _ (by omega)]
  unfold byteAt
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (hd _ (by omega))

/-- A constant word at offset `i`. -/
theorem CodeIn.w32 {M : Word → BitVec 8} {q : Word} {d : List Nat} (D : CodeIn M q d) {i : Nat} {v : Word}
    (h : i + 4 ≤ d.length)
    (hv : byteAt d (i + 3) ++ byteAt d (i + 2) ++ byteAt d (i + 1) ++ byteAt d i = v) :
    memLoad32 M (q + BitVec.ofNat 32 i) = v := by
  unfold memLoad32
  have b0 : M (q + BitVec.ofNat 32 i) = byteAt d i := D _ (by omega)
  have b1 : M (q + BitVec.ofNat 32 i + 1) = byteAt d (i + 1) := by
    rw [show q + BitVec.ofNat 32 i + 1 = q + BitVec.ofNat 32 (i + 1) from add_ofNat_assoc _ i 1]
    exact D _ (by omega)
  have b2 : M (q + BitVec.ofNat 32 i + 2) = byteAt d (i + 2) := by
    rw [show q + BitVec.ofNat 32 i + 2 = q + BitVec.ofNat 32 (i + 2) from add_ofNat_assoc _ i 2]
    exact D _ (by omega)
  have b3 : M (q + BitVec.ofNat 32 i + 3) = byteAt d (i + 3) := by
    rw [show q + BitVec.ofNat 32 i + 3 = q + BitVec.ofNat 32 (i + 3) from add_ofNat_assoc _ i 3]
    exact D _ (by omega)
  rw [b0, b1, b2, b3, hv]

end C3.RV32.Sv
