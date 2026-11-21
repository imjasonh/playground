import C3BootProofs.Proofs.FeReduceBody

/-!
# `FieldElement2625::reduce`

`curve25519_dalek`'s carry of ten `u64` limb sums back into a field element,
as compiled: a leaf function that saves `s0` through `s4`, runs the
straight-line body that `FeReduceBody.lean` proves, stores the ten words,
and returns.
-/

namespace C3.RV32

open C3.Image

/-- The ten words that `reduce` stores, read back. -/
theorem wordsAt_st10 (M : Word → BitVec 8) (b w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 : Word) :
    wordsAt (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M (b + 0x0) w0) (b + 0x4) w1) (b + 0x8) w2) (b + 0xC) w3) (b + 0x10) w4) (b + 0x14) w5) (b + 0x18) w6) (b + 0x1C) w7) (b + 0x20) w8) (b + 0x24) w9) b 10 = [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9] := by
  show [memLoad32 _ (b + 0x0), memLoad32 _ (b + 0x4), memLoad32 _ (b + 0x8), memLoad32 _ (b + 0xC), memLoad32 _ (b + 0x10), memLoad32 _ (b + 0x14), memLoad32 _ (b + 0x18), memLoad32 _ (b + 0x1C), memLoad32 _ (b + 0x20), memLoad32 _ (b + 0x24)] = _
  have e0 : memLoad32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M (b + 0x0) w0) (b + 0x4) w1) (b + 0x8) w2) (b + 0xC) w3) (b + 0x10) w4) (b + 0x14) w5) (b + 0x18) w6) (b + 0x1C) w7) (b + 0x20) w8) (b + 0x24) w9) (b + 0x0) = w0 := by
    rw [memLoad32_store32_sep (show Sep (b + 0x24) 4 (b + 0x0) 4 from sep_offsets b (c := 36) (n := 4) (d := 0) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (show Sep (b + 0x20) 4 (b + 0x0) 4 from sep_offsets b (c := 32) (n := 4) (d := 0) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (show Sep (b + 0x1C) 4 (b + 0x0) 4 from sep_offsets b (c := 28) (n := 4) (d := 0) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (show Sep (b + 0x18) 4 (b + 0x0) 4 from sep_offsets b (c := 24) (n := 4) (d := 0) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (show Sep (b + 0x14) 4 (b + 0x0) 4 from sep_offsets b (c := 20) (n := 4) (d := 0) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (show Sep (b + 0x10) 4 (b + 0x0) 4 from sep_offsets b (c := 16) (n := 4) (d := 0) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (show Sep (b + 0xC) 4 (b + 0x0) 4 from sep_offsets b (c := 12) (n := 4) (d := 0) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (show Sep (b + 0x8) 4 (b + 0x0) 4 from sep_offsets b (c := 8) (n := 4) (d := 0) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (show Sep (b + 0x4) 4 (b + 0x0) 4 from sep_offsets b (c := 4) (n := 4) (d := 0) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    exact memLoad32_store32_same _ _ _
  have e1 : memLoad32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M (b + 0x0) w0) (b + 0x4) w1) (b + 0x8) w2) (b + 0xC) w3) (b + 0x10) w4) (b + 0x14) w5) (b + 0x18) w6) (b + 0x1C) w7) (b + 0x20) w8) (b + 0x24) w9) (b + 0x4) = w1 := by
    rw [memLoad32_store32_sep (show Sep (b + 0x24) 4 (b + 0x4) 4 from sep_offsets b (c := 36) (n := 4) (d := 4) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (show Sep (b + 0x20) 4 (b + 0x4) 4 from sep_offsets b (c := 32) (n := 4) (d := 4) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (show Sep (b + 0x1C) 4 (b + 0x4) 4 from sep_offsets b (c := 28) (n := 4) (d := 4) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (show Sep (b + 0x18) 4 (b + 0x4) 4 from sep_offsets b (c := 24) (n := 4) (d := 4) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (show Sep (b + 0x14) 4 (b + 0x4) 4 from sep_offsets b (c := 20) (n := 4) (d := 4) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (show Sep (b + 0x10) 4 (b + 0x4) 4 from sep_offsets b (c := 16) (n := 4) (d := 4) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (show Sep (b + 0xC) 4 (b + 0x4) 4 from sep_offsets b (c := 12) (n := 4) (d := 4) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (show Sep (b + 0x8) 4 (b + 0x4) 4 from sep_offsets b (c := 8) (n := 4) (d := 4) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    exact memLoad32_store32_same _ _ _
  have e2 : memLoad32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M (b + 0x0) w0) (b + 0x4) w1) (b + 0x8) w2) (b + 0xC) w3) (b + 0x10) w4) (b + 0x14) w5) (b + 0x18) w6) (b + 0x1C) w7) (b + 0x20) w8) (b + 0x24) w9) (b + 0x8) = w2 := by
    rw [memLoad32_store32_sep (show Sep (b + 0x24) 4 (b + 0x8) 4 from sep_offsets b (c := 36) (n := 4) (d := 8) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (show Sep (b + 0x20) 4 (b + 0x8) 4 from sep_offsets b (c := 32) (n := 4) (d := 8) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (show Sep (b + 0x1C) 4 (b + 0x8) 4 from sep_offsets b (c := 28) (n := 4) (d := 8) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (show Sep (b + 0x18) 4 (b + 0x8) 4 from sep_offsets b (c := 24) (n := 4) (d := 8) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (show Sep (b + 0x14) 4 (b + 0x8) 4 from sep_offsets b (c := 20) (n := 4) (d := 8) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (show Sep (b + 0x10) 4 (b + 0x8) 4 from sep_offsets b (c := 16) (n := 4) (d := 8) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (show Sep (b + 0xC) 4 (b + 0x8) 4 from sep_offsets b (c := 12) (n := 4) (d := 8) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    exact memLoad32_store32_same _ _ _
  have e3 : memLoad32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M (b + 0x0) w0) (b + 0x4) w1) (b + 0x8) w2) (b + 0xC) w3) (b + 0x10) w4) (b + 0x14) w5) (b + 0x18) w6) (b + 0x1C) w7) (b + 0x20) w8) (b + 0x24) w9) (b + 0xC) = w3 := by
    rw [memLoad32_store32_sep (show Sep (b + 0x24) 4 (b + 0xC) 4 from sep_offsets b (c := 36) (n := 4) (d := 12) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (show Sep (b + 0x20) 4 (b + 0xC) 4 from sep_offsets b (c := 32) (n := 4) (d := 12) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (show Sep (b + 0x1C) 4 (b + 0xC) 4 from sep_offsets b (c := 28) (n := 4) (d := 12) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (show Sep (b + 0x18) 4 (b + 0xC) 4 from sep_offsets b (c := 24) (n := 4) (d := 12) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (show Sep (b + 0x14) 4 (b + 0xC) 4 from sep_offsets b (c := 20) (n := 4) (d := 12) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (show Sep (b + 0x10) 4 (b + 0xC) 4 from sep_offsets b (c := 16) (n := 4) (d := 12) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    exact memLoad32_store32_same _ _ _
  have e4 : memLoad32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M (b + 0x0) w0) (b + 0x4) w1) (b + 0x8) w2) (b + 0xC) w3) (b + 0x10) w4) (b + 0x14) w5) (b + 0x18) w6) (b + 0x1C) w7) (b + 0x20) w8) (b + 0x24) w9) (b + 0x10) = w4 := by
    rw [memLoad32_store32_sep (show Sep (b + 0x24) 4 (b + 0x10) 4 from sep_offsets b (c := 36) (n := 4) (d := 16) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (show Sep (b + 0x20) 4 (b + 0x10) 4 from sep_offsets b (c := 32) (n := 4) (d := 16) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (show Sep (b + 0x1C) 4 (b + 0x10) 4 from sep_offsets b (c := 28) (n := 4) (d := 16) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (show Sep (b + 0x18) 4 (b + 0x10) 4 from sep_offsets b (c := 24) (n := 4) (d := 16) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (show Sep (b + 0x14) 4 (b + 0x10) 4 from sep_offsets b (c := 20) (n := 4) (d := 16) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    exact memLoad32_store32_same _ _ _
  have e5 : memLoad32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M (b + 0x0) w0) (b + 0x4) w1) (b + 0x8) w2) (b + 0xC) w3) (b + 0x10) w4) (b + 0x14) w5) (b + 0x18) w6) (b + 0x1C) w7) (b + 0x20) w8) (b + 0x24) w9) (b + 0x14) = w5 := by
    rw [memLoad32_store32_sep (show Sep (b + 0x24) 4 (b + 0x14) 4 from sep_offsets b (c := 36) (n := 4) (d := 20) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (show Sep (b + 0x20) 4 (b + 0x14) 4 from sep_offsets b (c := 32) (n := 4) (d := 20) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (show Sep (b + 0x1C) 4 (b + 0x14) 4 from sep_offsets b (c := 28) (n := 4) (d := 20) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (show Sep (b + 0x18) 4 (b + 0x14) 4 from sep_offsets b (c := 24) (n := 4) (d := 20) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    exact memLoad32_store32_same _ _ _
  have e6 : memLoad32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M (b + 0x0) w0) (b + 0x4) w1) (b + 0x8) w2) (b + 0xC) w3) (b + 0x10) w4) (b + 0x14) w5) (b + 0x18) w6) (b + 0x1C) w7) (b + 0x20) w8) (b + 0x24) w9) (b + 0x18) = w6 := by
    rw [memLoad32_store32_sep (show Sep (b + 0x24) 4 (b + 0x18) 4 from sep_offsets b (c := 36) (n := 4) (d := 24) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (show Sep (b + 0x20) 4 (b + 0x18) 4 from sep_offsets b (c := 32) (n := 4) (d := 24) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (show Sep (b + 0x1C) 4 (b + 0x18) 4 from sep_offsets b (c := 28) (n := 4) (d := 24) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    exact memLoad32_store32_same _ _ _
  have e7 : memLoad32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M (b + 0x0) w0) (b + 0x4) w1) (b + 0x8) w2) (b + 0xC) w3) (b + 0x10) w4) (b + 0x14) w5) (b + 0x18) w6) (b + 0x1C) w7) (b + 0x20) w8) (b + 0x24) w9) (b + 0x1C) = w7 := by
    rw [memLoad32_store32_sep (show Sep (b + 0x24) 4 (b + 0x1C) 4 from sep_offsets b (c := 36) (n := 4) (d := 28) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (show Sep (b + 0x20) 4 (b + 0x1C) 4 from sep_offsets b (c := 32) (n := 4) (d := 28) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    exact memLoad32_store32_same _ _ _
  have e8 : memLoad32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M (b + 0x0) w0) (b + 0x4) w1) (b + 0x8) w2) (b + 0xC) w3) (b + 0x10) w4) (b + 0x14) w5) (b + 0x18) w6) (b + 0x1C) w7) (b + 0x20) w8) (b + 0x24) w9) (b + 0x20) = w8 := by
    rw [memLoad32_store32_sep (show Sep (b + 0x24) 4 (b + 0x20) 4 from sep_offsets b (c := 36) (n := 4) (d := 32) (k := 4) (.inr (by decide)) (by decide) (by decide))]
    exact memLoad32_store32_same _ _ _
  have e9 : memLoad32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M (b + 0x0) w0) (b + 0x4) w1) (b + 0x8) w2) (b + 0xC) w3) (b + 0x10) w4) (b + 0x14) w5) (b + 0x18) w6) (b + 0x1C) w7) (b + 0x20) w8) (b + 0x24) w9) (b + 0x24) = w9 := by
    exact memLoad32_store32_same _ _ _
  rw [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]

theorem st10_outside (M : Word → BitVec 8) (b w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 x : Word) (hx : Sep b 40 x 1) :
    (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M (b + 0x0) w0) (b + 0x4) w1) (b + 0x8) w2) (b + 0xC) w3) (b + 0x10) w4) (b + 0x14) w5) (b + 0x18) w6) (b + 0x1C) w7) (b + 0x20) w8) (b + 0x24) w9) x = M x := by
  rw [memStore32_get_sep (show Sep (b + 0x24) 4 x 1 from hx.sub (c := 36) (l := 4) (by decide))]
  rw [memStore32_get_sep (show Sep (b + 0x20) 4 x 1 from hx.sub (c := 32) (l := 4) (by decide))]
  rw [memStore32_get_sep (show Sep (b + 0x1C) 4 x 1 from hx.sub (c := 28) (l := 4) (by decide))]
  rw [memStore32_get_sep (show Sep (b + 0x18) 4 x 1 from hx.sub (c := 24) (l := 4) (by decide))]
  rw [memStore32_get_sep (show Sep (b + 0x14) 4 x 1 from hx.sub (c := 20) (l := 4) (by decide))]
  rw [memStore32_get_sep (show Sep (b + 0x10) 4 x 1 from hx.sub (c := 16) (l := 4) (by decide))]
  rw [memStore32_get_sep (show Sep (b + 0xC) 4 x 1 from hx.sub (c := 12) (l := 4) (by decide))]
  rw [memStore32_get_sep (show Sep (b + 0x8) 4 x 1 from hx.sub (c := 8) (l := 4) (by decide))]
  rw [memStore32_get_sep (show Sep (b + 0x4) 4 x 1 from hx.sub (c := 4) (l := 4) (by decide))]
  rw [memStore32_get_sep (show Sep (b + 0x0) 4 x 1 from hx.sub (c := 0) (l := 4) (by decide))]

/-- The stores at the end of `reduce`, from 0x1A4 to 0x1BE. -/
def frStores : List BInstr :=
  [.sw a0 a2 0x0, .sw a0 a3 0x4, .sw a0 a4 0x8, .sw a0 (8 : Fin 32) 0xC, .sw a0 a5 0x10, .sw a0 (5 : Fin 32) 0x14,
   .sw a0 a1 0x18, .sw a0 a6 0x1C, .sw a0 (6 : Fin 32) 0x20, .sw a0 (9 : Fin 32) 0x24]

/-- The registers `reduce` saves, at offsets from its `sp`. -/
abbrev frPs : List (Fin 32 × Word) :=
  [((8 : Fin 32), 0x1C), ((9 : Fin 32), 0x18), ((18 : Fin 32), 0x14), ((19 : Fin 32), 0x10), ((20 : Fin 32), 0xC)]

section
set_option maxRecDepth 20000
theorem frSave_end : blockEnd feReduceCode 2 (saveBlock frPs) = some 0xC := by decide
theorem frStores_end : blockEnd feReduceCode 0x1A4 frStores = some 0x1BE := by decide
theorem frRestore_end : blockEnd feReduceCode 0x1BE (restoreBlock frPs) = some 0x1C8 := by decide
theorem frPs_range : ∀ p ∈ frPs, p.2.toNat % 4 = 0 ∧ 0xC ≤ p.2.toNat ∧ p.2.toNat + 4 ≤ 0x20 := by decide
theorem frPs_sp : ∀ p ∈ frPs, p.1 ≠ sp := by decide
end

/-- Where `reduce` runs: its code at an even `P`, the 0x20 bytes of stack
below `sp0` that it saves registers in, the ten-word result at `out`, and
the ten `u64` limbs at `zp`, apart where they must be. -/
structure FREnv (M : Word → BitVec 8) (P sp0 out zp : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P feReduceCode
  hsp : sp0.toNat % 4 = 0
  hS : 0x20 ≤ sp0.toNat
  hout : out.toNat % 4 = 0
  hzp : zp.toNat % 4 = 0
  sSC : Sep (sp0 + 0xFFFFFFE0) 0x20 P feReduceCode.length
  sOC : Sep out 40 P feReduceCode.length
  sOS : Sep out 40 (sp0 + 0xFFFFFFE0) 0x20
  sZS : Sep zp 80 (sp0 + 0xFFFFFFE0) 0x20

/-- The registers `reduce` leaves as they were. -/
def frKeep (q : Fin 32) : Bool := q.val ∉ [5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31]

theorem frKeep_body : ∀ q, frKeep q = true → (q ∈ frPs.map Prod.fst ∨ frBodyKeep q = true) := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `FieldElement2625::reduce`**, called with the result at
`out` and ten `u64` limbs at `zp`: it stores `feReduceSpec` of the limbs,
returns with `sp` and every register but `t0` through `t6` and `a1` through
`a7` as they were, and changes no memory outside its 0x20 bytes of stack
and the result. -/
theorem feReduce_correct (m : Machine) {P sp0 out zp retAddr : Word} (env : FREnv m.mem P sp0 out zp)
    (hpc : m.pc = P) (ha0 : reg m a0 = out) (ha1 : reg m a1 = zp) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧ (∀ q, frKeep q = true → reg m' q = reg m q) ∧
      (wordsAt m'.mem out 10).map BitVec.toNat =
        feReduceSpec (u64At m.mem zp 0) (u64At m.mem zp 1) (u64At m.mem zp 2) (u64At m.mem zp 3)
          (u64At m.mem zp 4) (u64At m.mem zp 5) (u64At m.mem zp 6) (u64At m.mem zp 7) (u64At m.mem zp 8)
          (u64At m.mem zp 9) ∧
      ∀ x, Sep (sp0 + 0xFFFFFFE0) 0x20 x 1 → Sep out 40 x 1 → m'.mem x = m.mem x := by
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have hFa : (sp0 + 0xFFFFFFE0).toNat % 4 = 0 := aligned_add env.hsp (k := 0xFFFFFFE0) (by decide)
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.code fr_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFE0) sp = sp0 + 0xFFFFFFE0 := by
    simp +decide only [upd_app, ↓reduceIte]; rw [hsp]; rfl
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock frPs) u1 env.code frSave_end (saveBlock_ok _ frPs _ fun p hp => by
    rw [sp1]
    exact ⟨fr_al' hFa (frPs_range p hp).1, frm_sep' env.sSC (by have := frPs_range p hp; omega)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem (sp0 + 0xFFFFFFE0)
      (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFE0)) frPs = Msv := ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ x, Sep (sp0 + 0xFFFFFFE0) 0x20 x 1 → Msv x = m.mem x := fun x hx => by
    rw [← hMsv]; exact saveMem_outside frPs fun p hp => frm_sep' hx (by have := frPs_range p hp; omega)
  have hcS : CodeIn Msv P feReduceCode := fun i hi => by
    rw [frSv _ (env.sSC.subR (c := i) (l := 1) (by omega))]; exact env.code i hi
  have k2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q hq => by
    rw [u2.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, hq]
  have sp2 : reg m2 sp = sp0 + 0xFFFFFFE0 := by rw [u2.regs]; exact sp1
  -- the body
  obtain ⟨n3, c3, u3, hl3, k3⟩ := fr_body u2.self hcS (by rw [k2 a1 (by decide), ha1]) env.hzp
  have r3a0 : reg n3 a0 = out := by rw [k3 a0 rfl, k2 a0 (by decide), ha0]
  have r3sp : reg n3 sp = sp0 + 0xFFFFFFE0 := by rw [k3 sp rfl, sp2]
  -- the stores
  obtain ⟨n4, c4, u4⟩ := St.block frStores u3 hcS frStores_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, frStores, and_true]
    rw [r3a0]
    exact ⟨⟨fr_al' env.hout (by decide), frm_sep' env.sOC (by decide)⟩,
      ⟨fr_al' env.hout (by decide), frm_sep' env.sOC (by decide)⟩,
      ⟨fr_al' env.hout (by decide), frm_sep' env.sOC (by decide)⟩,
      ⟨fr_al' env.hout (by decide), frm_sep' env.sOC (by decide)⟩,
      ⟨fr_al' env.hout (by decide), frm_sep' env.sOC (by decide)⟩,
      ⟨fr_al' env.hout (by decide), frm_sep' env.sOC (by decide)⟩,
      ⟨fr_al' env.hout (by decide), frm_sep' env.sOC (by decide)⟩,
      ⟨fr_al' env.hout (by decide), frm_sep' env.sOC (by decide)⟩,
      ⟨fr_al' env.hout (by decide), frm_sep' env.sOC (by decide)⟩,
      fr_al' env.hout (by decide), frm_sep' env.sOC (by decide)⟩)
  simp only [runBlock, BInstr.run, frStores] at u4
  rw [r3a0] at u4
  obtain ⟨Mst, hMst⟩ : ∃ Mst, memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32
      (memStore32 (memStore32 (memStore32 (memStore32 Msv (out + 0x0) (reg n3 a2)) (out + 0x4) (reg n3 a3))
      (out + 0x8) (reg n3 a4)) (out + 0xC) (reg n3 (8 : Fin 32))) (out + 0x10) (reg n3 a5))
      (out + 0x14) (reg n3 (5 : Fin 32))) (out + 0x18) (reg n3 a1)) (out + 0x1C) (reg n3 a6))
      (out + 0x20) (reg n3 (6 : Fin 32))) (out + 0x24) (reg n3 (9 : Fin 32)) = Mst := ⟨_, rfl⟩
  rw [hMst] at u4
  have outSt : ∀ x, Sep out 40 x 1 → Mst x = Msv x := fun x hx => by rw [← hMst]; exact st10_outside _ _ _ _ _ _ _ _ _ _ _ _ _ hx
  have hcT : CodeIn Mst P feReduceCode := fun i hi => by
    rw [outSt _ (env.sOC.subR (c := i) (l := 1) (by omega))]; exact hcS i hi
  -- the restores and the return
  obtain ⟨n5, c5, u5⟩ := St.block (restoreBlock frPs) u4 hcT frRestore_end
    (restoreBlock_ok Mst _ frPs (reg n3) r3sp frPs_sp fun p hp => fr_al' hFa (frPs_range p hp).1)
  simp only [restoreBlock_run Mst _ frPs (reg n3) r3sp frPs_sp] at u5
  have rsp5 : restoreRegs Mst (sp0 + 0xFFFFFFE0) (reg n3) frPs sp = sp0 + 0xFFFFFFE0 := by
    rw [restoreRegs_sp _ _ _ _ frPs_sp]; exact r3sp
  obtain ⟨n6, d6, u6⟩ := u5.aluImm hcT fr_at_1c8 (off' := 0x1CA) (by decide)
  obtain ⟨n7, d7, pc7, mem7, regs7⟩ := u6.jalr hcT fr_at_1ca
  have slot : ∀ r o, (r, o) ∈ frPs → memLoad32 Mst (sp0 + 0xFFFFFFE0 + o) = reg m r := fun r o h => by
    obtain ⟨_, ho1, ho2⟩ := frPs_range (r, o) h
    dsimp only at ho1 ho2
    have hs : Sep out 40 (sp0 + 0xFFFFFFE0 + o) 4 := by
      have := env.sOS.subR (c := o.toNat) (l := 4) (by omega); rwa [ofNat_toNat_self] at this
    rw [load_frame outSt hs, ← hMsv]
    simp only [frPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  have zS : ∀ i, i < 10 → u64At Msv zp i = u64At m.mem zp i := fun i hi => by
    unfold u64At
    rw [load_frame frSv (env.sZS.symm.subR (c := 8 * i) (l := 4) (by omega)),
      load_frame frSv (env.sZS.symm.subR (c := 8 * i + 4) (l := 4) (by omega))]
  refine ⟨n7, .cons d1 (c2.trans (c3.trans (c4.trans (c5.trans (.cons d6 (.single d7)))))), ?_, ?_, ?_, ?_, ?_⟩
  · rw [pc7]; simp +decide only [upd_app, ↓reduceIte]
    simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
    rw [add_lit_zero, k3 ra rfl, k2 ra (by decide), hra, hret]
  · rw [regs7]; simp +decide only [upd_app, ↓reduceIte, aluEval]; rw [rsp5, BitVec.add_assoc]
    exact BitVec.add_zero _
  · intro q hq
    rw [regs7]
    by_cases hs : q = sp
    · subst hs
      simp +decide only [upd_app, ↓reduceIte, aluEval]; rw [rsp5, BitVec.add_assoc, hsp]
      exact BitVec.add_zero _
    rcases frKeep_body q hq with h | h
    · simp only [frPs, List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl <;>
      · simp +decide only [upd_app, ↓reduceIte]
        simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
        exact slot _ _ (by decide)
    · by_cases h0 : q.val = 0
      · have : q = 0 := Fin.ext h0
        subst this; simp [upd]; exact hz.symm
      rw [upd_ne h0 hs]
      simp only [restoreRegs]
      rw [upd_ne h0 (bkeep_ne h (r := 20) rfl), upd_ne h0 (bkeep_ne h (r := 19) rfl),
        upd_ne h0 (bkeep_ne h (r := 18) rfl), upd_ne h0 (bkeep_ne h (r := 9) rfl),
        upd_ne h0 (bkeep_ne h (r := 8) rfl), k3 q h, k2 q hs]
  · rw [mem7, ← hMst, wordsAt_st10, hl3, zS 0 (by decide), zS 1 (by decide), zS 2 (by decide), zS 3 (by decide),
      zS 4 (by decide), zS 5 (by decide), zS 6 (by decide), zS 7 (by decide), zS 8 (by decide), zS 9 (by decide)]
  · intro x hx ho
    rw [mem7, outSt x ho, frSv x hx]

end C3.RV32
