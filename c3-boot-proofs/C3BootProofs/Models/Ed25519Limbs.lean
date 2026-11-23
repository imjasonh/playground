import C3BootProofs.Models.Ed25519Ladder

/-!
# Limb routines that are linear in their inputs

`reduce` keeps the field value of ten limbs below 2^62 and leaves each limb
below 2^26 (`feReduce_val`). `neg` subtracts from `16p`, so `FeNegOK` holds.
-/

namespace C3.RV32.EdM

set_option maxHeartbeats 4000000 in
/-- **`FieldElement2625::reduce` keeps the value modulo `p`** and leaves each
limb below 2^26. -/
theorem feReduce_val (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 : Nat) (h0 : z0 < 2 ^ 62) (h1 : z1 < 2 ^ 62) (h2 : z2 < 2 ^ 62)
    (h3 : z3 < 2 ^ 62) (h4 : z4 < 2 ^ 62) (h5 : z5 < 2 ^ 62) (h6 : z6 < 2 ^ 62) (h7 : z7 < 2 ^ 62) (h8 : z8 < 2 ^ 62)
    (h9 : z9 < 2 ^ 62) :
    Lim (2 ^ 26) (feReduceSpec z0 z1 z2 z3 z4 z5 z6 z7 z8 z9) ∧
    fv (feReduceSpec z0 z1 z2 z3 z4 z5 z6 z7 z8 z9) = (z0 + 2 ^ 26 * z1 + 2 ^ 51 * z2 + 2 ^ 77 * z3 + 2 ^ 102 * z4 +
      2 ^ 128 * z5 + 2 ^ 153 * z6 + 2 ^ 179 * z7 + 2 ^ 204 * z8 + 2 ^ 230 * z9) % Ed25519.p := by
  simp only [feReduceSpec, fv, Lim]
  simp (disch := omega) only [Nat.mod_eq_of_lt]
  refine ⟨⟨rfl, ?_⟩, ?_⟩
  · intro i hi
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [List.getD_cons_succ, List.getD_cons_zero] <;> omega
  · unfold Ed25519.p
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    omega

theorem negZ_toNat (c v : Nat) (hc : c < 2 ^ 32) (hv : v ≤ c) :
    (BitVec.ofNat 32 c - BitVec.ofNat 32 v).toNat = c - v := by
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hv hc)]
  omega

/-- **`FieldElement2625::neg`** computes `-x` with limbs below 2^26. -/
theorem feNeg_ok : FeNegOK := by
  intro l hl
  obtain ⟨-, hb⟩ := hl
  have b0 := hb 0 (by decide); have b1 := hb 1 (by decide); have b2 := hb 2 (by decide)
  have b3 := hb 3 (by decide); have b4 := hb 4 (by decide); have b5 := hb 5 (by decide)
  have b6 := hb 6 (by decide); have b7 := hb 7 (by decide); have b8 := hb 8 (by decide)
  have b9 := hb 9 (by decide)
  have e : ∀ i, i < 10 → (feNegZ (limbF l) i).toNat =
      (if i = 0 then 0x3FFFFED0 else if i % 2 = 0 then 0x3FFFFFF0 else 0x1FFFFFF0) - l.getD i 0 := by
    intro i hi
    unfold feNegZ limbF
    have := hb i hi
    split
    · exact negZ_toNat _ _ (by decide) (by omega)
    · split
      · exact negZ_toNat _ _ (by decide) (by omega)
      · exact negZ_toNat _ _ (by decide) (by omega)
  unfold negL
  rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide), e 5 (by decide),
    e 6 (by decide), e 7 (by decide), e 8 (by decide), e 9 (by decide)]
  simp only [Nat.reduceMod, Nat.zero_ne_one, Nat.succ_ne_zero, ↓reduceIte, OfNat.ofNat_ne_zero, Nat.reduceEqDiff]
  obtain ⟨hL, hv⟩ := feReduce_val _ _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  refine ⟨hL, ?_⟩
  rw [hv]
  unfold fv Ed25519.p
  omega

end C3.RV32.EdM
