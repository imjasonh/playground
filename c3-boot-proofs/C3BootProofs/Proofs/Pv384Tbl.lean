import C3BootProofs.Proofs.Pv384Lib4

/-!
# `p384_verify_prehash`: tables of points in the frame

A table of `n` points at offset `c` of the frame, as one fact: the stages
that build and read the tables of the linear combination carry each table
this way instead of as 3·`n` separate limb facts.
-/

namespace C3.RV32.Pv

open C3.Image C3.RV32.P3 C3.RV32.Dq

/-- A point whose three coordinates the frame holds at offset `c`. -/
theorem ptV_mk {M : Word → BitVec 8} {B : Word} {c : Nat} {P : Pt}
    (h1 : accV M (B + 0x420 + BitVec.ofNat 32 c) 12 = P.1)
    (h2 : accV M (B + 0x420 + BitVec.ofNat 32 (c + 0x30)) 12 = P.2.1)
    (h3 : accV M (B + 0x420 + BitVec.ofNat 32 (c + 0x60)) 12 = P.2.2) : ptV M B c = P := by
  unfold ptV; rw [h1, h2, h3]

/-- A table survives a step that wrote elsewhere. -/
theorem tbl_keep {B : Word} {M M' : Word → BitVec 8} {c w c0 n : Nat} {T : Nat → Pt} (K : PvKeep B M M' c w)
    (hn : c0 + 0x90 * n ≤ 0x1D4C) (hs : c0 + 0x90 * n ≤ c ∨ c + w ≤ c0)
    (h : ∀ j, j < n → ptV M B (c0 + 0x90 * j) = T j) : ∀ j, j < n → ptV M' B (c0 + 0x90 * j) = T j :=
  fun j hj => by
    rw [← h j hj]; unfold ptV
    rw [K.acc (k := 12) (by omega) (by omega), K.acc (k := 12) (by omega) (by omega),
      K.acc (k := 12) (by omega) (by omega)]

/-- A table moves with a copy of the bytes that hold it. -/
theorem tbl_cp {B : Word} {M M' : Word → BitVec 8} {dst src N c0 d0 n : Nat} {T : Nat → Pt}
    (V : ∀ q, q < N → M' (B + 0x420 + BitVec.ofNat 32 (dst + q)) = M (B + 0x420 + BitVec.ofNat 32 (src + q)))
    (h1 : src ≤ c0) (h2 : c0 + 0x90 * n ≤ src + N) (hd : d0 + src = c0 + dst)
    (h : ∀ j, j < n → ptV M B (c0 + 0x90 * j) = T j) : ∀ j, j < n → ptV M' B (d0 + 0x90 * j) = T j :=
  fun j hj => by
    rw [← h j hj]; unfold ptV
    have e : ∀ o, o + 48 ≤ 0x90 → accV M' (B + 0x420 + BitVec.ofNat 32 (d0 + 0x90 * j + o)) 12 =
        accV M (B + 0x420 + BitVec.ofNat 32 (c0 + 0x90 * j + o)) 12 := fun o ho =>
      accV_S 12 fun q hq => by
        have := V (c0 - src + 0x90 * j + o + q) (by have := Nat.mul_le_mul_left 0x90 hj; omega)
        rwa [show dst + (c0 - src + 0x90 * j + o + q) = d0 + 0x90 * j + o + q by omega,
          show src + (c0 - src + 0x90 * j + o + q) = c0 + 0x90 * j + o + q by omega] at this
    have e0 := e 0 (by decide)
    rw [Nat.add_zero, Nat.add_zero] at e0
    rw [e0, e 0x30 (by decide), e 0x60 (by decide)]

end C3.RV32.Pv
