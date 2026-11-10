import C3BootProofs.Proof.Step

/-!
# Loads after stores

What a load reads after stores: the stored value at the stored address, and
the old value where `Sep` says the store didn't reach. `sep_offsets` gives
`Sep` for two ranges at different offsets from one base.
-/

namespace C3.RV32

theorem bytes_reassemble (v : Word) :
    v.extractLsb' 24 8 ++ v.extractLsb' 16 8 ++ v.extractLsb' 8 8 ++ v.extractLsb' 0 8 = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h0 : i < 8
  · simp [h0]
  · by_cases h1 : i - 8 < 8
    · simp [h0, h1]; congr 1; omega
    · by_cases h2 : i - 8 - 8 < 8
      · simp [h0, h1, h2]; congr 1; omega
      · have h3 : i - 8 - 8 - 8 < 8 := by omega
        simp [h0, h1, h2, h3]; congr 1; omega

theorem memStore8_same (M : Word → BitVec 8) (a : Word) (v : BitVec 8) :
    memStore8 M a v a = v := by
  unfold memStore8; exact ite_eq_left rfl

theorem memStore8_ne {M : Word → BitVec 8} {a x : Word} {v : BitVec 8} (h : x ≠ a) :
    memStore8 M a v x = M x := by
  unfold memStore8; exact ite_eq_right h

theorem ofNat_inj {c d : Nat} (hc : c < 2 ^ 32) (hd : d < 2 ^ 32)
    (h : BitVec.ofNat 32 c = BitVec.ofNat 32 d) : c = d := by
  have := congrArg BitVec.toNat h
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hd] at this

theorem add_ofNat_ne (b : Word) {c d : Nat} (hc : c < 2 ^ 32) (hd : d < 2 ^ 32) (h : c ≠ d) :
    b + BitVec.ofNat 32 c ≠ b + BitVec.ofNat 32 d := by
  intro e
  have e' : BitVec.ofNat 32 c = BitVec.ofNat 32 d := by
    have := congrArg (fun x => x - b) e
    rwa [BitVec.add_comm b, BitVec.add_sub_cancel, BitVec.add_comm b, BitVec.add_sub_cancel] at this
  exact h (ofNat_inj hc hd e')

/-- Two ranges at different offsets from one base don't overlap if the
offsets put them apart and neither passes `2 ^ 32`. -/
theorem sep_offsets (b : Word) {c n d k : Nat} (h : c + n ≤ d ∨ d + k ≤ c)
    (hc : c + n ≤ 2 ^ 32) (hd : d + k ≤ 2 ^ 32) :
    Sep (b + BitVec.ofNat 32 c) n (b + BitVec.ofNat 32 d) k := by
  intro i hi j hj
  rw [add_ofNat_assoc, add_ofNat_assoc]
  exact add_ofNat_ne b (by omega) (by omega) (by omega)

theorem Sep.symm {a b : Word} {n k : Nat} (h : Sep a n b k) : Sep b k a n :=
  fun i hi j hj e => h j hj i hi e.symm

theorem Sep.point {a b : Word} {n k : Nat} (h : Sep a n b k) {i j : Nat} (hi : i < n) (hj : j < k) :
    a + BitVec.ofNat 32 i ≠ b + BitVec.ofNat 32 j :=
  h i hi j hj

theorem memStore32_ne {M : Word → BitVec 8} {a x v : Word}
    (h : ∀ i, i < 4 → x ≠ a + BitVec.ofNat 32 i) : memStore32 M a v x = M x := by
  have h0 : x ≠ a := by
    have := h 0 (by decide)
    rwa [add_ofNat_zero] at this
  unfold memStore32
  rw [memStore8_ne (show x ≠ a + 3 from h 3 (by decide)),
    memStore8_ne (show x ≠ a + 2 from h 2 (by decide)),
    memStore8_ne (show x ≠ a + 1 from h 1 (by decide)), memStore8_ne h0]

theorem memLoad32_store32_same (M : Word → BitVec 8) (a v : Word) :
    memLoad32 (memStore32 M a v) a = v := by
  have n10 : a + 1 ≠ a := by
    have := add_ofNat_ne a (c := 1) (d := 0) (by decide) (by decide) (by decide)
    rwa [add_ofNat_zero] at this
  have n20 : a + 2 ≠ a := by
    have := add_ofNat_ne a (c := 2) (d := 0) (by decide) (by decide) (by decide)
    rwa [add_ofNat_zero] at this
  have n30 : a + 3 ≠ a := by
    have := add_ofNat_ne a (c := 3) (d := 0) (by decide) (by decide) (by decide)
    rwa [add_ofNat_zero] at this
  have n21 : a + 2 ≠ a + 1 := add_ofNat_ne a (c := 2) (d := 1) (by decide) (by decide) (by decide)
  have n31 : a + 3 ≠ a + 1 := add_ofNat_ne a (c := 3) (d := 1) (by decide) (by decide) (by decide)
  have n32 : a + 3 ≠ a + 2 := add_ofNat_ne a (c := 3) (d := 2) (by decide) (by decide) (by decide)
  unfold memLoad32 memStore32
  rw [memStore8_same, memStore8_ne n32.symm, memStore8_same, memStore8_ne n31.symm,
    memStore8_ne n21.symm, memStore8_same, memStore8_ne n30.symm, memStore8_ne n20.symm,
    memStore8_ne n10.symm, memStore8_same]
  exact bytes_reassemble v

theorem memLoad32_congr {M M' : Word → BitVec 8} {b : Word}
    (h : ∀ j, j < 4 → M' (b + BitVec.ofNat 32 j) = M (b + BitVec.ofNat 32 j)) :
    memLoad32 M' b = memLoad32 M b := by
  unfold memLoad32
  have h0 := h 0 (by decide)
  rw [add_ofNat_zero] at h0
  rw [h0, show b + 1 = b + BitVec.ofNat 32 1 from rfl, h 1 (by decide),
    show b + 2 = b + BitVec.ofNat 32 2 from rfl, h 2 (by decide),
    show b + 3 = b + BitVec.ofNat 32 3 from rfl, h 3 (by decide)]

theorem memLoad32_store32_sep {M : Word → BitVec 8} {a b v : Word} (h : Sep a 4 b 4) :
    memLoad32 (memStore32 M a v) b = memLoad32 M b :=
  memLoad32_congr fun j hj => memStore32_ne fun i hi e => h i hi j hj e.symm

theorem memLoad32_store8_sep {M : Word → BitVec 8} {a b : Word} {v : BitVec 8} (h : Sep a 1 b 4) :
    memLoad32 (memStore8 M a v) b = memLoad32 M b :=
  memLoad32_congr fun j hj => memStore8_ne fun e => h 0 (by decide) j hj
    (by rw [add_ofNat_zero]; exact e.symm)

theorem memStore32_get_sep {M : Word → BitVec 8} {a x v : Word} (h : Sep a 4 x 1) :
    memStore32 M a v x = M x :=
  memStore32_ne fun i hi e => h i hi 0 (by decide) (by rw [add_ofNat_zero]; exact e.symm)

end C3.RV32
