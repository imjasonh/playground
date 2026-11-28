import C3BootProofs.Proofs.Block
import C3BootProofs.Proofs.ShaSpec

/-!
# 64-bit numbers in two registers

`c3_verify::merkle::root_from_inclusion` keeps its 64-bit index and size
in pairs of registers, low word first. These lemmas read the instruction
sequences it uses on such pairs as operations on the 64-bit number.
-/

namespace C3.RV32

/-- The 64-bit number with low word `lo` and high word `hi`. -/
def pair64 (lo hi : Word) : Nat := hi.toNat * 2 ^ 32 + lo.toNat

theorem pair64_bound (lo hi : Word) : pair64 lo hi < 2 ^ 64 := by
  unfold pair64; have := lo.isLt; have := hi.isLt; omega

/-- `srli lo, lo, 1; slli t, hi, 31; or lo, lo, t; srli hi, hi, 1` halves the pair. -/
theorem pair64_shr1 (lo hi : Word) :
    pair64 (aluEval .or (aluEval .srl lo 1) (aluEval .sll hi 0x1F)) (aluEval .srl hi 1) = pair64 lo hi / 2 := by
  unfold pair64
  show (hi >>> ((1 : Word).toNat % 32)).toNat * 2 ^ 32 +
      ((lo >>> ((1 : Word).toNat % 32)) ||| (hi <<< ((0x1F : Word).toNat % 32))).toNat = _
  rw [show (1 : Word).toNat % 32 = 1 from rfl, show (0x1F : Word).toNat % 32 = 31 from rfl]
  have hl : (lo >>> 1).toNat = lo.toNat / 2 := by rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
  have hh : (hi >>> 1).toNat = hi.toNat / 2 := by rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
  have hs : (hi <<< 31).toNat = hi.toNat % 2 * 2 ^ 31 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; have := hi.isLt; omega
  have hor : ((lo >>> 1) ||| (hi <<< 31)).toNat = (lo >>> 1).toNat + (hi <<< 31).toNat := by
    rw [← Sha256.add_disj (fun i hi' => by
      simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
      by_cases h : i < 31
      · simp [h]
      · have : i = 31 := by omega
        subst this; simp), BitVec.toNat_add]
    rw [hl, hs]; have := lo.isLt; omega
  rw [hh, hor, hl, hs]
  have := lo.isLt; have := hi.isLt
  omega

/-- `andi t, lo, 1` is 1 exactly when the pair is odd. -/
theorem pair64_odd (lo hi : Word) : (aluEval .and lo 1 = 0) ↔ pair64 lo hi % 2 = 0 := by
  unfold pair64
  have e : (aluEval .and lo 1).toNat = lo.toNat % 2 := by
    show (lo &&& 1).toNat = _
    rw [BitVec.toNat_and, show (1 : Word).toNat = 1 from rfl, Nat.and_one_is_mod]
  constructor
  · intro h; have := congrArg BitVec.toNat h; rw [e, show (0 : Word).toNat = 0 from rfl] at this; omega
  · intro h; apply BitVec.eq_of_toNat_eq; rw [e]; show _ = 0; omega

/-- `or t, lo, hi` is 0 exactly when the pair is. -/
theorem pair64_zero (lo hi : Word) : (aluEval .or lo hi = 0) ↔ pair64 lo hi = 0 := by
  unfold pair64
  show (lo ||| hi = 0) ↔ _
  constructor
  · intro h
    have h1 : lo = 0 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi'
      have := congrArg (fun w => w.getLsbD i) h; simp only [BitVec.getLsbD_or] at this ⊢
      cases hl : lo.getLsbD i <;> simp_all
    have h2 : hi = 0 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi'
      have := congrArg (fun w => w.getLsbD i) h; simp only [BitVec.getLsbD_or] at this ⊢
      cases hl : hi.getLsbD i <;> simp_all
    subst h1; subst h2; rfl
  · intro h
    have h1 : lo.toNat = 0 := by omega
    have h2 : hi.toNat = 0 := by have := hi.isLt; omega
    rw [show lo = 0 from BitVec.eq_of_toNat_eq h1, show hi = 0 from BitVec.eq_of_toNat_eq h2]; rfl

theorem pair64_ext {lo hi lo' hi' : Word} (h : pair64 lo hi = pair64 lo' hi') : lo = lo' ∧ hi = hi' := by
  unfold pair64 at h
  have := lo.isLt; have := lo'.isLt
  exact ⟨BitVec.eq_of_toNat_eq (by omega), BitVec.eq_of_toNat_eq (by omega)⟩

/-- `xor t, lo, lo'; xor u, hi, hi'; or t, t, u` is 0 exactly when the pairs are equal. -/
theorem pair64_eq (lo hi lo' hi' : Word) :
    (aluEval .or (aluEval .xor lo lo') (aluEval .xor hi hi') = 0) ↔ pair64 lo hi = pair64 lo' hi' := by
  rw [pair64_zero]
  constructor
  · intro h
    unfold pair64 at h
    have h1 : (aluEval .xor lo lo') = 0 := BitVec.eq_of_toNat_eq (by
      show _ = 0; have := (aluEval .xor hi hi').isLt; omega)
    have h2 : (aluEval .xor hi hi') = 0 := BitVec.eq_of_toNat_eq (by show _ = 0; omega)
    have xe : ∀ a b : Word, a ^^^ b = 0 → a = b := fun a b hab => by
      calc a = a ^^^ (b ^^^ b) := by rw [BitVec.xor_self, BitVec.xor_zero]
        _ = (a ^^^ b) ^^^ b := (BitVec.xor_assoc a b b).symm
        _ = b := by rw [hab]; exact BitVec.zero_xor
    have e1 : lo = lo' := xe lo lo' h1
    have e2 : hi = hi' := xe hi hi' h2
    rw [e1, e2]
  · intro h
    obtain ⟨e1, e2⟩ := pair64_ext h
    subst e1; subst e2
    show pair64 (lo ^^^ lo) (hi ^^^ hi) = 0
    rw [BitVec.xor_self, BitVec.xor_self]; rfl

/-- `seqz t, lo; sub hi', hi, t; addi lo', lo, -1` subtracts 1 from a nonzero pair. -/
theorem pair64_dec (lo hi : Word) (h : 0 < pair64 lo hi) :
    pair64 (aluEval .add lo 0xFFFFFFFF) (aluEval .sub hi (aluEval .sltu lo 1)) = pair64 lo hi - 1 := by
  unfold pair64 at h ⊢
  show (hi - (if lo.ult 1 then 1 else 0)).toNat * 2 ^ 32 + (lo + 0xFFFFFFFF).toNat = _
  have hl := lo.isLt; have hh := hi.isLt
  by_cases h0 : lo.toNat = 0
  · have : lo.ult 1 = true := by simp [BitVec.ult, h0]
    rw [this, ite_eq_left rfl, BitVec.toNat_sub, BitVec.toNat_add, show (1 : Word).toNat = 1 from rfl,
      show (0xFFFFFFFF : Word).toNat = 2 ^ 32 - 1 from rfl]
    omega
  · have : lo.ult 1 = false := by simp [BitVec.ult]; omega
    have e : hi - (0 : Word) = hi := BitVec.sub_zero hi
    rw [this, ite_eq_right (by decide), e, BitVec.toNat_add, show (0xFFFFFFFF : Word).toNat = 2 ^ 32 - 1 from rfl]
    omega

/-- How `root_from_inclusion` compares its index and size: when the high
words are equal, `sltu` on the low words; otherwise `sltu` on the high
words. -/
theorem pair64_lt (lo hi lo' hi' : Word) :
    pair64 lo hi < pair64 lo' hi' ↔ (if hi = hi' then lo.ult lo' else hi.ult hi') = true := by
  unfold pair64
  have := lo.isLt; have := lo'.isLt
  by_cases h : hi = hi'
  · subst h; rw [ite_eq_left rfl]; simp only [BitVec.ult, decide_eq_true_eq]
    exact ⟨fun h1 => by omega, fun h1 => by omega⟩
  · rw [ite_eq_right h]
    simp only [BitVec.ult, decide_eq_true_eq]
    rcases Nat.lt_or_gt_of_ne (fun e => h (BitVec.eq_of_toNat_eq e)) with h2 | h2
    · exact ⟨fun _ => h2, fun _ => by omega⟩
    · exact ⟨fun h1 => by omega, fun h1 => absurd h1 (by omega)⟩

theorem testBit31 (i : Nat) : Nat.testBit 31 i = decide (i < 5) := by
  match i with
  | 0 | 1 | 2 | 3 | 4 => rfl
  | i + 5 =>
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (show 31 < 2 ^ 5 by decide)
      (Nat.pow_le_pow_right (by decide) (by omega)))]
    exact (decide_eq_false (by omega)).symm

theorem and31_nat (k : Nat) : k &&& 31 = k % 32 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, show (32 : Nat) = 2 ^ 5 from rfl, Nat.testBit_mod_two_pow, testBit31, Bool.and_comm]

/-- `andi rd, rs, 0x1F` keeps the value mod 32. -/
theorem toNat_and31 (x : Word) : (x &&& 0x1F#32).toNat = x.toNat % 32 := by
  rw [BitVec.toNat_and, show (0x1F#32).toNat = 31 from rfl, and31_nat]

/-- `srli rd, rs, 5` divides by 32. -/
theorem toNat_srl5 (x : Word) : (x >>> 5).toNat = x.toNat / 32 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

end C3.RV32
