import C3BootProofs.Spec.Sha512
import C3BootProofs.Proofs.ShaTools

/-!
# SHA-512's 64-bit words as pairs of 32-bit words

The compiled `compress512` keeps each 64-bit word in two registers. These
are the halves of the specification's operations, in the forms the compiled
code computes them: rotations and shifts as shifts and `or`s of both halves,
and additions as 32-bit additions with the carry from `sltu`. None of the
proofs uses `Classical.choice`.
-/

namespace C3.RV32

open C3.Sha512

/-- The low 32 bits of a 64-bit word. -/
def lo64 (x : W64) : Word := x.extractLsb' 0 32

/-- The high 32 bits of a 64-bit word. -/
def hi64 (x : W64) : Word := x.extractLsb' 32 32

theorem lo64_bit (x : W64) {i : Nat} (hi : i < 32) : (lo64 x).getLsbD i = x.getLsbD i := by
  unfold lo64; rw [BitVec.getLsbD_extractLsb', Nat.zero_add, decide_eq_true hi, Bool.true_and]

theorem hi64_bit (x : W64) {i : Nat} (hi : i < 32) : (hi64 x).getLsbD i = x.getLsbD (32 + i) := by
  unfold hi64; rw [BitVec.getLsbD_extractLsb', decide_eq_true hi, Bool.true_and]

theorem lo64_toNat (x : W64) : (lo64 x).toNat = x.toNat % 2 ^ 32 := by
  unfold lo64; rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]

theorem hi64_toNat (x : W64) : (hi64 x).toNat = x.toNat / 2 ^ 32 := by
  unfold hi64
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  exact Nat.mod_eq_of_lt (by omega)

/-- A 64-bit word is its two halves. -/
theorem val64 (x : W64) : x.toNat = (lo64 x).toNat + 2 ^ 32 * (hi64 x).toNat := by
  rw [lo64_toNat, hi64_toNat]; omega

theorem w64_ext {x y : W64} (hl : lo64 x = lo64 y) (hh : hi64 x = hi64 y) : x = y := by
  apply BitVec.eq_of_toNat_eq
  rw [val64 x, val64 y, hl, hh]

theorem bit32 {x y : Word} (h : ∀ i, i < 32 → x.getLsbD i = y.getLsbD i) : x = y :=
  BitVec.eq_of_getLsbD_eq fun i hi => h i hi

theorem lo64_xor (x y : W64) : lo64 (x ^^^ y) = lo64 x ^^^ lo64 y :=
  bit32 fun i hi => by rw [BitVec.getLsbD_xor, lo64_bit _ hi, lo64_bit _ hi, lo64_bit _ hi, BitVec.getLsbD_xor]

theorem hi64_xor (x y : W64) : hi64 (x ^^^ y) = hi64 x ^^^ hi64 y :=
  bit32 fun i hi => by rw [BitVec.getLsbD_xor, hi64_bit _ hi, hi64_bit _ hi, hi64_bit _ hi, BitVec.getLsbD_xor]

theorem lo64_and (x y : W64) : lo64 (x &&& y) = lo64 x &&& lo64 y :=
  bit32 fun i hi => by rw [BitVec.getLsbD_and, lo64_bit _ hi, lo64_bit _ hi, lo64_bit _ hi, BitVec.getLsbD_and]

theorem hi64_and (x y : W64) : hi64 (x &&& y) = hi64 x &&& hi64 y :=
  bit32 fun i hi => by rw [BitVec.getLsbD_and, hi64_bit _ hi, hi64_bit _ hi, hi64_bit _ hi, BitVec.getLsbD_and]

theorem bv_bit_eq {n : Nat} (x : BitVec n) {a b : Nat} (h : a = b) : x.getLsbD a = x.getLsbD b := by rw [h]

/-- A right rotation by `r` below 32, on the halves. -/
theorem lo64_rotr {r : Nat} (x : W64) (h0 : 0 < r) (h1 : r < 32) :
    lo64 (x.rotateRight r) = (lo64 x >>> r) ||| (hi64 x <<< (32 - r)) := by
  apply bit32; intro i hi
  have hm : r % 64 = r := Nat.mod_eq_of_lt (by omega)
  rw [lo64_bit _ hi, BitVec.getLsbD_rotateRight, hm, ite_eq_left (by omega : i < 64 - r), BitVec.getLsbD_or,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  by_cases hr : r + i < 32
  · rw [lo64_bit _ hr, decide_eq_true (show i < 32 - r by omega)]
    simp only [Bool.not_true, Bool.and_false, Bool.false_and, Bool.or_false]
  · rw [BitVec.getLsbD_of_ge (lo64 x) (r + i) (by omega), decide_eq_true hi,
      decide_eq_false (by omega : ¬ i < 32 - r), hi64_bit _ (by omega), Bool.false_or, Bool.true_and,
      Bool.not_false, Bool.true_and]
    exact bv_bit_eq x (by omega)

theorem hi64_rotr {r : Nat} (x : W64) (h0 : 0 < r) (h1 : r < 32) :
    hi64 (x.rotateRight r) = (hi64 x >>> r) ||| (lo64 x <<< (32 - r)) := by
  apply bit32; intro i hi
  have hm : r % 64 = r := Nat.mod_eq_of_lt (by omega)
  rw [hi64_bit _ hi, BitVec.getLsbD_rotateRight, hm, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_shiftLeft]
  by_cases hr : r + i < 32
  · rw [ite_eq_left (by omega : 32 + i < 64 - r), hi64_bit _ hr, decide_eq_true (show i < 32 - r by omega)]
    simp only [Bool.not_true, Bool.and_false, Bool.false_and, Bool.or_false]
    exact bv_bit_eq x (by omega)
  · rw [ite_eq_right (by omega : ¬ 32 + i < 64 - r), BitVec.getLsbD_of_ge (hi64 x) (r + i) (by omega),
      decide_eq_true hi, decide_eq_false (by omega : ¬ i < 32 - r), lo64_bit _ (by omega), Bool.false_or,
      Bool.true_and, Bool.not_false, Bool.true_and, decide_eq_true (by omega : 32 + i < 64), Bool.true_and]
    exact bv_bit_eq x (by omega)

/-- A right rotation by `r` above 32, on the halves: the halves trade
places. -/
theorem lo64_rotr' {r : Nat} (x : W64) (h0 : 32 < r) (h1 : r < 64) :
    lo64 (x.rotateRight r) = (hi64 x >>> (r - 32)) ||| (lo64 x <<< (64 - r)) := by
  apply bit32; intro i hi
  have hm : r % 64 = r := Nat.mod_eq_of_lt (by omega)
  rw [lo64_bit _ hi, BitVec.getLsbD_rotateRight, hm, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_shiftLeft]
  by_cases hr : r - 32 + i < 32
  · rw [ite_eq_left (by omega : i < 64 - r), hi64_bit _ hr, decide_eq_true (show i < 64 - r by omega)]
    simp only [Bool.not_true, Bool.and_false, Bool.false_and, Bool.or_false]
    exact bv_bit_eq x (by omega)
  · rw [ite_eq_right (by omega : ¬ i < 64 - r), BitVec.getLsbD_of_ge (hi64 x) (r - 32 + i) (by omega),
      decide_eq_true hi, decide_eq_false (by omega : ¬ i < 64 - r), lo64_bit _ (by omega), Bool.false_or,
      Bool.true_and, Bool.not_false, Bool.true_and, decide_eq_true (by omega : i < 64), Bool.true_and]

theorem hi64_rotr' {r : Nat} (x : W64) (h0 : 32 < r) (h1 : r < 64) :
    hi64 (x.rotateRight r) = (lo64 x >>> (r - 32)) ||| (hi64 x <<< (64 - r)) := by
  apply bit32; intro i hi
  have hm : r % 64 = r := Nat.mod_eq_of_lt (by omega)
  rw [hi64_bit _ hi, BitVec.getLsbD_rotateRight, hm, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_shiftLeft]
  by_cases hr : r - 32 + i < 32
  · rw [ite_eq_right (by omega : ¬ 32 + i < 64 - r), lo64_bit _ hr, decide_eq_true (show i < 64 - r by omega),
      decide_eq_true (by omega : 32 + i < 64)]
    simp only [Bool.not_true, Bool.and_false, Bool.false_and, Bool.or_false, Bool.true_and]
    exact bv_bit_eq x (by omega)
  · rw [ite_eq_right (by omega : ¬ 32 + i < 64 - r), BitVec.getLsbD_of_ge (lo64 x) (r - 32 + i) (by omega),
      decide_eq_true hi, decide_eq_false (by omega : ¬ i < 64 - r), hi64_bit _ (by omega), Bool.false_or,
      Bool.true_and, Bool.not_false, Bool.true_and, decide_eq_true (by omega : 32 + i < 64), Bool.true_and]
    exact bv_bit_eq x (by omega)

/-- A right shift by `r` below 32, on the halves. -/
theorem lo64_shr {r : Nat} (x : W64) (h0 : 0 < r) (h1 : r < 32) :
    lo64 (x >>> r) = (lo64 x >>> r) ||| (hi64 x <<< (32 - r)) := by
  apply bit32; intro i hi
  rw [lo64_bit _ hi, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_shiftLeft]
  by_cases hr : r + i < 32
  · rw [lo64_bit _ hr, decide_eq_true (show i < 32 - r by omega)]
    simp only [Bool.not_true, Bool.and_false, Bool.false_and, Bool.or_false]
  · rw [BitVec.getLsbD_of_ge (lo64 x) (r + i) (by omega), decide_eq_true hi,
      decide_eq_false (by omega : ¬ i < 32 - r), hi64_bit _ (by omega), Bool.false_or, Bool.true_and,
      Bool.not_false, Bool.true_and]
    exact bv_bit_eq x (by omega)

theorem hi64_shr (r : Nat) (x : W64) : hi64 (x >>> r) = hi64 x >>> r := by
  apply bit32; intro i hi
  rw [hi64_bit _ hi, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ushiftRight]
  by_cases hr : r + i < 32
  · rw [hi64_bit _ hr]; exact bv_bit_eq x (by omega)
  · rw [BitVec.getLsbD_of_ge (hi64 x) (r + i) (by omega), BitVec.getLsbD_of_ge x (r + (32 + i)) (by omega)]

/-- The carry out of a 32-bit addition, as `sltu` computes it. -/
theorem sltu_carry (x y : Word) : (aluEval .sltu (x + y) x).toNat = (x.toNat + y.toNat) / 2 ^ 32 := by
  have hx := x.isLt
  have hy := y.isLt
  have hs : (x + y).toNat = (x.toNat + y.toNat) % 2 ^ 32 := BitVec.toNat_add x y
  show (if (x + y).ult x then (1 : Word) else 0).toNat = _
  by_cases h : (x + y).toNat < x.toNat
  · rw [ite_eq_left (show (x + y).ult x = true from decide_eq_true h)]; show 1 = _; omega
  · rw [ite_eq_right (show ¬ (x + y).ult x = true from fun e => h (of_decide_eq_true e))]; show 0 = _; omega

theorem sltu_carry' (x y : Word) : (aluEval .sltu (x + y) y).toNat = (x.toNat + y.toNat) / 2 ^ 32 := by
  rw [BitVec.add_comm x y, sltu_carry, Nat.add_comm]

end C3.RV32
