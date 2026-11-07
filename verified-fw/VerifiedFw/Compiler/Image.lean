/-
The bytes the emitter writes, loaded by the trusted loader model, put the
compiled code in instruction memory.
-/
import VerifiedFw.Compiler.Exec
import VerifiedFw.Image
import VerifiedFw.Loader

namespace VerifiedFw.Compiler

open VerifiedFw.RiscV VerifiedFw.Loader VerifiedFw.Image

theorem leWord_wordBytes (w : Word) (b : List UInt8) (h : wordBytes w = b) (hl : b.length = 4) :
    leWord b[0] b[1] b[2] b[3] = w := by
  subst h
  apply BitVec.eq_of_toNat_eq
  have hw := w.isLt
  simp only [wordBytes, List.map_cons, List.map_nil, List.getElem_cons_zero,
    List.getElem_cons_succ, leWord, BitVec.toNat_ofNat, BitVec.toNat_ushiftRight,
    Nat.toUInt8, UInt8.toNat_ofNat', Nat.shiftRight_eq_div_pow]
  have h1 : w.toNat / 2 ^ 8 = w.toNat / 256 := rfl
  have h2 : w.toNat / 2 ^ 16 = w.toNat / 256 / 256 := by rw [Nat.div_div_eq_div_mul]
  have h3 : w.toNat / 2 ^ 24 = w.toNat / 256 / 256 / 256 := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
  rw [h1, h2, h3]
  simp only [Nat.pow_zero, Nat.div_one]
  omega

@[simp] theorem wordBytes_length (w : Word) : (wordBytes w).length = 4 := rfl

theorem codeBytes_length (code : List Instr) : (codeBytes code).length = 4 * code.length := by
  induction code with
  | nil => rfl
  | cons i is ih =>
    simp only [codeBytes, List.flatMap_cons, List.length_append, wordBytes_length] at *
    rw [ih]; simp; omega

theorem codeBytes_getElem (code : List Instr) (k j : Nat) (hk : k < code.length) (hj : j < 4) :
    (codeBytes code)[4 * k + j]'(by rw [codeBytes_length]; omega) =
      (wordBytes (encode code[k]))[j]'(by rw [wordBytes_length]; exact hj) := by
  induction code generalizing k with
  | nil => simp at hk
  | cons i is ih =>
    simp only [codeBytes, List.flatMap_cons] at *
    cases k with
    | zero =>
      simp only [Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero]
      rw [List.getElem_append_left]
    | succ k =>
      simp only [List.getElem_cons_succ]
      rw [List.getElem_append_right (by rw [wordBytes_length]; omega)]
      have := ih k (by simp at hk; omega)
      simp only [wordBytes_length]
      rw [← this]
      congr 1; omega

theorem imemOf_eq (base a : Word) (image : List UInt8) (off : Nat)
    (hoff : (a - base).toNat = off) (hlen : off + 4 ≤ image.length) (w : Word)
    (h0 : image[off] = (wordBytes w)[0]) (h1 : image[off + 1] = (wordBytes w)[1])
    (h2 : image[off + 2] = (wordBytes w)[2]) (h3 : image[off + 3] = (wordBytes w)[3]) :
    imemOf base image a = w := by
  subst hoff
  unfold imemOf
  simp only [hlen, ↓reduceDIte]
  rw [h0, h1, h2, h3]
  exact leWord_wordBytes _ _ rfl rfl

/-- An image of `pre` followed by `code`, loaded at `base`, holds `code` from
`base + pre.length`. -/
theorem codeAt_image (base : Word) (pre : List UInt8) (code : List Instr)
    (hfit : pre.length + 4 * code.length < 2 ^ 32) :
    CodeAt (imemOf base (pre ++ codeBytes code)) (base + .ofNat 32 pre.length) code := by
  intro k hk
  have hlen : (pre ++ codeBytes code).length = pre.length + 4 * code.length := by
    simp [codeBytes_length]
  have get : ∀ j (hj : j < 4), (pre ++ codeBytes code)[pre.length + 4 * k + j]'(by
      rw [hlen]; omega) = (wordBytes (encode code[k]))[j]'(by rw [wordBytes_length]; exact hj) := by
    intro j hj
    rw [List.getElem_append_right (by omega)]
    simp only [Nat.add_assoc, Nat.add_sub_cancel_left]
    exact codeBytes_getElem code k j hk hj
  apply imemOf_eq base _ _ (pre.length + 4 * k) _ (by rw [hlen]; omega) (encode code[k])
  · have g0 := get 0 (by omega)
    simp only [Nat.add_zero] at g0
    exact g0
  · exact get 1 (by omega)
  · exact get 2 (by omega)
  · exact get 3 (by omega)
  · simp only [after, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    have := base.isLt
    omega

end VerifiedFw.Compiler
