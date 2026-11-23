import C3BootProofs.Models.Ed25519Field
import C3BootProofs.Proofs.Ed25519PkOk

/-!
# Byte strings as numbers

`lv k l` is the number the first `k` bytes of `l` spell little-endian.
`less_than_le` (`ltLEb`) decides `<` on those numbers, `clearTop` takes the
number modulo 2^255, and two 32-byte strings with the same number are
equal. `decode_of_recoverX` unfolds the specification's `decode`.
-/

namespace C3.RV32.EdM

/-- The first `k` bytes of `l`, little-endian. -/
def lv : Nat → List Nat → Nat
  | 0, _ => 0
  | k + 1, l => lv k l + l.getD k 0 * 256 ^ k

/-- Every byte of `l` is below 256. -/
def Byt (l : List Nat) : Prop := ∀ i, l.getD i 0 < 256

theorem getD_of_lt {l : List Nat} {i : Nat} (h : i < l.length) : l.getD i 0 = l[i] := by simp [List.getD, h]

theorem getD_of_ge {l : List Nat} {i : Nat} (h : l.length ≤ i) : l.getD i 0 = 0 := by simp [List.getD, h]

theorem byt_memBytes (M : Word → BitVec 8) (a : Word) (n : Nat) : Byt (memBytes M a n) := fun i => by
  by_cases h : i < n
  · exact memBytes_lt M a h
  · rw [getD_of_ge (by rw [memBytes_length]; omega)]; decide

theorem lv_lt {l : List Nat} (h : Byt l) : ∀ k, lv k l < 256 ^ k
  | 0 => Nat.zero_lt_one
  | k + 1 => by
    have h1 := lv_lt h k
    have h2 : l.getD k 0 * 256 ^ k ≤ 255 * 256 ^ k := Nat.mul_le_mul_right _ (by have := h k; omega)
    simp only [lv, Nat.pow_succ]
    omega

theorem lv_congr {l l' : List Nat} : ∀ k, (∀ i, i < k → l.getD i 0 = l'.getD i 0) → lv k l = lv k l'
  | 0, _ => rfl
  | k + 1, h => by simp only [lv]; rw [lv_congr k fun i hi => h i (by omega), h k (by omega)]

theorem lv_cons (a : Nat) (l : List Nat) : ∀ k, lv (k + 1) (a :: l) = a + 256 * lv k l
  | 0 => by simp only [lv, List.getD_cons_zero, Nat.pow_zero, Nat.mul_one, Nat.zero_add, Nat.mul_zero, Nat.add_zero]
  | k + 1 => by
    rw [lv, lv_cons a l k, lv, List.getD_cons_succ, Nat.mul_add, Nat.pow_succ, Nat.mul_comm (256 ^ k) 256,
      ← Nat.mul_assoc, Nat.mul_comm (l.getD k 0) 256, Nat.mul_assoc, Nat.add_assoc]

theorem leNum_lv : ∀ l : List Nat, Ed25519.leNum l = lv l.length l
  | [] => rfl
  | a :: l => by
    rw [List.length_cons, lv_cons, ← leNum_lv l]
    simp only [Ed25519.leNum, List.foldr_cons]

/-- `less_than_le` decides `<` on the numbers the bytes spell. -/
theorem ltLEb_lt {x y : List Nat} (hx : Byt x) (hy : Byt y) : ∀ k, ltLEb x y k = true → lv k x < lv k y
  | 0, h => absurd h (by simp only [ltLEb, Bool.false_eq_true, not_false_eq_true])
  | k + 1, h => by
    simp only [ltLEb] at h
    simp only [lv]
    have hxk := lv_lt hx k
    have hyk := lv_lt hy k
    split at h
    · rename_i e
      rw [e]
      have := ltLEb_lt hx hy k h
      omega
    · have hlt := of_decide_eq_true h
      have : (x.getD k 0 + 1) * 256 ^ k ≤ y.getD k 0 * 256 ^ k := Nat.mul_le_mul_right _ hlt
      rw [Nat.add_mul, Nat.one_mul] at this
      omega

theorem lv_inj {l l' : List Nat} (hl : Byt l) (hl' : Byt l') :
    ∀ k, lv k l = lv k l' → ∀ i, i < k → l.getD i 0 = l'.getD i 0
  | 0, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | k + 1, h, i, hi => by
    simp only [lv] at h
    have h1 := lv_lt hl k
    have h2 := lv_lt hl' k
    have hp : 0 < 256 ^ k := Nat.pow_pos (by decide)
    have ek : l.getD k 0 = l'.getD k 0 := by
      have e1 : (lv k l + l.getD k 0 * 256 ^ k) / 256 ^ k = l.getD k 0 := by
        rw [Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt h1, Nat.zero_add]
      have e2 : (lv k l' + l'.getD k 0 * 256 ^ k) / 256 ^ k = l'.getD k 0 := by
        rw [Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt h2, Nat.zero_add]
      rw [← e1, ← e2, h]
    by_cases e : i = k
    · rw [e]; exact ek
    · rw [ek] at h
      exact lv_inj hl hl' k (by omega) i (by omega)

/-- Two 32-byte strings that spell the same number are equal. -/
theorem eq_of_leNum {l l' : List Nat} (hl : Byt l) (hl' : Byt l') (h1 : l.length = 32) (h2 : l'.length = 32)
    (h : Ed25519.leNum l = Ed25519.leNum l') : l = l' := by
  rw [leNum_lv, leNum_lv, h1, h2] at h
  refine List.ext_getElem (by rw [h1, h2]) fun i hi1 hi2 => ?_
  have := lv_inj hl hl' 32 h i (by omega)
  rwa [getD_of_lt hi1, getD_of_lt hi2] at this

theorem clearTop_getD (b : List Nat) (hb : b.length = 32) (i : Nat) :
    (clearTop b).getD i 0 = if i = 31 then b.getD 31 0 % 128 else b.getD i 0 := by
  unfold clearTop
  by_cases e : i = 31
  · subst e; simp [List.getD, hb]
  · simp [List.getD, e, Ne.symm e]

theorem clearTop_length (b : List Nat) : (clearTop b).length = b.length := List.length_set

theorem byt_clearTop {b : List Nat} (hb : b.length = 32) (h : Byt b) : Byt (clearTop b) := fun i => by
  rw [clearTop_getD b hb]; split
  · have := h 31; omega
  · exact h i

theorem lv_clearTop (b : List Nat) (hb : b.length = 32) (h : Byt b) :
    lv 32 (clearTop b) = lv 32 b % 2 ^ 255 ∧ lv 32 b / 2 ^ 255 = b.getD 31 0 / 128 := by
  have e : lv 31 (clearTop b) = lv 31 b := lv_congr 31 fun i hi => by rw [clearTop_getD b hb, ite_eq_right (by omega)]
  have h31 := lv_lt h 31
  have hb31 := h 31
  have u : ∀ l, lv 32 l = lv 31 l + l.getD 31 0 * 256 ^ 31 := fun _ => rfl
  rw [u, u, e, clearTop_getD b hb, ite_eq_left rfl]
  omega

/-- `clearTop` keeps the low 255 bits; the top bit is bit 7 of byte 31. -/
theorem leNum_clearTop (b : List Nat) (hb : b.length = 32) (h : Byt b) :
    Ed25519.leNum (clearTop b) = Ed25519.leNum b % 2 ^ 255 ∧ Ed25519.leNum b / 2 ^ 255 = b.getD 31 0 / 128 := by
  rw [leNum_lv, leNum_lv, clearTop_length, hb]
  exact lv_clearTop b hb h

/-- `decode` names the point `recoverX` finds. -/
theorem decode_of_recoverX (b : List Nat) (hb : b.length = 32) (hy : Ed25519.leNum b % 2 ^ 255 < Ed25519.p) (x : Nat)
    (hx : Ed25519.recoverX (Ed25519.leNum b % 2 ^ 255) (Ed25519.leNum b / 2 ^ 255) = some x) :
    Ed25519.decode b = some (x, Ed25519.leNum b % 2 ^ 255) := by
  simp only [Ed25519.decode, hb, beq_self_eq_true, require, ↓reduceIte, hy, decide_true, hx]
  rfl

end C3.RV32.EdM
