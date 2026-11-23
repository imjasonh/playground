import C3BootProofs.Proofs.NonAdjacentForm

/-!
# The NAF digits sum to the scalar

`nafSpec X` is the width-5 non-adjacent form that `ed25519_verify`
computes for a scalar `X`. For `X < 2^255`, this file proves that the
digits, read as signed bytes, sum to `X` (`nafVal_nafSpec`), that each
nonzero digit is odd (`nafSpec_odd`), and that the digits from index 256 on
are zero (`nafSpec_high`).
-/

namespace C3.RV32.EdM

/-- A digit byte as a signed integer. -/
def sval (b : BitVec 8) : Int := if b.toNat < 128 then (b.toNat : Int) else (b.toNat : Int) - 256

/-- The value of the first `n` digits: `∑ k < n, sval (d k) * 2^k`. -/
def nafVal (d : Nat → BitVec 8) : Nat → Int
  | 0 => 0
  | n + 1 => nafVal d n + sval (d n) * ((2 ^ n : Nat) : Int)

theorem sval_zero : sval 0 = 0 := rfl

theorem nafVal_set (nf : Nat → BitVec 8) (pos : Nat) (v : BitVec 8) (h0 : nf pos = 0) :
    ∀ n, nafVal (fun k => if k = pos then v else nf k) n =
      nafVal nf n + (if pos < n then sval v * ((2 ^ pos : Nat) : Int) else 0)
  | 0 => by simp only [nafVal, Nat.not_lt_zero, ↓reduceIte, Int.add_zero]
  | n + 1 => by
    simp only [nafVal]
    rw [nafVal_set nf pos v h0 n]
    by_cases e : n = pos
    · subst e
      simp only [↓reduceIte, Nat.lt_irrefl, Nat.lt_succ_self, h0, sval_zero, Int.zero_mul, Int.add_zero]
    · simp only [e, ↓reduceIte]
      by_cases h : pos < n
      · simp only [h, ↓reduceIte, show pos < n + 1 by omega]
        rw [Int.add_assoc, Int.add_assoc, Int.add_comm (sval v * _)]
      · simp only [h, ↓reduceIte, show ¬ pos < n + 1 by omega, Int.add_zero]

theorem nafVal_congr {d d' : Nat → BitVec 8} : ∀ n, (∀ k, k < n → d k = d' k) → nafVal d n = nafVal d' n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [nafVal]
    rw [nafVal_congr n fun k hk => h k (by omega), h n (by omega)]

theorem div_pow_succ (X pos : Nat) : X / 2 ^ (pos + 1) = X / 2 ^ pos / 2 := by
  rw [Nat.div_div_eq_div_mul, Nat.pow_succ]

theorem div_pow_add5 (X pos : Nat) : X / 2 ^ (pos + 5) = X / 2 ^ pos / 32 := by
  rw [Nat.div_div_eq_div_mul, Nat.pow_add]; rfl

/-- The digit an odd window `w` stores. -/
theorem sval_digit (w : Nat) (hw : w < 32) :
    sval (BitVec.ofNat 8 (if w < 16 then w else w + 224)) = if w < 16 then (w : Int) else (w : Int) - 32 := by
  by_cases h : w < 16
  · simp only [h, ↓reduceIte, sval, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    simp only [show w < 128 by omega, ↓reduceIte]
  · simp only [h, ↓reduceIte, sval, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    simp only [show ¬ w + 224 < 128 by omega, ↓reduceIte]
    omega

theorem pow_pos' (n : Nat) : 0 < 2 ^ n := Nat.pos_of_ne_zero (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos n))

/-- The bound `(carry + X / 2^pos) * 2^pos ≤ 2^255` survives an odd window. -/
theorem odd_bound (V pos : Nat) (hpos : pos < 256) (hodd : V % 2 = 1) (hV : V * 2 ^ pos ≤ 2 ^ 255) :
    (V + 16) / 32 * 2 ^ (pos + 5) ≤ 2 ^ 255 := by
  by_cases hp : pos ≤ 250
  · have e : 2 ^ 255 = 32 * 2 ^ (250 - pos) * 2 ^ pos := by
      rw [show (32 : Nat) = 2 ^ 5 from rfl, ← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
    rw [e] at hV
    have hV' : V ≤ 32 * 2 ^ (250 - pos) := Nat.le_of_mul_le_mul_right hV (pow_pos' pos)
    have hq : (V + 16) / 32 ≤ 2 ^ (250 - pos) := by
      generalize 2 ^ (250 - pos) = Q at hV'
      omega
    calc (V + 16) / 32 * 2 ^ (pos + 5) ≤ 2 ^ (250 - pos) * 2 ^ (pos + 5) := Nat.mul_le_mul_right _ hq
      _ = 2 ^ 255 := by rw [← Nat.pow_add]; congr 1; omega
  · have e : 2 ^ 255 = 2 ^ (255 - pos) * 2 ^ pos := by rw [← Nat.pow_add]; congr 1; omega
    rw [e] at hV
    have hV' : V ≤ 2 ^ (255 - pos) := Nat.le_of_mul_le_mul_right hV (pow_pos' pos)
    have h16 : 2 ^ (255 - pos) ≤ 2 ^ 4 := Nat.pow_le_pow_right (by decide) (by omega)
    have : (V + 16) / 32 = 0 := by
      have : V ≤ 16 := Nat.le_trans hV' h16
      omega
    rw [this, Nat.zero_mul]; exact Nat.zero_le _

/-- The bound survives an even window. -/
theorem even_bound (V pos : Nat) (heven : V % 2 = 0) (hV : V * 2 ^ pos ≤ 2 ^ 255) :
    V / 2 * 2 ^ (pos + 1) ≤ 2 ^ 255 := by
  have : V / 2 * 2 ^ (pos + 1) = V * 2 ^ pos := by
    rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (V / 2) (2 ^ pos), Nat.mul_assoc, Nat.mul_comm (2 ^ pos)]
    rw [Nat.mul_comm (V / 2 * 2), Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero heven)]
  rw [this]; exact hV

/-- `nafGo`'s invariant: the digits so far plus the rest of the scalar make
`X`, the rest is at most `2^255`, and no digit at or past `pos` is set. -/
theorem nafGo_val (X : Nat) :
    ∀ n pos carry nf, carry ≤ 1 → 256 ≤ pos + n → (∀ k, pos ≤ k → nf k = 0) →
      (carry + X / 2 ^ pos) * 2 ^ pos ≤ 2 ^ 255 →
      nafVal nf 256 + (((carry + X / 2 ^ pos) * 2 ^ pos : Nat) : Int) = X →
      nafVal (nafGo X n pos carry nf) 256 = X := by
  intro n
  induction n with
  | zero =>
    intro pos carry nf _ hp _ hb hv
    have h0 : (carry + X / 2 ^ pos) * 2 ^ pos = 0 := by
      have : 2 ^ 256 ≤ 2 ^ pos := Nat.pow_le_pow_right (by decide) (by omega)
      have h1 : (carry + X / 2 ^ pos) * 2 ^ pos < 1 * 2 ^ pos :=
        Nat.lt_of_le_of_lt hb (by rw [Nat.one_mul]; exact Nat.lt_of_lt_of_le (Nat.pow_lt_pow_right (by decide)
          (by decide : 255 < 256)) this)
      have := Nat.lt_of_mul_lt_mul_right h1
      rw [show carry + X / 2 ^ pos = 0 by omega, Nat.zero_mul]
    rw [h0] at hv
    simpa only [nafGo, Int.natCast_zero, Int.add_zero] using hv
  | succ n ih =>
    intro pos carry nf hc hp hz hb hv
    simp only [nafGo]
    by_cases hpos : 256 ≤ pos
    · simp only [hpos, ↓reduceIte]
      have := ih pos carry nf hc (by omega) hz hb hv
      cases n with
      | zero => simpa only [nafGo] using this
      | succ n => simpa only [nafGo, hpos, ↓reduceIte] using this
    simp only [hpos, ↓reduceIte]
    have hQ : X / 2 ^ pos = X / 2 ^ pos % 32 + 32 * (X / 2 ^ pos / 32) := (Nat.mod_add_div _ _).symm
    by_cases hev : (carry + X / 2 ^ pos % 32) % 2 = 0
    · simp only [hev, ↓reduceIte]
      have hc2 : carry + X / 2 ^ pos = 2 * (carry + X / 2 ^ (pos + 1)) := by rw [div_pow_succ]; omega
      refine ih (pos + 1) carry nf hc (by omega) (fun k hk => hz k (by omega)) ?_ ?_
      · have := even_bound (carry + X / 2 ^ pos) pos (by omega) hb
        rwa [hc2, Nat.mul_div_cancel_left _ (by decide)] at this
      · have e : (carry + X / 2 ^ (pos + 1)) * 2 ^ (pos + 1) = (carry + X / 2 ^ pos) * 2 ^ pos := by
          rw [hc2, Nat.pow_succ, Nat.mul_comm 2, Nat.mul_assoc, Nat.mul_comm 2]
        rw [e]; exact hv
    · simp only [hev, ↓reduceIte]
      have hw : carry + X / 2 ^ pos % 32 < 32 + 1 := by omega
      have hwodd : (carry + X / 2 ^ pos) % 2 = 1 := by omega
      refine ih (pos + 5) _ _ ?_ (by omega) ?_ ?_ ?_
      · split <;> omega
      · intro k hk
        simp only [show k ≠ pos by omega, ↓reduceIte]
        exact hz k (by omega)
      · have e : (if carry + X / 2 ^ pos % 32 < 16 then 0 else 1) + X / 2 ^ (pos + 5) =
            (carry + X / 2 ^ pos + 16) / 32 := by
          rw [div_pow_add5]; split <;> omega
        rw [e]; exact odd_bound _ pos (by omega) hwodd hb
      · rw [nafVal_set nf pos _ (hz pos (Nat.le_refl _)) 256]
        simp only [show pos < 256 by omega, ↓reduceIte]
        have hlt : carry + X / 2 ^ pos % 32 < 32 := by
          by_cases h16 : carry + X / 2 ^ pos % 32 < 16
          · omega
          · omega
        rw [sval_digit _ hlt]
        have key : (((if carry + X / 2 ^ pos % 32 < 16 then 0 else 1) + X / 2 ^ (pos + 5) : Nat) : Int) * 32 +
            (if carry + X / 2 ^ pos % 32 < 16 then ((carry + X / 2 ^ pos % 32 : Nat) : Int)
              else ((carry + X / 2 ^ pos % 32 : Nat) : Int) - 32) = ((carry + X / 2 ^ pos : Nat) : Int) := by
          rw [div_pow_add5]; split <;> omega
        rw [← hv]
        have e2 : ((((if carry + X / 2 ^ pos % 32 < 16 then 0 else 1) + X / 2 ^ (pos + 5)) * 2 ^ (pos + 5) : Nat) : Int)
            = (((if carry + X / 2 ^ pos % 32 < 16 then 0 else 1) + X / 2 ^ (pos + 5) : Nat) : Int) * 32 *
              ((2 ^ pos : Nat) : Int) := by
          rw [Nat.pow_add, Int.natCast_mul, Int.natCast_mul, Int.mul_comm (((2 ^ pos : Nat) : Int)), ← Int.mul_assoc]
          rfl
        have e3 : (((carry + X / 2 ^ pos) * 2 ^ pos : Nat) : Int) =
            ((carry + X / 2 ^ pos : Nat) : Int) * ((2 ^ pos : Nat) : Int) := Int.natCast_mul _ _
        rw [e2, e3, ← key, Int.add_mul, Int.add_assoc, Int.add_comm (_ * _ * _)]

/-- **The digits sum to the scalar.** -/
theorem nafVal_nafSpec (X : Nat) (hX : X < 2 ^ 255) : nafVal (nafSpec X) 256 = X := by
  refine nafGo_val X 256 0 0 _ (Nat.zero_le _) (Nat.le_refl _) (fun _ _ => rfl) ?_ ?_
  · simp only [Nat.pow_zero, Nat.div_one, Nat.zero_add, Nat.mul_one]; exact Nat.le_of_lt hX
  · have : nafVal (fun _ => (0 : BitVec 8)) 256 = 0 := by
      have g : ∀ n, nafVal (fun _ => (0 : BitVec 8)) n = 0 := fun n => by
        induction n with
        | zero => rfl
        | succ n ih => simp only [nafVal, ih, sval_zero, Int.zero_mul, Int.add_zero]
      exact g 256
    rw [this]; simp only [Nat.pow_zero, Nat.div_one, Nat.zero_add, Nat.mul_one, Int.zero_add]

theorem nafGo_shape (X : Nat) : ∀ n pos carry (nf : Nat → BitVec 8),
    (∀ k, nf k = 0 ∨ ((nf k).toNat % 2 = 1 ∧ k < 256)) →
    ∀ k, nafGo X n pos carry nf k = 0 ∨ ((nafGo X n pos carry nf k).toNat % 2 = 1 ∧ k < 256) := by
  intro n
  induction n with
  | zero => intro _ _ _ h; exact h
  | succ n ih =>
    intro pos carry nf h
    simp only [nafGo]
    split
    · exact h
    · rename_i hpos
      split
      · exact ih _ _ _ h
      · rename_i hodd
        refine ih _ _ _ fun k => ?_
        by_cases e : k = pos
        · simp only [e, ↓reduceIte]
          right
          refine ⟨?_, by omega⟩
          split <;> (rw [BitVec.toNat_ofNat]; omega)
        · simp only [e, ↓reduceIte]; exact h k

/-- Each digit is zero, or odd at an index below 256. -/
theorem nafSpec_shape (X k : Nat) : nafSpec X k = 0 ∨ ((nafSpec X k).toNat % 2 = 1 ∧ k < 256) :=
  nafGo_shape X 256 0 0 _ (fun _ => Or.inl rfl) k

theorem nafSpec_odd (X k : Nat) (h : nafSpec X k ≠ 0) : (nafSpec X k).toNat % 2 = 1 := by
  rcases nafSpec_shape X k with e | e
  · exact absurd e h
  · exact e.1

theorem nafSpec_high (X k : Nat) (h : 256 ≤ k) : nafSpec X k = 0 := by
  rcases nafSpec_shape X k with e | e
  · exact e
  · exact absurd e.2 (by omega)

end C3.RV32.EdM
