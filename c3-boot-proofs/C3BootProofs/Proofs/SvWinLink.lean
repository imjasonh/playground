import C3BootProofs.Proofs.SvCkptLink
import C3BootProofs.Spec.X509

/-!
# The times the code compared, as natural numbers

The code compares 64-bit times a 32-bit word at a time. These lemmas bound
the times `readTime` and `generalizedTime` return below `2 ^ 64`, so that
the code's halves are the whole time, and turn the code's comparison of the
halves into `≤` on the times.
-/

namespace C3.RV32.Sv

open C3.Image

theorem readDigits_lt : ∀ {n : Nat} {b r : Bytes} {v : Nat}, readDigits n b = some (v, r) → v < 10 ^ n
  | 0, b, r, v, h => by cases h; exact Nat.one_pos
  | n + 1, [], r, v, h => by cases h
  | n + 1, c :: rest, r, v, h => by
    simp only [readDigits, Option.bind_eq_bind] at h
    unfold require at h
    by_cases hc : (decide (48 ≤ c) && decide (c ≤ 57)) = true
    · rw [ite_eq_left hc] at h
      simp only [Option.bind_some] at h
      cases hd : readDigits n rest with
      | none => rw [hd] at h; cases h
      | some x =>
        obtain ⟨w, r'⟩ := x
        rw [hd] at h
        simp only [Option.bind_some, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        have hw := readDigits_lt hd
        have h57 : c ≤ 57 := of_decide_eq_true (Bool.and_eq_true_iff.mp hc).2
        have : (c - 48) * 10 ^ n ≤ 9 * 10 ^ n := Nat.mul_le_mul_right _ (by omega)
        rw [Nat.pow_succ]
        omega
    · rw [ite_eq_right hc] at h
      cases h

theorem daysInMonth_le (y m : Nat) : daysInMonth y m ≤ 31 := by
  unfold daysInMonth
  split
  · exact Nat.le_refl _
  · split
    · decide
    · split
      · split <;> decide
      · decide

theorem daysFromCivil_lt {year month day : Nat} (hy : year < 10000) (hm : month ≤ 12) (hd : day ≤ 31) :
    daysFromCivil year month day < 4000000 := by
  unfold daysFromCivil
  simp only
  split <;> split <;> omega

theorem readDateTime_lt {year : Nat} {b r : Bytes} {t : Nat} (hy : year < 10000)
    (h : readDateTime year b = some (t, r)) : t < 2 ^ 40 := by
  unfold readDateTime at h
  simp only [Option.bind_eq_bind] at h
  cases h1 : readDigits 2 b with
  | none => rw [h1] at h; cases h
  | some x1 =>
  obtain ⟨month, b1⟩ := x1
  rw [h1] at h
  simp only [Option.bind_some] at h
  cases h2 : readDigits 2 b1 with
  | none => rw [h2] at h; cases h
  | some x2 =>
  obtain ⟨day, b2⟩ := x2
  rw [h2] at h
  simp only [Option.bind_some] at h
  cases h3 : readDigits 2 b2 with
  | none => rw [h3] at h; cases h
  | some x3 =>
  obtain ⟨hour, b3⟩ := x3
  rw [h3] at h
  simp only [Option.bind_some] at h
  cases h4 : readDigits 2 b3 with
  | none => rw [h4] at h; cases h
  | some x4 =>
  obtain ⟨minute, b4⟩ := x4
  rw [h4] at h
  simp only [Option.bind_some] at h
  cases h5 : readDigits 2 b4 with
  | none => rw [h5] at h; cases h
  | some x5 =>
  obtain ⟨second, b5⟩ := x5
  rw [h5] at h
  simp only [Option.bind_some] at h
  unfold require at h
  split at h
  · rename_i hc
    simp only [Option.bind_some, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, hm⟩, -⟩, hd⟩, hh⟩, hmi⟩, hs⟩ := hc
    have hdl := daysFromCivil_lt hy hm (Nat.le_trans hd (daysInMonth_le year month))
    omega
  · cases h

theorem generalizedTime_lt {c : Bytes} {t : Nat} (h : generalizedTime c = some t) : t < 2 ^ 40 := by
  unfold generalizedTime at h
  simp only [Option.bind_eq_bind] at h
  cases h1 : readDigits 4 c with
  | none => rw [h1] at h; cases h
  | some x1 =>
  obtain ⟨year, r1⟩ := x1
  rw [h1] at h
  simp only [Option.bind_some] at h
  cases h2 : readDateTime year r1 with
  | none => rw [h2] at h; cases h
  | some x2 =>
  obtain ⟨t', r2⟩ := x2
  rw [h2] at h
  simp only [Option.bind_some] at h
  have hy := readDigits_lt h1
  have ht := readDateTime_lt (by simpa using hy) h2
  revert h
  split
  · intro h; rw [Option.pure_def] at h; cases h; exact ht
  · split
    · unfold require
      split
      · intro h; simp only [Option.bind_some, Option.pure_def, Option.some.injEq] at h; subst h; exact ht
      · intro h; cases h
    · intro h; cases h
  · intro h; cases h

theorem utcTime_lt {c : Bytes} {t : Nat} (h : utcTime c = some t) : t < 2 ^ 40 := by
  unfold utcTime at h
  simp only [Option.bind_eq_bind] at h
  cases h1 : readDigits 2 c with
  | none => rw [h1] at h; cases h
  | some x1 =>
  obtain ⟨yy, r1⟩ := x1
  rw [h1] at h
  simp only [Option.bind_some] at h
  have hy := readDigits_lt h1
  cases h2 : readDateTime (yy + if yy ≥ 50 then 1900 else 2000) r1 with
  | none => rw [h2] at h; cases h
  | some x2 =>
  obtain ⟨t', r2⟩ := x2
  rw [h2] at h
  simp only [Option.bind_some] at h
  have ht := readDateTime_lt (by split <;> simp at hy <;> omega) h2
  unfold require at h
  split at h
  · simp only [Option.bind_some, Option.pure_def, Option.some.injEq] at h; subst h; exact ht
  · cases h

theorem readTime_lt {b r : Bytes} {t : Nat} (h : readTime b = some (t, r)) : t < 2 ^ 40 := by
  unfold readTime at h
  simp only [Option.bind_eq_bind] at h
  cases h1 : readTlv b with
  | none => rw [h1] at h; cases h
  | some x =>
  obtain ⟨e, r'⟩ := x
  rw [h1] at h
  simp only [Option.bind_some] at h
  split at h
  · cases hu : utcTime e.content with
    | none => rw [hu] at h; cases h
    | some u =>
      rw [hu] at h
      simp only [Option.bind_some, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact utcTime_lt hu
  · split at h
    · cases hg : generalizedTime e.content with
      | none => rw [hg] at h; cases h
      | some g =>
        rw [hg] at h
        simp only [Option.bind_some, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact generalizedTime_lt hg
    · cases h

theorem pair64_halves {t : Nat} (ht : t < 2 ^ 64) :
    pair64 (BitVec.ofNat 32 (t % 2 ^ 32)) (BitVec.ofNat 32 (t / 2 ^ 32)) = t := by
  unfold pair64
  rw [ofNat_toNat_lt (Nat.mod_lt _ (by decide)), ofNat_toNat_lt (by omega)]
  omega

/-- The code's `≤` on 64-bit numbers, a word at a time. -/
theorem win_le {alo ahi blo bhi : Word}
    (h : (ahi = bhi ∧ aluEval .sltu blo alo = 0) ∨ (¬ ahi = bhi ∧ aluEval .sltu bhi ahi = 0)) :
    pair64 alo ahi ≤ pair64 blo bhi := by
  unfold pair64
  rcases h with ⟨rfl, h⟩ | ⟨hne, h⟩
  · have := sltu_zero h; omega
  · have h1 := sltu_zero h
    have h2 : ahi.toNat ≠ bhi.toNat := fun e => hne (BitVec.eq_of_toNat_eq e)
    have := alo.isLt
    have := blo.isLt
    have : ahi.toNat + 1 ≤ bhi.toNat := by omega
    have : (ahi.toNat + 1) * 2 ^ 32 ≤ bhi.toNat * 2 ^ 32 := Nat.mul_le_mul_right _ this
    omega

theorem sltu_ne {a b : Word} (h : aluEval .sltu a b ≠ 0) : a.toNat < b.toNat := by
  have := svSltu_tn a b
  by_cases hl : a.toNat < b.toNat
  · exact hl
  · rw [ite_eq_right hl] at this
    exact absurd (BitVec.eq_of_toNat_eq this) h

/-- The code's `<` on 64-bit numbers, a word at a time. -/
theorem win_lt {alo ahi blo bhi : Word}
    (h : (ahi = bhi ∧ aluEval .sltu alo blo ≠ 0) ∨ (¬ ahi = bhi ∧ aluEval .sltu ahi bhi ≠ 0)) :
    pair64 alo ahi < pair64 blo bhi := by
  unfold pair64
  rcases h with ⟨rfl, h⟩ | ⟨-, h⟩
  · have := sltu_ne h; omega
  · have h1 := sltu_ne h
    have := alo.isLt
    have := blo.isLt
    have : (ahi.toNat + 1) * 2 ^ 32 ≤ bhi.toNat * 2 ^ 32 := Nat.mul_le_mul_right _ h1
    omega

end C3.RV32.Sv
