import C3BootProofs.Models.EcdsaInv
import C3BootProofs.Proofs.P256Defs

/-!
# The P-256 check's inversions

`ivLoop8` inverts `s` modulo `n` and `zvLoop` inverts `Z` modulo `p`. Both
are `stepW` batches on 256-bit values, so they keep `IvOk`. When the batches
end with `f = ±1`, the normalized `d` is the inverse.
-/

namespace C3.Models

open C3.RV32 C3.RV32.Pv C3.RV32.Sv

theorem ivStep8_eq (N : Nat) (s : Iv) : ivStep8 N s = stepW 256 ivMI N s := rfl

theorem zvStep_eq (P : Nat) (s : Iv) : zvStep P s = stepW 256 zvMI P s := rfl

theorem normVal8_eq (σ fs X p : Nat) : normVal8 σ fs X p = normW 256 σ fs X p := rfl

theorem ivLoop8_ok {N : Nat} {x e0 : Int} (hN : N % 2 = 1) (hNW : N ≤ 2 ^ 256) (hMI : N * ivMI % 2 ^ 64 = 1) :
    ∀ k s, IvOk 256 N x e0 s → IvOk 256 N x e0 (ivLoop8 N k s)
  | 0, _, h => h
  | k + 1, s, h => by
    rw [ivLoop8]
    by_cases h0 : s.rem = 0 ∨ s.g = 0
    · rw [ite_eq_left h0]; exact h
    · rw [ite_eq_right h0, ivStep8_eq]; exact ivLoop8_ok hN hNW hMI k _ (stepW_ok hN hNW hMI h)

theorem zvLoop_ok {P : Nat} {x e0 : Int} (hP : P % 2 = 1) (hPW : P ≤ 2 ^ 256) (hMI : P * zvMI % 2 ^ 64 = 1) :
    ∀ k s, IvOk 256 P x e0 s → IvOk 256 P x e0 (zvLoop P k s)
  | 0, _, h => h
  | k + 1, s, h => by
    rw [zvLoop]
    by_cases h0 : s.rem = 0
    · rw [ite_eq_left h0]; exact h
    · rw [ite_eq_right h0, zvStep_eq]; exact zvLoop_ok hP hPW hMI k _ (stepW_ok hP hPW hMI h)

/-- The sign bytes and magnitudes that the code stores for `d` and `f`,
with `f`'s magnitude 1, give `normW` of `d` and `f`. -/
theorem normW_sgn {W σ σf Dv Fv N : Nat} {s : Iv} (hσ : σ ≤ 1) (hσf : σf ≤ 1) (hf : sgnVal σf Fv = s.f)
    (hd : sgnVal σ Dv = s.d) (hF : Fv = 1) :
    normW W σ σf Dv N = normW W (if s.d < 0 then 1 else 0) (if s.f < 0 then 1 else 0) s.d.natAbs N ∧
      s.f.natAbs = 1 := by
  subst hF
  unfold sgnVal at hf hd
  have n01 : (0 : Nat) ≠ 1 := by decide
  have z0 : normW W 1 σf 0 N = normW W 0 σf 0 N := by
    unfold normW; rw [ite_eq_right (fun h => h.2 rfl), ite_eq_right (fun h => h.2 rfl)]
  have fp : ¬ ((1 : Nat) : Int) < 0 := by omega
  have fn : -((1 : Nat) : Int) < 0 := by omega
  have dp : ¬ (Dv : Int) < 0 := by omega
  rcases (by omega : σ = 0 ∨ σ = 1) with rfl | rfl <;> rcases (by omega : σf = 0 ∨ σf = 1) with rfl | rfl
  · rw [ite_eq_right n01] at hf hd
    rw [← hf, ← hd, ite_eq_right dp, ite_eq_right fp, Int.natAbs_natCast]
    exact ⟨rfl, rfl⟩
  · rw [ite_eq_right n01] at hd
    rw [ite_eq_left rfl] at hf
    rw [← hf, ← hd, ite_eq_right dp, ite_eq_left fn, Int.natAbs_natCast]
    exact ⟨rfl, rfl⟩
  · rw [ite_eq_right n01] at hf
    rw [ite_eq_left rfl] at hd
    rw [← hf, ← hd, ite_eq_right fp, Int.natAbs_neg, Int.natAbs_natCast]
    by_cases hD : Dv = 0
    · subst hD; rw [ite_eq_right (show ¬ -((0 : Nat) : Int) < 0 by omega)]; exact ⟨z0, rfl⟩
    · rw [ite_eq_left (show -(Dv : Int) < 0 by omega)]; exact ⟨rfl, rfl⟩
  · rw [ite_eq_left rfl] at hf hd
    rw [← hf, ← hd, ite_eq_left fn, Int.natAbs_neg, Int.natAbs_natCast]
    by_cases hD : Dv = 0
    · subst hD; rw [ite_eq_right (show ¬ -((0 : Nat) : Int) < 0 by omega)]; exact ⟨z0, rfl⟩
    · rw [ite_eq_left (show -(Dv : Int) < 0 by omega)]; exact ⟨rfl, rfl⟩

/-- **The inversion of `s`**: when its batches end with `f = ±1`, as the
code checks, the normalized `d` is `s⁻¹` modulo `N`. -/
theorem ivLoop8_inv {N x : Nat} {σ σf Dv Fv : Nat} (hN : N % 2 = 1) (hN1 : 1 < N) (hNW : N < 2 ^ 256)
    (hMI : N * ivMI % 2 ^ 64 = 1) (hx : x < 2 ^ 256) (hσ : σ ≤ 1) (hσf : σf ≤ 1)
    (hf : sgnVal σf Fv = (ivLoop8 N 10 ⟨1, N, x, 0, 1, 0x24F⟩).f)
    (hd : sgnVal σ Dv = (ivLoop8 N 10 ⟨1, N, x, 0, 1, 0x24F⟩).d) (hF : Fv = 1) :
    MEq N ((normVal8 σ σf Dv N : Nat) * (x : Int)) 1 ∧ normVal8 σ σf Dv N < N := by
  have h0 := ivOk_init (W := 256) (x := x) (e0 := 1) 1 0x24F hN hNW hx hN1
  have h1 := ivLoop8_ok hN (Nat.le_of_lt hNW) hMI 10 _ h0
  obtain ⟨e, hf1⟩ := normW_sgn (W := 256) (N := N) hσ hσf hf hd hF
  rw [normVal8_eq, e]
  exact normW_inv (Nat.le_of_lt hNW) h1 hf1

/-- **The inversion of `Z`**: when its batches end with `f = ±1`, the
normalized `d` is `e₀ Z⁻¹` modulo `P`. -/
theorem zvLoop_inv {P x e0 : Nat} {σ σf Dv Fv : Nat} (hP : P % 2 = 1) (hPW : P < 2 ^ 256)
    (hMI : P * zvMI % 2 ^ 64 = 1) (hx : x < 2 ^ 256) (he : e0 < P) (hσ : σ ≤ 1) (hσf : σf ≤ 1)
    (hf : sgnVal σf Fv = (zvLoop P 10 ⟨1, P, x, 0, e0, 0x24F⟩).f)
    (hd : sgnVal σ Dv = (zvLoop P 10 ⟨1, P, x, 0, e0, 0x24F⟩).d) (hF : Fv = 1) :
    MEq P ((normVal8 σ σf Dv P : Nat) * (x : Int)) e0 ∧ normVal8 σ σf Dv P < P := by
  have h0 := ivOk_init (W := 256) (x := x) (e0 := e0) 1 0x24F hP hPW hx he
  have h1 := zvLoop_ok hP (Nat.le_of_lt hPW) hMI 10 _ h0
  obtain ⟨e, hf1⟩ := normW_sgn (W := 256) (N := P) hσ hσf hf hd hF
  rw [normVal8_eq, e]
  exact normW_inv (Nat.le_of_lt hPW) h1 hf1

end C3.Models
