import C3BootProofs.Proofs.SvZA
import C3BootProofs.Proofs.SvZB
import C3BootProofs.Proofs.SvZDs4

/-!
# `sigstore::verify`: the model of the inversion of `Z`

The batches of the inversion of the P-256 sum's `Z`, on integers: `min rem
62` constant-time divsteps on the low words of `f` and `g`, then their
matrix applied to `f`, `g`, `d`, and `e` with 8 limbs, `d` and `e` modulo
`p`. The lemmas turn what `sv_zb` stores into this model. It follows
`Pv384HLoop.lean`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

/-- What `update_fg::<8>` leaves for the row `[u, v]` and the shift `s`. -/
def fgUpd8 (F G u v : Int) (s : Nat) : Int :=
  sgnI (F * u + G * v) ((F * u + G * v).natAbs / 2 ^ s % 2 ^ 256)

/-- What `update_de::<8>` leaves for the row `[u, v]`, the shift `s`, the
modulus `M`, and `-M⁻¹ mod 2^64` as `MI`. -/
def deUpd8 (D E u v : Int) (MI s M : Nat) : Int :=
  let X := D * u + E * v
  let r := lrsm8 (if X < 0 then 1 else 0) X.natAbs MI s M
  sgnVal r.1 r.2

/-- `-p⁻¹ mod 2^64`, as the batches pass it to `update_de`. -/
abbrev zvMI : Nat := (BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat

/-- One batch of the inversion of `Z` modulo `P`. -/
def zvStep (P : Nat) (s : Iv) : Iv :=
  let n := min s.rem 62
  let t := dsIter n ⟨s.δ, lowestI s.f, lowestI s.g, 1, 0, 0, 1⟩
  ⟨t.δ, fgUpd8 s.f s.g (i64Val t.u) (i64Val t.v) n, fgUpd8 s.f s.g (i64Val t.q) (i64Val t.r) n,
    deUpd8 s.d s.e (i64Val t.u) (i64Val t.v) zvMI n P, deUpd8 s.d s.e (i64Val t.q) (i64Val t.r) zvMI n P, s.rem - n⟩

/-- Batches until no steps are left, with `k` batches at most. -/
def zvLoop (P : Nat) : Nat → Iv → Iv
  | 0, s => s
  | k + 1, s => if s.rem = 0 then s else zvLoop P k (zvStep P s)

theorem zvLoop_done (P : Nat) : ∀ k (s : Iv), s.rem = 0 → zvLoop P k s = s
  | 0, _, _ => rfl
  | _ + 1, s, h => by rw [zvLoop, ite_eq_left h]

theorem zvLoop_rem (P : Nat) : ∀ k (s : Iv), s.rem ≤ 62 * k → (zvLoop P k s).rem = 0
  | 0, s, h => by rw [zvLoop]; omega
  | k + 1, s, h => by
    rw [zvLoop]
    by_cases h0 : s.rem = 0
    · rw [ite_eq_left h0]; exact h0
    · rw [ite_eq_right h0]
      exact zvLoop_rem P k _ (by simp only [zvStep]; omega)

theorem sgn_ex (X : Int) : ∃ σ A, sgnVal σ A = X ∧ σ ≤ 1 := by
  by_cases h : X < 0
  · exact ⟨1, X.natAbs, by simp only [sgnVal, ite_true]; omega, Nat.le_refl 1⟩
  · exact ⟨0, X.natAbs, by simp only [sgnVal, show (0 : Nat) ≠ 1 from by decide, ite_false]; omega, Nat.zero_le 1⟩

theorem fgUpd8_of {σ A b R : Nat} {F G u v : Int} {s : Nat} (hσ : σ ≤ 1)
    (h : sgnVal σ A = F * u + G * v) (hb : b = σ) (hR : R = A / 2 ^ s % 2 ^ 256) :
    sgnVal b R = fgUpd8 F G u v s ∧ b ≤ 1 := by
  subst hb hR
  obtain ⟨n1, n2, n3⟩ := sgnVal_rep hσ h
  refine ⟨?_, hσ⟩
  unfold fgUpd8 sgnI sgnVal
  rcases Int.lt_trichotomy (F * u + G * v) 0 with h0 | h0 | h0
  · obtain ⟨e1, e2⟩ := n1 h0; rw [ite_eq_left e1, ite_eq_left h0, e2]
  · rw [n3 h0, Nat.zero_div, Nat.zero_mod, h0]; simp
  · obtain ⟨e1, e2⟩ := n2 h0; rw [ite_eq_right (by omega), ite_eq_right (by omega), e2]

theorem lrsm8_zero (σ MI s M : Nat) (hM : 0 < M) : (lrsm8 σ 0 MI s M).2 = 0 := by
  unfold lrsm8 lrsmMf; simp [hM]

theorem lrsm8_le {σ A MI s M : Nat} (hσ : σ ≤ 1) : (lrsm8 σ A MI s M).1 ≤ 1 := by
  unfold lrsm8; dsimp only; split <;> omega

theorem deUpd8_of {σ A b R MI s M : Nat} {D E u v : Int} (hσ : σ ≤ 1) (hM : 0 < M)
    (h : sgnVal σ A = D * u + E * v) (hb : b = (lrsm8 σ A MI s M).1) (hR : R = (lrsm8 σ A MI s M).2) :
    sgnVal b R = deUpd8 D E u v MI s M ∧ b ≤ 1 := by
  subst hb hR
  obtain ⟨n1, n2, n3⟩ := sgnVal_rep hσ h
  refine ⟨?_, lrsm8_le hσ⟩
  unfold deUpd8; dsimp only
  rcases Int.lt_trichotomy (D * u + E * v) 0 with h0 | h0 | h0
  · obtain ⟨e1, e2⟩ := n1 h0; rw [ite_eq_left h0, ← e1, ← e2]
  · rw [n3 h0, h0, Int.natAbs_zero, lrsm8_zero _ _ _ _ hM, lrsm8_zero _ _ _ _ hM]; simp [sgnVal]
  · obtain ⟨e1, e2⟩ := n2 h0; rw [ite_eq_right (by omega), ← e1, ← e2]

end C3.RV32.Sv
