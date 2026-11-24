import C3BootProofs.Models.Safegcd
import C3BootProofs.Proofs.SvP256All

/-!
# Safegcd: the range bound on `sigstore::verify`'s inversion of `Z`

The P-256 inversions in `sigstore::verify` start with `d = 0` and `e`
below the modulus, so `d` stays below it through every batch. With the
image's P-256 parameters in place (`P2Data`), the inverse of `Z` that
`normVal8` takes from `d` is below `p` for every `Z`, which is the
hypothesis `hzi` of `sv_verify_spec`.
-/

namespace C3.RV32.Safegcd

open C3.Image C3.RV32.Pv C3.RV32.Sv C3.RV32.P2

theorem deUpd8_lt {D E u v : Int} {MI s M : Nat} (hM : 0 < M) (hW : M ≤ 2 ^ 256) (hD : D.natAbs < M)
    (hE : E.natAbs < M) (huv : RowB (2 ^ s) u v) : (deUpd8 D E u v MI s M).natAbs < M := by
  have h := rowB_natAbs huv
  unfold deUpd8
  rw [sgnVal_natAbs]
  exact lrsm8_lt hM hW (lin_lt hD hE (by exact_mod_cast h))

theorem zvStep_deB {P : Nat} {s : Iv} (hP : 0 < P) (hW : P ≤ 2 ^ 256) (h : DeB P s) : DeB P (zvStep P s) :=
  have hr := batch_rows (Nat.min_le_right s.rem 62) s.δ (lowestI s.f) (lowestI s.g)
  ⟨deUpd8_lt hP hW h.1 h.2 hr.1, deUpd8_lt hP hW h.1 h.2 hr.2⟩

theorem zvLoop_deB {P : Nat} (hP : 0 < P) (hW : P ≤ 2 ^ 256) : ∀ k (s : Iv), DeB P s → DeB P (zvLoop P k s)
  | 0, _, h => h
  | k + 1, s, h => by
    rw [zvLoop]
    split
    · exact h
    · exact zvLoop_deB hP hW k _ (zvStep_deB hP hW h)

theorem ivStep8_deB {N : Nat} {s : Iv} (hN : 0 < N) (hW : N ≤ 2 ^ 256) (h : DeB N s) : DeB N (ivStep8 N s) :=
  have hr := batch_rows (Nat.min_le_right s.rem 62) s.δ (lowestI s.f) (lowestI s.g)
  ⟨deUpd8_lt hN hW h.1 h.2 hr.1, deUpd8_lt hN hW h.1 h.2 hr.2⟩

theorem ivLoop8_deB {N : Nat} (hN : 0 < N) (hW : N ≤ 2 ^ 256) :
    ∀ k (s : Iv), DeB N s → DeB N (ivLoop8 N k s)
  | 0, _, h => h
  | k + 1, s, h => by
    rw [ivLoop8]
    split
    · exact h
    · exact ivLoop8_deB hN hW k _ (ivStep8_deB hN hW h)

theorem p256_le : p256 ≤ 2 ^ 256 := by unfold p256; decide

/-- **The range bound on the inversion of `Z`**: with the image's P-256 parameters in place, the
inverse that `normVal8` takes from the inversion's `d` is below `p`, for every `Z`. -/
theorem hzi_holds {Me : Word → BitVec 8} (D0 : P2Data Me) :
    ∀ Z τd τf Dz Fz, τd ≤ 1 → τf ≤ 1 → sgnVal τf Fz = (p256Sz Me Z).f → sgnVal τd Dz = (p256Sz Me Z).d →
      normVal8 τd τf Dz (accV Me (BitVec.ofNat 32 0x3FCC4B38) 8) < p256 := by
  intro Z τd τf Dz Fz hτd _ _ hd
  have hP : accV Me (BitVec.ofNat 32 0x3FCC4B38) 8 = p256 := D0.N
  have hR : accV Me (BitVec.ofNat 32 0x3FCC4B78) 8 < accV Me (BitVec.ofNat 32 0x3FCC4B38) 8 := D0.r2lt
  have h0 : 0 < accV Me (BitVec.ofNat 32 0x3FCC4B38) 8 := by rw [hP]; unfold p256; decide
  have hW : accV Me (BitVec.ofNat 32 0x3FCC4B38) 8 ≤ 2 ^ 256 := by rw [hP]; exact p256_le
  have hdb : (p256Sz Me Z).d.natAbs < accV Me (BitVec.ofNat 32 0x3FCC4B38) 8 :=
    (zvLoop_deB h0 hW 10 (p256Zv0 Me Z) (deB_init hR)).1
  rw [sv_abs hτd hd]
  rw [hP] at hdb ⊢
  exact normVal8_lt hdb p256_le

end C3.RV32.Safegcd
