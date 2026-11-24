import C3BootProofs.Models.Safegcd
import C3BootProofs.Proofs.Pv384Main

/-!
# Safegcd: `p384_verify_prehash`'s side conditions

Both inversions in `p384_verify_prehash` start with `d = 0` and `e` below
the modulus, so `d` stays below it through every batch, and the inverse
that `normVal` takes from it is below the modulus. That is all
`PvSide` asks, so it holds for any memory and any arguments.
-/

namespace C3.RV32.Safegcd

open C3.Image C3.RV32.Pv C3.RV32.Dq

set_option exponentiation.threshold 600 in
theorem deUpd_lt {D E u v : Int} {MI s M : Nat} (hM : 0 < M) (hW : M ≤ 2 ^ 384) (hD : D.natAbs < M)
    (hE : E.natAbs < M) (huv : RowB (2 ^ s) u v) : (deUpd D E u v MI s M).natAbs < M := by
  have h := rowB_natAbs huv
  unfold deUpd
  rw [sgnVal_natAbs]
  exact lrsm_lt hM hW (lin_lt hD hE (by exact_mod_cast h))

set_option exponentiation.threshold 600 in
theorem n384_bounds : 0 < dataVal p384OrderData 0 12 ∧ dataVal p384OrderData 0 12 ≤ 2 ^ 384 := by
  rw [ord_val]; unfold n384; exact ⟨by decide, by decide⟩

set_option exponentiation.threshold 600 in
theorem p384_bounds : 0 < dataVal p384ParamsData 0 12 ∧ dataVal p384ParamsData 0 12 ≤ 2 ^ 384 := by
  rw [params_N]; unfold p384; exact ⟨by decide, by decide⟩

set_option exponentiation.threshold 600 in
theorem r2_lt_n384 : dataVal p384ScalarR2Data 0 12 < dataVal p384OrderData 0 12 := by
  rw [ord_val]; unfold n384; decide

theorem r2_lt_p384 : dataVal p384ParamsData 0x60 12 < dataVal p384ParamsData 0 12 := by
  rw [params_N]; exact params_r2

set_option exponentiation.threshold 600 in
theorem ivStep_deB {s : Iv} (h : DeB (dataVal p384OrderData 0 12) s) :
    DeB (dataVal p384OrderData 0 12) (ivStep s) :=
  have hr := batch_rows (Nat.min_le_right s.rem 62) s.δ (lowestI s.f) (lowestI s.g)
  ⟨deUpd_lt n384_bounds.1 n384_bounds.2 h.1 h.2 hr.1, deUpd_lt n384_bounds.1 n384_bounds.2 h.1 h.2 hr.2⟩

theorem ivLoop_deB : ∀ k (s : Iv), DeB (dataVal p384OrderData 0 12) s →
    DeB (dataVal p384OrderData 0 12) (ivLoop k s)
  | 0, _, h => h
  | k + 1, s, h => by
    rw [ivLoop]
    split
    · exact h
    · exact ivLoop_deB k _ (ivStep_deB h)

set_option exponentiation.threshold 600 in
theorem hvStep_deB {s : Iv} (h : DeB (dataVal p384ParamsData 0 12) s) :
    DeB (dataVal p384ParamsData 0 12) (hvStep s) :=
  have hr := batch_rows (Nat.min_le_right s.rem 62) s.δ (lowestI s.f) (lowestI s.g)
  ⟨deUpd_lt p384_bounds.1 p384_bounds.2 h.1 h.2 hr.1, deUpd_lt p384_bounds.1 p384_bounds.2 h.1 h.2 hr.2⟩

theorem hvLoop_deB : ∀ k (s : Iv), DeB (dataVal p384ParamsData 0 12) s →
    DeB (dataVal p384ParamsData 0 12) (hvLoop k s)
  | 0, _, h => h
  | k + 1, s, h => by
    rw [hvLoop]
    split
    · exact h
    · exact hvLoop_deB k _ (hvStep_deB h)

/-- The inverse of `s` that `p384_verify_prehash` computes is below `n`, for any `s`. -/
theorem pvInv_lt (M : Word → BitVec 8) (sp' : Word) : pvInv (pvW M sp') < n384 := by
  have hd : (pvW M sp').d.natAbs < dataVal p384OrderData 0 12 :=
    (ivLoop_deB 0x376 _ (deB_init r2_lt_n384)).1
  unfold pvInv
  rw [← ord_val]
  exact normVal_lt hd n384_bounds.2

/-- The inverse of `Z` that `p384_verify_prehash` computes is below `p`, for any `Z`. -/
theorem hvInv_lt (PZ : Nat) : hvInv (hvLoop 15 (hvInit PZ)) < p384 := by
  have hd : (hvLoop 15 (hvInit PZ)).d.natAbs < dataVal p384ParamsData 0 12 :=
    (hvLoop_deB 15 _ (deB_init r2_lt_p384)).1
  unfold hvInv
  rw [← params_N]
  exact normVal_lt hd p384_bounds.2

/-- **`p384_verify_prehash`'s side conditions hold** for any memory and arguments. -/
theorem pvSide_holds (M : Word → BitVec 8) (pk ph : Word) (len : Nat) (rp sp' : Word) :
    PvSide M pk ph len rp sp' :=
  ⟨fun _ _ _ => pvInv_lt M sp', fun _ _ _ _ _ _ => hvInv_lt _⟩

end C3.RV32.Safegcd
