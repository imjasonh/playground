import C3BootProofs.Models.EcdsaInv
import C3BootProofs.Proofs.Pv384Main

/-!
# The P-384 check's inversions

`ivLoop` inverts `s` modulo `n` and `hvLoop` inverts `Z` modulo `p`, both
in Montgomery form, starting from `e = 2^768`. Both are `stepW` batches on
384-bit values, so they keep `IvOk`. When the batches end with `f = ±1`, the
normalized `d` times the value inverted is `2^768`.
-/

namespace C3.Models

open C3.RV32 C3.RV32.Pv C3.RV32.P3 C3.RV32.Dq C3.Image

theorem ivStep_eq (s : Iv) : ivStep s = stepW 384 pvMI (dataVal p384OrderData 0 12) s := rfl

theorem hvStep_eq (s : Iv) : hvStep s = stepW 384 hvMI (dataVal p384ParamsData 0 12) s := rfl

theorem normVal_eq (σ fs X p : Nat) : normVal σ fs X p = normW 384 σ fs X p := rfl

set_option exponentiation.threshold 800 in
theorem scalarR2_val : dataVal p384ScalarR2Data 0 12 = 2 ^ 768 % n384 := by unfold n384; decide

set_option exponentiation.threshold 800 in
theorem paramsR2_val : dataVal p384ParamsData 0x60 12 = 2 ^ 768 % RV32.p384 := by unfold RV32.p384; decide

set_option exponentiation.threshold 800 in
theorem ivLoop_ok {x e0 : Int} (hMI : n384 * pvMI % 2 ^ 64 = 1) :
    ∀ k s, IvOk 384 n384 x e0 s → IvOk 384 n384 x e0 (ivLoop k s)
  | 0, _, h => h
  | k + 1, s, h => by
    rw [ivLoop]
    by_cases h0 : s.rem = 0 ∨ s.g = 0
    · rw [ite_eq_left h0]; exact h
    · rw [ite_eq_right h0, ivStep_eq, ord_val]
      exact ivLoop_ok hMI k _ (stepW_ok (by decide) (by decide) hMI h)

set_option exponentiation.threshold 800 in
theorem hvLoop_ok {x e0 : Int} (hMI : RV32.p384 * hvMI % 2 ^ 64 = 1) :
    ∀ k s, IvOk 384 RV32.p384 x e0 s → IvOk 384 RV32.p384 x e0 (hvLoop k s)
  | 0, _, h => h
  | k + 1, s, h => by
    rw [hvLoop]
    by_cases h0 : s.rem = 0
    · rw [ite_eq_left h0]; exact h
    · rw [ite_eq_right h0, hvStep_eq, params_N]
      exact hvLoop_ok hMI k _ (stepW_ok (by unfold RV32.p384; decide) (by unfold RV32.p384; decide) hMI h)

set_option exponentiation.threshold 800 in
/-- **The inversion of `s`**: when its batches end with `f = ±1`, as the
model requires, `pvInv` times `S` is `2^768` modulo `n`. -/
theorem pvInv_inv {S : Nat} (hS : S < n384) (hf : (ivLoop 0x376 (ivInit S)).f.natAbs = 1) :
    MEq n384 ((pvInv (ivLoop 0x376 (ivInit S)) : Nat) * (S : Int)) ((2 ^ 768 % n384 : Nat) : Int) ∧
      pvInv (ivLoop 0x376 (ivInit S)) < n384 := by
  have hi : ivInit S = ⟨1, (n384 : Int), (S : Int), 0, ((2 ^ 768 % n384 : Nat) : Int), 0x376⟩ := by
    unfold ivInit; rw [ord_val, scalarR2_val]
  have h0 := ivOk_init (W := 384) (x := S) (e0 := 2 ^ 768 % n384) 1 0x376 (by decide) (by decide)
    (Nat.lt_trans hS (by decide)) (Nat.mod_lt _ (by decide))
  have h1 := ivLoop_ok (by decide) 0x376 _ h0
  rw [← hi] at h1
  unfold pvInv
  rw [ord_val, normVal_eq]
  exact normW_inv (by decide) h1 hf

set_option exponentiation.threshold 800 in
/-- **The inversion of `Z`**: when it succeeds (`hvOk`), `hvInv` times `Z`
is `2^768` modulo `p`. -/
theorem hvInv_inv {Z : Nat} (hZ : Z < RV32.p384) (h : hvOk Z) :
    MEq RV32.p384 ((hvInv (hvLoop 15 (hvInit Z)) : Nat) * (Z : Int)) ((2 ^ 768 % RV32.p384 : Nat) : Int) ∧
      hvInv (hvLoop 15 (hvInit Z)) < RV32.p384 := by
  have hi : hvInit Z = ⟨1, (RV32.p384 : Int), (Z : Int), 0, ((2 ^ 768 % RV32.p384 : Nat) : Int), 0x376⟩ := by
    unfold hvInit; rw [params_N, paramsR2_val]
  have hp : RV32.p384 < 2 ^ 384 := by unfold RV32.p384; decide
  have h0 := ivOk_init (W := 384) (x := Z) (e0 := 2 ^ 768 % RV32.p384) 1 0x376 (by unfold RV32.p384; decide) hp
    (Nat.lt_trans hZ hp) (Nat.mod_lt _ (by unfold RV32.p384; decide))
  have h1 := hvLoop_ok (by unfold RV32.p384; decide) 15 _ h0
  rw [← hi] at h1
  unfold hvInv
  rw [params_N, normVal_eq]
  exact normW_inv (Nat.le_of_lt hp) h1 h.1

end C3.Models
