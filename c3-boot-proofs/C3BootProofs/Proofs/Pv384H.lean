import C3BootProofs.Proofs.Pv384HLoop
import C3BootProofs.Proofs.Pv384HP
import C3BootProofs.Proofs.Pv384I1
import C3BootProofs.Proofs.Pv384I0
import C3BootProofs.Proofs.Pv384C

/-!
# `p384_verify_prehash`: from the sum to the result

Stages H and I composed, from 0xBEE to the epilogue at 0x130: the inversion
of the sum's `Z`, the affine `x`, and its comparison with `r`.
-/

namespace C3.RV32.Pv

open C3.Image C3.RV32.P3 C3.RV32.Dq

set_option maxRecDepth 20000

/-- The inversion of `Z` starts from `f = p`, `g = Z`, `d = 0`, `e = R²`,
`δ = 1`, and 886 steps. -/
def hvInit (PZ : Nat) : Iv :=
  ⟨1, (dataVal p384ParamsData 0 12 : Int), (PZ : Int), 0, (dataVal p384ParamsData 0x60 12 : Int), 0x376⟩

/-- The inverse the model leaves: `d`, negated modulo `p` when it and `f`
have different signs. -/
def hvInv (st : Iv) : Nat :=
  normVal (if st.d < 0 then 1 else 0) (if st.f < 0 then 1 else 0) st.d.natAbs (dataVal p384ParamsData 0 12)

/-- The inversion succeeded: `f` ended as ±1 and `Z` was nonzero. -/
def hvOk (PZ : Nat) : Prop := (hvLoop 15 (hvInit PZ)).f.natAbs = 1 ∧ PZ ≠ 0

instance (PZ : Nat) : Decidable (hvOk PZ) := inferInstanceAs (Decidable (_ ∧ _))

/-- What `p384_verify_prehash` returns for the sum `(PX, PY, PZ)` and `r`
in Montgomery form `RM`: whether the affine `x`, reduced modulo `n`, is `r`. -/
def pvH (RM PX PZ : Nat) : Word :=
  if hvOk PZ then (if RM = p3fm (p3fm PX (hvInv (hvLoop 15 (hvInit PZ)))) 1 * 2 ^ 384 % n384 then 1 else 0)
  else (if RM = p3fm 0 1 * 2 ^ 384 % n384 then 1 else 0)

set_option maxHeartbeats 16000000 in
/-- **Stages H and I**, from 0xBEE to 0x130. -/
theorem pv_stH {B : Word} {PX PY PZ RM : Nat} {n0 : Machine} (F : Fr B 0x21A0) (E0 : PvEnv7 n0.mem)
    (s0 : St n0.mem PV n0 0xBEE (reg n0)) (g0_2 : reg n0 sp = B + 0x420)
    (a0_1b0 : accV n0.mem (B + 0x420 + BitVec.ofNat 32 0x1B0) 12 = RM)
    (a0_e10 : accV n0.mem (B + 0x420 + BitVec.ofNat 32 0xE10) 12 = PX)
    (a0_e40 : accV n0.mem (B + 0x420 + BitVec.ofNat 32 0xE40) 12 = PY)
    (a0_e70 : accV n0.mem (B + 0x420 + BitVec.ofNat 32 0xE70) 12 = PZ)
    (hINV : hvOk PZ → hvInv (hvLoop 15 (hvInit PZ)) < p384) :
    ∃ n', Steps n0 n' ∧ St n'.mem PV n' 0x130 (reg n') ∧ PvEnv7 n'.mem ∧ (∀ x, PvR B x → n'.mem x = n0.mem x) ∧
      reg n' sp = B + 0x420 ∧ reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
      reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧ reg n' a0 = pvH RM PX PZ := by
  obtain ⟨n1, t1, s1, E1, f1, g1_2, g1_3, g1_4, -, -, g1_10, -, g1_19, g1_24, a1_1b0, a1_270, a1_d50, a1_e10, -,
      a1_1714, a1_17a4, a1_1c88, a1_1cb8, -, b1_2a0, b1_d80, b1_1744, b1_17d4, w1_10, w1_40, w1_e70, w1_e74⟩ :=
    pv_stHS F E0.E.E.E.E s0 g0_2 rfl rfl a0_1b0 a0_e10 a0_e40 a0_e70
  have I1 : HvInv B n1 (reg n0 3) (reg n0 4) (if PZ = 0 then 0 else 1) RM PX PY (hvInit PZ) := by
    refine ⟨g1_2, g1_3, g1_4, g1_10, g1_19, by rw [w1_40, g1_24]; rfl, a1_1b0, a1_e10, a1_1c88, a1_1cb8, w1_10,
      w1_e70, w1_e74, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by show (0x376 : Nat) < 2 ^ 32; decide⟩
    · show sgnVal (n1.mem (B + 0x420 + BitVec.ofNat 32 0x2A0)).toNat _ = _; rw [b1_2a0, a1_270]; rfl
    · show (n1.mem (B + 0x420 + BitVec.ofNat 32 0x2A0)).toNat ≤ 1; rw [b1_2a0]; decide
    · show sgnVal (n1.mem (B + 0x420 + BitVec.ofNat 32 0xD80)).toNat _ = _; rw [b1_d80, a1_d50]; rfl
    · show (n1.mem (B + 0x420 + BitVec.ofNat 32 0xD80)).toNat ≤ 1; rw [b1_d80]; decide
    · show sgnVal (n1.mem (B + 0x420 + BitVec.ofNat 32 0x1744)).toNat _ = _; rw [b1_1744, a1_1714]; rfl
    · show (n1.mem (B + 0x420 + BitVec.ofNat 32 0x1744)).toNat ≤ 1; rw [b1_1744]; decide
    · show sgnVal (n1.mem (B + 0x420 + BitVec.ofNat 32 0x17D4)).toNat _ = _; rw [b1_17d4, a1_17a4]; rfl
    · show (n1.mem (B + 0x420 + BitVec.ofNat 32 0x17D4)).toNat ≤ 1; rw [b1_17d4]; decide
  obtain ⟨n2, t2, E2, f2, s2, I2⟩ := hv_loop F 15 E1 s1 I1 (by show (0x376 : Nat) ≠ 0; decide)
    (hvLoop_rem 15 _ (by show (0x376 : Nat) ≤ 62 * 15; decide))
  have hz : (if PZ = 0 then (0 : Word) else 1) = 0 ∨ (if PZ = 0 then (0 : Word) else 1) = 1 := by
    by_cases h : PZ = 0
    · exact .inl (by rw [ite_eq_left h])
    · exact .inr (by rw [ite_eq_right h])
  obtain ⟨n3, t3, s3, E3, f3, g3_2, g3_3, g3_4, g3_9, g3_10, g3_19, a3_1b0, a3_1c34, a3_1c88, a3_1cb8, -, -, -⟩ :=
    pv_stHP (sd := n2.mem (B + 0x420 + BitVec.ofNat 32 0x2A0)) (sf := n2.mem (B + 0x420 + BitVec.ofNat 32 0x1744))
      (Ad := accV n2.mem (B + 0x420 + BitVec.ofNat 32 0x270) 12)
      (Af := accV n2.mem (B + 0x420 + BitVec.ofNat 32 0x1714) 12)
      F E2 s2 I2.sp rfl rfl I2.g19 I2.a1b0 rfl I2.ae10 rfl I2.a1c88 I2.a1cb8 rfl rfl I2.w10 I2.ld I2.lf hz
  have hAf := sv_abs I2.lf I2.vf
  have fr3 : ∀ x, PvR B x → n3.mem x = n0.mem x := fun x hx => by rw [f3 x hx, f2 x hx, f1 x hx]
  have E3' : PvEnv7 n3.mem := E0.fr F fr3
  have g33 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [g3_3]; exact I2.g3
  have g34 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [g3_4]; exact I2.g4
  have hok : (accV n2.mem (B + 0x420 + BitVec.ofNat 32 0x1714) 12 = 1 ∧ (if PZ = 0 then (0 : Word) else 1) = 1) ↔
      hvOk PZ := by
    rw [hAf]
    constructor
    · intro ⟨h1, h2⟩
      refine ⟨h1, fun h => ?_⟩
      rw [ite_eq_left h] at h2; exact absurd h2 (by decide)
    · intro ⟨h1, h2⟩
      exact ⟨h1, by rw [ite_eq_right h2]⟩
  by_cases hk : hvOk PZ
  · rw [ite_eq_left (hok.2 hk)] at g3_10
    have hF0 : (hvLoop 15 (hvInit PZ)).f ≠ 0 := fun h => by
      have := hk.1; rw [h] at this; exact absurd this (by decide)
    have hN : normVal (n2.mem (B + 0x420 + BitVec.ofNat 32 0x2A0)).toNat
        ((n2.mem (B + 0x420 + BitVec.ofNat 32 0x1744)).zeroExtend 32 : Word).toNat
        (accV n2.mem (B + 0x420 + BitVec.ofNat 32 0x270) 12) (dataVal p384ParamsData 0x0 12) =
        hvInv (hvLoop 15 (hvInit PZ)) := by
      rw [zext_toNat]
      exact norm_model I2.ld I2.lf I2.vd I2.vf hF0
    rw [hN] at a3_1c34
    obtain ⟨n4, t4, s4, E4, f4, g4_2, g4_3, g4_4, g4_10, -, -, -, -⟩ :=
      pv_stI1 F E3' s3 g3_2 rfl rfl g3_9 g3_10 g3_19 a3_1b0 a3_1c34 a3_1c88 a3_1cb8 (hINV hk)
    obtain ⟨n5, d5, u5⟩ := s4.jump E4.E.E.E.E.E.C.self pv_at_11cc (off' := 0x130) (by decide) (by rw [s4.pc]; decide)
    refine ⟨n5, t1.trans (t2.trans (t3.trans (t4.trans (.single d5)))), ⟨u5.pc, rfl, fun _ => rfl⟩,
      by rw [u5.mem]; exact E4, fun x hx => by rw [u5.mem, f4 x hx, fr3 x hx], by rw [u5.regs, g4_2],
      by rw [u5.regs, g4_3, g33], by rw [u5.regs, g4_4, g34], ?_⟩
    rw [u5.regs, g4_10, pvH, ite_eq_left hk]
  · rw [ite_eq_right (fun h => hk (hok.1 h))] at g3_10
    obtain ⟨n4, t4, s4, E4, f4, g4_2, g4_3, g4_4, g4_10, -, -, -, -⟩ :=
      pv_stI0 F E3' s3 g3_2 rfl rfl g3_9 g3_10 g3_19 a3_1b0 a3_1c34 a3_1c88 a3_1cb8
    obtain ⟨n5, d5, u5⟩ := s4.jump E4.E.E.E.E.E.C.self pv_at_11cc (off' := 0x130) (by decide) (by rw [s4.pc]; decide)
    refine ⟨n5, t1.trans (t2.trans (t3.trans (t4.trans (.single d5)))), ⟨u5.pc, rfl, fun _ => rfl⟩,
      by rw [u5.mem]; exact E4, fun x hx => by rw [u5.mem, f4 x hx, fr3 x hx], by rw [u5.regs, g4_2],
      by rw [u5.regs, g4_3, g33], by rw [u5.regs, g4_4, g34], ?_⟩
    rw [u5.regs, g4_10, pvH, ite_eq_right hk]

end C3.RV32.Pv
