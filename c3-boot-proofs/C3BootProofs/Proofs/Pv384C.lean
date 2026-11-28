import C3BootProofs.Proofs.Pv384C0
import C3BootProofs.Proofs.Pv384CIt
import C3BootProofs.Proofs.Pv384C2a
import C3BootProofs.Proofs.Pv384C2b1
import C3BootProofs.Proofs.Pv384C2b0

/-!
# `p384_verify_prehash`: the inversion of `s`

From 0x3B0 to 0x730: the variable-time safegcd inversion of `s` in
Montgomery form, as the model `ivLoop` runs it, or a panic when the model
ends with `f` other than ±1.
-/

namespace C3.RV32.Pv

open C3.Image C3.RV32.P3 C3.RV32.Dq

set_option maxRecDepth 20000

theorem ivLoop_rem0 {s : Iv} (h : s.rem = 0) : ∀ k, ivLoop k s = s
  | 0 => rfl
  | _ + 1 => by simp only [ivLoop]; rw [ite_eq_left (Or.inl h)]

/-- **The loop** from 0x3EC to 0x628, with at most `k` batches. -/
theorem pv_loop {B r3 r4 : Word} {QX QY QZ RM SM ZM : Nat} (F : Fr B 0x21A0) :
    ∀ k {m : Machine} {st : Iv}, PvEnv3 m.mem → St m.mem PV m 0x3EC (reg m) →
      IvInv B m r3 r4 QX QY QZ RM SM ZM st → st.rem ≠ 0 → st.rem ≤ k →
      ∃ m', Steps m m' ∧ PvEnv3 m'.mem ∧ (∀ x, PvR B x → m'.mem x = m.mem x) ∧
        St m'.mem PV m' 0x628 (reg m') ∧ IvInv B m' r3 r4 QX QY QZ RM SM ZM (ivLoop k st)
  | 0, _, _, _, _, _, h0, hk => absurd (Nat.le_zero.1 hk) h0
  | k + 1, m, st, E, s, I, h0, hk => by
    obtain ⟨m1, c1, E1, f1, h⟩ := pv_iter F E s I h0
    rcases h with ⟨hg, s1, I1⟩ | ⟨hg, I1, ⟨hr, s1⟩ | ⟨hr, s1⟩⟩
    · refine ⟨m1, c1, E1, f1, s1, ?_⟩
      simp only [ivLoop]; rw [ite_eq_left (Or.inr hg)]; exact I1
    · refine ⟨m1, c1, E1, f1, s1, ?_⟩
      simp only [ivLoop]; rw [ite_eq_right (by omega), ivLoop_rem0 hr]; exact I1
    · have hk' : (ivStep st).rem ≤ k := by show st.rem - min st.rem 62 ≤ k; omega
      obtain ⟨m2, c2, E2, f2, s2, I2⟩ := pv_loop F k E1 s1 I1 hr hk'
      refine ⟨m2, c1.trans c2, E2, fun x hx => by rw [f2 x hx, f1 x hx], s2, ?_⟩
      simp only [ivLoop]; rw [ite_eq_right (by omega)]; exact I2

/-- The inversion's first state, for `s` in Montgomery form: `f = n`, `g = s`,
`d = 0`, and `e = 2^768 mod n`. -/
def ivInit (SM : Nat) : Iv :=
  ⟨1, (dataVal p384OrderData 0 12 : Int), (SM : Int), 0, (dataVal p384ScalarR2Data 0 12 : Int), 0x376⟩

/-- The inverse the model leaves: `d`, negated modulo `n` when it and `f`
have different signs. -/
def pvInv (st : Iv) : Nat :=
  normVal (if st.d < 0 then 1 else 0) (if st.f < 0 then 1 else 0) st.d.natAbs (dataVal p384OrderData 0 12)

theorem sv_abs {σ A : Nat} {X : Int} (hσ : σ ≤ 1) (h : sgnVal σ A = X) : A = X.natAbs := by
  obtain ⟨n1, n2, n3⟩ := sgnVal_rep hσ h
  rcases Int.lt_trichotomy X 0 with h0 | h0 | h0
  · exact (n1 h0).2
  · rw [n3 h0, h0]; rfl
  · exact (n2 h0).2

theorem norm_model {sd sf Ad Af N : Nat} {D F : Int} (hsd : sd ≤ 1) (hsf : sf ≤ 1) (hD : sgnVal sd Ad = D)
    (hF : sgnVal sf Af = F) (hF0 : F ≠ 0) :
    normVal sd sf Ad N = normVal (if D < 0 then 1 else 0) (if F < 0 then 1 else 0) D.natAbs N := by
  obtain ⟨d1, d2, d3⟩ := sgnVal_rep hsd hD
  obtain ⟨f1, f2, -⟩ := sgnVal_rep hsf hF
  have hs : sf = if F < 0 then 1 else 0 := by
    rcases Int.lt_trichotomy F 0 with h0 | h0 | h0
    · rw [ite_eq_left h0]; exact (f1 h0).1
    · exact absurd h0 hF0
    · rw [ite_eq_right (by omega)]; exact (f2 h0).1
  rw [← hs]
  rcases Int.lt_trichotomy D 0 with h0 | h0 | h0
  · rw [ite_eq_left h0, ← (d1 h0).1, ← (d1 h0).2]
  · rw [d3 h0, h0]; unfold normVal; simp
  · rw [ite_eq_right (by omega), ← (d2 h0).1, ← (d2 h0).2]

theorem zext_toNat (b : BitVec 8) : (b.zeroExtend 32 : BitVec 32).toNat = b.toNat := by
  have := b.isLt
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]

def pvP : List BInstr := [.lui a0 0x1000, .aluImm .add a0 a0 0x294, .alu .add a0 a0 sp]
theorem pvP_end : blockEnd p384VerifyPrehashCode 0x11D0 pvP = some 0x11D8 := by decide

/-- The panic at 0x11D0: `assert_failed` on the unwrap of the inverse. -/
theorem pv_panic11d0 {B : Word} {m : Machine} (F : Fr B 0x21A0) (E : PvEnv m.mem)
    (s : St m.mem PV m 0x11D0 (reg m)) (hsp : reg m sp = B + 0x420) : Panics m := by
  have FS : Fr (B + 0x420) 0x1D80 := F.sub (c := 0x420) (by decide) (by decide)
  obtain ⟨m1, c1, u1⟩ := s.block pvP E.C.self pvP_end ⟨trivial, trivial, trivial, trivial⟩
  have s1 : St m.mem PV m1 0x11D8 (reg m1) := ⟨u1.pc, u1.mem, fun _ => rfl⟩
  have sp1 : reg m1 sp = B + 0x420 := by
    rw [u1.regs, runBlock_reg _ _ _ sp s.zero (by decide)]; exact hsp
  obtain ⟨n1, c2, pc2, mem2, regs2⟩ := s1.callRa E.C.self pv_at_11d8 pv_at_11dc
    (cb := BitVec.ofNat 32 assertFailedU8Address) (by decide) (by decide)
  refine Panics.of_steps (c1.trans c2) (assertFailedU8_panics n1 (by rw [mem2]; exact E.C.K.panic) pc2 ?_)
  rw [regs2, upd_ne (by decide) (by decide), sp1]; exact FS.room (by decide)

set_option maxHeartbeats 16000000 in
/-- **Stage C**, from 0x3B0 to 0x730: the inversion of `s` in Montgomery form,
`SM`, as `ivLoop` from `ivInit SM`, with the inverse at 0xE10 when the model
ends with `f = ±1`, and a panic otherwise. -/
theorem pv_stC {B ph : Word} {len X Y R Sg : Nat} {n0 : Machine}
    (F : Fr B 0x21A0) (E0 : PvEnv3 n0.mem) (s0 : St n0.mem PV n0 0x3B0 (reg n0))
    (g0_2 : reg n0 sp = B + 0x420) (g0_8 : reg n0 (8 : Fin 32) = B + 0x420 + BitVec.ofNat 32 0xD80)
    (g0_9 : reg n0 (9 : Fin 32) = BitVec.ofNat 32 (img% p384ScalarR2Address))
    (g0_18 : reg n0 (18 : Fin 32) = BitVec.ofNat 32 (img% p384OrderAddress)) (g0_19 : reg n0 (19 : Fin 32) = BitVec.ofNat 32 len)
    (g0_20 : reg n0 (20 : Fin 32) = BitVec.ofNat 32 0x177023BB)
    (g0_21 : reg n0 (21 : Fin 32) = B + 0x420 + BitVec.ofNat 32 0x12C4)
    (g0_22 : reg n0 (22 : Fin 32) = BitVec.ofNat 32 0x912B9F76)
    (g0_23 : reg n0 (23 : Fin 32) = B + 0x420 + BitVec.ofNat 32 0x1744)
    (g0_24 : reg n0 (24 : Fin 32) = BitVec.ofNat 32 0x1)
    (a0_120 : accV n0.mem (B + 0x420 + BitVec.ofNat 32 0x120) 12 = X)
    (a0_150 : accV n0.mem (B + 0x420 + BitVec.ofNat 32 0x150) 12 = Y)
    (a0_180 : accV n0.mem (B + 0x420 + BitVec.ofNat 32 0x180) 12 = dataVal p384MontOneData 0 12)
    (a0_1b0 : accV n0.mem (B + 0x420 + BitVec.ofNat 32 0x1B0) 12 = R * 2 ^ 384 % n384)
    (a0_1e0 : accV n0.mem (B + 0x420 + BitVec.ofNat 32 0x1E0) 12 = Sg * 2 ^ 384 % n384)
    (a0_210 : accV n0.mem (B + 0x420 + BitVec.ofNat 32 0x210) 12 = beNat (memBytes n0.mem ph (min len 48)) * 2 ^ 384 % n384)
    (a0_d50 : accV n0.mem (B + 0x420 + BitVec.ofNat 32 0xD50) 12 = Sg * 2 ^ 384 % n384)
    (a0_e10 : accV n0.mem (B + 0x420 + BitVec.ofNat 32 0xE10) 12 = dataVal p384OrderData 0 12)
    (a0_e40 : accV n0.mem (B + 0x420 + BitVec.ofNat 32 0xE40) 12 = dataVal p384ScalarR2Data 0 12)
    (a0_1714 : accV n0.mem (B + 0x420 + BitVec.ofNat 32 0x1714) 12 = dataVal p384OrderData 0 12)
    (b0_1744 : n0.mem (B + 0x420 + BitVec.ofNat 32 0x1744) = 0)
    (w0_e70 : memLoad32 n0.mem (B + 0x420 + BitVec.ofNat 32 0xE70) = BitVec.ofNat 32 0x177023BB)
    (w0_e74 : memLoad32 n0.mem (B + 0x420 + BitVec.ofNat 32 0xE74) = BitVec.ofNat 32 0x912B9F76) :
    ((ivLoop 0x376 (ivInit (Sg * 2 ^ 384 % n384))).f.natAbs = 1 ∧
      ∃ n', Steps n0 n' ∧ St n'.mem PV n' 0x730 (reg n') ∧ PvEnv3 n'.mem ∧ (∀ x, PvR B x → n'.mem x = n0.mem x) ∧
        reg n' sp = B + 0x420 ∧ reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (9 : Fin 32) = BitVec.ofNat 32 0x1 ∧ reg n' (18 : Fin 32) = B + 0x420 + BitVec.ofNat 32 0x17A4 ∧
        reg n' (25 : Fin 32) = B + 0x420 + BitVec.ofNat 32 0xD80 ∧
        accV n'.mem (B + 0x420 + BitVec.ofNat 32 0x120) 12 = X ∧
        accV n'.mem (B + 0x420 + BitVec.ofNat 32 0x150) 12 = Y ∧
        accV n'.mem (B + 0x420 + BitVec.ofNat 32 0x180) 12 = dataVal p384MontOneData 0 12 ∧
        accV n'.mem (B + 0x420 + BitVec.ofNat 32 0x1B0) 12 = R * 2 ^ 384 % n384 ∧
        accV n'.mem (B + 0x420 + BitVec.ofNat 32 0x1E0) 12 = Sg * 2 ^ 384 % n384 ∧
        accV n'.mem (B + 0x420 + BitVec.ofNat 32 0x210) 12 = beNat (memBytes n0.mem ph (min len 48)) * 2 ^ 384 % n384 ∧
        accV n'.mem (B + 0x420 + BitVec.ofNat 32 0xE10) 12 = pvInv (ivLoop 0x376 (ivInit (Sg * 2 ^ 384 % n384)))) ∨
    ((ivLoop 0x376 (ivInit (Sg * 2 ^ 384 % n384))).f.natAbs ≠ 1 ∧ Panics n0) := by
  obtain ⟨n1, t1, s1, E1, f1, g1_2, g1_3, g1_4, g1_8, g1_9, g1_18, g1_19, g1_20, g1_21, g1_22, g1_23, g1_24, g1_25,
    g1_26, g1_27, a1_120, a1_150, a1_180, a1_1b0, a1_1e0, a1_210, a1_270, a1_d50, a1_e10, a1_e40, a1_1714, a1_17a4,
    b1_2a0, b1_d80, b1_1744, b1_17d4, w1_e70, w1_e74⟩ :=
    pv_stC0 F E0 s0 g0_2 rfl rfl g0_8 g0_9 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 rfl rfl rfl a0_120 a0_150
      a0_180 a0_1b0 a0_1e0 a0_210 a0_d50 a0_e10 a0_e40 a0_1714 b0_1744 w0_e70 w0_e74
  obtain ⟨n2, d2, u2⟩ := s1.notTaken E1.E.C.self 0x3EC pv_at_3e8 (by decide)
    (by show (reg n1 23 == reg n1 x0) = false; rw [g1_23, s1.zero]; decide)
  have e2 : reg n2 = reg n1 := funext u2.regs
  have m2 : n2.mem = n1.mem := u2.mem
  have z8 : (0 : BitVec 8).toNat = 0 := rfl
  have I1 : IvInv B n1 (reg n0 3) (reg n0 4) X Y (dataVal p384MontOneData 0 12) (R * 2 ^ 384 % n384)
      (Sg * 2 ^ 384 % n384) (beNat (memBytes n0.mem ph (min len 48)) * 2 ^ 384 % n384) (ivInit (Sg * 2 ^ 384 % n384)) := by
    refine ⟨g1_2, g1_3, g1_4, by rw [g1_21, g1_19]; rfl, g1_20, g1_22, g1_23, g1_24, g1_26, a1_120, a1_150, a1_180,
      a1_1b0, a1_1e0, a1_210, a1_e10, a1_e40, w1_e70, w1_e74, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      by show (0x376 : Nat) < 2 ^ 32; decide⟩
    · show sgnVal (n1.mem (B + 0x420 + BitVec.ofNat 32 0x2A0)).toNat _ = _; rw [b1_2a0, a1_270]; rfl
    · show (n1.mem (B + 0x420 + BitVec.ofNat 32 0x2A0)).toNat ≤ 1; rw [b1_2a0]; decide
    · show sgnVal (n1.mem (B + 0x420 + BitVec.ofNat 32 0xD80)).toNat _ = _; rw [b1_d80, a1_d50]; rfl
    · show (n1.mem (B + 0x420 + BitVec.ofNat 32 0xD80)).toNat ≤ 1; rw [b1_d80]; decide
    · show sgnVal (n1.mem (B + 0x420 + BitVec.ofNat 32 0x1744)).toNat _ = _; rw [b1_1744, a1_1714]; rfl
    · show (n1.mem (B + 0x420 + BitVec.ofNat 32 0x1744)).toNat ≤ 1; rw [b1_1744]; decide
    · show sgnVal (n1.mem (B + 0x420 + BitVec.ofNat 32 0x17D4)).toNat _ = _; rw [b1_17d4, a1_17a4]; rfl
    · show (n1.mem (B + 0x420 + BitVec.ofNat 32 0x17D4)).toNat ≤ 1; rw [b1_17d4]; decide
  have I2 := I1.of m2 fun q _ => by rw [e2]
  have E2 : PvEnv3 n2.mem := by rw [m2]; exact E1
  obtain ⟨n3, t3, E3, f3, s3, I3⟩ := pv_loop F 0x376 E2 ⟨u2.pc, rfl, fun _ => rfl⟩ I2
    (by show (0x376 : Nat) ≠ 0; decide) (by show (0x376 : Nat) ≤ 0x376; decide)
  obtain ⟨n4, t4, s4, E4, f4, g4_2, g4_3, g4_4, g4_9, g4_24, g4_10, a4_120, a4_150, a4_180, a4_1b0, a4_1e0, a4_210,
    a4_1294, -, -⟩ :=
    pv_stC2a (sd := n3.mem (B + 0x420 + BitVec.ofNat 32 0x2A0)) (sf := n3.mem (B + 0x420 + BitVec.ofNat 32 0x1744))
      (Ad := accV n3.mem (B + 0x420 + BitVec.ofNat 32 0x270) 12)
      (Af := accV n3.mem (B + 0x420 + BitVec.ofNat 32 0x1714) 12)
      F E3 s3 I3.sp rfl rfl I3.g24 I3.a120 I3.a150 I3.a180 I3.a1b0 I3.a1e0 I3.a210 rfl I3.ae10 rfl rfl rfl I3.ld I3.lf
  have hAf := sv_abs I3.lf I3.vf
  have fr4 : ∀ x, PvR B x → n4.mem x = n0.mem x := fun x hx => by
    rw [f4 x hx, f3 x hx, m2, f1 x hx]
  have g43 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [g4_3]; exact I3.g3
  have g44 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [g4_4]; exact I3.g4
  by_cases hok : accV n3.mem (B + 0x420 + BitVec.ofNat 32 0x1714) 12 = 1
  · rw [ite_eq_left hok] at g4_10
    obtain ⟨n5, t5, s5, E5, f5, g5_2, g5_3, g5_4, g5_9, g5_10, g5_18, g5_25, a5_120, a5_150, a5_180, a5_1b0,
      a5_1e0, a5_210, a5_e10⟩ :=
      pv_stC2b1 F E4 s4 g4_2 rfl rfl g4_9 g4_10 g4_24 a4_120 a4_150 a4_180 a4_1b0 a4_1e0 a4_210 a4_1294
    obtain ⟨n6, d6, u6⟩ := s5.notTaken E5.E.C.self 0x730 pv_at_72c (by decide)
      (by show (reg n5 9 != reg n5 a0) = false; rw [g5_9, g5_10]; rfl)
    have hF : (ivLoop 0x376 (ivInit (Sg * 2 ^ 384 % n384))).f.natAbs = 1 := by rw [← hAf]; exact hok
    refine .inl ⟨hF, n6, t1.trans (.cons d2 (t3.trans (t4.trans (t5.trans (.single d6))))), ⟨u6.pc, rfl, fun _ => rfl⟩,
      by rw [u6.mem]; exact E5, fun x hx => by rw [u6.mem, f5 x hx, fr4 x hx],
      by rw [u6.regs, g5_2], by rw [u6.regs, g5_3, g43], by rw [u6.regs, g5_4, g44], by rw [u6.regs, g5_9],
      by rw [u6.regs, g5_18], by rw [u6.regs, g5_25], by rw [u6.mem]; exact a5_120, by rw [u6.mem]; exact a5_150,
      by rw [u6.mem]; exact a5_180, by rw [u6.mem]; exact a5_1b0, by rw [u6.mem]; exact a5_1e0,
      by rw [u6.mem]; exact a5_210, ?_⟩
    rw [u6.mem, a5_e10]
    unfold pvInv
    rw [zext_toNat]
    exact norm_model I3.ld I3.lf I3.vd I3.vf (fun h => by rw [h] at hF; exact absurd hF (by decide))
  · rw [ite_eq_right hok] at g4_10
    obtain ⟨n5, t5, s5, E5, f5, g5_2, -, -, g5_9, g5_10, -, -, -, -, -, -, -, -, -⟩ :=
      pv_stC2b0 F E4 s4 g4_2 rfl rfl g4_9 g4_10 g4_24 a4_120 a4_150 a4_180 a4_1b0 a4_1e0 a4_210 a4_1294
    obtain ⟨n6, d6, u6⟩ := s5.taken E5.E.C.self 0x11D0 pv_at_72c (by decide)
      (by show (reg n5 9 != reg n5 a0) = true; rw [g5_9, g5_10]; rfl)
    refine .inr ⟨fun h => hok (by rw [hAf]; exact h), Panics.of_steps
      (t1.trans (.cons d2 (t3.trans (t4.trans (t5.trans (.single d6)))))) ?_⟩
    exact pv_panic11d0 F (by rw [u6.mem]; exact E5.E) ⟨u6.pc, rfl, fun _ => rfl⟩ (by rw [u6.regs, g5_2])

end C3.RV32.Pv
