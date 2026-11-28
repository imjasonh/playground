import C3BootProofs.Proofs.Pv384HB
import C3BootProofs.Proofs.Pv384CIt

/-!
# `p384_verify_prehash`: the loop of the inversion of `Z`

The batches of stage H, from 0xCE8 back to 0xCE8: `min rem 62` constant-time
divsteps, then their matrix applied to `f`, `g`, `d`, and `e`, until no
steps are left. Unlike the inversion of `s`, the loop doesn't stop early
when `g` is zero.
-/

namespace C3.RV32.Pv

open C3.Image C3.RV32.P3 C3.RV32.Dq

set_option maxRecDepth 20000

/-- `-p⁻¹ mod 2^64`, as the batches pass it to `update_de`. -/
abbrev hvMI : Nat := (BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFE).toNat

/-- One batch of the inversion of `Z`: `min rem 62` divsteps on the low
words of `f` and `g`, then their matrix applied to `f`, `g`, `d`, and `e`
modulo `p`. -/
def hvStep (s : Iv) : Iv :=
  let n := min s.rem 62
  let t := dsIter n ⟨s.δ, lowestI s.f, lowestI s.g, 1, 0, 0, 1⟩
  ⟨t.δ, fgUpd s.f s.g (i64Val t.u) (i64Val t.v) n, fgUpd s.f s.g (i64Val t.q) (i64Val t.r) n,
    deUpd s.d s.e (i64Val t.u) (i64Val t.v) hvMI n (dataVal p384ParamsData 0 12),
    deUpd s.d s.e (i64Val t.q) (i64Val t.r) hvMI n (dataVal p384ParamsData 0 12), s.rem - n⟩

/-- Batches until no steps are left, with `k` batches at most. -/
def hvLoop : Nat → Iv → Iv
  | 0, s => s
  | k + 1, s => if s.rem = 0 then s else hvLoop k (hvStep s)

theorem hvLoop_done : ∀ k (s : Iv), s.rem = 0 → hvLoop k s = s
  | 0, _, _ => rfl
  | _ + 1, s, h => by rw [hvLoop, ite_eq_left h]

theorem hvLoop_rem : ∀ k (s : Iv), s.rem ≤ 62 * k → (hvLoop k s).rem = 0
  | 0, s, h => by rw [hvLoop]; omega
  | k + 1, s, h => by
    rw [hvLoop]
    by_cases h0 : s.rem = 0
    · rw [ite_eq_left h0]; exact h0
    · rw [ite_eq_right h0]
      exact hvLoop_rem k _ (by simp only [hvStep]; omega)

/-- The bytes that the constant-time divsteps leave alone. -/
def CtKeep (B : Word) (M M' : Word → BitVec 8) : Prop :=
  ∀ e, e + 1 ≤ 0x1D4C → (e < 0x1C ∨ 0x58 ≤ e) → e ≠ 0x1294 →
    M' (B + 0x420 + BitVec.ofNat 32 e) = M (B + 0x420 + BitVec.ofNat 32 e)

theorem CtKeep.acc {B : Word} {M M' : Word → BitVec 8} (h : CtKeep B M M') {d k : Nat}
    (hd : d + 4 * k ≤ 0x1D4C) (hs : d + 4 * k ≤ 0x1C ∨ 0x58 ≤ d) (hn : d + 4 * k ≤ 0x1294 ∨ 0x1295 ≤ d) :
    accV M' (B + 0x420 + BitVec.ofNat 32 d) k = accV M (B + 0x420 + BitVec.ofNat 32 d) k :=
  accV_S k fun q hq => h _ (by omega) (by omega) (by omega)

theorem CtKeep.w32 {B : Word} {M M' : Word → BitVec 8} (h : CtKeep B M M') {d : Nat}
    (hd : d + 4 ≤ 0x1D4C) (hs : d + 4 ≤ 0x1C ∨ 0x58 ≤ d) (hn : d + 4 ≤ 0x1294 ∨ 0x1295 ≤ d) :
    memLoad32 M' (B + 0x420 + BitVec.ofNat 32 d) = memLoad32 M (B + 0x420 + BitVec.ofNat 32 d) :=
  memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact h _ (by omega) (by omega) (by omega)

/-- What holds at 0xCE8, the head of the loop, for the state `st`. -/
structure HvInv (B : Word) (m : Machine) (r3 r4 zf : Word) (RM PX PY : Nat) (st : Iv) : Prop where
  sp : reg m sp = B + 0x420
  g3 : reg m (3 : Fin 32) = r3
  g4 : reg m (4 : Fin 32) = r4
  a0 : reg m a0 = BitVec.ofNat 32 st.rem
  g19 : reg m (19 : Fin 32) = B + 0x420 + BitVec.ofNat 32 0xD80
  dl : W64 (memLoad32 m.mem (B + 0x420 + BitVec.ofNat 32 0x40)) (reg m (24 : Fin 32)) = st.δ
  a1b0 : accV m.mem (B + 0x420 + BitVec.ofNat 32 0x1B0) 12 = RM
  ae10 : accV m.mem (B + 0x420 + BitVec.ofNat 32 0xE10) 12 = dataVal p384ParamsData 0x0 12
  a1c88 : accV m.mem (B + 0x420 + BitVec.ofNat 32 0x1C88) 12 = PX
  a1cb8 : accV m.mem (B + 0x420 + BitVec.ofNat 32 0x1CB8) 12 = PY
  w10 : memLoad32 m.mem (B + 0x420 + BitVec.ofNat 32 0x10) = zf
  we70 : memLoad32 m.mem (B + 0x420 + BitVec.ofNat 32 0xE70) = BitVec.ofNat 32 0xFFFFFFFF
  we74 : memLoad32 m.mem (B + 0x420 + BitVec.ofNat 32 0xE74) = BitVec.ofNat 32 0xFFFFFFFE
  vd : sgnVal (m.mem (B + 0x420 + BitVec.ofNat 32 (0x270 + 0x30))).toNat
    (accV m.mem (B + 0x420 + BitVec.ofNat 32 0x270) 12) = st.d
  ld : (m.mem (B + 0x420 + BitVec.ofNat 32 (0x270 + 0x30))).toNat ≤ 1
  vg : sgnVal (m.mem (B + 0x420 + BitVec.ofNat 32 (0xD50 + 0x30))).toNat
    (accV m.mem (B + 0x420 + BitVec.ofNat 32 0xD50) 12) = st.g
  lg : (m.mem (B + 0x420 + BitVec.ofNat 32 (0xD50 + 0x30))).toNat ≤ 1
  vf : sgnVal (m.mem (B + 0x420 + BitVec.ofNat 32 (0x1714 + 0x30))).toNat
    (accV m.mem (B + 0x420 + BitVec.ofNat 32 0x1714) 12) = st.f
  lf : (m.mem (B + 0x420 + BitVec.ofNat 32 (0x1714 + 0x30))).toNat ≤ 1
  ve : sgnVal (m.mem (B + 0x420 + BitVec.ofNat 32 (0x17A4 + 0x30))).toNat
    (accV m.mem (B + 0x420 + BitVec.ofNat 32 0x17A4) 12) = st.e
  le : (m.mem (B + 0x420 + BitVec.ofNat 32 (0x17A4 + 0x30))).toNat ≤ 1
  rem : st.rem < 2 ^ 32

theorem ct_ofNat (n : Nat) (h : 1 ≤ n) : BitVec.ofNat 32 n = BitVec.ofNat 32 (n - 1 + 1) := by
  rw [Nat.sub_add_cancel h]

set_option maxHeartbeats 16000000 in
/-- **One batch** of the inversion of `Z`, from 0xCE8: `hvStep`, then back
to 0xCE8 or, when no steps are left, on to 0xFFC. -/
theorem hv_iter {B r3 r4 zf : Word} {RM PX PY : Nat} {m : Machine} {st : Iv} (F : Fr B 0x21A0)
    (E : PvEnv3 m.mem) (s : St m.mem PV m 0xCE8 (reg m)) (I : HvInv B m r3 r4 zf RM PX PY st)
    (h0 : st.rem ≠ 0) :
    ∃ m', Steps m m' ∧ PvEnv3 m'.mem ∧ (∀ x, PvR B x → m'.mem x = m.mem x) ∧
      HvInv B m' r3 r4 zf RM PX PY (hvStep st) ∧
      (((hvStep st).rem = 0 ∧ St m'.mem PV m' 0xFFC (reg m')) ∨
       ((hvStep st).rem ≠ 0 ∧ St m'.mem PV m' 0xCE8 (reg m'))) := by
  have hn1 : 1 ≤ min st.rem 62 := by omega
  have hn2 : min st.rem 62 ≤ 62 := Nat.min_le_right _ _
  obtain ⟨n1, c1, s1, E1, fr1, sp1, r1_3, r1_4, r1_8, r1_13, r1_14, r1_18, r1_19, r1_20, r1_22, r1_23, r1_24,
      r1_25, r1_26, wf1, wg1, a1_1b0, a1_e10, a1_1c88, a1_1cb8, w1_10, w1_14, w1_18, w1_40, w1_54, w1_e70, w1_e74,
      v1_270, l1_270, v1_d50, l1_d50, v1_1714, l1_1714, v1_17a4, l1_17a4⟩ :=
    pv_stHA (dl := memLoad32 m.mem (B + 0x420 + BitVec.ofNat 32 0x40)) (dh := reg m (24 : Fin 32)) F E s I.sp rfl rfl
      I.a0 I.g19 rfl I.a1b0 I.ae10 I.a1c88 I.a1cb8 I.w10 rfl I.we70 I.we74 I.vd I.ld I.vg I.lg I.vf I.lf I.ve I.le
      I.rem h0
  have C1 : CtRegs B n1.mem (reg n1) ⟨st.δ, lowestI st.f, lowestI st.g, 1, 0, 0, 1⟩ := by
    refine ⟨?_, wf1, wg1, ?_, ?_, ?_, ?_⟩
    · show W64 (memLoad32 n1.mem (B + 0x420 + BitVec.ofNat 32 0x40)) (reg n1 (24 : Fin 32)) = _
      rw [w1_40, r1_24]; exact I.dl
    · rw [r1_23, r1_26]; rfl
    · rw [r1_20, r1_25]; rfl
    · show W64 (memLoad32 n1.mem (B + 0x420 + BitVec.ofNat 32 0x54)) (reg n1 (18 : Fin 32)) = _
      rw [w1_54, r1_18]; rfl
    · rw [r1_22, r1_13]; rfl
  obtain ⟨n2, c2, E2, fr2, fk2, s2, sp2, r2_8, r2_3, r2_4, C2⟩ :=
    ct_loop F (min st.rem 62 - 1) E1 s1 sp1 r1_8 (by rw [r1_14]; exact ct_ofNat _ hn1) (by omega) C1
  rw [Nat.sub_add_cancel hn1] at C2
  have K : CtKeep B n1.mem n2.mem := fk2
  obtain ⟨Cd, Cf, Cg, Cu, Cv, Cq, Cr⟩ := C2
  have Cq' : W64 (memLoad32 n2.mem (B + 0x420 + BitVec.ofNat 32 0x54)) (reg n2 (18 : Fin 32)) = _ := Cq
  obtain ⟨n3, c3, s3, E3, fr3, sp3, r3_3, r3_4, r3_10, r3_19, r3_24, a3_1b0, a3_e10, a3_1c88, a3_1cb8, w3_10, w3_40,
      w3_e70, w3_e74, v3_270, l3_270, v3_d50, l3_d50, v3_1714, l3_1714, v3_17a4, l3_17a4⟩ :=
    pv_stHB (zf := zf) (dl := memLoad32 n2.mem (B + 0x420 + BitVec.ofNat 32 0x40)) (dh := reg n2 (24 : Fin 32))
      (ulo := reg n2 (23 : Fin 32)) (uhi := reg n2 (26 : Fin 32)) (vlo := reg n2 (20 : Fin 32))
      (vhi := reg n2 (25 : Fin 32)) (qlo := memLoad32 n2.mem (B + 0x420 + BitVec.ofNat 32 0x54))
      (qhi := reg n2 (18 : Fin 32)) (rlo := reg n2 (22 : Fin 32)) (rhi := reg n2 a3) (rem := st.rem)
      (n := min st.rem 62) (RM := RM) (PX := PX) (PY := PY) (Fv := st.f) (Gv := st.g) (Dv := st.d) (Ev := st.e) F E2 s2 sp2 rfl rfl r2_8 rfl rfl rfl rfl rfl rfl rfl rfl
      (by rw [K.acc (by decide) (by decide) (by decide)]; exact a1_1b0)
      (by rw [K.acc (by decide) (by decide) (by decide)]; exact a1_e10)
      (by rw [K.acc (by decide) (by decide) (by decide)]; exact a1_1c88)
      (by rw [K.acc (by decide) (by decide) (by decide)]; exact a1_1cb8)
      (by rw [K.w32 (by decide) (by decide) (by decide)]; exact w1_10)
      (by rw [K.w32 (by decide) (by decide) (by decide)]; exact w1_14)
      (by rw [K.w32 (by decide) (by decide) (by decide)]; exact w1_18)
      rfl rfl
      (by rw [K.w32 (by decide) (by decide) (by decide)]; exact w1_e70)
      (by rw [K.w32 (by decide) (by decide) (by decide)]; exact w1_e74)
      (by rw [K _ (by decide) (by decide) (by decide), K.acc (by decide) (by decide) (by decide)]; exact v1_270)
      (by rw [K _ (by decide) (by decide) (by decide)]; exact l1_270)
      (by rw [K _ (by decide) (by decide) (by decide), K.acc (by decide) (by decide) (by decide)]; exact v1_d50)
      (by rw [K _ (by decide) (by decide) (by decide)]; exact l1_d50)
      (by rw [K _ (by decide) (by decide) (by decide), K.acc (by decide) (by decide) (by decide)]; exact v1_1714)
      (by rw [K _ (by decide) (by decide) (by decide)]; exact l1_1714)
      (by rw [K _ (by decide) (by decide) (by decide), K.acc (by decide) (by decide) (by decide)]; exact v1_17a4)
      (by rw [K _ (by decide) (by decide) (by decide)]; exact l1_17a4)
      hn1 hn2
  have I3 : HvInv B n3 r3 r4 zf RM PX PY (hvStep st) := by
    refine ⟨sp3, by rw [r3_3, r2_3, r1_3]; exact I.g3, by rw [r3_4, r2_4, r1_4]; exact I.g4,
      by rw [r3_10, ofNat_sub_ofNat (Nat.min_le_left _ _) I.rem]; rfl, r3_19,
      by rw [w3_40, r3_24]; exact Cd, a3_1b0, a3_e10, a3_1c88, a3_1cb8, w3_10, w3_e70, w3_e74, ?_, l3_270, ?_, l3_d50,
      ?_, l3_1714, ?_, l3_17a4, by simp only [hvStep]; have := I.rem; omega⟩
    · rw [v3_270, Cu, Cv]; rfl
    · rw [v3_d50, Cq', Cr]; rfl
    · rw [v3_1714, Cu, Cv]; rfl
    · rw [v3_17a4, Cq', Cr]; rfl
  have hr : (hvStep st).rem = st.rem - min st.rem 62 := rfl
  have ha0 : reg n3 a0 = BitVec.ofNat 32 (hvStep st).rem := I3.a0
  have hlt := I3.rem
  by_cases hz : (hvStep st).rem = 0
  · obtain ⟨n4, d4, u4⟩ := s3.notTaken E3.E.C.self 0xFFC pv_at_ff8 (by decide)
      (by rw [ha0, hz, s3.zero]; rfl)
    refine ⟨n4, c1.trans (c2.trans (c3.trans (.single d4))), by rw [u4.mem]; exact E3,
      fun x hx => by rw [u4.mem, fr3 x hx, fr2 x hx, fr1 x hx], ?_, .inl ⟨hz, ⟨u4.pc, rfl, fun _ => rfl⟩⟩⟩
    exact ⟨by rw [u4.regs]; exact I3.sp, by rw [u4.regs]; exact I3.g3, by rw [u4.regs]; exact I3.g4,
      by rw [u4.regs]; exact I3.a0, by rw [u4.regs]; exact I3.g19, by rw [u4.regs, u4.mem]; exact I3.dl,
      by rw [u4.mem]; exact I3.a1b0, by rw [u4.mem]; exact I3.ae10, by rw [u4.mem]; exact I3.a1c88,
      by rw [u4.mem]; exact I3.a1cb8, by rw [u4.mem]; exact I3.w10, by rw [u4.mem]; exact I3.we70,
      by rw [u4.mem]; exact I3.we74, by rw [u4.mem]; exact I3.vd, by rw [u4.mem]; exact I3.ld,
      by rw [u4.mem]; exact I3.vg, by rw [u4.mem]; exact I3.lg, by rw [u4.mem]; exact I3.vf,
      by rw [u4.mem]; exact I3.lf, by rw [u4.mem]; exact I3.ve, by rw [u4.mem]; exact I3.le, I3.rem⟩
  · obtain ⟨n4, d4, u4⟩ := s3.taken E3.E.C.self 0xCE8 pv_at_ff8 (by decide)
      (by rw [ha0, s3.zero]; exact bne_iff_ne.mpr (umin_ne0' (by omega) hlt))
    refine ⟨n4, c1.trans (c2.trans (c3.trans (.single d4))), by rw [u4.mem]; exact E3,
      fun x hx => by rw [u4.mem, fr3 x hx, fr2 x hx, fr1 x hx], ?_, .inr ⟨hz, ⟨u4.pc, rfl, fun _ => rfl⟩⟩⟩
    exact ⟨by rw [u4.regs]; exact I3.sp, by rw [u4.regs]; exact I3.g3, by rw [u4.regs]; exact I3.g4,
      by rw [u4.regs]; exact I3.a0, by rw [u4.regs]; exact I3.g19, by rw [u4.regs, u4.mem]; exact I3.dl,
      by rw [u4.mem]; exact I3.a1b0, by rw [u4.mem]; exact I3.ae10, by rw [u4.mem]; exact I3.a1c88,
      by rw [u4.mem]; exact I3.a1cb8, by rw [u4.mem]; exact I3.w10, by rw [u4.mem]; exact I3.we70,
      by rw [u4.mem]; exact I3.we74, by rw [u4.mem]; exact I3.vd, by rw [u4.mem]; exact I3.ld,
      by rw [u4.mem]; exact I3.vg, by rw [u4.mem]; exact I3.lg, by rw [u4.mem]; exact I3.vf,
      by rw [u4.mem]; exact I3.lf, by rw [u4.mem]; exact I3.ve, by rw [u4.mem]; exact I3.le, I3.rem⟩

/-- **The loop** of the inversion of `Z`: from 0xCE8 to 0xFFC, as many
batches as `hvLoop` runs. -/
theorem hv_loop {B r3 r4 zf : Word} {RM PX PY : Nat} (F : Fr B 0x21A0) :
    ∀ k {m : Machine} {st : Iv}, PvEnv3 m.mem → St m.mem PV m 0xCE8 (reg m) → HvInv B m r3 r4 zf RM PX PY st →
      st.rem ≠ 0 → (hvLoop k st).rem = 0 →
      ∃ m', Steps m m' ∧ PvEnv3 m'.mem ∧ (∀ x, PvR B x → m'.mem x = m.mem x) ∧
        St m'.mem PV m' 0xFFC (reg m') ∧ HvInv B m' r3 r4 zf RM PX PY (hvLoop k st)
  | 0, _, st, _, _, _, h0, hk => absurd hk (by rw [hvLoop]; exact h0)
  | k + 1, m, st, E, s, I, h0, hk => by
    rw [hvLoop, ite_eq_right h0] at hk ⊢
    obtain ⟨n1, c1, E1, fr1, I1, h1⟩ := hv_iter F E s I h0
    rcases h1 with ⟨hz, s1⟩ | ⟨hz, s1⟩
    · rw [hvLoop_done k _ hz]
      exact ⟨n1, c1, E1, fr1, s1, I1⟩
    · obtain ⟨n2, c2, E2, fr2, s2, I2⟩ := hv_loop F k E1 s1 I1 hz hk
      exact ⟨n2, c1.trans c2, E2, fun x hx => by rw [fr2 x hx, fr1 x hx], s2, I2⟩

end C3.RV32.Pv
