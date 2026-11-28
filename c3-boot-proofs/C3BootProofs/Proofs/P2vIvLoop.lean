import C3BootProofs.Proofs.P2vIvA
import C3BootProofs.Proofs.P2vIvB
import C3BootProofs.Proofs.P256Batch

/-!
# `p256VerifyPrehash`: the batches of the inversion of `s`

From the inversion's head at 0x3E4 back to it: the block at 0x3E4 and
`p2v_scan` look for a nonzero limb of `g`, `p2v_iva` loads the low words,
`ec_loop` runs the divsteps, and `p2v_ivb` applies their matrix, which is
one `ivStep8`. `p2v_ivloop` runs batches as `ivLoop8` does, out to 0x610
once no steps are left or `g` is zero.
-/

namespace C3.RV32.P2v

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Sv

set_option maxRecDepth 100000

/-- What holds at the inversion's head 0x3E4 for the state `st`. -/
structure IvInv (B : Word) (m : Machine) (v : Nat → Word) (r3 r4 : Word) (qx qy qz rv sv zv N : Nat)
    (st : Iv) : Prop where
  E : P2vCode m.mem
  IC : P2vIvCode m.mem
  EC : P2vEcCode m.mem
  UC : P2vUpCode m.mem
  V : P2vSaves B m.mem v
  sp : reg m sp = B + 0x21A0
  g3 : reg m (3 : Fin 32) = r3
  g4 : reg m (4 : Fin 32) = r4
  g8 : reg m (8 : Fin 32) = BitVec.ofNat 32 0x11FF43B1
  g9 : reg m (9 : Fin 32) = BitVec.ofNat 32 0x332E3755
  g22 : reg m (22 : Fin 32) = BitVec.ofNat 32 0x1
  g23 : reg m (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xCA4
  g26 : reg m (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920
  g27 : reg m (27 : Fin 32) = BitVec.ofNat 32 0x7
  wd : W64 (reg m (19 : Fin 32)) (reg m (21 : Fin 32)) = st.δ
  g24 : reg m (24 : Fin 32) = BitVec.ofNat 32 st.rem
  rem : st.rem < 2 ^ 32
  aN : accV m.mem (BitVec.ofNat 32 (img% b2sOrder256Address)) 8 = N
  a120 : accV m.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) 8 = qx
  a140 : accV m.mem (B + 0x21A0 + BitVec.ofNat 32 0x140) 8 = qy
  a160 : accV m.mem (B + 0x21A0 + BitVec.ofNat 32 0x160) 8 = qz
  a180 : accV m.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv
  a1a0 : accV m.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv
  a1c0 : accV m.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv
  vf : sgnVal (m.mem (B + 0x21A0 + BitVec.ofNat 32 0x920)).toNat (accV m.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8) = st.f
  lf : (m.mem (B + 0x21A0 + BitVec.ofNat 32 0x920)).toNat ≤ 1
  vg : sgnVal (m.mem (B + 0x21A0 + BitVec.ofNat 32 0x220)).toNat (accV m.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8) = st.g
  lg : (m.mem (B + 0x21A0 + BitVec.ofNat 32 0x220)).toNat ≤ 1
  vd : sgnVal (m.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004)).toNat (accV m.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8) = st.d
  ld : (m.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004)).toNat ≤ 1
  ve : sgnVal (m.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0)).toNat (accV m.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8) = st.e
  le : (m.mem (B + 0x21A0 + BitVec.ofNat 32 0x9A0)).toNat ≤ 1

theorem IvInv.of {B r3 r4 : Word} {qx qy qz rv sv zv N : Nat} {v : Nat → Word} {m m' : Machine} {st : Iv}
    (I : IvInv B m v r3 r4 qx qy qz rv sv zv N st) (hm : m'.mem = m.mem)
    (hr : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 19, 21, 22, 23, 24, 26, 27] → reg m' q = reg m q) :
    IvInv B m' v r3 r4 qx qy qz rv sv zv N st := by
  exact ⟨by rw [hm]; exact I.E,
    by rw [hm]; exact I.IC,
    by rw [hm]; exact I.EC,
    by rw [hm]; exact I.UC,
    by rw [hm]; exact I.V,
    by rw [hr 2 (by decide)]; exact I.sp,
    by rw [hr 3 (by decide)]; exact I.g3,
    by rw [hr 4 (by decide)]; exact I.g4,
    by rw [hr 8 (by decide)]; exact I.g8,
    by rw [hr 9 (by decide)]; exact I.g9,
    by rw [hr 22 (by decide)]; exact I.g22,
    by rw [hr 23 (by decide)]; exact I.g23,
    by rw [hr 26 (by decide)]; exact I.g26,
    by rw [hr 27 (by decide)]; exact I.g27,
    by rw [hr 19 (by decide), hr 21 (by decide)]; exact I.wd,
    by rw [hr 24 (by decide)]; exact I.g24,
    I.rem,
    by rw [hm]; exact I.aN,
    by rw [hm]; exact I.a120,
    by rw [hm]; exact I.a140,
    by rw [hm]; exact I.a160,
    by rw [hm]; exact I.a180,
    by rw [hm]; exact I.a1a0,
    by rw [hm]; exact I.a1c0,
    by rw [hm]; exact I.vf,
    by rw [hm]; exact I.lf,
    by rw [hm]; exact I.vg,
    by rw [hm]; exact I.lg,
    by rw [hm]; exact I.vd,
    by rw [hm]; exact I.ld,
    by rw [hm]; exact I.ve,
    by rw [hm]; exact I.le⟩

theorem ofNat_ne0' {k : Nat} (h0 : 0 < k) (h1 : k < 2 ^ 32) : BitVec.ofNat 32 k ≠ 0 := fun h' => by
  have := congrArg BitVec.toNat h'
  rw [BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl] at this; omega

def p2vScA : List BInstr := [.aluImm .add a0 x0 0xFFFFFFFF, .aluImm .add a1 sp 0x200]
theorem p2vScA_end : blockEnd p256VerifyPrehashCode 0x3E4 p2vScA = some 0x3E8 := by decide

set_option maxHeartbeats 4000000 in
/-- **One batch** of the inversion of `s`, from its head at 0x3E4: to 0x610
when `g` is zero, and otherwise after one `ivStep8`, to 0x610 when no steps
are left and back to the head when some are. -/
theorem p2v_iviter {B r3 r4 : Word} {qx qy qz rv sv zv N : Nat} {v : Nat → Word} {m : Machine} {st : Iv}
    (F : Fr B 0x3590) (hret : v 0 &&& ~~~1 = v 0) (hN : 0 < N)
    (s : St m.mem P2V m 0x3E4 (reg m)) (I : IvInv B m v r3 r4 qx qy qz rv sv zv N st) (h0 : st.rem ≠ 0) :
    ∃ m', Steps m m' ∧ (∀ x, P2vR B x → m'.mem x = m.mem x) ∧
      ((st.g = 0 ∧ St m'.mem P2V m' 0x610 (reg m') ∧ IvInv B m' v r3 r4 qx qy qz rv sv zv N st) ∨
       (st.g ≠ 0 ∧ IvInv B m' v r3 r4 qx qy qz rv sv zv N (ivStep8 N st) ∧
         (((ivStep8 N st).rem = 0 ∧ St m'.mem P2V m' 0x610 (reg m')) ∨
          ((ivStep8 N st).rem ≠ 0 ∧ St m'.mem P2V m' 0x3E4 (reg m'))))) := by
  have hz := s.zero
  obtain ⟨m1, c1, u1⟩ := s.block p2vScA I.E.self p2vScA_end ⟨trivial, trivial, trivial⟩
  have s1 : St m.mem P2V m1 0x3E8 (reg m1) := ⟨u1.pc, u1.mem, fun _ => rfl⟩
  have k1 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → reg m1 q = reg m q := fun q h0' h1' => by
    have hq : q ∉ p2vScA.filterMap BInstr.dst := by
      simp only [p2vScA, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; simp [h0', h1']
    rw [u1.regs, runBlock_reg _ _ _ q hz hq]
  have r1a0 : reg m1 a0 = BitVec.ofNat 32 0 + 0xFFFFFFFF := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, p2vScA, upd, ↓reduceIte, aluEval, hz]
  have r1a1 : reg m1 a1 = B + 0x21A0 + BitVec.ofNat 32 0x200 + BitVec.ofNat 32 (4 * 0) := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, p2vScA, upd, ↓reduceIte, aluEval, hz]; rw [I.sp]
    exact (add_ofNat_zero _).symm
  obtain ⟨m2, c2, k2, h2⟩ := p2v_scan F I.E.self 8 0 rfl s1 r1a0 r1a1
    (by rw [k1 27 (by decide) (by decide)]; exact I.g27) (fun k hk => absurd hk (Nat.not_lt_zero _))
  have kk : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 19, 21, 22, 23, 24, 26, 27] → reg m2 q = reg m q := fun q hq => by
    rw [k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide),
      k1 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
  rcases h2 with ⟨hzr, s2⟩ | ⟨hnz, s2⟩
  · have hg : st.g = 0 := by
      rw [← I.vg, sv_zero.2]
      exact (accV_zero_iff 8).2 hzr
    have m2m : m2.mem = m.mem := s2.mem
    exact ⟨m2, c1.trans c2, fun x _ => by rw [m2m], .inl ⟨hg, ⟨s2.pc, rfl, fun _ => rfl⟩, I.of m2m kk⟩⟩
  have hg : st.g ≠ 0 := by
    rw [← I.vg]; intro h
    exact hnz ((accV_zero_iff 8).1 (sv_zero.1 h))
  have m2m : m2.mem = m.mem := s2.mem
  have s2' : St m2.mem P2V m2 0x3F8 (reg m2) := ⟨s2.pc, rfl, fun _ => rfl⟩
  have I2 := I.of m2m kk
  have hrem' : BitVec.ofNat 32 st.rem ≠ 0 := ofNat_ne0' (by omega) I.rem
  have hns := umin_ofNat I.rem
  have hn : min st.rem 62 - 1 + 1 = min st.rem 62 := by omega
  rcases p2v_iva F I2.E I2.V hret s2' m2.mem (fun _ _ => rfl) I2.sp I2.g8 I2.g9 rfl rfl I2.g22 I2.g23 I2.g24
      I2.g26 I2.g27 I2.a120 I2.a140 I2.a160 I2.a180 I2.a1a0 I2.a1c0 rfl rfl rfl rfl rfl rfl rfl rfl I2.IC hrem'
      I2.lf I2.lg with ⟨h, _⟩ | ⟨n3, c3, s3, E3, V3, fR3, r3_2, r3_3, r3_4, r3_5, r3_6, r3_7, r3_8, r3_9, r3_a0,
      r3_a1, r3_a2, r3_a6, r3_a7, r3_18, r3_19, r3_20, r3_21, r3_22, r3_23, r3_24, r3_25, r3_26, r3_27, r3_30,
      w3_50, w3_54, b3_220, b3_920, b3_9a0, b3_1004, a3_120, a3_140, a3_160, a3_180, a3_1a0, a3_1c0, a3_200,
      a3_900, a3_980, a3_fe4, K3⟩
  · exact absurd trivial h
  have hds : EcDsRegs (reg n3) ⟨st.δ, lowestI st.f, lowestI st.g, 1, 0, 0, 1⟩ := by
    refine ⟨by rw [r3_19, r3_21]; exact I2.wd, ?_, ?_, by rw [r3_9, r3_a7]; rfl, by rw [r3_a2, r3_a6]; rfl,
      by rw [r3_25, r3_7]; rfl, by rw [r3_30, r3_6]; rfl⟩
    · rw [r3_20, r3_26, w64_ofNat_split (lowestVal_lt _ _), lowestI_of I2.lf I2.vf]
    · rw [r3_a0, r3_a1, w64_ofNat_split (lowestVal_lt _ _), lowestI_of I2.lg I2.vg]
  obtain ⟨n4, c4, s4, h4, k4⟩ := ec_loop E3.self (min st.rem 62 - 1) s3 hds
    (by rw [hn]; exact r3_5.trans hns) (by have := I.rem; omega)
  rw [hn] at h4
  have m4 : n4.mem = n3.mem := s4.mem
  have s4' : St n4.mem P2V n4 0x51E (reg n4) := ⟨s4.pc, rfl, fun _ => rfl⟩
  have CH4 : ∀ x, P2vR B x → n4.mem x = m.mem x := fun x hx => by rw [m4, fR3 x hx, m2m]
  rw [← m4] at E3 V3 w3_50 w3_54 a3_120 a3_140 a3_160 a3_180 a3_1a0 a3_1c0
  rw [← m4] at a3_200 a3_900 a3_980 a3_fe4 b3_220 b3_920 b3_9a0 b3_1004
  rcases p2v_ivb (ns := min st.rem 62) F E3 V3 hret s4' n4.mem
      (fun _ _ => rfl) ((k4 2 (by decide)).trans r3_2) rfl rfl rfl rfl rfl rfl
      ((k4 18 (by decide)).trans (r3_18.trans hns)) rfl rfl ((k4 22 (by decide)).trans r3_22)
      ((k4 23 (by decide)).trans r3_23) ((k4 24 (by decide)).trans r3_24) rfl ((k4 27 (by decide)).trans r3_27) rfl
      w3_50 w3_54 a3_120 a3_140
      a3_160 a3_180 a3_1a0 a3_1c0
      a3_200 a3_900 a3_980 a3_fe4
      b3_220 b3_920 b3_9a0 b3_1004
      (by omega) (Nat.min_le_right _ _) (I.UC.p2v F CH4) I2.lf I2.lg I2.ld I2.le
      with ⟨h, _⟩ | ⟨σa, Aa, ea, la, σb, Ab, eb, lb, σc, Ac, ec, lc, σd, Ad, ed, ld, n5, c5, s5, E5, V5, fR5,
      r5_2, r5_3, r5_4, r5_8, r5_9, r5_19, r5_21, r5_22, r5_23, r5_24, r5_26, r5_27, w5_50, w5_54, w5_f80, w5_f84,
      w5_f88, w5_f8c, w5_f90, w5_f94, w5_f98, w5_f9c, b5_220, b5_920, b5_9a0, b5_ca0, b5_cc4, b5_1004, a5_120,
      a5_140, a5_160, a5_180, a5_1a0, a5_1c0, a5_200, a5_900, a5_980, a5_c80, a5_ca4, a5_fe4, K5⟩
  · exact absurd (sc4 _ _ _ _) h
  have CH5 : ∀ x, P2vR B x → n5.mem x = m.mem x := fun x hx => by rw [fR5 x hx, CH4 x hx]
  have hNv : accV n4.mem (BitVec.ofNat 32 (img% b2sOrder256Address)) 8 = N := by
    rw [accV_dataR F CH4 (by decide) (by decide), I.aN]
  have hMI : (BitVec.ofNat 32 0x11FF43B1 : Word).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x332E3755 : Word).toNat = ivMI :=
    rfl
  obtain ⟨Zd, -, -, Zu, Zv, Zq, Zr⟩ := h4
  have eu : i64Val ((reg n4 (9 : Fin 32)).toNat + 2 ^ 32 * (reg n4 a7).toNat) =
      i64Val (dsIter (min st.rem 62) ⟨st.δ, lowestI st.f, lowestI st.g, 1, 0, 0, 1⟩).u := by rw [← Zu]
  have ev : i64Val ((reg n4 a2).toNat + 2 ^ 32 * (reg n4 a6).toNat) =
      i64Val (dsIter (min st.rem 62) ⟨st.δ, lowestI st.f, lowestI st.g, 1, 0, 0, 1⟩).v := by rw [← Zv]
  have eq : i64Val ((reg n4 (25 : Fin 32)).toNat + 2 ^ 32 * (reg n4 (7 : Fin 32)).toNat) =
      i64Val (dsIter (min st.rem 62) ⟨st.δ, lowestI st.f, lowestI st.g, 1, 0, 0, 1⟩).q := by rw [← Zq]
  have er : i64Val ((reg n4 (30 : Fin 32)).toNat + 2 ^ 32 * (reg n4 (6 : Fin 32)).toNat) =
      i64Val (dsIter (min st.rem 62) ⟨st.δ, lowestI st.f, lowestI st.g, 1, 0, 0, 1⟩).r := by rw [← Zr]
  rw [I2.vf, I2.vg, eu, ev] at ea
  rw [I2.vf, I2.vg, eq, er] at eb
  rw [I2.vd, I2.ve, eu, ev] at ec
  rw [I2.vd, I2.ve, eq, er] at ed
  obtain ⟨vf', lf'⟩ := fgUpd8_of la ea (tn8 (by omega)) rfl
  obtain ⟨vg', lg'⟩ := fgUpd8_of lb eb (tn8 (by omega)) rfl
  rw [hNv, hMI] at b5_9a0 a5_980 b5_1004 a5_fe4
  obtain ⟨vd', ld'⟩ := deUpd8_of lc hN ec (tn8 (Nat.lt_of_le_of_lt (lrsm8_le lc) (by decide))) rfl
  obtain ⟨ve', le'⟩ := deUpd8_of ld hN ed (tn8 (Nat.lt_of_le_of_lt (lrsm8_le ld) (by decide))) rfl
  have I5 : IvInv B n5 v r3 r4 qx qy qz rv sv zv N (ivStep8 N st) :=
    ⟨E5, I.IC.p2v F CH5, I.EC.p2v F CH5, I.UC.p2v F CH5, V5, r5_2,
      by rw [r5_3, k4 3 (by decide), r3_3]; exact I2.g3, by rw [r5_4, k4 4 (by decide), r3_4]; exact I2.g4,
      r5_8, r5_9, r5_22, r5_23, r5_26, r5_27, by rw [r5_19, r5_21]; exact Zd,
      by rw [r5_24, ofNat_sub_ofNat (Nat.min_le_left _ _) I.rem]; rfl,
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) I.rem,
      by rw [accV_dataR F CH5 (by decide) (by decide)]; exact I.aN,
      a5_120, a5_140, a5_160, a5_180, a5_1a0, a5_1c0,
      by rw [b5_920, a5_900]; exact vf', by rw [b5_920]; exact lf',
      by rw [b5_220, a5_200]; exact vg', by rw [b5_220]; exact lg',
      by rw [b5_1004, a5_fe4]; exact vd', by rw [b5_1004]; exact ld',
      by rw [b5_9a0, a5_980]; exact ve', by rw [b5_9a0]; exact le'⟩
  have cc := c1.trans (c2.trans (c3.trans (c4.trans c5)))
  have hr' : (ivStep8 N st).rem = st.rem - min st.rem 62 := rfl
  by_cases hz' : st.rem - min st.rem 62 = 0
  · obtain ⟨n6, d6, u6⟩ := s5.notTaken E5.self 0x610 p2v_at_60c (by decide)
      (by show (reg n5 24 != reg n5 x0) = false; rw [I5.g24, s5.zero, hr', hz']; rfl)
    exact ⟨n6, cc.trans (.single d6), fun x hx => by rw [u6.mem]; exact CH5 x hx,
      .inr ⟨hg, I5.of u6.mem fun q _ => u6.regs q, .inl ⟨hz', ⟨u6.pc, rfl, fun _ => rfl⟩⟩⟩⟩
  · have hne : BitVec.ofNat 32 (st.rem - min st.rem 62) ≠ 0 :=
      ofNat_ne0' (by omega) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) I.rem)
    obtain ⟨n6, d6, u6⟩ := s5.taken E5.self 0x3E4 p2v_at_60c (by decide)
      (by show (reg n5 24 != reg n5 x0) = true; rw [I5.g24, s5.zero, hr']; simpa using hne)
    exact ⟨n6, cc.trans (.single d6), fun x hx => by rw [u6.mem]; exact CH5 x hx,
      .inr ⟨hg, I5.of u6.mem fun q _ => u6.regs q, .inr ⟨hz', ⟨u6.pc, rfl, fun _ => rfl⟩⟩⟩⟩

/-- **The batches** of the inversion of `s`, from its head at 0x3E4 out to
0x610, as `ivLoop8` runs them. -/
theorem p2v_ivloop {B r3 r4 : Word} {qx qy qz rv sv zv N : Nat} {v : Nat → Word}
    (F : Fr B 0x3590) (hret : v 0 &&& ~~~1 = v 0) (hN : 0 < N) :
    ∀ k {m : Machine} {st : Iv}, St m.mem P2V m 0x3E4 (reg m) → IvInv B m v r3 r4 qx qy qz rv sv zv N st →
      st.rem ≠ 0 → st.rem ≤ 62 * k →
      ∃ m', Steps m m' ∧ (∀ x, P2vR B x → m'.mem x = m.mem x) ∧ St m'.mem P2V m' 0x610 (reg m') ∧
        IvInv B m' v r3 r4 qx qy qz rv sv zv N (ivLoop8 N k st)
  | 0, _, _, _, _, h0, hk => absurd (Nat.le_zero.1 hk) h0
  | k + 1, m, st, s, I, h0, hk => by
    obtain ⟨n1, c1, fr1, h1⟩ := p2v_iviter F hret hN s I h0
    rcases h1 with ⟨hg, s1, I1⟩ | ⟨hg, I1, ⟨hz, s1⟩ | ⟨hz, s1⟩⟩
    · rw [ivLoop8_done N _ _ (.inr hg)]
      exact ⟨n1, c1, fr1, s1, I1⟩
    · rw [ivLoop8, ite_eq_right (fun h => h.elim h0 hg), ivLoop8_done N _ _ (.inl hz)]
      exact ⟨n1, c1, fr1, s1, I1⟩
    · rw [ivLoop8, ite_eq_right (fun h => h.elim h0 hg)]
      have hk' : (ivStep8 N st).rem ≤ 62 * k := by
        show st.rem - min st.rem 62 ≤ 62 * k
        omega
      obtain ⟨n2, c2, fr2, s2, I2⟩ := p2v_ivloop F hret hN k s1 I1 hz hk'
      exact ⟨n2, c1.trans c2, fun x hx => by rw [fr2 x hx, fr1 x hx], s2, I2⟩

end C3.RV32.P2v
