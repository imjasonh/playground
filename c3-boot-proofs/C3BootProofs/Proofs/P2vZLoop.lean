import C3BootProofs.Proofs.P2vZA
import C3BootProofs.Proofs.P2vZB
import C3BootProofs.Proofs.P2vZDs4
import C3BootProofs.Proofs.P256Batch

/-!
# `p256VerifyPrehash`: the batches of the inversion of `Z`

From the inversion's head at 0xBEE back to it: `p2v_za` starts a batch,
`ct2_loop` runs its divsteps, and `p2v_zb` applies their matrix, which is one
`zvStep`. `p2v_zvloop` runs batches as `zvLoop` does, out to 0xF00 once no
steps are left.
-/

namespace C3.RV32.P2v

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Sv

set_option maxRecDepth 100000

/-- What holds at the inversion's head 0xBEE for the state `st`. -/
structure ZvInv (B : Word) (m : Machine) (v : Nat → Word) (r3 r4 nzw : Word) (rv X Y P : Nat) (st : Iv) : Prop where
  E : P2vCode m.mem
  IC : P2vIvCode m.mem
  UC : P2vUpCode m.mem
  V : P2vSaves B m.mem v
  sp : reg m sp = B + 0x21A0
  g3 : reg m (3 : Fin 32) = r3
  g4 : reg m (4 : Fin 32) = r4
  g10 : reg m a0 = BitVec.ofNat 32 st.rem
  g14 : reg m a4 = B + 0x21A0 + BitVec.ofNat 32 0x920
  wd : W64 (memLoad32 m.mem (B + 0x21A0 + BitVec.ofNat 32 0x40)) (reg m (24 : Fin 32)) = st.δ
  rem : st.rem < 2 ^ 32
  w10 : memLoad32 m.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = nzw
  aP : accV m.mem (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 = P
  a980 : accV m.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = P
  a180 : accV m.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv
  a1338 : accV m.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) 8 = X
  a1358 : accV m.mem (B + 0x21A0 + BitVec.ofNat 32 0x1358) 8 = Y
  vf : sgnVal (m.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0)).toNat (accV m.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8) = st.f
  lf : (m.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0)).toNat ≤ 1
  vg : sgnVal (m.mem (B + 0x21A0 + BitVec.ofNat 32 0x920)).toNat (accV m.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8) = st.g
  lg : (m.mem (B + 0x21A0 + BitVec.ofNat 32 0x920)).toNat ≤ 1
  vd : sgnVal (m.mem (B + 0x21A0 + BitVec.ofNat 32 0x220)).toNat (accV m.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) 8) = st.d
  ld : (m.mem (B + 0x21A0 + BitVec.ofNat 32 0x220)).toNat ≤ 1
  ve : sgnVal (m.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004)).toNat (accV m.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8) = st.e
  le : (m.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004)).toNat ≤ 1

theorem ZvInv.of {B r3 r4 nzw : Word} {rv X Y P : Nat} {v : Nat → Word} {m m' : Machine} {st : Iv}
    (I : ZvInv B m v r3 r4 nzw rv X Y P st) (hm : m'.mem = m.mem)
    (hr : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 10, 14, 24] → reg m' q = reg m q) :
    ZvInv B m' v r3 r4 nzw rv X Y P st := by
  exact ⟨by rw [hm]; exact I.E, by rw [hm]; exact I.IC, by rw [hm]; exact I.UC, by rw [hm]; exact I.V,
    by rw [hr 2 (by decide)]; exact I.sp, by rw [hr 3 (by decide)]; exact I.g3, by rw [hr 4 (by decide)]; exact I.g4,
    by rw [hr 10 (by decide)]; exact I.g10, by rw [hr 14 (by decide)]; exact I.g14,
    by rw [hm, hr 24 (by decide)]; exact I.wd, I.rem, by rw [hm]; exact I.w10, by rw [hm]; exact I.aP,
    by rw [hm]; exact I.a980, by rw [hm]; exact I.a180, by rw [hm]; exact I.a1338, by rw [hm]; exact I.a1358,
    by rw [hm]; exact I.vf, by rw [hm]; exact I.lf, by rw [hm]; exact I.vg, by rw [hm]; exact I.lg,
    by rw [hm]; exact I.vd, by rw [hm]; exact I.ld, by rw [hm]; exact I.ve, by rw [hm]; exact I.le⟩

/-- The frame bytes that `ct2_loop` keeps, as a `P2vKeepL`. -/
theorem ct2_keepL {B : Word} {M M' : Word → BitVec 8}
    (K : ∀ e, e + 1 ≤ 0x13F0 → (e < 0x1C ∨ 0x58 ≤ e) → e ≠ 0xC80 →
      M' (B + 0x21A0 + BitVec.ofNat 32 e) = M (B + 0x21A0 + BitVec.ofNat 32 e)) :
    P2vKeepL B M M' [(0x1C, 0x3C), (0xC80, 1)] := fun e he hL => by
  have h1 := hL (0x1C, 0x3C) (List.mem_cons_self ..)
  have h2 := hL (0xC80, 1) (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  refine K e he ?_ ?_
  · rcases h1 with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rcases h2 with h | h
    · exact Nat.ne_of_lt h
    · exact Nat.ne_of_gt h

theorem ofNat_ne0'' {k : Nat} (h0 : 0 < k) (h1 : k < 2 ^ 32) : BitVec.ofNat 32 k ≠ 0 := fun h' => by
  have := congrArg BitVec.toNat h'
  rw [BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl] at this; omega

set_option maxHeartbeats 8000000 in
/-- **One batch** of the inversion of `Z`, from its head at 0xBEE: one
`zvStep`, then to 0xF00 when no steps are left and back to the head when some
are. -/
theorem p2v_zviter {B r3 r4 nzw : Word} {rv X Y P : Nat} {v : Nat → Word} {m : Machine} {st : Iv}
    (F : Fr B 0x3590) (hret : v 0 &&& ~~~1 = v 0) (hP : 0 < P)
    (s : St m.mem P2V m 0xBEE (reg m)) (I : ZvInv B m v r3 r4 nzw rv X Y P st) (h0 : st.rem ≠ 0) :
    ∃ m', Steps m m' ∧ (∀ x, P2vR B x → m'.mem x = m.mem x) ∧ ZvInv B m' v r3 r4 nzw rv X Y P (zvStep P st) ∧
      (((zvStep P st).rem = 0 ∧ St m'.mem P2V m' 0xF00 (reg m')) ∨
       ((zvStep P st).rem ≠ 0 ∧ St m'.mem P2V m' 0xBEE (reg m'))) := by
  have hrem' : BitVec.ofNat 32 st.rem ≠ 0 := ofNat_ne0'' (by omega) I.rem
  have hns := umin_ofNat I.rem
  have hn : min st.rem 62 - 1 + 1 = min st.rem 62 := by omega
  rcases p2v_za F I.E I.V hret s m.mem (fun _ _ => rfl) I.sp I.g10 I.g14 rfl I.w10 rfl I.a180 rfl rfl
      (I.a980.trans I.aP.symm) rfl rfl I.a1338 I.a1358 rfl rfl rfl rfl I.IC hrem' I.lf I.lg with
    ⟨h, _⟩ | ⟨n2, c2, s2, E2, V2, fR2, r2_2, r2_3, r2_4, r2_8, r2_9, r2_13, r2_14, r2_18, r2_20, r2_22, r2_23,
      r2_24, r2_25, r2_26, w2_10, w2_14, w2_18, w2_40, w2_44, w2_48, w2_4c, w2_50, w2_54, b2_220, b2_920, b2_fa0,
      b2_1004, a2_180, a2_200, a2_900, a2_980, a2_f80, a2_fe4, a2_1338, a2_1358, K2⟩
  · exact absurd trivial h
  have hds : CtRegs2 B n2.mem (reg n2) ⟨st.δ, lowestI st.f, lowestI st.g, 1, 0, 0, 1⟩ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show W64 (memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x40)) (reg n2 (24 : Fin 32)) = _
      rw [w2_40, r2_24]; exact I.wd
    · show W64 (memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x50))
        (memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x48)) = _
      rw [w2_50, w2_48, w64_ofNat_split (lowestVal_lt _ _), lowestI_of I.lf I.vf]
    · show W64 (memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x44))
        (memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C)) = _
      rw [w2_44, w2_4c, w64_ofNat_split (lowestVal_lt _ _), lowestI_of I.lg I.vg]
    · rw [r2_23, r2_26]; rfl
    · rw [r2_20, r2_25]; rfl
    · show W64 (memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x54)) (reg n2 (18 : Fin 32)) = _
      rw [w2_54, r2_18]; rfl
    · rw [r2_22, r2_13]; rfl
  have CH2 : ∀ x, P2vR B x → n2.mem x = m.mem x := fR2
  obtain ⟨n3, c3, E3, -, fr3, K3', s3, sp3, r3_8, r3_3, r3_4, Z3⟩ :=
    ct2_loop F (min st.rem 62 - 1) E2 (I.IC.p2v F CH2) s2 r2_2 r2_8
      (by rw [hn, r2_14, hns]) (by have := I.rem; omega) hds
  rw [hn] at Z3
  have K3 := ct2_keepL K3'
  have CH3 : ∀ x, P2vR B x → n3.mem x = m.mem x := fun x hx => (fr3 x hx).trans (CH2 x hx)
  rcases p2v_zb (ns := min st.rem 62) F E3 (V2.keepL K3 (by decide)) hret s3 m.mem CH3 sp3 r3_8 rfl rfl rfl rfl
      rfl rfl rfl rfl ((K3.w32 (by decide) (by decide)).trans w2_10)
      ((K3.w32 (by decide) (by decide)).trans (w2_14.trans hns)) ((K3.w32 (by decide) (by decide)).trans w2_18) rfl rfl
      ((K3.acc (by decide) (by decide)).trans a2_180) ((K3.acc (by decide) (by decide)).trans a2_200)
      ((K3.acc (by decide) (by decide)).trans a2_900) ((K3.acc (by decide) (by decide)).trans a2_980)
      ((K3.acc (by decide) (by decide)).trans a2_f80) ((K3.acc (by decide) (by decide)).trans a2_fe4)
      ((K3.acc (by decide) (by decide)).trans a2_1338) ((K3.acc (by decide) (by decide)).trans a2_1358)
      ((K3.b8 (by decide) (by decide)).trans b2_220) ((K3.b8 (by decide) (by decide)).trans b2_920)
      ((K3.b8 (by decide) (by decide)).trans b2_fa0) ((K3.b8 (by decide) (by decide)).trans b2_1004)
      I.UC (by omega) (Nat.min_le_right _ _) I.lf I.lg I.ld I.le with
    ⟨h, _⟩ | ⟨σa, Aa, ea, la, σb, Ab, eb, lb, σc, Ac, ec, lc, σd, Ad, ed, ld, n4, c4, s4, E4, V4, fR4, r4_2, r4_3,
      r4_4, r4_10, r4_14, r4_24, w4_10, w4_40, b4_220, b4_920, -, -, b4_fa0, b4_1004, a4_180, a4_200, a4_900,
      a4_980, -, -, a4_f80, a4_fe4, a4_1338, a4_1358, -⟩
  · exact absurd (sc4 _ _ _ _) h
  have CH4 : ∀ x, P2vR B x → n4.mem x = m.mem x := fR4
  obtain ⟨Zd, -, -, Zu, Zv, Zq, Zr⟩ := Z3
  have eu : i64Val ((reg n3 (23 : Fin 32)).toNat + 2 ^ 32 * (reg n3 (26 : Fin 32)).toNat) =
      i64Val (dsIter (min st.rem 62) ⟨st.δ, lowestI st.f, lowestI st.g, 1, 0, 0, 1⟩).u := by rw [← Zu]
  have ev : i64Val ((reg n3 (20 : Fin 32)).toNat + 2 ^ 32 * (reg n3 (25 : Fin 32)).toNat) =
      i64Val (dsIter (min st.rem 62) ⟨st.δ, lowestI st.f, lowestI st.g, 1, 0, 0, 1⟩).v := by rw [← Zv]
  have eq : i64Val ((memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x54)).toNat + 2 ^ 32 *
      (reg n3 (18 : Fin 32)).toNat) = i64Val (dsIter (min st.rem 62) ⟨st.δ, lowestI st.f, lowestI st.g, 1, 0, 0, 1⟩).q := by
    rw [← Zq]; rfl
  have er : i64Val ((reg n3 (22 : Fin 32)).toNat + 2 ^ 32 * (reg n3 a3).toNat) =
      i64Val (dsIter (min st.rem 62) ⟨st.δ, lowestI st.f, lowestI st.g, 1, 0, 0, 1⟩).r := by rw [← Zr]
  rw [I.vf, I.vg, eu, ev] at ea
  rw [I.vf, I.vg, eq, er] at eb
  rw [I.vd, I.ve, eu, ev] at ec
  rw [I.vd, I.ve, eq, er] at ed
  obtain ⟨vf', lf'⟩ := fgUpd8_of la ea (tn8 (by omega)) rfl
  obtain ⟨vg', lg'⟩ := fgUpd8_of lb eb (tn8 (by omega)) rfl
  rw [I.aP] at b4_220 a4_200 b4_1004 a4_fe4
  obtain ⟨vd', ld'⟩ := deUpd8_of lc hP ec (tn8 (Nat.lt_of_le_of_lt (lrsm8_le lc) (by decide))) rfl
  obtain ⟨ve', le'⟩ := deUpd8_of ld hP ed (tn8 (Nat.lt_of_le_of_lt (lrsm8_le ld) (by decide))) rfl
  have I4 : ZvInv B n4 v r3 r4 nzw rv X Y P (zvStep P st) :=
    ⟨E4, I.IC.p2v F CH4, I.UC.p2v F CH4, V4, r4_2,
      by rw [r4_3, r3_3, r2_3]; exact I.g3, by rw [r4_4, r3_4, r2_4]; exact I.g4,
      by rw [r4_10, ofNat_sub_ofNat (Nat.min_le_left _ _) I.rem]; rfl, r4_14,
      by rw [w4_40, r4_24]; exact Zd, Nat.lt_of_le_of_lt (Nat.sub_le _ _) I.rem, w4_10,
      by rw [accV_dataR F CH4 (by decide) (by decide)]; exact I.aP, a4_980.trans I.aP, a4_180, a4_1338, a4_1358,
      by rw [b4_fa0, a4_f80]; exact vf', by rw [b4_fa0]; exact lf',
      by rw [b4_920, a4_900]; exact vg', by rw [b4_920]; exact lg',
      by rw [b4_220, a4_200]; exact vd', by rw [b4_220]; exact ld',
      by rw [b4_1004, a4_fe4]; exact ve', by rw [b4_1004]; exact le'⟩
  have cc := c2.trans (c3.trans c4)
  have hr' : (zvStep P st).rem = st.rem - min st.rem 62 := rfl
  by_cases hz' : st.rem - min st.rem 62 = 0
  · obtain ⟨n6, d6, u6⟩ := s4.notTaken E4.self 0xF00 p2v_at_efc (by decide)
      (by show (reg n4 a0 != reg n4 x0) = false; rw [I4.g10, s4.zero, hr', hz']; rfl)
    exact ⟨n6, cc.trans (.single d6), fun x hx => by rw [u6.mem]; exact CH4 x hx,
      I4.of u6.mem fun q _ => u6.regs q, .inl ⟨hz', ⟨u6.pc, rfl, fun _ => rfl⟩⟩⟩
  · have hne : BitVec.ofNat 32 (st.rem - min st.rem 62) ≠ 0 :=
      ofNat_ne0'' (by omega) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) I.rem)
    obtain ⟨n6, d6, u6⟩ := s4.taken E4.self 0xBEE p2v_at_efc (by decide)
      (by show (reg n4 a0 != reg n4 x0) = true; rw [I4.g10, s4.zero, hr']; simpa using hne)
    exact ⟨n6, cc.trans (.single d6), fun x hx => by rw [u6.mem]; exact CH4 x hx,
      I4.of u6.mem fun q _ => u6.regs q, .inr ⟨hz', ⟨u6.pc, rfl, fun _ => rfl⟩⟩⟩

/-- **The batches** of the inversion of `Z`, from its head at 0xBEE out to
0xF00, as `zvLoop` runs them. -/
theorem p2v_zvloop {B r3 r4 nzw : Word} {rv X Y P : Nat} {v : Nat → Word}
    (F : Fr B 0x3590) (hret : v 0 &&& ~~~1 = v 0) (hP : 0 < P) :
    ∀ k {m : Machine} {st : Iv}, St m.mem P2V m 0xBEE (reg m) → ZvInv B m v r3 r4 nzw rv X Y P st →
      st.rem ≠ 0 → st.rem ≤ 62 * k →
      ∃ m', Steps m m' ∧ (∀ x, P2vR B x → m'.mem x = m.mem x) ∧ St m'.mem P2V m' 0xF00 (reg m') ∧
        ZvInv B m' v r3 r4 nzw rv X Y P (zvLoop P k st)
  | 0, _, _, _, _, h0, hk => absurd (Nat.le_zero.1 hk) h0
  | k + 1, m, st, s, I, h0, hk => by
    obtain ⟨n1, c1, fr1, I1, h1⟩ := p2v_zviter F hret hP s I h0
    rw [zvLoop, ite_eq_right h0]
    rcases h1 with ⟨hz, s1⟩ | ⟨hz, s1⟩
    · rw [zvLoop_done P _ _ hz]
      exact ⟨n1, c1, fr1, s1, I1⟩
    · have hk' : (zvStep P st).rem ≤ 62 * k := by
        show st.rem - min st.rem 62 ≤ 62 * k
        omega
      obtain ⟨n2, c2, fr2, s2, I2⟩ := p2v_zvloop F hret hP k s1 I1 hz hk'
      exact ⟨n2, c1.trans c2, fun x hx => by rw [fr2 x hx, fr1 x hx], s2, I2⟩

end C3.RV32.P2v
