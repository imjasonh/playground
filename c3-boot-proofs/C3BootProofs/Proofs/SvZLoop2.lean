import C3BootProofs.Proofs.SvZLoop

/-!
# `sigstore::verify`: the batches of the inversion of `Z`

From the inversion's head at 0x1B54 back to it: `sv_za` starts a batch, `zt_loop` runs its divsteps, and
`sv_zb` applies its matrix, which is one `zvStep`. `zv_loop` runs batches until no steps are left. It
follows `Pv384HLoop.lean`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 100000

/-- The frame words that the inversion of `Z` leaves alone. -/
def ziWords : List Nat := [0x4C, 0x50, 0x54, 0x58, 0x64, 0x68, 0x6C, 0x7C, 0x80, 0x84, 0x88, 0x8C, 0x90, 0x94, 0x98, 0x9C, 0xA0, 0xA4, 0xA8, 0xAC, 0xB0, 0xB4, 0xB8, 0xBC, 0xC0, 0xC4, 0xC8, 0xCC, 0xD0, 0xD4, 0xD8, 0xDC, 0xE0, 0xE4, 0xE8, 0xEC, 0xF0, 0xF4, 0xF8, 0xFC, 0x100, 0x104, 0x108, 0x10C, 0x110, 0x114, 0x118, 0x11C, 0x120, 0x124, 0x128, 0x12C, 0x130]

theorem w64_ofNat_split {L : Nat} (hL : L < 2 ^ 64) :
    W64 (BitVec.ofNat 32 (L % 2 ^ 32)) (BitVec.ofNat 32 (L / 2 ^ 32)) = L := by
  simp only [W64, BitVec.toNat_ofNat]; omega

theorem lowestVal_lt (σ v : Nat) : lowestVal σ v < 2 ^ 64 := by
  unfold lowestVal; split <;> omega

theorem sc4 (X1 X2 X3 X4 : Int) : ∃ σ1 A1, sgnVal σ1 A1 = X1 ∧ σ1 ≤ 1 ∧ ∃ σ2 A2, sgnVal σ2 A2 = X2 ∧ σ2 ≤ 1 ∧
    ∃ σ3 A3, sgnVal σ3 A3 = X3 ∧ σ3 ≤ 1 ∧ ∃ σ4 A4, sgnVal σ4 A4 = X4 ∧ σ4 ≤ 1 ∧ True := by
  obtain ⟨a1, b1, e1, l1⟩ := sgn_ex X1; obtain ⟨a2, b2, e2, l2⟩ := sgn_ex X2
  obtain ⟨a3, b3, e3, l3⟩ := sgn_ex X3; obtain ⟨a4, b4, e4, l4⟩ := sgn_ex X4
  exact ⟨a1, b1, e1, l1, a2, b2, e2, l2, a3, b3, e3, l3, a4, b4, e4, l4, trivial⟩

/-- What holds at the inversion's head 0x1B54 for the state `st`. -/
structure ZvInv (B : Word) (m : Machine) (v : Nat → Word) (r3 r4 out bp x26 nzw : Word) (rv sv zv X Y P R2 : Nat)
    (W : Nat → Word) (st : Iv) : Prop where
  E : SvCode m.mem
  IC : SvIvCode m.mem
  EC : SvEcCode m.mem
  UC : SvUpCode m.mem
  V : SvSaves B m.mem v
  sp : reg m sp = B + 0x21A0
  g3 : reg m (3 : Fin 32) = r3
  g4 : reg m (4 : Fin 32) = r4
  g18 : reg m (18 : Fin 32) = out
  g19 : reg m (19 : Fin 32) = bp
  g26 : reg m (26 : Fin 32) = x26
  g27 : reg m (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20
  w20 : memLoad32 m.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = nzw
  wd : W64 (memLoad32 m.mem (B + 0x21A0 + BitVec.ofNat 32 0x34)) (memLoad32 m.mem (B + 0x21A0 + BitVec.ofNat 32 0x38)) = st.δ
  wr : memLoad32 m.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 st.rem
  rem : st.rem < 2 ^ 32
  w460 : memLoad32 m.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF
  w464 : memLoad32 m.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF
  a420 : accV m.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = P
  aP : accV m.mem (BitVec.ofNat 32 0x3FCC4B38) 8 = P
  a440 : accV m.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = R2
  aR : accV m.mem (BitVec.ofNat 32 0x3FCC4B78) 8 = R2
  a2a0 : accV m.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv
  a2c0 : accV m.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv
  a2e0 : accV m.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv
  a15a8 : accV m.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X
  a15c8 : accV m.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y
  vf : sgnVal (m.mem (B + 0x21A0 + BitVec.ofNat 32 0x340)).toNat (accV m.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8) = st.f
  lf : (m.mem (B + 0x21A0 + BitVec.ofNat 32 0x340)).toNat ≤ 1
  vg : sgnVal (m.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0)).toNat (accV m.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8) = st.g
  lg : (m.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0)).toNat ≤ 1
  vd : sgnVal (m.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0)).toNat (accV m.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8) = st.d
  ld : (m.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0)).toNat ≤ 1
  ve : sgnVal (m.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040)).toNat (accV m.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8) = st.e
  le : (m.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040)).toNat ≤ 1
  ww : ∀ e, e ∈ ziWords → memLoad32 m.mem (B + 0x21A0 + BitVec.ofNat 32 e) = W e
theorem tn8 {σ : Nat} (h : σ < 256) : (BitVec.ofNat 8 σ).toNat = σ := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem zv_s0 {B : Word} {m : Machine} {st : Iv} {fs gs : BitVec 8} {fv gv : Nat}
    (hfs : fs.toNat ≤ 1) (hgs : gs.toNat ≤ 1) (vf : sgnVal fs.toNat fv = st.f) (vg : sgnVal gs.toNat gv = st.g)
    (w24 : memLoad32 m.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) % 2 ^ 32))
    (w28 : memLoad32 m.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = BitVec.ofNat 32 ((lowestVal (gs).toNat ((gv) % 2 ^ 64)) / 2 ^ 32))
    (w2c : memLoad32 m.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) / 2 ^ 32))
    (w30 : memLoad32 m.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = BitVec.ofNat 32 ((lowestVal (fs).toNat ((fv) % 2 ^ 64)) % 2 ^ 32))
    (wd : W64 (memLoad32 m.mem (B + 0x21A0 + BitVec.ofNat 32 0x34)) (memLoad32 m.mem (B + 0x21A0 + BitVec.ofNat 32 0x38)) = st.δ)
    (r24 : reg m (24 : Fin 32) = BitVec.ofNat 32 0x1)
    (w3c : memLoad32 m.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = BitVec.ofNat 32 0x0)
    (w40 : memLoad32 m.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = BitVec.ofNat 32 0x0)
    (w44 : memLoad32 m.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x0)
    (w5c : memLoad32 m.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 0x1)
    (w60 : memLoad32 m.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = BitVec.ofNat 32 0x0)
    (w70 : memLoad32 m.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = BitVec.ofNat 32 0x0)
    (w74 : memLoad32 m.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 0x0)
    : ZtRegs B m.mem (reg m) ⟨st.δ, lowestI st.f, lowestI st.g, 1, 0, 0, 1⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show W64 (memLoad32 m.mem (B + 0x21A0 + BitVec.ofNat 32 0x34)) (memLoad32 m.mem (B + 0x21A0 + BitVec.ofNat 32 0x38)) = _; exact wd
  · show W64 (memLoad32 m.mem (B + 0x21A0 + BitVec.ofNat 32 0x30)) (memLoad32 m.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C)) = _
    rw [w30, w2c, w64_ofNat_split (lowestVal_lt _ _), lowestI_of hfs vf]
  · show W64 (memLoad32 m.mem (B + 0x21A0 + BitVec.ofNat 32 0x24)) (memLoad32 m.mem (B + 0x21A0 + BitVec.ofNat 32 0x28)) = _
    rw [w24, w28, w64_ofNat_split (lowestVal_lt _ _), lowestI_of hgs vg]
  · show W64 (reg m (24 : Fin 32)) (memLoad32 m.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C)) = _; rw [r24, w3c]; rfl
  · show W64 (memLoad32 m.mem (B + 0x21A0 + BitVec.ofNat 32 0x44)) (memLoad32 m.mem (B + 0x21A0 + BitVec.ofNat 32 0x40)) = _; rw [w44, w40]; rfl
  · show W64 (memLoad32 m.mem (B + 0x21A0 + BitVec.ofNat 32 0x70)) (memLoad32 m.mem (B + 0x21A0 + BitVec.ofNat 32 0x60)) = _; rw [w70, w60]; rfl
  · show W64 (memLoad32 m.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C)) (memLoad32 m.mem (B + 0x21A0 + BitVec.ofNat 32 0x74)) = _; rw [w5c, w74]; rfl

set_option maxHeartbeats 64000000 in
/-- **One batch** of the inversion of `Z`, from its head at 0x1B54 back to it: `zvStep`. -/
theorem zv_iter {B r3 r4 out bp x26 nzw : Word} {rv sv zv X Y P R2 : Nat} {W v : Nat → Word} {m : Machine} {st : Iv}
    (F : Fr B 0x3830) (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (hP : 0 < P)
    (s : St m.mem SV m 0x1B54 (reg m)) (I : ZvInv B m v r3 r4 out bp x26 nzw rv sv zv X Y P R2 W st)
    (h0 : st.rem ≠ 0) :
    ∃ m', Steps m m' ∧ (∀ x, SvR B x → m'.mem x = m.mem x) ∧ St m'.mem SV m' 0x1B54 (reg m') ∧
      ZvInv B m' v r3 r4 out bp x26 nzw rv sv zv X Y P R2 W (zvStep P st) := by
  have hn1 : 1 ≤ min st.rem 62 := by omega
  have hn2 : min st.rem 62 ≤ 62 := Nat.min_le_right _ _
  have hrem' : BitVec.ofNat 32 st.rem ≠ 0 := Pv.ofNat_ne0 (by omega) I.rem
  have hns := umin_ofNat I.rem
  rcases sv_za F I.E I.V hret hO s m.mem (fun _ _ => rfl) I.sp I.g18 I.g19 I.g26 I.g27 I.w20 rfl rfl (I.ww 0x4C (by decide)) (I.ww 0x50 (by decide)) (I.ww 0x54 (by decide)) (I.ww 0x58 (by decide)) (I.ww 0x64 (by decide)) (I.ww 0x68 (by decide)) (I.ww 0x6C (by decide)) I.wr (I.ww 0x7C (by decide)) (I.ww 0x80 (by decide)) (I.ww 0x84 (by decide)) (I.ww 0x88 (by decide)) (I.ww 0x8C (by decide)) (I.ww 0x90 (by decide)) (I.ww 0x94 (by decide)) (I.ww 0x98 (by decide)) (I.ww 0x9C (by decide)) (I.ww 0xA0 (by decide)) (I.ww 0xA4 (by decide)) (I.ww 0xA8 (by decide)) (I.ww 0xAC (by decide)) (I.ww 0xB0 (by decide)) (I.ww 0xB4 (by decide)) (I.ww 0xB8 (by decide)) (I.ww 0xBC (by decide)) (I.ww 0xC0 (by decide)) (I.ww 0xC4 (by decide)) (I.ww 0xC8 (by decide)) (I.ww 0xCC (by decide)) (I.ww 0xD0 (by decide)) (I.ww 0xD4 (by decide)) (I.ww 0xD8 (by decide)) (I.ww 0xDC (by decide)) (I.ww 0xE0 (by decide)) (I.ww 0xE4 (by decide)) (I.ww 0xE8 (by decide)) (I.ww 0xEC (by decide)) (I.ww 0xF0 (by decide)) (I.ww 0xF4 (by decide)) (I.ww 0xF8 (by decide)) (I.ww 0xFC (by decide)) (I.ww 0x100 (by decide)) (I.ww 0x104 (by decide)) (I.ww 0x108 (by decide)) (I.ww 0x10C (by decide)) (I.ww 0x110 (by decide)) (I.ww 0x114 (by decide)) (I.ww 0x118 (by decide)) (I.ww 0x11C (by decide)) (I.ww 0x120 (by decide)) (I.ww 0x124 (by decide)) (I.ww 0x128 (by decide)) (I.ww 0x12C (by decide)) (I.ww 0x130 (by decide)) I.w460 I.w464 I.a2a0 I.a2c0 I.a2e0 rfl (I.a420.trans I.aP.symm) (I.a440.trans I.aR.symm) rfl rfl rfl I.a15a8 I.a15c8 rfl rfl rfl rfl I.IC I.EC hrem' I.lf I.lg with ⟨h, _⟩ | ⟨n1, c1, s1, E1, V1, fR1, r1_2, r1_3, r1_4, r1_8, r1_18, r1_19, r1_24, r1_26, r1_27, w1_1c, w1_20, w1_24, w1_28, w1_2c, w1_30, w1_34, w1_38, w1_3c, w1_40, w1_44, w1_48, w1_4c, w1_50, w1_54, w1_58, w1_5c, w1_60, w1_64, w1_68, w1_6c, w1_70, w1_74, w1_78, w1_7c, w1_80, w1_84, w1_88, w1_8c, w1_90, w1_94, w1_98, w1_9c, w1_a0, w1_a4, w1_a8, w1_ac, w1_b0, w1_b4, w1_b8, w1_bc, w1_c0, w1_c4, w1_c8, w1_cc, w1_d0, w1_d4, w1_d8, w1_dc, w1_e0, w1_e4, w1_e8, w1_ec, w1_f0, w1_f4, w1_f8, w1_fc, w1_100, w1_104, w1_108, w1_10c, w1_110, w1_114, w1_118, w1_11c, w1_120, w1_124, w1_128, w1_12c, w1_130, w1_460, w1_464, b1_340, b1_1040, b1_13a0, b1_14a0, a1_2a0, a1_2c0, a1_2e0, a1_320, a1_420, a1_440, a1_1020, a1_1380, a1_1480, a1_15a8, a1_15c8⟩
  · exact absurd trivial h
  have IC1 : SvIvCode n1.mem := I.IC.sv F fR1
  obtain ⟨n2, c2, E2, IC2, fr2, K2, s2, sp2, r2_3, r2_4, r2_k, r2_27, w2_48, Z2⟩ :=
    zt_loop F (min st.rem 62) E1 IC1 s1 r1_2 (by rw [r1_27]; rfl)
      (by show memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = _; rw [w1_48, hns]) (by omega)
      (zv_s0 I.lf I.lg I.vf I.vg w1_24 w1_28 w1_2c w1_30 (by rw [w1_34, w1_38]; exact I.wd) r1_24 w1_3c w1_40 w1_44 w1_5c
        w1_60 w1_70 w1_74)
  rcases sv_zb F E2 (V1.keepL K2 (by decide)) hret hO s2 n2.mem (fun _ _ => rfl) sp2 (by rw [r2_k _ (by decide), r1_18]) (by rw [r2_k _ (by decide), r1_19]) (by rw [r2_k _ (by decide), r1_26]) (by rw [r2_27]; rfl) ((K2.w32 (by decide) (by decide)).trans w1_20) rfl rfl ((K2.w32 (by decide) (by decide)).trans w1_4c) ((K2.w32 (by decide) (by decide)).trans w1_50) ((K2.w32 (by decide) (by decide)).trans w1_54) ((K2.w32 (by decide) (by decide)).trans w1_58) ((K2.w32 (by decide) (by decide)).trans w1_64) ((K2.w32 (by decide) (by decide)).trans w1_68) ((K2.w32 (by decide) (by decide)).trans w1_6c) ((K2.w32 (by decide) (by decide)).trans w1_78) ((K2.w32 (by decide) (by decide)).trans w1_7c) ((K2.w32 (by decide) (by decide)).trans w1_80) ((K2.w32 (by decide) (by decide)).trans w1_84) ((K2.w32 (by decide) (by decide)).trans w1_88) ((K2.w32 (by decide) (by decide)).trans w1_8c) ((K2.w32 (by decide) (by decide)).trans w1_90) ((K2.w32 (by decide) (by decide)).trans w1_94) ((K2.w32 (by decide) (by decide)).trans w1_98) ((K2.w32 (by decide) (by decide)).trans w1_9c) ((K2.w32 (by decide) (by decide)).trans w1_a0) ((K2.w32 (by decide) (by decide)).trans w1_a4) ((K2.w32 (by decide) (by decide)).trans w1_a8) ((K2.w32 (by decide) (by decide)).trans w1_ac) ((K2.w32 (by decide) (by decide)).trans w1_b0) ((K2.w32 (by decide) (by decide)).trans w1_b4) ((K2.w32 (by decide) (by decide)).trans w1_b8) ((K2.w32 (by decide) (by decide)).trans w1_bc) ((K2.w32 (by decide) (by decide)).trans w1_c0) ((K2.w32 (by decide) (by decide)).trans w1_c4) ((K2.w32 (by decide) (by decide)).trans w1_c8) ((K2.w32 (by decide) (by decide)).trans w1_cc) ((K2.w32 (by decide) (by decide)).trans w1_d0) ((K2.w32 (by decide) (by decide)).trans w1_d4) ((K2.w32 (by decide) (by decide)).trans w1_d8) ((K2.w32 (by decide) (by decide)).trans w1_dc) ((K2.w32 (by decide) (by decide)).trans w1_e0) ((K2.w32 (by decide) (by decide)).trans w1_e4) ((K2.w32 (by decide) (by decide)).trans w1_e8) ((K2.w32 (by decide) (by decide)).trans w1_ec) ((K2.w32 (by decide) (by decide)).trans w1_f0) ((K2.w32 (by decide) (by decide)).trans w1_f4) ((K2.w32 (by decide) (by decide)).trans w1_f8) ((K2.w32 (by decide) (by decide)).trans w1_fc) ((K2.w32 (by decide) (by decide)).trans w1_100) ((K2.w32 (by decide) (by decide)).trans w1_104) ((K2.w32 (by decide) (by decide)).trans w1_108) ((K2.w32 (by decide) (by decide)).trans w1_10c) ((K2.w32 (by decide) (by decide)).trans w1_110) ((K2.w32 (by decide) (by decide)).trans w1_114) ((K2.w32 (by decide) (by decide)).trans w1_118) ((K2.w32 (by decide) (by decide)).trans w1_11c) ((K2.w32 (by decide) (by decide)).trans w1_120) ((K2.w32 (by decide) (by decide)).trans w1_124) ((K2.w32 (by decide) (by decide)).trans w1_128) ((K2.w32 (by decide) (by decide)).trans w1_12c) ((K2.w32 (by decide) (by decide)).trans w1_130) ((K2.w32 (by decide) (by decide)).trans w1_460) ((K2.w32 (by decide) (by decide)).trans w1_464) ((K2.acc (by decide) (by decide)).trans a1_2a0) ((K2.acc (by decide) (by decide)).trans a1_2c0) ((K2.acc (by decide) (by decide)).trans a1_2e0) ((K2.acc (by decide) (by decide)).trans a1_320) (by rw [K2.acc (by decide) (by decide), a1_420, accV_dataR F (fun x hx => (fr2 x hx).trans (fR1 x hx)) (by decide) (by decide)]) (by rw [K2.acc (by decide) (by decide), a1_440, accV_dataR F (fun x hx => (fr2 x hx).trans (fR1 x hx)) (by decide) (by decide)]) ((K2.acc (by decide) (by decide)).trans a1_1020) ((K2.acc (by decide) (by decide)).trans a1_1380) ((K2.acc (by decide) (by decide)).trans a1_1480) ((K2.acc (by decide) (by decide)).trans a1_15a8) ((K2.acc (by decide) (by decide)).trans a1_15c8) ((K2.b8 (by decide) (by decide)).trans b1_340) ((K2.b8 (by decide) (by decide)).trans b1_1040) ((K2.b8 (by decide) (by decide)).trans b1_13a0) ((K2.b8 (by decide) (by decide)).trans b1_14a0) IC2 (I.EC.sv F (fun x hx => (fr2 x hx).trans (fR1 x hx))) rfl rfl rfl rfl rfl rfl rfl rfl ((K2.w32 (by decide) (by decide)).trans (w1_1c.trans hns)) hn1 hn2 (I.UC.sv F (fun x hx => (fr2 x hx).trans (fR1 x hx))) I.lf I.lg I.ld I.le with ⟨h, _⟩ | ⟨σa, Aa, ea, la, σb, Ab, eb, lb, σc, Ac, ec, lc,
      σd, Ad, ed, ld, n3, c3, s3, E3, V3, fR3, r3_2, r3_3, r3_4, r3_18, r3_19, r3_26, r3_27, w3_1c, w3_20, w3_34, w3_38, w3_3c, w3_40, w3_44, w3_4c, w3_50, w3_54, w3_58, w3_5c, w3_60, w3_64, w3_68, w3_6c, w3_70, w3_74, w3_78, w3_7c, w3_80, w3_84, w3_88, w3_8c, w3_90, w3_94, w3_98, w3_9c, w3_a0, w3_a4, w3_a8, w3_ac, w3_b0, w3_b4, w3_b8, w3_bc, w3_c0, w3_c4, w3_c8, w3_cc, w3_d0, w3_d4, w3_d8, w3_dc, w3_e0, w3_e4, w3_e8, w3_ec, w3_f0, w3_f4, w3_f8, w3_fc, w3_100, w3_104, w3_108, w3_10c, w3_110, w3_114, w3_118, w3_11c, w3_120, w3_124, w3_128, w3_12c, w3_130, w3_460, w3_464, w3_1320, w3_1324, w3_1328, w3_132c, w3_1330, w3_1334, w3_1338, w3_133c, b3_340, b3_a40, b3_a64, b3_1040, b3_13a0, b3_14a0, a3_2a0, a3_2c0, a3_2e0, a3_320, a3_420, a3_440, a3_a20, a3_a44, a3_1020, a3_1380, a3_1480, a3_15a8, a3_15c8⟩
  · exact absurd (sc4 _ _ _ _) h
  obtain ⟨Zd, -, -, Zu, Zv, Zq, Zr⟩ := Z2
  have CH3 : ∀ x, SvR B x → n3.mem x = m.mem x := fun x hx => by rw [fR3 x hx, fr2 x hx, fR1 x hx]
  have CH2 : ∀ x, SvR B x → n2.mem x = m.mem x := (fun x hx => (fr2 x hx).trans (fR1 x hx))
  have hM : accV n2.mem (BitVec.ofNat 32 0x3FCC4B38) 8 = P := by rw [accV_dataR F CH2 (by decide) (by decide), I.aP]
  have eu : i64Val ((reg n2 (24 : Fin 32)).toNat + 2 ^ 32 *
      (memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C)).toNat) = i64Val (dsIter (min st.rem 62) ⟨st.δ, lowestI st.f, lowestI st.g, 1, 0, 0, 1⟩).u := by
    rw [← Zu]; rfl
  have ev : i64Val ((memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x44)).toNat + 2 ^ 32 *
      (memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x40)).toNat) = i64Val (dsIter (min st.rem 62) ⟨st.δ, lowestI st.f, lowestI st.g, 1, 0, 0, 1⟩).v := by
    rw [← Zv]; rfl
  have eq : i64Val ((memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x70)).toNat + 2 ^ 32 *
      (memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x60)).toNat) = i64Val (dsIter (min st.rem 62) ⟨st.δ, lowestI st.f, lowestI st.g, 1, 0, 0, 1⟩).q := by
    rw [← Zq]; rfl
  have er : i64Val ((memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C)).toNat + 2 ^ 32 *
      (memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x74)).toNat) = i64Val (dsIter (min st.rem 62) ⟨st.δ, lowestI st.f, lowestI st.g, 1, 0, 0, 1⟩).r := by
    rw [← Zr]; rfl
  rw [I.vf, I.vg, eu, ev] at ea
  rw [I.vf, I.vg, eq, er] at eb
  rw [I.vd, I.ve, eu, ev] at ec
  rw [I.vd, I.ve, eq, er] at ed
  obtain ⟨vf', lf'⟩ := fgUpd8_of la ea (tn8 (by omega)) rfl
  obtain ⟨vg', lg'⟩ := fgUpd8_of lb eb (tn8 (by omega)) rfl
  rw [hM] at b3_14a0 a3_1480 b3_1040 a3_1020
  obtain ⟨vd', ld'⟩ := deUpd8_of lc hP ec (tn8 (Nat.lt_of_le_of_lt (lrsm8_le lc) (by decide))) rfl
  obtain ⟨ve', le'⟩ := deUpd8_of ld hP ed (tn8 (Nat.lt_of_le_of_lt (lrsm8_le ld) (by decide))) rfl
  refine ⟨n3, c1.trans (c2.trans c3), CH3, s3, E3, I.IC.sv F CH3, I.EC.sv F CH3, I.UC.sv F CH3, V3, r3_2,
    by rw [r3_3, r2_3, r1_3]; exact I.g3, by rw [r3_4, r2_4, r1_4]; exact I.g4, r3_18, r3_19, r3_26, r3_27, w3_20,
    by rw [w3_34, w3_38]; exact Zd, by rw [w3_78, ofNat_sub_ofNat (Nat.min_le_left _ _) I.rem]; rfl,
    by simp only [zvStep]; have := I.rem; omega, w3_460, w3_464,
    by rw [a3_420, hM], by rw [accV_dataR F CH3 (by decide) (by decide)]; exact I.aP,
    by rw [a3_440, accV_dataR F CH2 (by decide) (by decide)]; exact I.aR,
    by rw [accV_dataR F CH3 (by decide) (by decide)]; exact I.aR, a3_2a0, a3_2c0, a3_2e0, a3_15a8, a3_15c8,
    by rw [b3_340, a3_320]; exact vf', by rw [b3_340]; exact lf',
    by rw [b3_13a0, a3_1380]; exact vg', by rw [b3_13a0]; exact lg',
    by rw [b3_14a0, a3_1480]; exact vd', by rw [b3_14a0]; exact ld',
    by rw [b3_1040, a3_1020]; exact ve', by rw [b3_1040]; exact le', fun e he => ?_⟩
  simp only [ziWords, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact w3_4c
  · exact w3_50
  · exact w3_54
  · exact w3_58
  · exact w3_64
  · exact w3_68
  · exact w3_6c
  · exact w3_7c
  · exact w3_80
  · exact w3_84
  · exact w3_88
  · exact w3_8c
  · exact w3_90
  · exact w3_94
  · exact w3_98
  · exact w3_9c
  · exact w3_a0
  · exact w3_a4
  · exact w3_a8
  · exact w3_ac
  · exact w3_b0
  · exact w3_b4
  · exact w3_b8
  · exact w3_bc
  · exact w3_c0
  · exact w3_c4
  · exact w3_c8
  · exact w3_cc
  · exact w3_d0
  · exact w3_d4
  · exact w3_d8
  · exact w3_dc
  · exact w3_e0
  · exact w3_e4
  · exact w3_e8
  · exact w3_ec
  · exact w3_f0
  · exact w3_f4
  · exact w3_f8
  · exact w3_fc
  · exact w3_100
  · exact w3_104
  · exact w3_108
  · exact w3_10c
  · exact w3_110
  · exact w3_114
  · exact w3_118
  · exact w3_11c
  · exact w3_120
  · exact w3_124
  · exact w3_128
  · exact w3_12c
  · exact w3_130

/-- **The batches** of the inversion of `Z`, from its head at 0x1B54 back to it, as many as `zvLoop` runs. -/
theorem zv_loop {B r3 r4 out bp x26 nzw : Word} {rv sv zv X Y P R2 : Nat} {W v : Nat → Word} (F : Fr B 0x3830)
    (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (hP : 0 < P) :
    ∀ k {m : Machine} {st : Iv}, St m.mem SV m 0x1B54 (reg m) →
      ZvInv B m v r3 r4 out bp x26 nzw rv sv zv X Y P R2 W st →
      ∃ m', Steps m m' ∧ (∀ x, SvR B x → m'.mem x = m.mem x) ∧ St m'.mem SV m' 0x1B54 (reg m') ∧
        ZvInv B m' v r3 r4 out bp x26 nzw rv sv zv X Y P R2 W (zvLoop P k st)
  | 0, m, st, s, I => ⟨m, .refl m, fun _ _ => rfl, s, I⟩
  | k + 1, m, st, s, I => by
    by_cases h0 : st.rem = 0
    · rw [zvLoop, ite_eq_left h0]; exact ⟨m, .refl m, fun _ _ => rfl, s, I⟩
    rw [zvLoop, ite_eq_right h0]
    obtain ⟨n1, c1, fr1, s1, I1⟩ := zv_iter F hret hO hP s I h0
    obtain ⟨n2, c2, fr2, s2, I2⟩ := zv_loop F hret hO hP k s1 I1
    exact ⟨n2, c1.trans c2, fun x hx => by rw [fr2 x hx, fr1 x hx], s2, I2⟩

end C3.RV32.Sv
