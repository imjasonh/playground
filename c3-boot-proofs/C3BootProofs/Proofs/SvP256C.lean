import C3BootProofs.Proofs.SvP256B
import C3BootProofs.Proofs.SvZS
import C3BootProofs.Proofs.SvZLoop2

/-!
# `sigstore::verify`: the P-256 check from the inverse to the inversion of `Z`

From 0x1556 to the inversion of the sum's `Z` at 0x1B54: `sv_p256_tab`, then the main loop `ml2_main`,
then `sv_zs`, which leaves `ZvInv` for the starting `zvLoop` state `p256Zv0`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 100000

/-- The inversion of `Z`'s starting state: `f` is the prime `p`, `g` is `Z`, `d` is 0, `e` is `R²`, and
591 divsteps are left. -/
def p256Zv0 (M0 : Word → BitVec 8) (Z : Nat) : Iv :=
  ⟨1, (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 : Int), (Z : Int), 0, (accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 : Int), 0x24F⟩

set_option maxHeartbeats 64000000 in
/-- **The P-256 check from the inverse to the inversion of `Z`**: from 0x1556 to 0x1B54, or a panic. -/
theorem sv_p256_z {B r3 r4 out bp x26 : Word} {qx qy qz rv sv zv N : Nat} {W v : Nat → Word} {n0 : Machine}
    {st : Iv} (F : Fr B 0x3830) (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (s : St n0.mem SV n0 0x1556 (reg n0))
    (I : IvInv B n0 v r3 r4 out bp (BitVec.ofNat 32 0x1) x26 qx qy qz rv sv zv N W st)
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (IC0 : SvIvCode M0) (EC0 : SvEcCode M0) (UC0 : SvUpCode M0) (UE0 : CodeIn M0 (BitVec.ofNat 32 uint8EqAddress) uint8EqCode) (N80 : CodeIn M0 (BitVec.ofNat 32 norm8Address) norm8Code) (RS : SvRoSep B) (PM0 : CodeIn M0 (BitVec.ofNat 32 p256ScalarMulAddress) p256ScalarMulCode) (WM0 : CodeIn M0 (BitVec.ofNat 32 wideMulAddress) wideMulCode) (PT0 : SvPtCode M0) (WN0 : SvWnCode M0) (ME : MlEnv M0)
    (hG : Pt2Lt (accV M0 (BitVec.ofNat 32 0x3FCC4690 + BitVec.ofNat 32 0x0) 8, accV M0 (BitVec.ofNat 32 0x3FCC4690 + BitVec.ofNat 32 0x20) 8, accV M0 (BitVec.ofNat 32 0x3FCC4690 + BitVec.ofNat 32 0x40) 8))
    (hQ : Pt2Lt (qx, qy, qz))
    (hid : CodeIn M0 (BitVec.ofNat 32 p256IdentityAddress) p256IdentityData) :
    Panics n0 ∨
    (((((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8) = accV M0 (BitVec.ofNat 32 0x3FCC42E8) 8)) ∧ True) ∧ ∃ stm, mlMain2 (tbl2 (accV M0 (BitVec.ofNat 32 0x3FCC4690 + BitVec.ofNat 32 0x0) 8, accV M0 (BitVec.ofNat 32 0x3FCC4690 + BitVec.ofNat 32 0x20) 8, accV M0 (BitVec.ofNat 32 0x3FCC4690 + BitVec.ofNat 32 0x40) 8)) (tbl2 (qx, qy, qz)) (wnafBytes (wnafGo ((psmVal ((zv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8)) (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)))))) 0x100 0x101 0 0) 0x101) (wnafBytes (wnafGo ((psmVal ((rv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8)) (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)))))) 0x100 0x101 0 0) 0x101) (max (wnafGo ((psmVal ((zv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8)) (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)))))) 0x100 0x101 0 0).length (wnafGo ((psmVal ((rv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8)) (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)))))) 0x100 0x101 0 0).length) = some stm ∧ Pt2Lt stm.1 ∧
      ∃ m', Steps n0 m' ∧ (∀ x, SvR B x → m'.mem x = M0 x) ∧ St m'.mem SV m' 0x1B54 (reg m') ∧
        ZvInv B m' v r3 r4 out bp x26 (((if stm.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF) rv sv zv stm.1.1 stm.1.2.1
          (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8) (accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8) W (p256Zv0 M0 stm.1.2.2)) := by
  rcases sv_p256_tab F hret hO s I M0 fM IC0 EC0 UC0 UE0 N80 RS PM0 WM0 PT0 WN0 ME hG hQ with ⟨-, e⟩ | ⟨x1, n1, c1, fR1, s1, ME1, V1, g1_3, g1_4,
      r1_2, r1_9, r1_a0, r1_18, r1_19, r1_20, r1_21, r1_23, r1_24, r1_25, r1_26, r1_27, w1_24, w1_28, w1_2c, w1_30, w1_34, w1_38, w1_3c, w1_40, w1_44, w1_48, w1_4c, w1_50, w1_54, w1_58, w1_5c, w1_60, w1_64, w1_68, w1_6c, w1_70, w1_78, w1_7c, w1_80, w1_84, w1_88, w1_8c, w1_90, w1_94, w1_98, w1_9c, w1_a0, w1_a4, w1_a8, w1_ac, w1_b0, w1_b4, w1_b8, w1_bc, w1_c0, w1_c4, w1_c8, w1_cc, w1_d0, w1_d4, w1_d8, w1_dc, w1_e0, w1_e4, w1_e8, w1_ec, w1_f0, w1_f4, w1_f8, w1_fc, w1_100, w1_104, w1_108, w1_10c, w1_110, w1_114, w1_118, w1_11c, w1_120, w1_124, w1_128, w1_12c, w1_130, w1_a20, w1_b28, w1_1020, w1_1128, w1_1480, a1_2a0, a1_2c0, a1_2e0, a1_380, a1_400, a1_13e0, a1_1460, a1_1588, l1_n1320, G1⟩
  · exact .inl e
  have hL0 : (wnafGo ((psmVal ((zv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8)) (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)))))) 0x100 0x101 0 0).length ≤ 0x101 :=
    wnafGo_len (by have := accV_lt n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8; rw [a1_380] at this; exact this) _ _ _ (by decide) (by decide)
  have hL1 : (wnafGo ((psmVal ((rv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8)) (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)))))) 0x100 0x101 0 0).length ≤ 0x101 :=
    wnafGo_len (by have := accV_lt n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8; rw [a1_400] at this; exact this) _ _ _ (by decide) (by decide)
  rcases ml2_main F ME1 RS (F.dataIn fR1 hid (by decide) (by decide)) s1 r1_2 r1_9 r1_a0 r1_27 hL0 hL1 G1 with
    ⟨-, hp⟩ | ⟨stm, hst, n2, c2, E2, fr2, K2, s2, X2, r2_22, -, -, A2, l2⟩
  · exact .inl (Panics.of_steps c1 hp)
  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  rcases sv_zs F E2.C (V1.keepL K2 (by decide)) hret hO s2 M0 fR2 X2.sp (X2.s2.trans r1_18) (X2.s3.trans r1_19) X2.s4 X2.s5 r2_22 X2.s8 (X2.s10.trans r1_26) X2.s11 ((K2.w32 (by decide) (by decide)).trans w1_24) ((K2.w32 (by decide) (by decide)).trans w1_28) ((K2.w32 (by decide) (by decide)).trans w1_2c) ((K2.w32 (by decide) (by decide)).trans w1_30) ((K2.w32 (by decide) (by decide)).trans w1_34) ((K2.w32 (by decide) (by decide)).trans w1_38) ((K2.w32 (by decide) (by decide)).trans w1_3c) ((K2.w32 (by decide) (by decide)).trans w1_40) ((K2.w32 (by decide) (by decide)).trans w1_44) ((K2.w32 (by decide) (by decide)).trans w1_48) ((K2.w32 (by decide) (by decide)).trans w1_4c) ((K2.w32 (by decide) (by decide)).trans w1_50) ((K2.w32 (by decide) (by decide)).trans w1_54) ((K2.w32 (by decide) (by decide)).trans w1_58) ((K2.w32 (by decide) (by decide)).trans w1_5c) ((K2.w32 (by decide) (by decide)).trans w1_60) ((K2.w32 (by decide) (by decide)).trans w1_64) ((K2.w32 (by decide) (by decide)).trans w1_68) ((K2.w32 (by decide) (by decide)).trans w1_6c) ((K2.w32 (by decide) (by decide)).trans w1_70) ((K2.w32 (by decide) (by decide)).trans w1_7c) ((K2.w32 (by decide) (by decide)).trans w1_80) ((K2.w32 (by decide) (by decide)).trans w1_84) ((K2.w32 (by decide) (by decide)).trans w1_88) ((K2.w32 (by decide) (by decide)).trans w1_8c) ((K2.w32 (by decide) (by decide)).trans w1_90) ((K2.w32 (by decide) (by decide)).trans w1_94) ((K2.w32 (by decide) (by decide)).trans w1_98) ((K2.w32 (by decide) (by decide)).trans w1_9c) ((K2.w32 (by decide) (by decide)).trans w1_a0) ((K2.w32 (by decide) (by decide)).trans w1_a4) ((K2.w32 (by decide) (by decide)).trans w1_a8) ((K2.w32 (by decide) (by decide)).trans w1_ac) ((K2.w32 (by decide) (by decide)).trans w1_b0) ((K2.w32 (by decide) (by decide)).trans w1_b4) ((K2.w32 (by decide) (by decide)).trans w1_b8) ((K2.w32 (by decide) (by decide)).trans w1_bc) ((K2.w32 (by decide) (by decide)).trans w1_c0) ((K2.w32 (by decide) (by decide)).trans w1_c4) ((K2.w32 (by decide) (by decide)).trans w1_c8) ((K2.w32 (by decide) (by decide)).trans w1_cc) ((K2.w32 (by decide) (by decide)).trans w1_d0) ((K2.w32 (by decide) (by decide)).trans w1_d4) ((K2.w32 (by decide) (by decide)).trans w1_d8) ((K2.w32 (by decide) (by decide)).trans w1_dc) ((K2.w32 (by decide) (by decide)).trans w1_e0) ((K2.w32 (by decide) (by decide)).trans w1_e4) ((K2.w32 (by decide) (by decide)).trans w1_e8) ((K2.w32 (by decide) (by decide)).trans w1_ec) ((K2.w32 (by decide) (by decide)).trans w1_f0) ((K2.w32 (by decide) (by decide)).trans w1_f4) ((K2.w32 (by decide) (by decide)).trans w1_f8) ((K2.w32 (by decide) (by decide)).trans w1_fc) ((K2.w32 (by decide) (by decide)).trans w1_100) ((K2.w32 (by decide) (by decide)).trans w1_104) ((K2.w32 (by decide) (by decide)).trans w1_108) ((K2.w32 (by decide) (by decide)).trans w1_10c) ((K2.w32 (by decide) (by decide)).trans w1_110) ((K2.w32 (by decide) (by decide)).trans w1_114) ((K2.w32 (by decide) (by decide)).trans w1_118) ((K2.w32 (by decide) (by decide)).trans w1_11c) ((K2.w32 (by decide) (by decide)).trans w1_120) ((K2.w32 (by decide) (by decide)).trans w1_124) ((K2.w32 (by decide) (by decide)).trans w1_128) ((K2.w32 (by decide) (by decide)).trans w1_12c) ((K2.w32 (by decide) (by decide)).trans w1_130) ((K2.acc (by decide) (by decide)).trans a1_2a0) ((K2.acc (by decide) (by decide)).trans a1_2c0) ((K2.acc (by decide) (by decide)).trans a1_2e0) (congrArg Prod.fst A2) (congrArg (fun p => p.2.1) A2) (congrArg (fun p => p.2.2) A2) RS EC0 with ⟨hn, -⟩ | ⟨n3, c3, s3, E3, V3, fR3, r3_2, r3_3, r3_4, r3_18, r3_19, r3_20, r3_21, r3_22, r3_23, r3_24, r3_26, r3_27, w3_20, w3_24, w3_28, w3_2c, w3_30, w3_34, w3_38, w3_3c, w3_40, w3_44, w3_48, w3_4c, w3_50, w3_54, w3_58, w3_5c, w3_60, w3_64, w3_68, w3_6c, w3_70, w3_78, w3_7c, w3_80, w3_84, w3_88, w3_8c, w3_90, w3_94, w3_98, w3_9c, w3_a0, w3_a4, w3_a8, w3_ac, w3_b0, w3_b4, w3_b8, w3_bc, w3_c0, w3_c4, w3_c8, w3_cc, w3_d0, w3_d4, w3_d8, w3_dc, w3_e0, w3_e4, w3_e8, w3_ec, w3_f0, w3_f4, w3_f8, w3_fc, w3_100, w3_104, w3_108, w3_10c, w3_110, w3_114, w3_118, w3_11c, w3_120, w3_124, w3_128, w3_12c, w3_130, w3_460, w3_464, b3_340, b3_1040, b3_13a0, b3_14a0, q3_320, q3_420, q3_440, q3_1020, a3_2a0, a3_2c0, a3_2e0, a3_320, a3_420, a3_440, a3_1020, a3_1380, a3_1480, a3_14c0, a3_15a8, a3_15c8, a3_15e8, K3_L⟩
  · exact absurd trivial hn
  refine .inr ⟨x1, stm, hst, l2, n3, c1.trans (c2.trans c3), fR3, s3, E3, IC0.sv F fR3, EC0.sv F fR3, UC0.sv F fR3, V3, r3_2, by rw [r3_3, X2.g3]; exact g1_3, by rw [r3_4, X2.g4]; exact g1_4, r3_18, r3_19, r3_26, r3_27, w3_20, by rw [w3_34, w3_38]; rfl, w3_78, by show 0x24F < 2 ^ 32; decide, w3_460, w3_464, a3_420, accV_dataR F fR3 (by decide) (by decide), a3_440, accV_dataR F fR3 (by decide) (by decide), a3_2a0, a3_2c0, a3_2e0, a3_15a8, a3_15c8, by rw [b3_340, a3_320]; rfl, by rw [b3_340]; decide, by rw [b3_13a0, a3_1380]; rfl, by rw [b3_13a0]; decide, by rw [b3_14a0, a3_1480]; rfl, by rw [b3_14a0]; decide, by rw [b3_1040, a3_1020]; rfl, by rw [b3_1040]; decide, fun e he => ?_⟩
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

end C3.RV32.Sv
