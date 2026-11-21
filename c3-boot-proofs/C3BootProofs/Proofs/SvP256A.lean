import C3BootProofs.Proofs.SvIvLoop
import C3BootProofs.Proofs.SvSeg
import C3BootProofs.Proofs.SvEcA1
import C3BootProofs.Proofs.SvEcA2
import C3BootProofs.Proofs.SvEcA3

/-!
# `sigstore::verify`: the P-256 check up to the inversion of `s`

From 0xFBA to the inversion's head at 0x1328: `sv_eca1`, `sv_eca2`, and `sv_eca3` check `r` and `s`, decode
the key, and set up the inversion, whose state is then `IvInv` for the starting `ivLoop8` state `p256Iv0`.
The frame words the inversion keeps are those at the start.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 100000

/-- The inversion of `s`'s starting state: `f` is the order `n`, `g` is `s`, `d` is 0, `e` is 1, and
591 divsteps are left. -/
def p256Iv0 (M0 : Word → BitVec 8) (es : Bytes) : Iv :=
  ⟨1, (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8 : Int), (beNat (b32 es) : Int), 0, (accV M0 (BitVec.ofNat 32 0x3FCC42E8) 8 : Int), 0x24F⟩

set_option maxHeartbeats 64000000 in
/-- **The P-256 check up to the inversion of `s`**: from 0xFBA to 0x1328, or an error return when `r` or
`s` is out of range or the key isn't a point on the curve. -/
theorem sv_p256_inv {B out bp x21 x26 : Word} {er es : Bytes} {v : Nat → Word} {n0 : Machine}
    (F : Fr B 0x3830) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0xFBA (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_26 : reg n0 (26 : Fin 32) = x26)
    (g0_27 : reg n0 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20)
    (b0_138 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x138) = BitVec.ofNat 8 (er.getD 0 0))
    (q0_139 : ∀ j, j < 31 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x139 + j)) = BitVec.ofNat 8 (er.getD (1 + j) 0))
    (b0_158 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = BitVec.ofNat 8 (es.getD 0 0))
    (q0_159 : ∀ j, j < 31 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x159 + j)) = BitVec.ofNat 8 (es.getD (1 + j) 0))
    (EC0 : SvEcCode M0)
    (IC0 : SvIvCode M0) (UC0 : SvUpCode M0) (D0 : P2Data M0) (BG0 : BGEnv M0) (RS : SvRoSep B) (BY0 : BYEnv M0)
    (k1 : SvIn B x21 1) (k41 : SvIn B x21 0x41) (dg_in : SvIn B (memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x84)) 32) :
    (¬ (((inScalarRange (b32 er) (memBytes M0 (BitVec.ofNat 32 0x3FCC4288) 32) = true) ∧ (inScalarRange (b32 es) (memBytes M0 (BitVec.ofNat 32 0x3FCC4288) 32) = true) ∧ (M0 x21 = 4) ∧ True) ∧ ((GsOk M0 x21) ∧ (beNat (b32 er) < C3.p256.n) ∧ (beNat (b32 es) < C3.p256.n) ∧ (beNat (b32 er) ≠ 0) ∧ (beNat (b32 es) ≠ 0) ∧ True)) ∧ SvErrRet B out v n0) ∨
    (((inScalarRange (b32 er) (memBytes M0 (BitVec.ofNat 32 0x3FCC4288) 32) = true) ∧ (inScalarRange (b32 es) (memBytes M0 (BitVec.ofNat 32 0x3FCC4288) 32) = true) ∧ (M0 x21 = 4) ∧ True) ∧ ((GsOk M0 x21) ∧ (beNat (b32 er) < C3.p256.n) ∧ (beNat (b32 es) < C3.p256.n) ∧ (beNat (b32 er) ≠ 0) ∧ (beNat (b32 es) ≠ 0) ∧ True) ∧
      ∃ m, Steps n0 m ∧ (∀ x, SvR B x → m.mem x = M0 x) ∧ St m.mem SV m 0x1328 (reg m) ∧
        IvInv B m v (reg n0 (3 : Fin 32)) (reg n0 (4 : Fin 32)) out bp (BitVec.ofNat 32 0x1) x26
          (gsVal M0 x21 1 * 2 ^ 256 % p256) (gsVal M0 x21 0x21 * 2 ^ 256 % p256)
          (accV M0 (BitVec.ofNat 32 0x3FCC43A8) 8) (beNat (b32 er)) (beNat (b32 es))
          (beNat (memBytes M0 (memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x84)) 32) % C3.p256.n) (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)
          (fun e => memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 e)) (p256Iv0 M0 es)) := by
  rcases sv_eca1 F E0 V0 hret hO s0 M0 fM g0_2 g0_18 g0_19 g0_20 g0_21 g0_26 g0_27 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl b0_138 q0_139 b0_158 q0_159 EC0 k1 with ⟨hn, e⟩ | ⟨x1_0, x1_1, x1_2, n1, c1, s1, E1, V1, fR1, r1_2, r1_3, r1_4, r1_18, r1_19, r1_20, r1_21, r1_26, r1_27, w1_24, w1_28, w1_2c, w1_30, w1_34, w1_38, w1_3c, w1_40, w1_44, w1_48, w1_4c, w1_50, w1_54, w1_58, w1_5c, w1_60, w1_64, w1_68, w1_6c, w1_70, w1_7c, w1_80, w1_84, w1_88, w1_8c, w1_90, w1_94, w1_98, w1_9c, w1_a0, w1_a4, w1_a8, w1_ac, w1_b0, w1_b4, w1_b8, w1_bc, w1_c0, w1_c4, w1_c8, w1_cc, w1_d0, w1_d4, w1_d8, w1_dc, w1_e0, w1_e4, w1_e8, w1_ec, w1_f0, w1_f4, w1_f8, w1_fc, w1_100, w1_104, w1_108, w1_10c, w1_110, w1_114, w1_118, w1_11c, w1_120, w1_124, w1_128, w1_12c, w1_130, b1_138, b1_158, q1_139, q1_159, K1_L⟩
  · exact .inl ⟨fun h => hn h.1, e⟩
  have h1 : (inScalarRange (b32 er) (memBytes M0 (BitVec.ofNat 32 0x3FCC4288) 32) = true) ∧ (inScalarRange (b32 es) (memBytes M0 (BitVec.ofNat 32 0x3FCC4288) 32) = true) ∧ (M0 x21 = 4) ∧ True := ⟨x1_0, x1_1, x1_2, trivial⟩
  have CH1 : ∀ x, SvR B x → n1.mem x = n0.mem x := fun x hx => (fR1 x hx).trans (fM x hx).symm
  rcases sv_eca2 F E1 V1 hret hO s1 M0 fR1 r1_2 r1_18 r1_19 r1_20 r1_21 r1_26 r1_27 w1_24 w1_28 w1_2c w1_30 w1_34 w1_38 w1_3c w1_40 w1_44 w1_48 w1_4c w1_50 w1_54 w1_58 w1_5c w1_60 w1_64 w1_68 w1_6c w1_70 w1_7c w1_80 w1_84 w1_88 w1_8c w1_90 w1_94 w1_98 w1_9c w1_a0 w1_a4 w1_a8 w1_ac w1_b0 w1_b4 w1_b8 w1_bc w1_c0 w1_c4 w1_c8 w1_cc w1_d0 w1_d4 w1_d8 w1_dc w1_e0 w1_e4 w1_e8 w1_ec w1_f0 w1_f4 w1_f8 w1_fc w1_100 w1_104 w1_108 w1_10c w1_110 w1_114 w1_118 w1_11c w1_120 w1_124 w1_128 w1_12c w1_130 b1_138 q1_139 b1_158 q1_159 EC0 D0 BG0 k41 with ⟨hn, e⟩ | ⟨x2_0, x2_1, x2_2, x2_3, x2_4, n2, c2, s2, E2, V2, fR2, r2_2, r2_3, r2_4, r2_18, r2_19, r2_20, r2_21, r2_22, r2_26, r2_27, w2_24, w2_28, w2_2c, w2_30, w2_34, w2_38, w2_3c, w2_40, w2_44, w2_48, w2_4c, w2_50, w2_54, w2_58, w2_5c, w2_60, w2_64, w2_68, w2_6c, w2_70, w2_7c, w2_80, w2_84, w2_88, w2_8c, w2_90, w2_94, w2_98, w2_9c, w2_a0, w2_a4, w2_a8, w2_ac, w2_b0, w2_b4, w2_b8, w2_bc, w2_c0, w2_c4, w2_c8, w2_cc, w2_d0, w2_d4, w2_d8, w2_dc, w2_e0, w2_e4, w2_e8, w2_ec, w2_f0, w2_f4, w2_f8, w2_fc, w2_100, w2_104, w2_108, w2_10c, w2_110, w2_114, w2_118, w2_11c, w2_120, w2_124, w2_128, w2_12c, w2_130, w2_1b8, w2_a20, b2_138, b2_158, b2_1fc, q2_139, q2_159, a2_178, a2_198, a2_1bc, a2_1dc, a2_a24, a2_1020, a2_1480, K2_L⟩
  · exact .inl ⟨fun h => hn h.2, SvErrRet.pre c1 r1_3 r1_4 CH1 e⟩
  have h2 : (GsOk M0 x21) ∧ (beNat (b32 er) < C3.p256.n) ∧ (beNat (b32 es) < C3.p256.n) ∧ (beNat (b32 er) ≠ 0) ∧ (beNat (b32 es) ≠ 0) ∧ True := ⟨x2_0, x2_1, x2_2, x2_3, x2_4, trivial⟩
  rcases sv_eca3 F E2 V2 hret hO s2 M0 fR2 r2_2 r2_18 r2_19 r2_20 r2_21 r2_26 r2_27 w2_24 w2_28 w2_2c w2_30 w2_34 w2_38 w2_3c w2_40 w2_44 w2_48 w2_4c w2_50 w2_54 w2_58 w2_5c w2_60 w2_64 w2_68 w2_6c w2_70 w2_7c w2_80 w2_84 w2_88 w2_8c w2_90 w2_94 w2_98 w2_9c w2_a0 w2_a4 w2_a8 w2_ac w2_b0 w2_b4 w2_b8 w2_bc w2_c0 w2_c4 w2_c8 w2_cc w2_d0 w2_d4 w2_d8 w2_dc w2_e0 w2_e4 w2_e8 w2_ec w2_f0 w2_f4 w2_f8 w2_fc w2_100 w2_104 w2_108 w2_10c w2_110 w2_114 w2_118 w2_11c w2_120 w2_124 w2_128 w2_12c w2_130 b2_138 q2_139 b2_158 q2_159 EC0 r2_22 a2_178 a2_198 a2_1480 a2_1020 RS BY0 x2_3 x2_4 dg_in with ⟨hn, -⟩ | ⟨n3, c3, s3, E3, V3, fR3, r3_2, r3_3, r3_4, r3_18, r3_19, r3_20, r3_21, r3_23, r3_24, r3_25, r3_26, r3_27, w3_24, w3_28, w3_2c, w3_30, w3_34, w3_38, w3_3c, w3_40, w3_44, w3_48, w3_4c, w3_50, w3_54, w3_58, w3_5c, w3_60, w3_64, w3_68, w3_6c, w3_70, w3_78, w3_7c, w3_80, w3_84, w3_88, w3_8c, w3_90, w3_94, w3_98, w3_9c, w3_a0, w3_a4, w3_a8, w3_ac, w3_b0, w3_b4, w3_b8, w3_bc, w3_c0, w3_c4, w3_c8, w3_cc, w3_d0, w3_d4, w3_d8, w3_dc, w3_e0, w3_e4, w3_e8, w3_ec, w3_f0, w3_f4, w3_f8, w3_fc, w3_100, w3_104, w3_108, w3_10c, w3_110, w3_114, w3_118, w3_11c, w3_120, w3_124, w3_128, w3_12c, w3_130, b3_138, b3_158, b3_440, b3_1040, b3_13a0, b3_14a0, q3_139, q3_159, q3_420, q3_a60, q3_1380, a3_178, a3_198, a3_200, a3_220, a3_240, a3_260, a3_280, a3_2a0, a3_2c0, a3_2e0, a3_420, a3_a20, a3_a40, a3_a60, a3_1020, a3_1380, a3_1480, K3_L⟩
  · exact absurd trivial hn
  refine .inr ⟨h1, h2, n3, c1.trans (c2.trans c3), fR3, s3, E3, IC0.sv F fR3, EC0.sv F fR3, UC0.sv F fR3, V3, r3_2, by rw [r3_3, r2_3, r1_3], by rw [r3_4, r2_4, r1_4], r3_18, r3_19, r3_21, r3_24, r3_26, r3_27, by rw [r3_23, r3_25]; rfl, w3_78, by show 0x24F < 2 ^ 32; decide, w3_60, w3_70, accV_dataR F fR3 (by decide) (by decide), a3_240, a3_260, a3_280, a3_2a0, a3_2c0, a3_2e0, by rw [b3_13a0, a3_1380]; rfl, by rw [b3_13a0]; decide, by rw [b3_14a0, a3_1480]; rfl, by rw [b3_14a0]; decide, by rw [b3_1040, a3_1020]; rfl, by rw [b3_1040]; decide, by rw [b3_440, a3_420]; rfl, by rw [b3_440]; decide, fun e he => ?_⟩
  simp only [ivWords, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact w3_24
  · exact w3_28
  · exact w3_2c
  · exact w3_30
  · exact w3_34
  · exact w3_38
  · exact w3_3c
  · exact w3_40
  · exact w3_44
  · exact w3_48
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
