import C3BootProofs.Proofs.P2vIvLoop
import C3BootProofs.Proofs.P2vEcMl
import C3BootProofs.Proofs.P2vIvE
import C3BootProofs.Proofs.P2vEcD
import C3BootProofs.Proofs.P2vEcT0a
import C3BootProofs.Proofs.P2vEcT0c
import C3BootProofs.Proofs.P2vEcT0b
import C3BootProofs.Proofs.P2vEcT1a
import C3BootProofs.Proofs.P2vEcT1c
import C3BootProofs.Proofs.P2vEcT1b
import C3BootProofs.Proofs.P2vEcW2
import C3BootProofs.Proofs.P2vEcW3

/-!
# `p256VerifyPrehash`: the check from the inverse to the main loop

From 0x610, where the inversion of `s` ends, to the main loop at 0x998: `p2v_ive` normalizes the
inverse, `p2v_ecd` computes `u₁` and `u₂`, the `p2v_ect*` stages build the tables of odd multiples, and
`p2v_ecw2` and `p2v_ecw3` write the wNAF digits, which leaves what `ml2_main` takes.
-/

namespace C3.RV32.P2v

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2 C3.RV32.Sv

set_option maxRecDepth 100000

theorem p2v_ptF_of {M : Word → BitVec 8} {B : Word} {c x y z : Nat}
    (hx : accV M (B + 0x21A0 + BitVec.ofNat 32 c) 8 = x) (hy : accV M (B + 0x21A0 + BitVec.ofNat 32 (c + 0x20)) 8 = y)
    (hz : accV M (B + 0x21A0 + BitVec.ofNat 32 (c + 0x40)) 8 = z) : ptF M B c = (x, y, z) := by
  unfold ptF; rw [hx, hy, hz]

set_option maxHeartbeats 64000000 in
/-- **The check from the inverse to the main loop**: from 0x610 to 0x998, or a panic when the
inversion's `f` isn't 1. -/
theorem p2v_p256_tab {B r3 r4 : Word} {qx qy qz rv sv zv N : Nat} {v : Nat → Word} {n0 : Machine}
    {st : Iv} (F : Fr B 0x3590) (hret : v 0 &&& ~~~1 = v 0) (s : St n0.mem P2V n0 0x610 (reg n0))
    (I : IvInv B n0 v r3 r4 qx qy qz rv sv zv N st)
    (M0 : Word → BitVec 8) (fM : ∀ x, P2vR B x → n0.mem x = M0 x)
    (EC0 : P2vEcCode M0) (UC0 : P2vUpCode M0) (UE0 : CodeIn M0 (BitVec.ofNat 32 uint8EqAddress) uint8EqCode) (N80 : CodeIn M0 (BitVec.ofNat 32 norm8Address) norm8Code) (RS : P2vRoSep B) (PM0 : CodeIn M0 (BitVec.ofNat 32 p256ScalarMulAddress) p256ScalarMulCode) (WM0 : CodeIn M0 (BitVec.ofNat 32 wideMulAddress) wideMulCode) (PT0 : P2vPtCode M0) (WN0 : P2vWnCode M0) (ME : MlEnv M0)
    (hG : Pt2Lt (accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8, accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8, accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8))
    (hQ : Pt2Lt (qx, qy, qz)) :
    (¬ ((((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8) = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8)) ∧ True) ∧ Panics n0) ∨
    (((((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8) = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8)) ∧ True) ∧ ∃ m', Steps n0 m' ∧ (∀ x, P2vR B x → m'.mem x = M0 x) ∧ St m'.mem P2V m' 0x998 (reg m') ∧
      MlEnv m'.mem ∧ P2vSaves B m'.mem v ∧ reg m' (3 : Fin 32) = r3 ∧ reg m' (4 : Fin 32) = r4 ∧
      reg m' sp = B + 0x21A0 ∧
      reg m' (8 : Fin 32) = BitVec.ofNat 32 0x2 ∧
      reg m' (9 : Fin 32) = BitVec.ofNat 32 (wnafGo ((psmVal ((zv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x920))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8)) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)))))) 0x100 0x101 0 0).length ∧
      reg m' a0 = BitVec.ofNat 32 (wnafGo ((psmVal ((rv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x920))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8)) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)))))) 0x100 0x101 0 0).length ∧
      reg m' (18 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xC84 ∧
      reg m' (19 : Fin 32) = BitVec.ofNat 32 0x2 ∧
      reg m' (20 : Fin 32) = BitVec.ofNat 32 0x108 ∧
      reg m' (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x10E4 ∧
      reg m' (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x920 ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) = BitVec.ofNat 32 (wnafGo ((psmVal ((rv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x920))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8)) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)))))) 0x100 0x101 0 0).length ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC80) = BitVec.ofNat 32 (wnafGo ((psmVal ((rv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x920))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8)) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)))))) 0x100 0x101 0 0).length ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x10E4) = BitVec.ofNat 32 (wnafGo ((psmVal ((zv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x920))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8)) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)))))) 0x100 0x101 0 0).length ∧
      memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x11EC) = BitVec.ofNat 32 (wnafGo ((psmVal ((rv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x920))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8)) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)))))) 0x100 0x101 0 0).length ∧
      accV m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) 8 = rv ∧
      accV m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1A0) 8 = sv ∧
      accV m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C0) 8 = zv ∧
      accV m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = (psmVal ((zv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x920))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8)) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8))))) ∧
      accV m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = (psmVal ((rv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x920))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8)) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8))))) ∧
      accV m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = (psmVal ((rv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x920))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8)) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8))))) ∧
      accV m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) 8 = (psmVal ((zv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x920))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8)) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8))))) ∧
      accV m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C4) 8 = (psmVal ((rv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x920))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8)) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8))))) ∧
      GM2 B m'.mem (tbl2 (accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8, accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8, accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8)) (tbl2 (qx, qy, qz))
        (wnafBytes (wnafGo ((psmVal ((zv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x920))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8)) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)))))) 0x100 0x101 0 0) 0x101)
        (wnafBytes (wnafGo ((psmVal ((rv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x920))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8)) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)))))) 0x100 0x101 0 0) 0x101)) := by
  rcases p2v_ive F I.E I.V hret s M0 fM I.sp I.g8 I.g9 rfl rfl I.g22 I.g23 rfl I.g26 I.g27 I.a120 I.a140 I.a160 I.a180 I.a1a0 I.a1c0 rfl rfl rfl rfl rfl rfl rfl rfl UC0 EC0 UE0 N80 I.lf I.ld with ⟨hn, e⟩ | ⟨x1_0, n1, c1, s1, E1, V1, fR1, r1_2, r1_3, r1_4, r1_8, r1_9, r1_18, r1_19, r1_21, r1_22, r1_23, r1_24, r1_26, r1_27, b1_220, b1_920, b1_9a0, b1_c80, b1_1004, a1_120, a1_140, a1_160, a1_180, a1_1a0, a1_1c0, a1_200, a1_900, a1_980, a1_fe4, K1_L⟩
  · exact .inl ⟨hn, e⟩
  rcases p2v_ecd (ev := 0) F E1 V1 hret s1 M0 fR1 r1_2 r1_18 r1_19 r1_21 r1_22 r1_23 r1_24 r1_26 r1_27 a1_120 a1_140 a1_160 a1_180 a1_1a0 a1_1c0 a1_200 a1_900 a1_fe4 b1_220 b1_920 b1_9a0 b1_1004 a1_980 RS PM0 WM0 with ⟨hn, -⟩ | ⟨n2, c2, s2, E2, V2, fR2, r2_2, r2_3, r2_4, r2_a0, r2_18, r2_19, r2_20, r2_21, r2_22, r2_23, r2_24, r2_26, r2_27, b2_920, q2_200, q2_980, q2_fe4, a2_120, a2_140, a2_160, a2_180, a2_1a0, a2_1c0, a2_1e0, a2_200, a2_220, a2_240, a2_260, a2_280, a2_2a0, a2_2c0, a2_2e0, a2_900, a2_980, a2_9a0, a2_9c0, a2_9e0, a2_c80, a2_ca0, a2_cc0, a2_ce0, a2_fe4, a2_1004, a2_1024, a2_1044, a2_1064, a2_1084, a2_10a4, a2_10c4, K2_L⟩
  · exact absurd trivial hn
  rcases p2v_ect0a (dlo := 0) (dhi := 0) (gs := 0) (ds := 0) (es := 0) (gv := 0) (dv := 0) (ev := 0) F E2 V2 hret s2 M0 fR2 r2_2 r2_a0 r2_18 r2_19 r2_20 r2_21 r2_22 r2_23 r2_24 r2_26 r2_27 b2_920 a2_120 a2_140 a2_160 a2_180 a2_1a0 a2_1c0 a2_1e0 a2_260 a2_2e0 a2_900 a2_980 a2_9a0 a2_9c0 a2_9e0 a2_c80 a2_ca0 a2_cc0 a2_ce0 a2_1044 a2_10c4 (p2v_ptF_of a2_200 a2_220 a2_240) (p2v_ptF_of a2_280 a2_2a0 a2_2c0) (p2v_ptF_of a2_fe4 a2_1004 a2_1024) (p2v_ptF_of a2_1064 a2_1084 a2_10a4) RS hG hQ RS PT0 with ⟨hn, -⟩ | ⟨n3, c3, s3, E3, V3, fR3, r3_2, r3_3, r3_4, r3_8, r3_9, r3_18, r3_19, r3_20, r3_21, r3_22, r3_23, r3_24, r3_26, r3_27, q3_980, q3_9e0, q3_a40, q3_aa0, q3_b00, q3_b60, q3_bc0, q3_c20, q3_c80, q3_ce0, q3_d40, q3_da0, q3_e00, q3_e60, q3_ec0, q3_f20, a3_120, a3_140, a3_160, a3_180, a3_1a0, a3_1c0, a3_1e0, a3_260, a3_2e0, a3_960, a3_1044, a3_10c4, p3_200, p3_280, p3_900, p3_fe4, p3_1064, K3_L⟩
  · exact absurd trivial hn
  rcases p2v_ect0c (dlo := 0) (dhi := 0) (fs := 0) (gs := 0) (ds := 0) (es := 0) (fv := 0) (gv := 0) (dv := 0) (ev := 0) F E3 V3 hret s3 M0 fR3 r3_2 r3_8 r3_9 r3_18 r3_19 r3_20 r3_21 r3_22 r3_23 r3_24 r3_26 r3_27 q3_980 q3_9e0 q3_a40 q3_aa0 q3_b00 q3_b60 q3_bc0 q3_c20 q3_c80 q3_ce0 q3_d40 q3_da0 q3_e00 q3_e60 q3_ec0 q3_f20 a3_120 a3_140 a3_160 a3_180 a3_1a0 a3_1c0 a3_1e0 a3_260 a3_2e0 a3_960 a3_1044 a3_10c4 p3_200 p3_280 p3_900 p3_fe4 p3_1064 RS hG hQ RS PT0 with ⟨hn, -⟩ | ⟨n4, c4, s4, E4, V4, fR4, r4_2, r4_3, r4_4, r4_8, r4_9, r4_18, r4_19, r4_20, r4_21, r4_22, r4_23, r4_24, r4_26, r4_27, q4_b00, q4_b60, q4_bc0, q4_c20, q4_ce0, q4_d40, q4_da0, q4_e00, q4_e60, q4_ec0, q4_f20, a4_120, a4_140, a4_160, a4_180, a4_1a0, a4_1c0, a4_1e0, a4_260, a4_2e0, a4_960, a4_1044, a4_10c4, p4_200, p4_280, p4_900, p4_980, p4_9e0, p4_a40, p4_aa0, p4_c80, p4_f80, p4_fe4, p4_1064, K4_L⟩
  · exact absurd trivial hn
  rcases p2v_ect0b (dlo := 0) (dhi := 0) (fs := 0) (gs := 0) (ds := 0) (es := 0) (fv := 0) (gv := 0) (dv := 0) (ev := 0) F E4 V4 hret s4 M0 fR4 r4_2 r4_8 r4_9 r4_18 r4_19 r4_20 r4_21 r4_22 r4_23 r4_24 r4_26 r4_27 q4_b00 q4_b60 q4_bc0 q4_c20 q4_ce0 q4_d40 q4_da0 q4_e00 q4_e60 q4_ec0 q4_f20 a4_120 a4_140 a4_160 a4_180 a4_1a0 a4_1c0 a4_1e0 a4_260 a4_2e0 a4_960 a4_1044 a4_10c4 p4_200 p4_280 p4_900 p4_980 p4_9e0 p4_a40 p4_aa0 p4_c80 p4_f80 p4_fe4 p4_1064 RS hG hQ RS PT0 with ⟨hn, -⟩ | ⟨n5, c5, s5, E5, V5, fR5, r5_2, r5_3, r5_4, r5_8, r5_9, r5_a0, r5_18, r5_19, r5_20, r5_21, r5_22, r5_23, r5_24, r5_26, r5_27, a5_120, a5_140, a5_160, a5_180, a5_1a0, a5_1c0, a5_1e0, a5_260, a5_2e0, a5_960, a5_1044, a5_10c4, p5_200, p5_280, p5_300, p5_360, p5_3c0, p5_420, p5_480, p5_4e0, p5_540, p5_5a0, p5_900, p5_980, p5_9e0, p5_a40, p5_aa0, p5_b00, p5_b60, p5_bc0, p5_c20, p5_c80, p5_ce0, p5_d40, p5_da0, p5_e00, p5_e60, p5_ec0, p5_f20, p5_f80, p5_fe4, p5_1064, K5_L⟩
  · exact absurd trivial hn
  rcases p2v_ect1a (dlo := 0) (dhi := 0) (fs := 0) (gs := 0) (ds := 0) (es := 0) (fv := 0) (gv := 0) (dv := 0) (ev := 0) F E5 V5 hret s5 M0 fR5 r5_2 r5_8 r5_9 r5_a0 r5_18 r5_19 r5_20 r5_21 r5_22 r5_23 r5_24 r5_26 r5_27 a5_120 a5_140 a5_160 a5_180 a5_1a0 a5_1c0 a5_1e0 a5_260 a5_2e0 a5_960 a5_1044 a5_10c4 p5_200 p5_280 p5_300 p5_360 p5_3c0 p5_420 p5_480 p5_4e0 p5_540 p5_5a0 p5_900 p5_980 p5_9e0 p5_a40 p5_aa0 p5_b00 p5_b60 p5_bc0 p5_c20 p5_c80 p5_ce0 p5_d40 p5_da0 p5_e00 p5_e60 p5_ec0 p5_f20 p5_f80 p5_fe4 p5_1064 RS hG hQ RS PT0 with ⟨hn, -⟩ | ⟨n6, c6, s6, E6, V6, fR6, r6_2, r6_3, r6_4, r6_8, r6_9, r6_18, r6_19, r6_20, r6_21, r6_22, r6_23, r6_24, r6_26, r6_27, q6_980, q6_9e0, q6_a40, q6_aa0, q6_b00, q6_b60, q6_bc0, q6_c20, q6_c80, q6_ce0, q6_d40, q6_da0, q6_e00, q6_e60, q6_ec0, q6_f20, a6_120, a6_140, a6_160, a6_180, a6_1a0, a6_1c0, a6_1e0, a6_260, a6_2e0, a6_960, a6_1044, a6_10c4, p6_200, p6_280, p6_300, p6_360, p6_3c0, p6_420, p6_480, p6_4e0, p6_540, p6_5a0, p6_900, p6_f80, p6_fe4, p6_1064, K6_L⟩
  · exact absurd trivial hn
  rcases p2v_ect1c (dlo := 0) (dhi := 0) (fs := 0) (gs := 0) (ds := 0) (es := 0) (fv := 0) (gv := 0) (dv := 0) (ev := 0) F E6 V6 hret s6 M0 fR6 r6_2 r6_8 r6_9 r6_18 r6_19 r6_20 r6_21 r6_22 r6_23 r6_24 r6_26 r6_27 q6_980 q6_9e0 q6_a40 q6_aa0 q6_b00 q6_b60 q6_bc0 q6_c20 q6_c80 q6_ce0 q6_d40 q6_da0 q6_e00 q6_e60 q6_ec0 q6_f20 a6_120 a6_140 a6_160 a6_180 a6_1a0 a6_1c0 a6_1e0 a6_260 a6_2e0 a6_960 a6_1044 a6_10c4 p6_200 p6_280 p6_300 p6_360 p6_3c0 p6_420 p6_480 p6_4e0 p6_540 p6_5a0 p6_900 p6_f80 p6_fe4 p6_1064 RS hG hQ RS PT0 with ⟨hn, -⟩ | ⟨n7, c7, s7, E7, V7, fR7, r7_2, r7_3, r7_4, r7_8, r7_9, r7_18, r7_19, r7_20, r7_21, r7_22, r7_23, r7_24, r7_26, r7_27, q7_b00, q7_b60, q7_bc0, q7_c20, q7_ce0, q7_d40, q7_da0, q7_e00, q7_e60, q7_ec0, q7_f20, a7_120, a7_140, a7_160, a7_180, a7_1a0, a7_1c0, a7_1e0, a7_260, a7_2e0, a7_960, a7_1044, a7_10c4, p7_200, p7_280, p7_300, p7_360, p7_3c0, p7_420, p7_480, p7_4e0, p7_540, p7_5a0, p7_900, p7_980, p7_9e0, p7_a40, p7_aa0, p7_c80, p7_f80, p7_fe4, p7_1064, K7_L⟩
  · exact absurd trivial hn
  rcases p2v_ect1b (dlo := 0) (dhi := 0) (fs := 0) (gs := 0) (ds := 0) (es := 0) (fv := 0) (gv := 0) (dv := 0) (ev := 0) F E7 V7 hret s7 M0 fR7 r7_2 r7_8 r7_9 r7_18 r7_19 r7_20 r7_21 r7_22 r7_23 r7_24 r7_26 r7_27 q7_b00 q7_b60 q7_bc0 q7_c20 q7_ce0 q7_d40 q7_da0 q7_e00 q7_e60 q7_ec0 q7_f20 a7_120 a7_140 a7_160 a7_180 a7_1a0 a7_1c0 a7_1e0 a7_260 a7_2e0 a7_960 a7_1044 a7_10c4 p7_200 p7_280 p7_300 p7_360 p7_3c0 p7_420 p7_480 p7_4e0 p7_540 p7_5a0 p7_900 p7_980 p7_9e0 p7_a40 p7_aa0 p7_c80 p7_f80 p7_fe4 p7_1064 RS hG hQ RS PT0 with ⟨hn, -⟩ | ⟨n8, c8, s8, E8, V8, fR8, r8_2, r8_3, r8_4, r8_8, r8_9, r8_a0, r8_18, r8_19, r8_20, r8_21, r8_22, r8_23, r8_24, r8_26, r8_27, a8_120, a8_140, a8_160, a8_180, a8_1a0, a8_1c0, a8_1e0, a8_260, a8_2e0, a8_960, a8_1044, a8_10c4, p8_200, p8_280, p8_300, p8_360, p8_3c0, p8_420, p8_480, p8_4e0, p8_540, p8_5a0, p8_600, p8_660, p8_6c0, p8_720, p8_780, p8_7e0, p8_840, p8_8a0, p8_900, p8_980, p8_9e0, p8_a40, p8_aa0, p8_b00, p8_b60, p8_bc0, p8_c20, p8_c80, p8_ce0, p8_d40, p8_da0, p8_e00, p8_e60, p8_ec0, p8_f20, p8_f80, p8_fe4, p8_1064, K8_L⟩
  · exact absurd trivial hn
  rcases p2v_ecw2 F E8 V8 hret s8 M0 fR8 r8_2 r8_a0 r8_26 a8_180 a8_1a0 a8_1c0 a8_260 a8_2e0 p8_300 p8_360 p8_3c0 p8_420 p8_480 p8_4e0 p8_540 p8_5a0 p8_600 p8_660 p8_6c0 p8_720 p8_780 p8_7e0 p8_840 p8_8a0 WN0 with ⟨hn, -⟩ | ⟨n9, c9, s9, E9, V9, fR9, r9_2, r9_3, r9_4, r9_8, r9_9, r9_18, r9_19, r9_20, r9_21, r9_26, w9_980, w9_c80, w9_10e4, a9_180, a9_1a0, a9_1c0, a9_260, a9_2e0, a9_f80, a9_1044, a9_10c4, p9_300, p9_360, p9_3c0, p9_420, p9_480, p9_4e0, p9_540, p9_5a0, p9_600, p9_660, p9_6c0, p9_720, p9_780, p9_7e0, p9_840, p9_8a0, l9_n900, mb9_984, mb9_c84, mb9_10e8, K9_L⟩
  · exact absurd trivial hn
  rcases p2v_ecw3 F E9 V9 hret s9 M0 fR9 r9_2 r9_8 r9_9 r9_18 r9_19 r9_20 r9_21 r9_26 w9_980 w9_c80 w9_10e4 a9_180 a9_1a0 a9_1c0 a9_260 a9_2e0 a9_f80 a9_1044 a9_10c4 p9_300 p9_360 p9_3c0 p9_420 p9_480 p9_4e0 p9_540 p9_5a0 p9_600 p9_660 p9_6c0 p9_720 p9_780 p9_7e0 p9_840 p9_8a0 l9_n900 mb9_984 mb9_c84 mb9_10e8 WN0 with ⟨hn, -⟩ | ⟨n10, c10, s10, E10, V10, fR10, r10_2, r10_3, r10_4, r10_8, r10_9, r10_a0, r10_18, r10_19, r10_20, r10_21, r10_26, w10_980, w10_c80, w10_10e4, w10_11ec, a10_180, a10_1a0, a10_1c0, a10_260, a10_2e0, a10_f80, a10_1044, a10_10c4, p10_300, p10_360, p10_3c0, p10_420, p10_480, p10_4e0, p10_540, p10_5a0, p10_600, p10_660, p10_6c0, p10_720, p10_780, p10_7e0, p10_840, p10_8a0, l10_n900, mb10_984, mb10_c84, mb10_10e8, mb10_11f0, K10_L⟩
  · exact absurd trivial hn
  refine .inr ⟨⟨x1_0, trivial⟩, n10, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans (c10))))))))), fR10, s10, ME.fr F fR10, V10,
    by rw [r10_3, r9_3, r8_3, r7_3, r6_3, r5_3, r4_3, r3_3, r2_3, r1_3]; exact I.g3, by rw [r10_4, r9_4, r8_4, r7_4, r6_4, r5_4, r4_4, r3_4, r2_4, r1_4]; exact I.g4,
    r10_2, r10_8, r10_9, r10_a0, r10_18, r10_19, r10_20, r10_21, r10_26, w10_980, w10_c80, w10_10e4, w10_11ec, a10_180, a10_1a0, a10_1c0, a10_260, a10_2e0, a10_f80, a10_1044, a10_10c4,
    ⟨fun j hj => ?_, fun j hj => ?_, fun j _ => ⟨tbl2_lt hG j, tbl2_lt hQ j⟩, mb10_10e8, mb10_11f0⟩⟩
  · rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j
    · exact p10_300
    · exact p10_360
    · exact p10_3c0
    · exact p10_420
    · exact p10_480
    · exact p10_4e0
    · exact p10_540
    · exact p10_5a0
    · omega
  · rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j
    · exact p10_600
    · exact p10_660
    · exact p10_6c0
    · exact p10_720
    · exact p10_780
    · exact p10_7e0
    · exact p10_840
    · exact p10_8a0
    · omega

end C3.RV32.P2v
