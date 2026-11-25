import C3BootProofs.Proofs.SvSegCk
import C3BootProofs.Proofs.SvCk1
import C3BootProofs.Proofs.SvCk2

/-!
# `sigstore::verify`: The checkpoint's origin and size

Composed from generated stages by `scripts/gen-sv-segs.py`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 100000

set_option maxHeartbeats 64000000 in
/-- **The checkpoint's origin and size**: from 0x142E to the size loop at 0x14FE, `sv_ck1` and `sv_ck2`. -/
theorem sv_seg_ck {B out bp x20 x21 x22 x23 x24 x25 x26 x27 pv ckp ckl : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out)
    (s0 : St n0.mem SV n0 0x142E (reg n0))
    (M0 : Word → BitVec 8)
    (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_10 : reg n0 a0 = pv)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = x20)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_22 : reg n0 (22 : Fin 32) = x22)
    (g0_23 : reg n0 (23 : Fin 32) = x23)
    (g0_24 : reg n0 (24 : Fin 32) = x24)
    (g0_25 : reg n0 (25 : Fin 32) = x25)
    (g0_26 : reg n0 (26 : Fin 32) = x26)
    (g0_27 : reg n0 (27 : Fin 32) = x27)
    (CK0 : SvCkCode M0)
    (hckp : memLoad32 M0 (bp + 0x18) = ckp)
    (hckl : memLoad32 M0 (bp + 0x1C) = ckl)
    (ckp_in4 : SvIn B (bp + 0x18) 4)
    (ckl_in4 : SvIn B (bp + 0x1C) 4)
    (a_ckp : (bp + 0x18).toNat % 4 = 0)
    (a_ckl : (bp + 0x1C).toNat % 4 = 0)
    (ck_in : SvIn B ckp ckl.toNat) :
    SvErrRet B out v n0 ∨
    ((pv ≠ 0) ∧
      ∃ ix8_1, nlScan M0 (ckp) 0 ((ckl).toNat) = some ix8_1 ∧
      ∃ ix18_1, nlScan M0 ((ckp) + BitVec.ofNat 32 (ix8_1 + 1)) 0 (((ckl).toNat) - (ix8_1 + 1)) = some ix18_1 ∧
      ∃ ix26_1, nlScan M0 (((ckp) + BitVec.ofNat 32 (ix8_1 + 1)) + BitVec.ofNat 32 (ix18_1 + 1)) 0 ((((ckl).toNat) - (ix8_1 + 1)) - (ix18_1 + 1)) = some ix26_1 ∧
      ∃ ix34_1, nlScan M0 ((((ckp) + BitVec.ofNat 32 (ix8_1 + 1)) + BitVec.ofNat 32 (ix18_1 + 1)) + BitVec.ofNat 32 (ix26_1 + 1)) 0 (((((ckl).toNat) - (ix8_1 + 1)) - (ix18_1 + 1)) - (ix26_1 + 1)) = some ix34_1 ∧
      (BitVec.ofNat 32 ix34_1 = 0) ∧
      (BitVec.ofNat 32 (((((ckl).toNat) - (ix8_1 + 1)) - (ix18_1 + 1)) - (ix26_1 + 1)) - BitVec.ofNat 32 (ix34_1 + 1) ≠ 0) ∧
      (((1 < (BitVec.ofNat 32 ix18_1).toNat) ∧ ((BitVec.ofNat 32 (((((ckl).toNat) - (ix8_1 + 1)) - (ix18_1 + 1)) - (ix26_1 + 1)) - BitVec.ofNat 32 (ix34_1 + 1)).toNat < ckl.toNat) ∧ (¬ (ckl).toNat < ((aluEval .xor ((BitVec.ofNat 32 (((((ckl).toNat) - (ix8_1 + 1)) - (ix18_1 + 1)) - (ix26_1 + 1)) - BitVec.ofNat 32 (ix34_1 + 1))) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl)).toNat) ∧ (¬ (((BitVec.ofNat 32 ix18_1)) + BitVec.ofNat 32 0xFFFFFFEC).toNat < (BitVec.ofNat 32 0xFFFFFFED).toNat) ∧ (M0 ((ckp) + BitVec.ofNat 32 (ix8_1 + 1)) ≠ 0x30)) ∨ ((¬ (1 < (BitVec.ofNat 32 ix18_1).toNat)) ∧ ((BitVec.ofNat 32 (((((ckl).toNat) - (ix8_1 + 1)) - (ix18_1 + 1)) - (ix26_1 + 1)) - BitVec.ofNat 32 (ix34_1 + 1)).toNat < ckl.toNat) ∧ (¬ (ckl).toNat < ((aluEval .xor ((BitVec.ofNat 32 (((((ckl).toNat) - (ix8_1 + 1)) - (ix18_1 + 1)) - (ix26_1 + 1)) - BitVec.ofNat 32 (ix34_1 + 1))) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl)).toNat) ∧ (¬ (((BitVec.ofNat 32 ix18_1)) + BitVec.ofNat 32 0xFFFFFFEC).toNat < (BitVec.ofNat 32 0xFFFFFFED).toNat))) ∧
    ∃ n', Steps n0 n' ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        St n'.mem SV n' 0x14FE (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (8 : Fin 32) = (BitVec.ofNat 32 ix18_1) ∧
        reg n' (9 : Fin 32) = ckl ∧
        reg n' a0 = BitVec.ofNat 32 0xA ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = x20 ∧
        reg n' (21 : Fin 32) = x21 ∧
        reg n' (22 : Fin 32) = x22 ∧
        reg n' (23 : Fin 32) = x23 ∧
        reg n' (24 : Fin 32) = ((ckp) + BitVec.ofNat 32 (ix8_1 + 1)) ∧
        reg n' (25 : Fin 32) = (((ckp) + BitVec.ofNat 32 (ix8_1 + 1)) + BitVec.ofNat 32 (ix18_1 + 1)) ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = (BitVec.ofNat 32 ix26_1) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = (aluEval .xor ((BitVec.ofNat 32 (((((ckl).toNat) - (ix8_1 + 1)) - (ix18_1 + 1)) - (ix26_1 + 1)) - BitVec.ofNat 32 (ix34_1 + 1))) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = (((((ckp) + BitVec.ofNat 32 (ix8_1 + 1)) + BitVec.ofNat 32 (ix18_1 + 1)) + BitVec.ofNat 32 (ix26_1 + 1)) + BitVec.ofNat 32 (ix34_1 + 1)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = (BitVec.ofNat 32 (((((ckl).toNat) - (ix8_1 + 1)) - (ix18_1 + 1)) - (ix26_1 + 1)) - BitVec.ofNat 32 (ix34_1 + 1)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 0x0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 0x0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((((ckp) + BitVec.ofNat 32 (ix8_1 + 1)) + BitVec.ofNat 32 (ix18_1 + 1)) + BitVec.ofNat 32 (ix26_1 + 1)) + BitVec.ofNat 32 (ix34_1 + 1)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 ix8_1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ckp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (((((ckl).toNat) - (ix8_1 + 1)) - (ix18_1 + 1)) - (ix26_1 + 1)) - BitVec.ofNat 32 (ix34_1 + 1) ∧
        SvKeepL B n0.mem n'.mem [(0x28, 0x4), (0x420, 0x10), (0x48, 0x4), (0x44, 0x4), (0x420, 0x10), (0x420, 0x10), (0x420, 0x10), (0x50, 0x4), (0x24, 0x4), (0x38, 0x4), (0x64, 0x4), (0x74, 0x4)]) := by
  rcases sv_ck1 FW E0 V0 hret hO s0 M0 fM g0_2 g0_10 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 CK0 hckp hckl ckp_in4 ckl_in4 a_ckp a_ckl ck_in with ⟨-, e⟩ | hx1
  · exact .inl e
  obtain ⟨x1_0, hx1⟩ := hx1
  obtain ⟨ix8_1, hx1⟩ := hx1
  obtain ⟨x1_1, hx1⟩ := hx1
  obtain ⟨ix18_1, hx1⟩ := hx1
  obtain ⟨x1_2, hx1⟩ := hx1
  obtain ⟨ix26_1, hx1⟩ := hx1
  obtain ⟨x1_3, hx1⟩ := hx1
  obtain ⟨ix34_1, hx1⟩ := hx1
  obtain ⟨x1_4, hx1⟩ := hx1
  obtain ⟨x1_5, hx1⟩ := hx1
  obtain ⟨x1_6, hx1⟩ := hx1
  obtain ⟨n1, hx1⟩ := hx1
  obtain ⟨c1, hx1⟩ := hx1
  obtain ⟨s1, hx1⟩ := hx1
  obtain ⟨E1, hx1⟩ := hx1
  obtain ⟨V1, hx1⟩ := hx1
  obtain ⟨fR1, hx1⟩ := hx1
  obtain ⟨r1_2, hx1⟩ := hx1
  obtain ⟨r1_3, hx1⟩ := hx1
  obtain ⟨r1_4, hx1⟩ := hx1
  obtain ⟨r1_8, hx1⟩ := hx1
  obtain ⟨r1_9, hx1⟩ := hx1
  obtain ⟨r1_18, hx1⟩ := hx1
  obtain ⟨r1_19, hx1⟩ := hx1
  obtain ⟨r1_20, hx1⟩ := hx1
  obtain ⟨r1_21, hx1⟩ := hx1
  obtain ⟨r1_22, hx1⟩ := hx1
  obtain ⟨r1_23, hx1⟩ := hx1
  obtain ⟨r1_24, hx1⟩ := hx1
  obtain ⟨r1_25, hx1⟩ := hx1
  obtain ⟨r1_26, hx1⟩ := hx1
  obtain ⟨r1_27, hx1⟩ := hx1
  obtain ⟨w1_28, hx1⟩ := hx1
  obtain ⟨w1_44, hx1⟩ := hx1
  obtain ⟨w1_48, hx1⟩ := hx1
  obtain ⟨w1_50, hx1⟩ := hx1
  obtain ⟨w1_428, hx1⟩ := hx1
  obtain ⟨w1_42c, hx1⟩ := hx1
  have K1_L := hx1
  rcases sv_ck2 FW E1 V1 hret hO s1 M0 fR1 r1_2 r1_8 r1_9 r1_18 r1_19 r1_20 r1_21 r1_22 r1_23 r1_24 r1_25 r1_26 r1_27 w1_50 w1_428 ((((ck_in).nlRest x1_1).nlLine x1_2).ofNatLen) with e | hx2
  · exact .inl (SvErrRet.pre (c1) (by rw [r1_3]) (by rw [r1_4])
      (fun x hx => (fR1 x hx).trans (fM x hx).symm) e)
  obtain ⟨x2_0, hx2⟩ := hx2
  obtain ⟨n2, hx2⟩ := hx2
  obtain ⟨c2, hx2⟩ := hx2
  obtain ⟨s2, hx2⟩ := hx2
  obtain ⟨E2, hx2⟩ := hx2
  obtain ⟨V2, hx2⟩ := hx2
  obtain ⟨fR2, hx2⟩ := hx2
  obtain ⟨r2_2, hx2⟩ := hx2
  obtain ⟨r2_3, hx2⟩ := hx2
  obtain ⟨r2_4, hx2⟩ := hx2
  obtain ⟨r2_8, hx2⟩ := hx2
  obtain ⟨r2_9, hx2⟩ := hx2
  obtain ⟨r2_a0, hx2⟩ := hx2
  obtain ⟨r2_18, hx2⟩ := hx2
  obtain ⟨r2_19, hx2⟩ := hx2
  obtain ⟨r2_20, hx2⟩ := hx2
  obtain ⟨r2_21, hx2⟩ := hx2
  obtain ⟨r2_22, hx2⟩ := hx2
  obtain ⟨r2_23, hx2⟩ := hx2
  obtain ⟨r2_24, hx2⟩ := hx2
  obtain ⟨r2_25, hx2⟩ := hx2
  obtain ⟨r2_26, hx2⟩ := hx2
  obtain ⟨r2_27, hx2⟩ := hx2
  obtain ⟨w2_24, hx2⟩ := hx2
  obtain ⟨w2_38, hx2⟩ := hx2
  obtain ⟨w2_50, hx2⟩ := hx2
  obtain ⟨w2_64, hx2⟩ := hx2
  obtain ⟨w2_74, hx2⟩ := hx2
  obtain ⟨w2_428, hx2⟩ := hx2
  have K2_L := hx2
  exact .inr ⟨x1_0, ix8_1, x1_1, ix18_1, x1_2, ix26_1, x1_3, ix34_1, x1_4, x1_5, x1_6, x2_0, n2, c1.trans (c2), fR2, s2, E2, V2,
    by rw [r2_3, r1_3], by rw [r2_4, r1_4], r2_2, r2_8, r2_9, r2_a0, r2_18, r2_19, r2_20, r2_21, r2_22, r2_23, r2_24, r2_25, r2_26, r2_27, w2_24, w2_38, w2_50, w2_64, w2_74, w2_428, ((K2_L.w32 (by decide) (by decide)).trans w1_28), ((K2_L.w32 (by decide) (by decide)).trans w1_44), ((K2_L.w32 (by decide) (by decide)).trans w1_48), ((K2_L.w32 (by decide) (by decide)).trans w1_42c), ((K1_L).trans K2_L).mono (by decide)⟩

end C3.RV32.Sv
