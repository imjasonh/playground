import C3BootProofs.Proofs.SvSegCk
import C3BootProofs.Proofs.SvCsa
import C3BootProofs.Proofs.SvNSearch
import C3BootProofs.Proofs.SvCgLoop

/-!
# `sigstore::verify`: One signature line of the checkpoint

Composed from generated stages by `scripts/gen-sv-segs.py`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 100000

set_option maxHeartbeats 64000000 in
/-- **One signature line of the checkpoint**: from the signature loop's head at 0x1642 back to it. -/
theorem sv_seg_cosig {B out bp x20 x21 x22 x23 x24 x25 x26 x27 f w38 w50 kh w48 w44 kp ckp bl : Word} {sg : Bytes} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out)
    (s0 : St n0.mem SV n0 0x1642 (reg n0))
    (M0 : Word → BitVec 8)
    (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
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
    (w0_18 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh)
    (w0_24 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl)
    (w0_28 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp)
    (w0_30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f)
    (w0_34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp)
    (w0_38 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38)
    (w0_44 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44)
    (w0_48 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48)
    (w0_50 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50)
    (b0_14 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0))
    (q0_1fc : ∀ j, j < 63 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0))
    (hrem : w50 ≠ 0)
    (sg_in : SvIn B w38 w50.toNat)
    (CK0 : SvCkCode M0)
    (l_in : SvIn B w48 w44.toNat) :
    SvErrRet B out v n0 ∨
    (∃ ix9_1, nlScan M0 (w38) 0 ((w50).toNat) = some ix9_1 ∧
      (4 ≤ ix9_1 ∧ memBytes M0 w38 4 = memBytes M0 (BitVec.ofNat 32 (img% svDashAddress)) 4) ∧
      (4 < ix9_1) ∧
      ∃ k_2, k_2 < ((BitVec.ofNat 32 (ix9_1 - 4)).toNat - 1) + 1 ∧
      (∀ i, i < k_2 → ∀ ni'_2, ni'_2 = svIter (fun s => (s) + BitVec.ofNat 32 0x1) i (BitVec.ofNat 32 0x0) → ¬ (M0 ((w38 + BitVec.ofNat 32 4) + ni'_2) = 0x20)) ∧
      ∃ ni'_2, ni'_2 = svIter (fun s => (s) + BitVec.ofNat 32 0x1) k_2 (BitVec.ofNat 32 0x0) ∧ (M0 ((w38 + BitVec.ofNat 32 4) + ni'_2) = 0x20) ∧
      ni'_2 = (BitVec.ofNat 32 0x0) + BitVec.ofNat 32 (k_2 * 1) ∧
      (ni'_2 ≠ 0) ∧ ((((BitVec.ofNat 32 (ix9_1 - 4))) - ((ni'_2) + BitVec.ofNat 32 0x1)) &&& BitVec.ofNat 32 0x3 = 0) ∧
      ∃ pg'_3 gi'_3, (pg'_3, gi'_3) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0x4, ((s.2)) + BitVec.ofNat 32 0x1)) (((((BitVec.ofNat 32 (ix9_1 - 4))) - ((ni'_2) + BitVec.ofNat 32 0x1)) >>> 2).toNat) ((((w38 + BitVec.ofNat 32 4)) + ((ni'_2) + BitVec.ofNat 32 0x1)), (BitVec.ofNat 32 0x0)) ∧ (∀ i, i < (((((BitVec.ofNat 32 (ix9_1 - 4))) - ((ni'_2) + BitVec.ofNat 32 0x1)) >>> 2).toNat) → ∀ pg'_3 gi'_3, (pg'_3, gi'_3) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0x4, ((s.2)) + BitVec.ofNat 32 0x1)) i ((((w38 + BitVec.ofNat 32 4)) + ((ni'_2) + BitVec.ofNat 32 0x1)), (BitVec.ofNat 32 0x0)) → ((((M0 (pg'_3) = 0x3D) ∧ ((gi'_3) + BitVec.ofNat 32 0x1 = ((((BitVec.ofNat 32 (ix9_1 - 4))) - ((ni'_2) + BitVec.ofNat 32 0x1)) >>> 2)) ∧ ∃ bq27, base64Decode (memBytes M0 pg'_3 4) = some bq27 ∧ (bq27.length ≤ 3)) ∨ ((¬ (M0 (pg'_3) = 0x3D)) ∧ (M0 ((pg'_3) + BitVec.ofNat 32 0x1) = 0x3D) ∧ ((gi'_3) + BitVec.ofNat 32 0x1 = ((((BitVec.ofNat 32 (ix9_1 - 4))) - ((ni'_2) + BitVec.ofNat 32 0x1)) >>> 2)) ∧ ∃ bq33, base64Decode (memBytes M0 pg'_3 4) = some bq33 ∧ (bq33.length ≤ 3)) ∨ ((¬ (M0 (pg'_3) = 0x3D)) ∧ (¬ (M0 ((pg'_3) + BitVec.ofNat 32 0x1) = 0x3D)) ∧ (M0 (((pg'_3) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D) ∧ ((gi'_3) + BitVec.ofNat 32 0x1 = ((((BitVec.ofNat 32 (ix9_1 - 4))) - ((ni'_2) + BitVec.ofNat 32 0x1)) >>> 2)) ∧ ∃ bq39, base64Decode (memBytes M0 pg'_3 4) = some bq39 ∧ (bq39.length ≤ 3)) ∨ ((¬ (M0 (pg'_3) = 0x3D)) ∧ (¬ (M0 ((pg'_3) + BitVec.ofNat 32 0x1) = 0x3D)) ∧ (¬ (M0 (((pg'_3) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D)) ∧ (M0 ((((pg'_3) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D) ∧ ((gi'_3) + BitVec.ofNat 32 0x1 = ((((BitVec.ofNat 32 (ix9_1 - 4))) - ((ni'_2) + BitVec.ofNat 32 0x1)) >>> 2)) ∧ ∃ bq45, base64Decode (memBytes M0 pg'_3 4) = some bq45 ∧ (bq45.length ≤ 3)) ∨ ((¬ (M0 (pg'_3) = 0x3D)) ∧ (¬ (M0 ((pg'_3) + BitVec.ofNat 32 0x1) = 0x3D)) ∧ (¬ (M0 (((pg'_3) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D)) ∧ (¬ (M0 ((((pg'_3) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D)) ∧ ∃ bq44, base64Decode (memBytes M0 pg'_3 4) = some bq44 ∧ (bq44.length ≤ 3))))) ∧
      ∃ cm_sg_3 : Bytes, ∃ cm_w30_3 : Word, ((False) ∨ (False) ∨ (False) ∨ (∃ bs, base64Decode (memBytes M0 (((w38 + BitVec.ofNat 32 4)) + ((ni'_2) + BitVec.ofNat 32 0x1)) (((BitVec.ofNat 32 (ix9_1 - 4))) - ((ni'_2) + BitVec.ofNat 32 0x1)).toNat) = some bs ∧ (¬ ((BitVec.ofNat 32 (ix9_1 - 4)) = ((ni'_2) + BitVec.ofNat 32 0x1))) ∧ (memBytes M0 (w38 + BitVec.ofNat 32 4) ni'_2.toNat = memBytes M0 w48 w44.toNat) ∧ (¬ (base64Decode (memBytes M0 (((w38 + BitVec.ofNat 32 4)) + ((ni'_2) + BitVec.ofNat 32 0x1)) (((BitVec.ofNat 32 (ix9_1 - 4))) - ((ni'_2) + BitVec.ofNat 32 0x1)).toNat) = none)) ∧ (¬ (0x60 < bs.length)) ∧ (bs.length < 4) ∧ cm_sg_3 = sg ∧ cm_w30_3 = f) ∨ (∃ bs, base64Decode (memBytes M0 (((w38 + BitVec.ofNat 32 4)) + ((ni'_2) + BitVec.ofNat 32 0x1)) (((BitVec.ofNat 32 (ix9_1 - 4))) - ((ni'_2) + BitVec.ofNat 32 0x1)).toNat) = some bs ∧ (¬ ((BitVec.ofNat 32 (ix9_1 - 4)) = ((ni'_2) + BitVec.ofNat 32 0x1))) ∧ (memBytes M0 (w38 + BitVec.ofNat 32 4) ni'_2.toNat = memBytes M0 w48 w44.toNat) ∧ (¬ (base64Decode (memBytes M0 (((w38 + BitVec.ofNat 32 4)) + ((ni'_2) + BitVec.ofNat 32 0x1)) (((BitVec.ofNat 32 (ix9_1 - 4))) - ((ni'_2) + BitVec.ofNat 32 0x1)).toNat) = none)) ∧ (¬ (0x60 < bs.length)) ∧ (¬ (bs.length < 4)) ∧ (le4 bs 0 = kh) ∧ (bs.length = 68) ∧ (((f) &&& BitVec.ofNat 32 0x1) = 0) ∧ cm_sg_3 = (bs.drop 4) ∧ cm_w30_3 = BitVec.ofNat 32 0x1) ∨ (False) ∨ (∃ bs, base64Decode (memBytes M0 (((w38 + BitVec.ofNat 32 4)) + ((ni'_2) + BitVec.ofNat 32 0x1)) (((BitVec.ofNat 32 (ix9_1 - 4))) - ((ni'_2) + BitVec.ofNat 32 0x1)).toNat) = some bs ∧ (¬ ((BitVec.ofNat 32 (ix9_1 - 4)) = ((ni'_2) + BitVec.ofNat 32 0x1))) ∧ (memBytes M0 (w38 + BitVec.ofNat 32 4) ni'_2.toNat = memBytes M0 w48 w44.toNat) ∧ (¬ (base64Decode (memBytes M0 (((w38 + BitVec.ofNat 32 4)) + ((ni'_2) + BitVec.ofNat 32 0x1)) (((BitVec.ofNat 32 (ix9_1 - 4))) - ((ni'_2) + BitVec.ofNat 32 0x1)).toNat) = none)) ∧ (¬ (0x60 < bs.length)) ∧ (¬ (bs.length < 4)) ∧ (¬ (le4 bs 0 = kh)) ∧ cm_sg_3 = sg ∧ cm_w30_3 = f) ∨ ((¬ ((BitVec.ofNat 32 (ix9_1 - 4)) = ((ni'_2) + BitVec.ofNat 32 0x1))) ∧ (¬ (memBytes M0 (w38 + BitVec.ofNat 32 4) ni'_2.toNat = memBytes M0 w48 w44.toNat)) ∧ cm_sg_3 = sg ∧ cm_w30_3 = f)) ∧
    ∃ n', Steps n0 n' ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        St n'.mem SV n' 0x1642 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (8 : Fin 32) = (BitVec.ofNat 32 (ix9_1 - 4)) ∧
        reg n' (9 : Fin 32) = ((ni'_2) + BitVec.ofNat 32 0x1) ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = x20 ∧
        reg n' (21 : Fin 32) = gi'_3 ∧
        reg n' (22 : Fin 32) = x22 ∧
        reg n' (23 : Fin 32) = x23 ∧
        reg n' (24 : Fin 32) = ni'_2 ∧
        reg n' (25 : Fin 32) = x25 ∧
        reg n' (26 : Fin 32) = (((BitVec.ofNat 32 (ix9_1 - 4))) - ((ni'_2) + BitVec.ofNat 32 0x1)) ∧
        reg n' (27 : Fin 32) = (w38 + BitVec.ofNat 32 4) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = ((aluEval .sll ((((BitVec.ofNat 32 (ix9_1 - 4))) - ((ni'_2) + BitVec.ofNat 32 0x1)) >>> 2) (BitVec.ofNat 32 0x2)) + (((w38 + BitVec.ofNat 32 4)) + ((ni'_2) + BitVec.ofNat 32 0x1))) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = ((((BitVec.ofNat 32 (ix9_1 - 4))) - ((ni'_2) + BitVec.ofNat 32 0x1)) >>> 2) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = (((w38 + BitVec.ofNat 32 4)) + ((ni'_2) + BitVec.ofNat 32 0x1)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = ((f) &&& BitVec.ofNat 32 0x1) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = cm_w30_3 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = ((w38) + BitVec.ofNat 32 (ix9_1 + 1)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = (BitVec.ofNat 32 ((w50).toNat) - BitVec.ofNat 32 (ix9_1 + 1)) ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (cm_sg_3.getD 0 0) ∧
        (∀ j, j < 63 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (cm_sg_3.getD (1 + j) 0)) ∧
        SvKeepL B n0.mem n'.mem [(0x2C, 0x4), (0x420, 0x10), (0x38, 0x4), (0x50, 0x4), (0xC, 0x4), (0x8, 0x4), (0x10, 0x4), (0x4, 0x4), (0x400, 0x4), (0x420, 0x8), (0x370, 0x3), (0x420, 0x60), (0x400, 0x8), (0x14, 0x4), (0x1FC, 0x3F), (0x30, 0x4)]) := by
  rcases sv_csa FW E0 V0 hret hO s0 M0 fM g0_2 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_18 w0_24 w0_28 w0_30 w0_34 w0_38 w0_44 w0_48 w0_50 b0_14 q0_1fc hrem sg_in CK0 with ⟨-, e⟩ | hx1
  · exact .inl e
  obtain ⟨ix9_1, hx1⟩ := hx1
  obtain ⟨x1_0, hx1⟩ := hx1
  obtain ⟨x1_1, hx1⟩ := hx1
  obtain ⟨x1_2, hx1⟩ := hx1
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
  obtain ⟨w1_18, hx1⟩ := hx1
  obtain ⟨w1_24, hx1⟩ := hx1
  obtain ⟨w1_28, hx1⟩ := hx1
  obtain ⟨w1_2c, hx1⟩ := hx1
  obtain ⟨w1_30, hx1⟩ := hx1
  obtain ⟨w1_34, hx1⟩ := hx1
  obtain ⟨w1_38, hx1⟩ := hx1
  obtain ⟨w1_44, hx1⟩ := hx1
  obtain ⟨w1_48, hx1⟩ := hx1
  obtain ⟨w1_50, hx1⟩ := hx1
  obtain ⟨w1_420, hx1⟩ := hx1
  obtain ⟨w1_424, hx1⟩ := hx1
  obtain ⟨w1_428, hx1⟩ := hx1
  obtain ⟨w1_42c, hx1⟩ := hx1
  obtain ⟨b1_14, hx1⟩ := hx1
  obtain ⟨q1_1fc, hx1⟩ := hx1
  have K1_L := hx1
  rcases sv_nsearch_run (x24 := 0) (x27 := 0) FW hret hO M0 E1 V1 s1 fR1 r1_2 r1_18 r1_19 r1_20 r1_21 r1_22 r1_23 r1_25 r1_26 w1_18 w1_24 w1_28 w1_30 w1_34 w1_38 w1_44 w1_48 w1_50 b1_14 q1_1fc r1_8 r1_24 r1_27 ((((sg_in).nlLine x1_0).drop x1_1.1).ofNatLen) (by intro h; have h1 := x1_2; have h2 := (nlScan_lt _ _ _ x1_0).2; have h3 := BitVec.isLt w50; have h4 := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat, Nat.reducePow, BitVec.ofNat_eq_ofNat] at h4; omega) with e | hx2
  · exact .inl (SvErrRet.pre (c1) (by rw [r1_3]) (by rw [r1_4])
      (fun x hx => (fR1 x hx).trans (fM x hx).symm) e)
  obtain ⟨k_2, hx2⟩ := hx2
  obtain ⟨x2_0, hx2⟩ := hx2
  obtain ⟨x2_1, hx2⟩ := hx2
  obtain ⟨ni'_2, hx2⟩ := hx2
  obtain ⟨x2_2, hx2⟩ := hx2
  obtain ⟨x2_3, hx2⟩ := hx2
  obtain ⟨x2_4, hx2⟩ := hx2
  obtain ⟨x2_5, hx2⟩ := hx2
  obtain ⟨x2_6, hx2⟩ := hx2
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
  obtain ⟨r2_a1, hx2⟩ := hx2
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
  obtain ⟨w2_8, hx2⟩ := hx2
  obtain ⟨w2_c, hx2⟩ := hx2
  obtain ⟨w2_10, hx2⟩ := hx2
  obtain ⟨w2_18, hx2⟩ := hx2
  obtain ⟨w2_24, hx2⟩ := hx2
  obtain ⟨w2_28, hx2⟩ := hx2
  obtain ⟨w2_30, hx2⟩ := hx2
  obtain ⟨w2_34, hx2⟩ := hx2
  obtain ⟨w2_38, hx2⟩ := hx2
  obtain ⟨w2_44, hx2⟩ := hx2
  obtain ⟨w2_48, hx2⟩ := hx2
  obtain ⟨w2_50, hx2⟩ := hx2
  obtain ⟨b2_14, hx2⟩ := hx2
  obtain ⟨q2_1fc, hx2⟩ := hx2
  have K2_L := hx2
  rcases sv_cgloop_run (x21 := 0) (x24 := 0) (x26 := 0) (x27 := 0) FW hret hO M0 E2 V2 s2 fR2 r2_2 r2_8 r2_9 r2_a0 r2_18 r2_19 r2_20 r2_21 r2_22 r2_23 r2_24 r2_25 r2_26 r2_27 w2_8 w2_c w2_10 w2_18 w2_24 w2_28 ((K2_L.w32 (by decide) (by decide)).trans w1_2c) w2_30 w2_34 w2_38 w2_44 w2_48 w2_50 b2_14 q2_1fc (by rw [svSll2]; exact BitVec.add_comm _ _) (SvIn.afterSep ((((sg_in).nlLine x1_0).drop x1_1.1).ofNatLen) (show k_2 < (BitVec.ofNat 32 (ix9_1 - 4)).toNat from by have h := x2_0; have hz : BitVec.ofNat 32 (ix9_1 - 4) ≠ 0 := (by intro h; have h1 := x1_2; have h2 := (nlScan_lt _ _ _ x1_0).2; have h3 := BitVec.isLt w50; have h4 := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat, Nat.reducePow, BitVec.ofNat_eq_ofNat] at h4; omega); have h' : (BitVec.ofNat 32 (ix9_1 - 4)).toNat ≠ 0 := fun e => hz (BitVec.eq_of_toNat_eq (by rw [e]; rfl)); omega) x2_4) (SvIn.afterSepAll ((((sg_in).nlLine x1_0).drop x1_1.1).ofNatLen) (show k_2 < (BitVec.ofNat 32 (ix9_1 - 4)).toNat from by have h := x2_0; have hz : BitVec.ofNat 32 (ix9_1 - 4) ≠ 0 := (by intro h; have h1 := x1_2; have h2 := (nlScan_lt _ _ _ x1_0).2; have h3 := BitVec.isLt w50; have h4 := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat, Nat.reducePow, BitVec.ofNat_eq_ofNat] at h4; omega); have h' : (BitVec.ofNat 32 (ix9_1 - 4)).toNat ≠ 0 := fun e => hz (BitVec.eq_of_toNat_eq (by rw [e]; rfl)); omega) x2_4) CK0 l_in (SvIn.beforeSep ((((sg_in).nlLine x1_0).drop x1_1.1).ofNatLen) (show k_2 < (BitVec.ofNat 32 (ix9_1 - 4)).toNat from by have h := x2_0; have hz : BitVec.ofNat 32 (ix9_1 - 4) ≠ 0 := (by intro h; have h1 := x1_2; have h2 := (nlScan_lt _ _ _ x1_0).2; have h3 := BitVec.isLt w50; have h4 := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat, Nat.reducePow, BitVec.ofNat_eq_ofNat] at h4; omega); have h' : (BitVec.ofNat 32 (ix9_1 - 4)).toNat ≠ 0 := fun e => hz (BitVec.eq_of_toNat_eq (by rw [e]; rfl)); omega) x2_4) with e | hx3
  · exact .inl (SvErrRet.pre (c1.trans (c2)) (by rw [r2_3, r1_3]) (by rw [r2_4, r1_4])
      (fun x hx => (fR2 x hx).trans (fM x hx).symm) e)
  obtain ⟨pg'_3, hx3⟩ := hx3
  obtain ⟨gi'_3, hx3⟩ := hx3
  obtain ⟨x3_0, hx3⟩ := hx3
  obtain ⟨x3_1, hx3⟩ := hx3
  obtain ⟨cm_sg_3, hx3⟩ := hx3
  obtain ⟨cm_w30_3, hx3⟩ := hx3
  obtain ⟨x3_2, hx3⟩ := hx3
  obtain ⟨n3, hx3⟩ := hx3
  obtain ⟨c3, hx3⟩ := hx3
  obtain ⟨s3, hx3⟩ := hx3
  obtain ⟨E3, hx3⟩ := hx3
  obtain ⟨V3, hx3⟩ := hx3
  obtain ⟨fR3, hx3⟩ := hx3
  obtain ⟨r3_2, hx3⟩ := hx3
  obtain ⟨r3_3, hx3⟩ := hx3
  obtain ⟨r3_4, hx3⟩ := hx3
  obtain ⟨r3_8, hx3⟩ := hx3
  obtain ⟨r3_9, hx3⟩ := hx3
  obtain ⟨r3_18, hx3⟩ := hx3
  obtain ⟨r3_19, hx3⟩ := hx3
  obtain ⟨r3_20, hx3⟩ := hx3
  obtain ⟨r3_21, hx3⟩ := hx3
  obtain ⟨r3_22, hx3⟩ := hx3
  obtain ⟨r3_23, hx3⟩ := hx3
  obtain ⟨r3_24, hx3⟩ := hx3
  obtain ⟨r3_25, hx3⟩ := hx3
  obtain ⟨r3_26, hx3⟩ := hx3
  obtain ⟨r3_27, hx3⟩ := hx3
  obtain ⟨w3_8, hx3⟩ := hx3
  obtain ⟨w3_c, hx3⟩ := hx3
  obtain ⟨w3_10, hx3⟩ := hx3
  obtain ⟨w3_18, hx3⟩ := hx3
  obtain ⟨w3_24, hx3⟩ := hx3
  obtain ⟨w3_28, hx3⟩ := hx3
  obtain ⟨w3_2c, hx3⟩ := hx3
  obtain ⟨w3_30, hx3⟩ := hx3
  obtain ⟨w3_34, hx3⟩ := hx3
  obtain ⟨w3_38, hx3⟩ := hx3
  obtain ⟨w3_44, hx3⟩ := hx3
  obtain ⟨w3_48, hx3⟩ := hx3
  obtain ⟨w3_50, hx3⟩ := hx3
  obtain ⟨b3_14, hx3⟩ := hx3
  obtain ⟨q3_1fc, hx3⟩ := hx3
  have K3_L := hx3
  exact .inr ⟨ix9_1, x1_0, x1_1, x1_2, k_2, x2_0, x2_1, ni'_2, x2_2, x2_3, x2_4, x2_5, x2_6, pg'_3, gi'_3, x3_0, x3_1, cm_sg_3, cm_w30_3, x3_2, n3, c1.trans (c2.trans (c3)), fR3, s3, E3, V3,
    by rw [r3_3, r2_3, r1_3], by rw [r3_4, r2_4, r1_4], r3_2, r3_8, r3_9, r3_18, r3_19, r3_20, r3_21, r3_22, r3_23, r3_24, r3_25, r3_26, r3_27, w3_8, w3_c, w3_10, w3_18, w3_24, w3_28, w3_2c, w3_30, w3_34, w3_38, w3_44, w3_48, w3_50, b3_14, q3_1fc, (((K1_L).trans K2_L).trans K3_L).mono (by decide)⟩

end C3.RV32.Sv
