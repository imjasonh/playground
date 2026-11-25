import C3BootProofs.Proofs.SvSegCk
import C3BootProofs.Proofs.SvDbc1
import C3BootProofs.Proofs.SvDbc2m

/-!
# `sigstore::verify`: A `BasicConstraints` extension

Composed from generated stages by `scripts/gen-sv-segs.py`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 100000

set_option maxHeartbeats 64000000 in
/-- **A `BasicConstraints` extension**: from the OID tests at 0x4E2 back to the extensions loop at 0x3B8, `sv_dbc1` and `sv_dbc2m`. -/
theorem sv_seg_dbc {B out bp tbp dg rootp ll sgp kp sgl tbl f2c f30 p0 L cur sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 sl9 w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c op ol vp vl rest : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out)
    (s0 : St n0.mem SV n0 0x4E2 (reg n0))
    (M0 : Word → BitVec 8)
    (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_9 : reg n0 (9 : Fin 32) = tbp)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = dg)
    (g0_21 : reg n0 (21 : Fin 32) = rootp)
    (g0_22 : reg n0 (22 : Fin 32) = ll)
    (g0_23 : reg n0 (23 : Fin 32) = sgp)
    (g0_24 : reg n0 (24 : Fin 32) = kp)
    (g0_25 : reg n0 (25 : Fin 32) = sgl)
    (g0_27 : reg n0 (27 : Fin 32) = tbl)
    (w0_2c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c)
    (w0_30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30)
    (w0_54 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54)
    (w0_58 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58)
    (w0_5c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c)
    (w0_60 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60)
    (w0_64 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64)
    (w0_68 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68)
    (w0_6c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c)
    (w0_70 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70)
    (w0_74 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74)
    (w0_78 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78)
    (w0_7c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c)
    (w0_80 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0)
    (w0_84 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1)
    (w0_88 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2)
    (w0_8c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3)
    (w0_90 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4)
    (w0_94 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5)
    (w0_98 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6)
    (w0_9c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7)
    (w0_a0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8)
    (w0_a4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9)
    (w0_150 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0)
    (w0_154 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L)
    (w0_34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl)
    (w0_38 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp)
    (w0_48 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol)
    (w0_4c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op)
    (w0_158 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur)
    (w0_15c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest)
    (val_in : SvIn B vp vl.toNat)
    (oid_in : SvIn B op ol.toNat)
    (SD0 : SvData M0)
    (hku : ¬ memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress)) 3)
    (heku : ¬ memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x9)) 3)
    (hbc : memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x6)) 3) :
    SvErrRet B out v n0 ∨
    (∃ tl27_1, derElement 0x30 (memBytes M0 (vp) (vl).toNat) = .ok tl27_1 ∧
      ((vl) - BitVec.ofNat 32 (tl27_1.header + tl27_1.len) = 0) ∧
      ((((BitVec.ofNat 32 tl27_1.len) = 0)) ∨ ((¬ ((BitVec.ofNat 32 tl27_1.len) = 0)) ∧ (M0 ((vp) + BitVec.ofNat 32 tl27_1.header) ≠ BitVec.ofNat 8 1) ∧ (M0 ((vp) + BitVec.ofNat 32 tl27_1.header) = BitVec.ofNat 8 2) ∧ ∃ ip10 il10, derIntOf (memBytes M0 (((vp) + BitVec.ofNat 32 tl27_1.header)) ((BitVec.ofNat 32 tl27_1.len)).toNat) (((vp) + BitVec.ofNat 32 tl27_1.header)) (derElement 2 (memBytes M0 (((vp) + BitVec.ofNat 32 tl27_1.header)) ((BitVec.ofNat 32 tl27_1.len)).toNat)) = .ok (ip10, il10) ∧ ∃ ti10, derElement 2 (memBytes M0 (((vp) + BitVec.ofNat 32 tl27_1.header)) ((BitVec.ofNat 32 tl27_1.len)).toNat) = .ok ti10 ∧ (((BitVec.ofNat 32 tl27_1.len)) - BitVec.ofNat 32 (ti10.header + ti10.len) = 0))) ∧
    ∃ n', Steps n0 n' ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        St n'.mem SV n' 0x3B8 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (9 : Fin 32) = tbp ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = dg ∧
        reg n' (21 : Fin 32) = rootp ∧
        reg n' (22 : Fin 32) = ll ∧
        reg n' (23 : Fin 32) = sgp ∧
        reg n' (24 : Fin 32) = kp ∧
        reg n' (25 : Fin 32) = sgl ∧
        reg n' (27 : Fin 32) = tbl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rest ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = vl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op ∧
        SvKeepL B n0.mem n'.mem [(0x1FC, 0x4), (0x200, 0x4), (0x204, 0x4), (0x208, 0x4), (0x420, 0x10), (0x204, 0x8), (0x50, 0x4), (0x385, 0xB), (0x380, 0x4), (0x384, 0x1), (0x50, 0x4), (0x420, 0x8), (0x388, 0x8)]) := by
  rcases sv_dbc1 (rem := 0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_9 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_27 w0_2c w0_30 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_150 w0_154 w0_34 w0_38 w0_48 w0_4c w0_158 w0_15c val_in oid_in SD0 hku heku hbc with ⟨-, e⟩ | hx1
  · exact .inl e
  obtain ⟨tl27_1, hx1⟩ := hx1
  obtain ⟨x1_0, hx1⟩ := hx1
  obtain ⟨x1_1, hx1⟩ := hx1
  obtain ⟨n1, hx1⟩ := hx1
  obtain ⟨c1, hx1⟩ := hx1
  obtain ⟨s1, hx1⟩ := hx1
  obtain ⟨E1, hx1⟩ := hx1
  obtain ⟨V1, hx1⟩ := hx1
  obtain ⟨fR1, hx1⟩ := hx1
  obtain ⟨r1_2, hx1⟩ := hx1
  obtain ⟨r1_3, hx1⟩ := hx1
  obtain ⟨r1_4, hx1⟩ := hx1
  obtain ⟨r1_9, hx1⟩ := hx1
  obtain ⟨r1_18, hx1⟩ := hx1
  obtain ⟨r1_19, hx1⟩ := hx1
  obtain ⟨r1_20, hx1⟩ := hx1
  obtain ⟨r1_21, hx1⟩ := hx1
  obtain ⟨r1_22, hx1⟩ := hx1
  obtain ⟨r1_23, hx1⟩ := hx1
  obtain ⟨r1_24, hx1⟩ := hx1
  obtain ⟨r1_25, hx1⟩ := hx1
  obtain ⟨r1_27, hx1⟩ := hx1
  obtain ⟨w1_2c, hx1⟩ := hx1
  obtain ⟨w1_30, hx1⟩ := hx1
  obtain ⟨w1_54, hx1⟩ := hx1
  obtain ⟨w1_58, hx1⟩ := hx1
  obtain ⟨w1_5c, hx1⟩ := hx1
  obtain ⟨w1_60, hx1⟩ := hx1
  obtain ⟨w1_64, hx1⟩ := hx1
  obtain ⟨w1_68, hx1⟩ := hx1
  obtain ⟨w1_6c, hx1⟩ := hx1
  obtain ⟨w1_70, hx1⟩ := hx1
  obtain ⟨w1_74, hx1⟩ := hx1
  obtain ⟨w1_78, hx1⟩ := hx1
  obtain ⟨w1_7c, hx1⟩ := hx1
  obtain ⟨w1_80, hx1⟩ := hx1
  obtain ⟨w1_84, hx1⟩ := hx1
  obtain ⟨w1_88, hx1⟩ := hx1
  obtain ⟨w1_8c, hx1⟩ := hx1
  obtain ⟨w1_90, hx1⟩ := hx1
  obtain ⟨w1_94, hx1⟩ := hx1
  obtain ⟨w1_98, hx1⟩ := hx1
  obtain ⟨w1_9c, hx1⟩ := hx1
  obtain ⟨w1_a0, hx1⟩ := hx1
  obtain ⟨w1_a4, hx1⟩ := hx1
  obtain ⟨w1_150, hx1⟩ := hx1
  obtain ⟨w1_154, hx1⟩ := hx1
  obtain ⟨w1_158, hx1⟩ := hx1
  obtain ⟨w1_15c, hx1⟩ := hx1
  obtain ⟨w1_388, hx1⟩ := hx1
  obtain ⟨w1_38c, hx1⟩ := hx1
  have K1_L := hx1
  rcases sv_dbc2m (rem := 0) FW E1 V1 hret hO s1 M0 fR1 r1_2 r1_9 r1_18 r1_19 r1_20 r1_21 r1_22 r1_23 r1_24 r1_25 r1_27 w1_2c w1_30 w1_54 w1_58 w1_5c w1_60 w1_64 w1_68 w1_6c w1_70 w1_74 w1_78 w1_7c w1_80 w1_84 w1_88 w1_8c w1_90 w1_94 w1_98 w1_9c w1_a0 w1_a4 w1_150 w1_154 w1_158 w1_15c w1_388 w1_38c (((val_in).content x1_0).ofNatLen) SD0 with e | hx2
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
  obtain ⟨r2_9, hx2⟩ := hx2
  obtain ⟨r2_18, hx2⟩ := hx2
  obtain ⟨r2_19, hx2⟩ := hx2
  obtain ⟨r2_20, hx2⟩ := hx2
  obtain ⟨r2_21, hx2⟩ := hx2
  obtain ⟨r2_22, hx2⟩ := hx2
  obtain ⟨r2_23, hx2⟩ := hx2
  obtain ⟨r2_24, hx2⟩ := hx2
  obtain ⟨r2_25, hx2⟩ := hx2
  obtain ⟨r2_27, hx2⟩ := hx2
  obtain ⟨w2_2c, hx2⟩ := hx2
  obtain ⟨w2_30, hx2⟩ := hx2
  obtain ⟨w2_50, hx2⟩ := hx2
  obtain ⟨w2_54, hx2⟩ := hx2
  obtain ⟨w2_58, hx2⟩ := hx2
  obtain ⟨w2_5c, hx2⟩ := hx2
  obtain ⟨w2_60, hx2⟩ := hx2
  obtain ⟨w2_64, hx2⟩ := hx2
  obtain ⟨w2_68, hx2⟩ := hx2
  obtain ⟨w2_6c, hx2⟩ := hx2
  obtain ⟨w2_70, hx2⟩ := hx2
  obtain ⟨w2_74, hx2⟩ := hx2
  obtain ⟨w2_78, hx2⟩ := hx2
  obtain ⟨w2_7c, hx2⟩ := hx2
  obtain ⟨w2_80, hx2⟩ := hx2
  obtain ⟨w2_84, hx2⟩ := hx2
  obtain ⟨w2_88, hx2⟩ := hx2
  obtain ⟨w2_8c, hx2⟩ := hx2
  obtain ⟨w2_90, hx2⟩ := hx2
  obtain ⟨w2_94, hx2⟩ := hx2
  obtain ⟨w2_98, hx2⟩ := hx2
  obtain ⟨w2_9c, hx2⟩ := hx2
  obtain ⟨w2_a0, hx2⟩ := hx2
  obtain ⟨w2_a4, hx2⟩ := hx2
  obtain ⟨w2_150, hx2⟩ := hx2
  obtain ⟨w2_154, hx2⟩ := hx2
  obtain ⟨w2_158, hx2⟩ := hx2
  obtain ⟨w2_15c, hx2⟩ := hx2
  have K2_L := hx2
  exact .inr ⟨tl27_1, x1_0, x1_1, x2_0, n2, c1.trans (c2), fR2, s2, E2, V2,
    by rw [r2_3, r1_3], by rw [r2_4, r1_4], r2_2, r2_9, r2_18, r2_19, r2_20, r2_21, r2_22, r2_23, r2_24, r2_25, r2_27, w2_2c, w2_30, w2_50, w2_54, w2_58, w2_5c, w2_60, w2_64, w2_68, w2_6c, w2_70, w2_74, w2_78, w2_7c, w2_80, w2_84, w2_88, w2_8c, w2_90, w2_94, w2_98, w2_9c, w2_a0, w2_a4, w2_150, w2_154, w2_158, w2_15c, ((K2_L.w32 (by decide) (by decide)).trans ((K1_L.w32 (by decide) (by decide)).trans w0_34)), ((K2_L.w32 (by decide) (by decide)).trans ((K1_L.w32 (by decide) (by decide)).trans w0_38)), ((K2_L.w32 (by decide) (by decide)).trans ((K1_L.w32 (by decide) (by decide)).trans w0_48)), ((K2_L.w32 (by decide) (by decide)).trans ((K1_L.w32 (by decide) (by decide)).trans w0_4c)), ((K1_L).trans K2_L).mono (by decide)⟩

end C3.RV32.Sv
