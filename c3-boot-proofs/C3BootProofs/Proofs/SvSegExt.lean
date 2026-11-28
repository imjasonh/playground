import C3BootProofs.Proofs.SvSegCk
import C3BootProofs.Proofs.SvX1
import C3BootProofs.Proofs.SvX2
import C3BootProofs.Proofs.SvD

/-!
# `sigstore::verify`: One extension of the leaf

Composed from generated stages by `scripts/gen-sv-segs.py`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 100000

set_option maxHeartbeats 64000000 in
/-- **One extension of the leaf**: from the extensions loop's head at 0x3B8 back to it, `sv_x1`, `sv_x2`, and `sv_d`. -/
theorem sv_seg_ext {B out bp tbp dg rootp ll sgp kp sgl tbl f2c f30 rem p0 L cur sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 sl9 w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out)
    (s0 : St n0.mem SV n0 0x3B8 (reg n0))
    (M0 : Word → BitVec 8)
    (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_8 : reg n0 (8 : Fin 32) = BitVec.ofNat 32 0x15)
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
    (w0_50 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem)
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
    (w0_158 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur)
    (w0_15c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rem)
    (xl_in : SvIn B (cur) (rem).toNat)
    (ea_in : SvIn B p0 (L.toNat - rem.toNat))
    (hrem : rem ≠ 0)
    (SD0 : SvData M0)
    (sl0_or0 : sl0 = 0 ∨ SvIn B sl0 sl1.toNat)
    (sl2_or0 : sl2 = 0 ∨ SvIn B sl2 sl3.toNat)
    (sl4_or0 : sl4 = 0 ∨ SvIn B sl4 sl5.toNat)
    (sl6_or0 : sl6 = 0 ∨ SvIn B sl6 sl7.toNat)
    (sl8_or0 : sl8 = 0 ∨ SvIn B sl8 sl9.toNat) :
    SvErrRet B out v n0 ∨
    ((rem.toNat ≤ L.toNat) ∧
      ∃ tl10_1, derElement 0x30 (memBytes M0 (cur) (rem).toNat) = .ok tl10_1 ∧
      ∃ op21_1 ol21_1, derContent ((cur) + BitVec.ofNat 32 tl10_1.header) (derOid (memBytes M0 ((cur) + BitVec.ofNat 32 tl10_1.header) (BitVec.ofNat 32 tl10_1.len).toNat)) = .ok (op21_1, ol21_1) ∧
      ∃ to21_1, derOid (memBytes M0 ((cur) + BitVec.ofNat 32 tl10_1.header) (BitVec.ofNat 32 tl10_1.len).toNat) = .ok to21_1 ∧
      ∃ x2_w34_2 : Word, ∃ x2_w38_2 : Word, ((False) ∨ ((¬ (((BitVec.ofNat 32 tl10_1.len) - BitVec.ofNat 32 (to21_1.header + to21_1.len)) = 0)) ∧ (M0 (((cur) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (to21_1.header + to21_1.len)) = BitVec.ofNat 8 1) ∧ derBoolOf (memBytes M0 ((((cur) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (to21_1.header + to21_1.len))) (((BitVec.ofNat 32 tl10_1.len) - BitVec.ofNat 32 (to21_1.header + to21_1.len))).toNat) (derElement 1 (memBytes M0 ((((cur) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (to21_1.header + to21_1.len))) (((BitVec.ofNat 32 tl10_1.len) - BitVec.ofNat 32 (to21_1.header + to21_1.len))).toNat)) = .ok () ∧ ∃ tb7_1, derElement 1 (memBytes M0 ((((cur) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (to21_1.header + to21_1.len))) (((BitVec.ofNat 32 tl10_1.len) - BitVec.ofNat 32 (to21_1.header + to21_1.len))).toNat) = .ok tb7_1 ∧ ∃ vp14_1 vl14_1, derContent (((((cur) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (to21_1.header + to21_1.len))) + BitVec.ofNat 32 (tb7_1.header + tb7_1.len)) (derElement 4 (memBytes M0 (((((cur) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (to21_1.header + to21_1.len))) + BitVec.ofNat 32 (tb7_1.header + tb7_1.len)) ((((BitVec.ofNat 32 tl10_1.len) - BitVec.ofNat 32 (to21_1.header + to21_1.len))) - BitVec.ofNat 32 (tb7_1.header + tb7_1.len)).toNat)) = .ok (vp14_1, vl14_1) ∧ ∃ te14_1, derElement 4 (memBytes M0 (((((cur) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (to21_1.header + to21_1.len))) + BitVec.ofNat 32 (tb7_1.header + tb7_1.len)) ((((BitVec.ofNat 32 tl10_1.len) - BitVec.ofNat 32 (to21_1.header + to21_1.len))) - BitVec.ofNat 32 (tb7_1.header + tb7_1.len)).toNat) = .ok te14_1 ∧ (((((BitVec.ofNat 32 tl10_1.len) - BitVec.ofNat 32 (to21_1.header + to21_1.len))) - BitVec.ofNat 32 (tb7_1.header + tb7_1.len)) - BitVec.ofNat 32 (te14_1.header + te14_1.len) = 0) ∧ listsOidOf M0 p0 (L.toNat - rem.toNat) (memBytes M0 op21_1 ol21_1.toNat) = .ok false ∧ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress)) 3 = memBytes M0 op21_1 ol21_1.toNat ∨ memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x3)) 3 = memBytes M0 op21_1 ol21_1.toNat ∨ memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x6)) 3 = memBytes M0 op21_1 ol21_1.toNat ∨ memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x9)) 3 = memBytes M0 op21_1 ol21_1.toNat) ∧ x2_w34_2 = vl14_1 ∧ x2_w38_2 = vp14_1) ∨ ((¬ (((BitVec.ofNat 32 tl10_1.len) - BitVec.ofNat 32 (to21_1.header + to21_1.len)) = 0)) ∧ (¬ (M0 (((cur) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (to21_1.header + to21_1.len)) = BitVec.ofNat 8 1)) ∧ ∃ vp8 vl8, derContent ((((cur) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (to21_1.header + to21_1.len))) (derElement 4 (memBytes M0 ((((cur) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (to21_1.header + to21_1.len))) (((BitVec.ofNat 32 tl10_1.len) - BitVec.ofNat 32 (to21_1.header + to21_1.len))).toNat)) = .ok (vp8, vl8) ∧ ∃ te8, derElement 4 (memBytes M0 ((((cur) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (to21_1.header + to21_1.len))) (((BitVec.ofNat 32 tl10_1.len) - BitVec.ofNat 32 (to21_1.header + to21_1.len))).toNat) = .ok te8 ∧ ((((BitVec.ofNat 32 tl10_1.len) - BitVec.ofNat 32 (to21_1.header + to21_1.len))) - BitVec.ofNat 32 (te8.header + te8.len) = 0) ∧ listsOidOf M0 p0 (L.toNat - rem.toNat) (memBytes M0 op21_1 ol21_1.toNat) = .ok false ∧ x2_w34_2 = vl8 ∧ x2_w38_2 = vp8)) ∧ SvIn B x2_w38_2 x2_w34_2.toNat ∧
      ∃ d_w2c_3 : Word, ∃ d_w30_3 : Word, ∃ d_w80_3 : Word, ∃ d_w84_3 : Word, ∃ d_w88_3 : Word, ∃ d_w8c_3 : Word, ∃ d_w90_3 : Word, ∃ d_w94_3 : Word, ∃ d_w98_3 : Word, ∃ d_w9c_3 : Word, ∃ d_wa0_3 : Word, ∃ d_wa4_3 : Word, (((memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress)) 3) ∧ ∃ tl15_1, derElement 0x3 (memBytes M0 (x2_w38_2) (x2_w34_2).toNat) = .ok tl15_1 ∧ (2 ≤ (BitVec.ofNat 32 tl15_1.len).toNat) ∧ (BitVec.ofNat 32 (kuUnused (M0 (((((x2_w38_2) + BitVec.ofNat 32 tl15_1.header)) + ((BitVec.ofNat 32 tl15_1.len))) + BitVec.ofNat 32 0xFFFFFFFF))) = (M0 ((x2_w38_2) + BitVec.ofNat 32 tl15_1.header)).zeroExtend 32) ∧ (((x2_w34_2) - BitVec.ofNat 32 (tl15_1.header + tl15_1.len)) = 0) ∧ (¬ (M0 (((x2_w38_2) + BitVec.ofNat 32 tl15_1.header) + 0x1)).toNat < 0x80) ∧ d_w2c_3 = f2c ∧ d_w30_3 = BitVec.ofNat 32 0x1 ∧ d_w80_3 = sl0 ∧ d_w84_3 = sl1 ∧ d_w88_3 = sl2 ∧ d_w8c_3 = sl3 ∧ d_w90_3 = sl4 ∧ d_w94_3 = sl5 ∧ d_w98_3 = sl6 ∧ d_w9c_3 = sl7 ∧ d_wa0_3 = sl8 ∧ d_wa4_3 = sl9) ∨ ((¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress)) 3)) ∧ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x9)) 3) ∧ ∃ tl21_1, derElement 0x30 (memBytes M0 (x2_w38_2) (x2_w34_2).toNat) = .ok tl21_1 ∧ ((x2_w34_2) - BitVec.ofNat 32 (tl21_1.header + tl21_1.len) = 0) ∧ ∃ k_2 cp'_2 cl'_2 found'_2, svChain (sv_ekuStep B out bp tbp dg rootp ll sgp kp sgl tbl f2c f30 0 p0 L ((cur) + BitVec.ofNat 32 (tl10_1.header + tl10_1.len)) sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 sl9 w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c ((rem) - BitVec.ofNat 32 (tl10_1.header + tl10_1.len)) v M0) k_2 (((x2_w38_2) + BitVec.ofNat 32 tl21_1.header), (BitVec.ofNat 32 tl21_1.len), (BitVec.ofNat 32 0x0)) (cp'_2, cl'_2, found'_2) ∧ cl'_2 = 0 ∧ (found'_2 &&& BitVec.ofNat 32 0x1 ≠ 0) ∧ d_w2c_3 = BitVec.ofNat 32 0x1 ∧ d_w30_3 = f30 ∧ d_w80_3 = sl0 ∧ d_w84_3 = sl1 ∧ d_w88_3 = sl2 ∧ d_w8c_3 = sl3 ∧ d_w90_3 = sl4 ∧ d_w94_3 = sl5 ∧ d_w98_3 = sl6 ∧ d_w9c_3 = sl7 ∧ d_wa0_3 = sl8 ∧ d_wa4_3 = sl9) ∨ ((¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress)) 3)) ∧ (¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x9)) 3)) ∧ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x6)) 3) ∧ ∃ tl27_1, derElement 0x30 (memBytes M0 (x2_w38_2) (x2_w34_2).toNat) = .ok tl27_1 ∧ ((x2_w34_2) - BitVec.ofNat 32 (tl27_1.header + tl27_1.len) = 0) ∧ ((((BitVec.ofNat 32 tl27_1.len) = 0)) ∨ ((¬ ((BitVec.ofNat 32 tl27_1.len) = 0)) ∧ (M0 ((x2_w38_2) + BitVec.ofNat 32 tl27_1.header) ≠ BitVec.ofNat 8 1) ∧ (M0 ((x2_w38_2) + BitVec.ofNat 32 tl27_1.header) = BitVec.ofNat 8 2) ∧ ∃ ip10 il10, derIntOf (memBytes M0 (((x2_w38_2) + BitVec.ofNat 32 tl27_1.header)) ((BitVec.ofNat 32 tl27_1.len)).toNat) (((x2_w38_2) + BitVec.ofNat 32 tl27_1.header)) (derElement 2 (memBytes M0 (((x2_w38_2) + BitVec.ofNat 32 tl27_1.header)) ((BitVec.ofNat 32 tl27_1.len)).toNat)) = .ok (ip10, il10) ∧ ∃ ti10, derElement 2 (memBytes M0 (((x2_w38_2) + BitVec.ofNat 32 tl27_1.header)) ((BitVec.ofNat 32 tl27_1.len)).toNat) = .ok ti10 ∧ (((BitVec.ofNat 32 tl27_1.len)) - BitVec.ofNat 32 (ti10.header + ti10.len) = 0))) ∧ d_w2c_3 = f2c ∧ d_w30_3 = f30 ∧ d_w80_3 = sl0 ∧ d_w84_3 = sl1 ∧ d_w88_3 = sl2 ∧ d_w8c_3 = sl3 ∧ d_w90_3 = sl4 ∧ d_w94_3 = sl5 ∧ d_w98_3 = sl6 ∧ d_w9c_3 = sl7 ∧ d_wa0_3 = sl8 ∧ d_wa4_3 = sl9) ∨ ((¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress)) 3)) ∧ (¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x9)) 3)) ∧ (¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x6)) 3)) ∧ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x2D)) 10 = memBytes M0 op21_1 ol21_1.toNat) ∧ ∃ tl43, derTlv (memBytes M0 (x2_w38_2) (x2_w34_2).toNat) = .ok tl43 ∧ (BitVec.ofNat 8 tl43.tag = BitVec.ofNat 8 0xC) ∧ ((x2_w34_2) - BitVec.ofNat 32 (tl43.header + tl43.len) = 0) ∧ d_w2c_3 = f2c ∧ d_w30_3 = f30 ∧ d_w80_3 = (x2_w38_2) + BitVec.ofNat 32 tl43.header ∧ d_w84_3 = BitVec.ofNat 32 tl43.len ∧ d_w88_3 = sl2 ∧ d_w8c_3 = sl3 ∧ d_w90_3 = sl4 ∧ d_w94_3 = sl5 ∧ d_w98_3 = sl6 ∧ d_w9c_3 = sl7 ∧ d_wa0_3 = sl8 ∧ d_wa4_3 = sl9) ∨ ((¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress)) 3)) ∧ (¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x9)) 3)) ∧ (¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x6)) 3)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x2D)) 10 = memBytes M0 op21_1 ol21_1.toNat)) ∧ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x37)) 10 = memBytes M0 op21_1 ol21_1.toNat) ∧ ∃ tl56, derTlv (memBytes M0 (x2_w38_2) (x2_w34_2).toNat) = .ok tl56 ∧ (BitVec.ofNat 8 tl56.tag = BitVec.ofNat 8 0xC) ∧ ((x2_w34_2) - BitVec.ofNat 32 (tl56.header + tl56.len) = 0) ∧ d_w2c_3 = f2c ∧ d_w30_3 = f30 ∧ d_w80_3 = sl0 ∧ d_w84_3 = sl1 ∧ d_w88_3 = (x2_w38_2) + BitVec.ofNat 32 tl56.header ∧ d_w8c_3 = BitVec.ofNat 32 tl56.len ∧ d_w90_3 = sl4 ∧ d_w94_3 = sl5 ∧ d_w98_3 = sl6 ∧ d_w9c_3 = sl7 ∧ d_wa0_3 = sl8 ∧ d_wa4_3 = sl9) ∨ ((¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress)) 3)) ∧ (¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x9)) 3)) ∧ (¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x6)) 3)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x2D)) 10 = memBytes M0 op21_1 ol21_1.toNat)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x37)) 10 = memBytes M0 op21_1 ol21_1.toNat)) ∧ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x41)) 10 = memBytes M0 op21_1 ol21_1.toNat) ∧ ∃ tl69, derTlv (memBytes M0 (x2_w38_2) (x2_w34_2).toNat) = .ok tl69 ∧ (BitVec.ofNat 8 tl69.tag = BitVec.ofNat 8 0xC) ∧ ((x2_w34_2) - BitVec.ofNat 32 (tl69.header + tl69.len) = 0) ∧ d_w2c_3 = f2c ∧ d_w30_3 = f30 ∧ d_w80_3 = sl0 ∧ d_w84_3 = sl1 ∧ d_w88_3 = sl2 ∧ d_w8c_3 = sl3 ∧ d_w90_3 = (x2_w38_2) + BitVec.ofNat 32 tl69.header ∧ d_w94_3 = BitVec.ofNat 32 tl69.len ∧ d_w98_3 = sl6 ∧ d_w9c_3 = sl7 ∧ d_wa0_3 = sl8 ∧ d_wa4_3 = sl9) ∨ ((¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress)) 3)) ∧ (¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x9)) 3)) ∧ (¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x6)) 3)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x2D)) 10 = memBytes M0 op21_1 ol21_1.toNat)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x37)) 10 = memBytes M0 op21_1 ol21_1.toNat)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x41)) 10 = memBytes M0 op21_1 ol21_1.toNat)) ∧ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x4B)) 10 = memBytes M0 op21_1 ol21_1.toNat) ∧ ∃ tl82, derTlv (memBytes M0 (x2_w38_2) (x2_w34_2).toNat) = .ok tl82 ∧ (BitVec.ofNat 8 tl82.tag = BitVec.ofNat 8 0xC) ∧ ((x2_w34_2) - BitVec.ofNat 32 (tl82.header + tl82.len) = 0) ∧ d_w2c_3 = f2c ∧ d_w30_3 = f30 ∧ d_w80_3 = sl0 ∧ d_w84_3 = sl1 ∧ d_w88_3 = sl2 ∧ d_w8c_3 = sl3 ∧ d_w90_3 = sl4 ∧ d_w94_3 = sl5 ∧ d_w98_3 = (x2_w38_2) + BitVec.ofNat 32 tl82.header ∧ d_w9c_3 = BitVec.ofNat 32 tl82.len ∧ d_wa0_3 = sl8 ∧ d_wa4_3 = sl9) ∨ ((¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress)) 3)) ∧ (¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x9)) 3)) ∧ (¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x6)) 3)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x2D)) 10 = memBytes M0 op21_1 ol21_1.toNat)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x37)) 10 = memBytes M0 op21_1 ol21_1.toNat)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x41)) 10 = memBytes M0 op21_1 ol21_1.toNat)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x4B)) 10 = memBytes M0 op21_1 ol21_1.toNat)) ∧ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x55)) 10 = memBytes M0 op21_1 ol21_1.toNat) ∧ ∃ tl95, derTlv (memBytes M0 (x2_w38_2) (x2_w34_2).toNat) = .ok tl95 ∧ (BitVec.ofNat 8 tl95.tag = BitVec.ofNat 8 0xC) ∧ ((x2_w34_2) - BitVec.ofNat 32 (tl95.header + tl95.len) = 0) ∧ d_w2c_3 = f2c ∧ d_w30_3 = f30 ∧ d_w80_3 = sl0 ∧ d_w84_3 = sl1 ∧ d_w88_3 = sl2 ∧ d_w8c_3 = sl3 ∧ d_w90_3 = sl4 ∧ d_w94_3 = sl5 ∧ d_w98_3 = sl6 ∧ d_w9c_3 = sl7 ∧ d_wa0_3 = (x2_w38_2) + BitVec.ofNat 32 tl95.header ∧ d_wa4_3 = BitVec.ofNat 32 tl95.len) ∨ ((¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress)) 3)) ∧ (¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x9)) 3)) ∧ (¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x6)) 3)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x2D)) 10 = memBytes M0 op21_1 ol21_1.toNat)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x37)) 10 = memBytes M0 op21_1 ol21_1.toNat)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x41)) 10 = memBytes M0 op21_1 ol21_1.toNat)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x4B)) 10 = memBytes M0 op21_1 ol21_1.toNat)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x55)) 10 = memBytes M0 op21_1 ol21_1.toNat)) ∧ d_w2c_3 = f2c ∧ d_w30_3 = f30 ∧ d_w80_3 = sl0 ∧ d_w84_3 = sl1 ∧ d_w88_3 = sl2 ∧ d_w8c_3 = sl3 ∧ d_w90_3 = sl4 ∧ d_w94_3 = sl5 ∧ d_w98_3 = sl6 ∧ d_w9c_3 = sl7 ∧ d_wa0_3 = sl8 ∧ d_wa4_3 = sl9)) ∧ (d_w80_3 = 0 ∨ SvIn B d_w80_3 d_w84_3.toNat) ∧ (d_w88_3 = 0 ∨ SvIn B d_w88_3 d_w8c_3.toNat) ∧ (d_w90_3 = 0 ∨ SvIn B d_w90_3 d_w94_3.toNat) ∧ (d_w98_3 = 0 ∨ SvIn B d_w98_3 d_w9c_3.toNat) ∧ (d_wa0_3 = 0 ∨ SvIn B d_wa0_3 d_wa4_3.toNat) ∧
    ∃ n', Steps n0 n' ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        St n'.mem SV n' 0x3B8 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (8 : Fin 32) = BitVec.ofNat 32 0x15 ∧
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
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = d_w2c_3 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = d_w30_3 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = ((rem) - BitVec.ofNat 32 (tl10_1.header + tl10_1.len)) ∧
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
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = d_w80_3 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = d_w84_3 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = d_w88_3 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = d_w8c_3 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = d_w90_3 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = d_w94_3 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = d_w98_3 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = d_w9c_3 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = d_wa0_3 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = d_wa4_3 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = ((cur) + BitVec.ofNat 32 (tl10_1.header + tl10_1.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = ((rem) - BitVec.ofNat 32 (tl10_1.header + tl10_1.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol21_1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op21_1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (cur) + BitVec.ofNat 32 tl10_1.header ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = x2_w34_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = x2_w38_2 ∧
        SvKeepL B n0.mem n'.mem [(0x40, 0x4), (0x3C, 0x4), (0x420, 0x10), (0x158, 0x8), (0x44, 0x4), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1), (0x420, 0x8), (0x408, 0x8), (0x4C, 0x4), (0x48, 0x4), (0x38, 0x4), (0x34, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8), (0x30, 0x4), (0x1FC, 0x4), (0x200, 0x4), (0x204, 0x4), (0x208, 0x4), (0x204, 0x8), (0x385, 0xB), (0x384, 0x1), (0x2C, 0x4), (0x80, 0x4), (0x84, 0x4), (0x88, 0x4), (0x8C, 0x4), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4), (0x9C, 0x4), (0xA0, 0x4), (0xA4, 0x4)]) := by
  rcases sv_x1 FW E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_9 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_27 w0_2c w0_30 w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_150 w0_154 w0_158 w0_15c xl_in ea_in hrem with ⟨-, e⟩ | hx1
  · exact .inl e
  obtain ⟨x1_0, hx1⟩ := hx1
  obtain ⟨tl10_1, hx1⟩ := hx1
  obtain ⟨x1_1, hx1⟩ := hx1
  obtain ⟨op21_1, hx1⟩ := hx1
  obtain ⟨ol21_1, hx1⟩ := hx1
  obtain ⟨x1_2, hx1⟩ := hx1
  obtain ⟨to21_1, hx1⟩ := hx1
  obtain ⟨x1_3, hx1⟩ := hx1
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
  obtain ⟨r1_a0, hx1⟩ := hx1
  obtain ⟨r1_a1, hx1⟩ := hx1
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
  obtain ⟨w1_3c, hx1⟩ := hx1
  obtain ⟨w1_40, hx1⟩ := hx1
  obtain ⟨w1_44, hx1⟩ := hx1
  obtain ⟨w1_48, hx1⟩ := hx1
  obtain ⟨w1_4c, hx1⟩ := hx1
  obtain ⟨w1_50, hx1⟩ := hx1
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
  obtain ⟨w1_400, hx1⟩ := hx1
  obtain ⟨w1_408, hx1⟩ := hx1
  obtain ⟨w1_40c, hx1⟩ := hx1
  have K1_L := hx1
  rcases sv_x2 FW E1 V1 hret hO s1 M0 fR1 r1_2 r1_8 r1_9 r1_a0 r1_a1 r1_18 r1_19 r1_20 r1_21 r1_22 r1_23 r1_24 r1_25 r1_27 w1_2c w1_30 w1_50 w1_54 w1_58 w1_5c w1_60 w1_64 w1_68 w1_6c w1_70 w1_74 w1_78 w1_7c w1_80 w1_84 w1_88 w1_8c w1_90 w1_94 w1_98 w1_9c w1_a0 w1_a4 w1_150 w1_154 w1_3c w1_40 w1_48 w1_4c w1_158 w1_15c w1_408 w1_40c ((((xl_in).content x1_1).ofNatLen).restW (derOid_ok_elem x1_3)) ((((xl_in).content x1_1).ofNatLen).oidIn x1_2) ea_in x1_0 SD0 with e | hx2
  · exact .inl (SvErrRet.pre (c1) (by rw [r1_3]) (by rw [r1_4])
      (fun x hx => (fR1 x hx).trans (fM x hx).symm) e)
  obtain ⟨x2_w34_2, hx2⟩ := hx2
  obtain ⟨x2_w38_2, hx2⟩ := hx2
  obtain ⟨x2_0, hx2⟩ := hx2
  obtain ⟨x2_1, hx2⟩ := hx2
  obtain ⟨n2, hx2⟩ := hx2
  obtain ⟨c2, hx2⟩ := hx2
  obtain ⟨fR2, hx2⟩ := hx2
  obtain ⟨s2, hx2⟩ := hx2
  obtain ⟨E2, hx2⟩ := hx2
  obtain ⟨V2, hx2⟩ := hx2
  obtain ⟨r2_3, hx2⟩ := hx2
  obtain ⟨r2_4, hx2⟩ := hx2
  obtain ⟨r2_2, hx2⟩ := hx2
  obtain ⟨r2_8, hx2⟩ := hx2
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
  obtain ⟨w2_34, hx2⟩ := hx2
  obtain ⟨w2_38, hx2⟩ := hx2
  obtain ⟨w2_44, hx2⟩ := hx2
  obtain ⟨w2_48, hx2⟩ := hx2
  obtain ⟨w2_4c, hx2⟩ := hx2
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
  obtain ⟨w2_3c, hx2⟩ := hx2
  obtain ⟨w2_40, hx2⟩ := hx2
  have K2_L := hx2
  rcases sv_d (rem := 0) FW E2 V2 hret hO s2 M0 fR2 r2_2 r2_8 r2_9 r2_18 r2_19 r2_20 r2_21 r2_22 r2_23 r2_24 r2_25 r2_27 w2_2c w2_30 w2_54 w2_58 w2_5c w2_60 w2_64 w2_68 w2_6c w2_70 w2_74 w2_78 w2_7c w2_80 w2_84 w2_88 w2_8c w2_90 w2_94 w2_98 w2_9c w2_a0 w2_a4 w2_150 w2_154 w2_34 w2_38 w2_48 w2_4c w2_158 w2_15c w2_44 x2_1 ((((xl_in).content x1_1).ofNatLen).oidIn x1_2) SD0 sl0_or0 sl2_or0 sl4_or0 sl6_or0 sl8_or0 with e | hx3
  · exact .inl (SvErrRet.pre (c1.trans (c2)) (by rw [r2_3, r1_3]) (by rw [r2_4, r1_4])
      (fun x hx => (fR2 x hx).trans (fM x hx).symm) e)
  obtain ⟨d_w2c_3, hx3⟩ := hx3
  obtain ⟨d_w30_3, hx3⟩ := hx3
  obtain ⟨d_w80_3, hx3⟩ := hx3
  obtain ⟨d_w84_3, hx3⟩ := hx3
  obtain ⟨d_w88_3, hx3⟩ := hx3
  obtain ⟨d_w8c_3, hx3⟩ := hx3
  obtain ⟨d_w90_3, hx3⟩ := hx3
  obtain ⟨d_w94_3, hx3⟩ := hx3
  obtain ⟨d_w98_3, hx3⟩ := hx3
  obtain ⟨d_w9c_3, hx3⟩ := hx3
  obtain ⟨d_wa0_3, hx3⟩ := hx3
  obtain ⟨d_wa4_3, hx3⟩ := hx3
  obtain ⟨x3_0, hx3⟩ := hx3
  obtain ⟨x3_1, hx3⟩ := hx3
  obtain ⟨x3_2, hx3⟩ := hx3
  obtain ⟨x3_3, hx3⟩ := hx3
  obtain ⟨x3_4, hx3⟩ := hx3
  obtain ⟨x3_5, hx3⟩ := hx3
  obtain ⟨n3, hx3⟩ := hx3
  obtain ⟨c3, hx3⟩ := hx3
  obtain ⟨fR3, hx3⟩ := hx3
  obtain ⟨s3, hx3⟩ := hx3
  obtain ⟨E3, hx3⟩ := hx3
  obtain ⟨V3, hx3⟩ := hx3
  obtain ⟨r3_3, hx3⟩ := hx3
  obtain ⟨r3_4, hx3⟩ := hx3
  obtain ⟨r3_2, hx3⟩ := hx3
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
  obtain ⟨r3_27, hx3⟩ := hx3
  obtain ⟨w3_2c, hx3⟩ := hx3
  obtain ⟨w3_30, hx3⟩ := hx3
  obtain ⟨w3_50, hx3⟩ := hx3
  obtain ⟨w3_54, hx3⟩ := hx3
  obtain ⟨w3_58, hx3⟩ := hx3
  obtain ⟨w3_5c, hx3⟩ := hx3
  obtain ⟨w3_60, hx3⟩ := hx3
  obtain ⟨w3_64, hx3⟩ := hx3
  obtain ⟨w3_68, hx3⟩ := hx3
  obtain ⟨w3_6c, hx3⟩ := hx3
  obtain ⟨w3_70, hx3⟩ := hx3
  obtain ⟨w3_74, hx3⟩ := hx3
  obtain ⟨w3_78, hx3⟩ := hx3
  obtain ⟨w3_7c, hx3⟩ := hx3
  obtain ⟨w3_80, hx3⟩ := hx3
  obtain ⟨w3_84, hx3⟩ := hx3
  obtain ⟨w3_88, hx3⟩ := hx3
  obtain ⟨w3_8c, hx3⟩ := hx3
  obtain ⟨w3_90, hx3⟩ := hx3
  obtain ⟨w3_94, hx3⟩ := hx3
  obtain ⟨w3_98, hx3⟩ := hx3
  obtain ⟨w3_9c, hx3⟩ := hx3
  obtain ⟨w3_a0, hx3⟩ := hx3
  obtain ⟨w3_a4, hx3⟩ := hx3
  obtain ⟨w3_150, hx3⟩ := hx3
  obtain ⟨w3_154, hx3⟩ := hx3
  obtain ⟨w3_158, hx3⟩ := hx3
  obtain ⟨w3_15c, hx3⟩ := hx3
  have K3_L := hx3
  exact .inr ⟨x1_0, tl10_1, x1_1, op21_1, ol21_1, x1_2, to21_1, x1_3, x2_w34_2, x2_w38_2, x2_0, x2_1, d_w2c_3, d_w30_3, d_w80_3, d_w84_3, d_w88_3, d_w8c_3, d_w90_3, d_w94_3, d_w98_3, d_w9c_3, d_wa0_3, d_wa4_3, x3_0, x3_1, x3_2, x3_3, x3_4, x3_5, n3, c1.trans (c2.trans (c3)), fR3, s3, E3, V3,
    by rw [r3_3, r2_3, r1_3], by rw [r3_4, r2_4, r1_4], r3_2, r3_8, r3_9, r3_18, r3_19, r3_20, r3_21, r3_22, r3_23, r3_24, r3_25, r3_27, w3_2c, w3_30, w3_50, w3_54, w3_58, w3_5c, w3_60, w3_64, w3_68, w3_6c, w3_70, w3_74, w3_78, w3_7c, w3_80, w3_84, w3_88, w3_8c, w3_90, w3_94, w3_98, w3_9c, w3_a0, w3_a4, w3_150, w3_154, w3_158, w3_15c, ((K3_L.w32 (by decide) (by decide)).trans w2_3c), ((K3_L.w32 (by decide) (by decide)).trans w2_40), ((K3_L.w32 (by decide) (by decide)).trans w2_44), ((K3_L.w32 (by decide) (by decide)).trans w2_48), ((K3_L.w32 (by decide) (by decide)).trans w2_4c), ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_400)), ((K3_L.w32 (by decide) (by decide)).trans w2_34), ((K3_L.w32 (by decide) (by decide)).trans w2_38), (((K1_L).trans K2_L).trans K3_L).mono (by decide)⟩

end C3.RV32.Sv
