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
/-- **One extension of the leaf**: from the extensions loop's head at 0x4EA back to it, `sv_x1`, `sv_x2`, and `sv_d`. -/
theorem sv_seg_ext {B out bp x9 x21 x25 x26 f30 f34 rem p0 L cur sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 sl9 w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c w80 w84 : Word} {v : Nat → Word} {n0 : Machine}
    (F : Fr B 0x3830)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out)
    (s0 : St n0.mem SV n0 0x4EA (reg n0))
    (M0 : Word → BitVec 8)
    (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_9 : reg n0 (9 : Fin 32) = x9)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_25 : reg n0 (25 : Fin 32) = x25)
    (g0_26 : reg n0 (26 : Fin 32) = x26)
    (g0_27 : reg n0 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20)
    (w0_30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30)
    (w0_34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34)
    (w0_40 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem)
    (w0_4c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c)
    (w0_50 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50)
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
    (w0_80 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80)
    (w0_84 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84)
    (w0_88 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0)
    (w0_8c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L)
    (w0_90 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur)
    (w0_94 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem)
    (w0_a20 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0)
    (w0_a24 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1)
    (w0_a28 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2)
    (w0_a2c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3)
    (w0_a30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4)
    (w0_a34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5)
    (w0_a38 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6)
    (w0_a3c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7)
    (w0_a40 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8)
    (w0_a44 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9)
    (xl_in : SvIn B (cur) (rem).toNat)
    (ea_in : SvIn B p0 (L.toNat - rem.toNat))
    (hrem : rem ≠ 0)
    (SD0 : SvData M0) :
    SvErrRet B out v n0 ∨
    ((rem.toNat ≤ L.toNat) ∧
      ∃ tl8_1, derElement 0x30 (memBytes M0 (cur) (rem).toNat) = .ok tl8_1 ∧
      ∃ op19_1 ol19_1, derContent ((cur) + BitVec.ofNat 32 tl8_1.header) (derOid (memBytes M0 ((cur) + BitVec.ofNat 32 tl8_1.header) (BitVec.ofNat 32 tl8_1.len).toNat)) = .ok (op19_1, ol19_1) ∧
      ∃ to19_1, derOid (memBytes M0 ((cur) + BitVec.ofNat 32 tl8_1.header) (BitVec.ofNat 32 tl8_1.len).toNat) = .ok to19_1 ∧
      ∃ x2_w38_2 : Word, ∃ x2_w3c_2 : Word, ((False) ∨ (derBoolOf (memBytes M0 ((((cur) + BitVec.ofNat 32 tl8_1.header) + BitVec.ofNat 32 (to19_1.header + to19_1.len))) (((BitVec.ofNat 32 tl8_1.len) - BitVec.ofNat 32 (to19_1.header + to19_1.len))).toNat) (derElement 1 (memBytes M0 ((((cur) + BitVec.ofNat 32 tl8_1.header) + BitVec.ofNat 32 (to19_1.header + to19_1.len))) (((BitVec.ofNat 32 tl8_1.len) - BitVec.ofNat 32 (to19_1.header + to19_1.len))).toNat)) = .ok () ∧ ∃ tb7, derElement 1 (memBytes M0 ((((cur) + BitVec.ofNat 32 tl8_1.header) + BitVec.ofNat 32 (to19_1.header + to19_1.len))) (((BitVec.ofNat 32 tl8_1.len) - BitVec.ofNat 32 (to19_1.header + to19_1.len))).toNat) = .ok tb7 ∧ ∃ vp14 vl14, derContent (((((cur) + BitVec.ofNat 32 tl8_1.header) + BitVec.ofNat 32 (to19_1.header + to19_1.len))) + BitVec.ofNat 32 (tb7.header + tb7.len)) (derElement 4 (memBytes M0 (((((cur) + BitVec.ofNat 32 tl8_1.header) + BitVec.ofNat 32 (to19_1.header + to19_1.len))) + BitVec.ofNat 32 (tb7.header + tb7.len)) ((((BitVec.ofNat 32 tl8_1.len) - BitVec.ofNat 32 (to19_1.header + to19_1.len))) - BitVec.ofNat 32 (tb7.header + tb7.len)).toNat)) = .ok (vp14, vl14) ∧ ∃ te14, derElement 4 (memBytes M0 (((((cur) + BitVec.ofNat 32 tl8_1.header) + BitVec.ofNat 32 (to19_1.header + to19_1.len))) + BitVec.ofNat 32 (tb7.header + tb7.len)) ((((BitVec.ofNat 32 tl8_1.len) - BitVec.ofNat 32 (to19_1.header + to19_1.len))) - BitVec.ofNat 32 (tb7.header + tb7.len)).toNat) = .ok te14 ∧ (((((BitVec.ofNat 32 tl8_1.len) - BitVec.ofNat 32 (to19_1.header + to19_1.len))) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) = 0) ∧ listsOidOf M0 p0 (L.toNat - rem.toNat) (memBytes M0 op19_1 ol19_1.toNat) = .ok false ∧ (memBytes M0 (BitVec.ofNat 32 0x3FCC4889) 3 = memBytes M0 op19_1 ol19_1.toNat ∨ memBytes M0 (BitVec.ofNat 32 0x3FCC488C) 3 = memBytes M0 op19_1 ol19_1.toNat ∨ memBytes M0 (BitVec.ofNat 32 0x3FCC488F) 3 = memBytes M0 op19_1 ol19_1.toNat ∨ memBytes M0 (BitVec.ofNat 32 0x3FCC4892) 3 = memBytes M0 op19_1 ol19_1.toNat) ∧ x2_w38_2 = vl14 ∧ x2_w3c_2 = vp14) ∨ (∃ vp8 vl8, derContent ((((cur) + BitVec.ofNat 32 tl8_1.header) + BitVec.ofNat 32 (to19_1.header + to19_1.len))) (derElement 4 (memBytes M0 ((((cur) + BitVec.ofNat 32 tl8_1.header) + BitVec.ofNat 32 (to19_1.header + to19_1.len))) (((BitVec.ofNat 32 tl8_1.len) - BitVec.ofNat 32 (to19_1.header + to19_1.len))).toNat)) = .ok (vp8, vl8) ∧ ∃ te8, derElement 4 (memBytes M0 ((((cur) + BitVec.ofNat 32 tl8_1.header) + BitVec.ofNat 32 (to19_1.header + to19_1.len))) (((BitVec.ofNat 32 tl8_1.len) - BitVec.ofNat 32 (to19_1.header + to19_1.len))).toNat) = .ok te8 ∧ ((((BitVec.ofNat 32 tl8_1.len) - BitVec.ofNat 32 (to19_1.header + to19_1.len))) - BitVec.ofNat 32 (te8.header + te8.len) = 0) ∧ listsOidOf M0 p0 (L.toNat - rem.toNat) (memBytes M0 op19_1 ol19_1.toNat) = .ok false ∧ x2_w38_2 = vl8 ∧ x2_w3c_2 = vp8)) ∧ SvIn B x2_w3c_2 x2_w38_2.toNat ∧
      ∃ d_w30_3 : Word, ∃ d_w34_3 : Word, ∃ d_wa20_3 : Word, ∃ d_wa24_3 : Word, ∃ d_wa28_3 : Word, ∃ d_wa2c_3 : Word, ∃ d_wa30_3 : Word, ∃ d_wa34_3 : Word, ∃ d_wa38_3 : Word, ∃ d_wa3c_3 : Word, ∃ d_wa40_3 : Word, ∃ d_wa44_3 : Word, ((∃ tl16_1, derElement 0x3 (memBytes M0 (x2_w3c_2) (x2_w38_2).toNat) = .ok tl16_1 ∧ (2 ≤ (BitVec.ofNat 32 tl16_1.len).toNat) ∧ (BitVec.ofNat 32 (kuUnused (M0 (((((x2_w3c_2) + BitVec.ofNat 32 tl16_1.header)) + ((BitVec.ofNat 32 tl16_1.len))) + BitVec.ofNat 32 0xFFFFFFFF))) = (M0 ((x2_w3c_2) + BitVec.ofNat 32 tl16_1.header)).zeroExtend 32) ∧ (((x2_w38_2) - BitVec.ofNat 32 (tl16_1.header + tl16_1.len)) = 0) ∧ (¬ (M0 (((x2_w3c_2) + BitVec.ofNat 32 tl16_1.header) + 0x1)).toNat < 0x80) ∧ d_w30_3 = f30 ∧ d_w34_3 = BitVec.ofNat 32 0x1 ∧ d_wa20_3 = sl0 ∧ d_wa24_3 = sl1 ∧ d_wa28_3 = sl2 ∧ d_wa2c_3 = sl3 ∧ d_wa30_3 = sl4 ∧ d_wa34_3 = sl5 ∧ d_wa38_3 = sl6 ∧ d_wa3c_3 = sl7 ∧ d_wa40_3 = sl8 ∧ d_wa44_3 = sl9) ∨ (∃ tl19_1, derElement 0x30 (memBytes M0 (x2_w3c_2) (x2_w38_2).toNat) = .ok tl19_1 ∧ ((x2_w38_2) - BitVec.ofNat 32 (tl19_1.header + tl19_1.len) = 0) ∧ ∃ k_2 found'_2 cp'_2 cl'_2, svChain (sv_ekuStep B out bp x9 x21 x25 x26 f30 f34 rem p0 L ((cur) + BitVec.ofNat 32 (tl8_1.header + tl8_1.len)) sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 sl9 w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c w80 w84 ((rem) - BitVec.ofNat 32 (tl8_1.header + tl8_1.len)) v M0) k_2 ((BitVec.ofNat 32 0x0), ((x2_w3c_2) + BitVec.ofNat 32 tl19_1.header), (BitVec.ofNat 32 tl19_1.len)) (found'_2, cp'_2, cl'_2) ∧ cl'_2 = 0 ∧ (found'_2 &&& BitVec.ofNat 32 0x1 ≠ 0) ∧ d_w30_3 = BitVec.ofNat 32 0x1 ∧ d_w34_3 = f34 ∧ d_wa20_3 = sl0 ∧ d_wa24_3 = sl1 ∧ d_wa28_3 = sl2 ∧ d_wa2c_3 = sl3 ∧ d_wa30_3 = sl4 ∧ d_wa34_3 = sl5 ∧ d_wa38_3 = sl6 ∧ d_wa3c_3 = sl7 ∧ d_wa40_3 = sl8 ∧ d_wa44_3 = sl9) ∨ (∃ tl24_1, derElement 0x30 (memBytes M0 (x2_w3c_2) (x2_w38_2).toNat) = .ok tl24_1 ∧ ((x2_w38_2) - BitVec.ofNat 32 (tl24_1.header + tl24_1.len) = 0) ∧ ((True) ∨ ((M0 ((x2_w3c_2) + BitVec.ofNat 32 tl24_1.header) ≠ BitVec.ofNat 8 1) ∧ (M0 ((x2_w3c_2) + BitVec.ofNat 32 tl24_1.header) = BitVec.ofNat 8 2) ∧ ∃ ip10 il10, derIntOf (memBytes M0 (((x2_w3c_2) + BitVec.ofNat 32 tl24_1.header)) ((BitVec.ofNat 32 tl24_1.len)).toNat) (((x2_w3c_2) + BitVec.ofNat 32 tl24_1.header)) (derElement 2 (memBytes M0 (((x2_w3c_2) + BitVec.ofNat 32 tl24_1.header)) ((BitVec.ofNat 32 tl24_1.len)).toNat)) = .ok (ip10, il10) ∧ ∃ ti10, derElement 2 (memBytes M0 (((x2_w3c_2) + BitVec.ofNat 32 tl24_1.header)) ((BitVec.ofNat 32 tl24_1.len)).toNat) = .ok ti10 ∧ (((BitVec.ofNat 32 tl24_1.len)) - BitVec.ofNat 32 (ti10.header + ti10.len) = 0))) ∧ d_w30_3 = f30 ∧ d_w34_3 = f34 ∧ d_wa20_3 = sl0 ∧ d_wa24_3 = sl1 ∧ d_wa28_3 = sl2 ∧ d_wa2c_3 = sl3 ∧ d_wa30_3 = sl4 ∧ d_wa34_3 = sl5 ∧ d_wa38_3 = sl6 ∧ d_wa3c_3 = sl7 ∧ d_wa40_3 = sl8 ∧ d_wa44_3 = sl9) ∨ (∃ tl35, derTlv (memBytes M0 (x2_w3c_2) (x2_w38_2).toNat) = .ok tl35 ∧ (BitVec.ofNat 8 tl35.tag = BitVec.ofNat 8 0xC) ∧ ((x2_w38_2) - BitVec.ofNat 32 (tl35.header + tl35.len) = 0) ∧ d_w30_3 = f30 ∧ d_w34_3 = f34 ∧ d_wa20_3 = (x2_w3c_2) + BitVec.ofNat 32 tl35.header ∧ d_wa24_3 = BitVec.ofNat 32 tl35.len ∧ d_wa28_3 = sl2 ∧ d_wa2c_3 = sl3 ∧ d_wa30_3 = sl4 ∧ d_wa34_3 = sl5 ∧ d_wa38_3 = sl6 ∧ d_wa3c_3 = sl7 ∧ d_wa40_3 = sl8 ∧ d_wa44_3 = sl9) ∨ (∃ tl43, derTlv (memBytes M0 (x2_w3c_2) (x2_w38_2).toNat) = .ok tl43 ∧ (BitVec.ofNat 8 tl43.tag = BitVec.ofNat 8 0xC) ∧ ((x2_w38_2) - BitVec.ofNat 32 (tl43.header + tl43.len) = 0) ∧ d_w30_3 = f30 ∧ d_w34_3 = f34 ∧ d_wa20_3 = sl0 ∧ d_wa24_3 = sl1 ∧ d_wa28_3 = (x2_w3c_2) + BitVec.ofNat 32 tl43.header ∧ d_wa2c_3 = BitVec.ofNat 32 tl43.len ∧ d_wa30_3 = sl4 ∧ d_wa34_3 = sl5 ∧ d_wa38_3 = sl6 ∧ d_wa3c_3 = sl7 ∧ d_wa40_3 = sl8 ∧ d_wa44_3 = sl9) ∨ (∃ tl51, derTlv (memBytes M0 (x2_w3c_2) (x2_w38_2).toNat) = .ok tl51 ∧ (BitVec.ofNat 8 tl51.tag = BitVec.ofNat 8 0xC) ∧ ((x2_w38_2) - BitVec.ofNat 32 (tl51.header + tl51.len) = 0) ∧ d_w30_3 = f30 ∧ d_w34_3 = f34 ∧ d_wa20_3 = sl0 ∧ d_wa24_3 = sl1 ∧ d_wa28_3 = sl2 ∧ d_wa2c_3 = sl3 ∧ d_wa30_3 = (x2_w3c_2) + BitVec.ofNat 32 tl51.header ∧ d_wa34_3 = BitVec.ofNat 32 tl51.len ∧ d_wa38_3 = sl6 ∧ d_wa3c_3 = sl7 ∧ d_wa40_3 = sl8 ∧ d_wa44_3 = sl9) ∨ (∃ tl59, derTlv (memBytes M0 (x2_w3c_2) (x2_w38_2).toNat) = .ok tl59 ∧ (BitVec.ofNat 8 tl59.tag = BitVec.ofNat 8 0xC) ∧ ((x2_w38_2) - BitVec.ofNat 32 (tl59.header + tl59.len) = 0) ∧ d_w30_3 = f30 ∧ d_w34_3 = f34 ∧ d_wa20_3 = sl0 ∧ d_wa24_3 = sl1 ∧ d_wa28_3 = sl2 ∧ d_wa2c_3 = sl3 ∧ d_wa30_3 = sl4 ∧ d_wa34_3 = sl5 ∧ d_wa38_3 = (x2_w3c_2) + BitVec.ofNat 32 tl59.header ∧ d_wa3c_3 = BitVec.ofNat 32 tl59.len ∧ d_wa40_3 = sl8 ∧ d_wa44_3 = sl9) ∨ (∃ tl67, derTlv (memBytes M0 (x2_w3c_2) (x2_w38_2).toNat) = .ok tl67 ∧ (BitVec.ofNat 8 tl67.tag = BitVec.ofNat 8 0xC) ∧ ((x2_w38_2) - BitVec.ofNat 32 (tl67.header + tl67.len) = 0) ∧ d_w30_3 = f30 ∧ d_w34_3 = f34 ∧ d_wa20_3 = sl0 ∧ d_wa24_3 = sl1 ∧ d_wa28_3 = sl2 ∧ d_wa2c_3 = sl3 ∧ d_wa30_3 = sl4 ∧ d_wa34_3 = sl5 ∧ d_wa38_3 = sl6 ∧ d_wa3c_3 = sl7 ∧ d_wa40_3 = (x2_w3c_2) + BitVec.ofNat 32 tl67.header ∧ d_wa44_3 = BitVec.ofNat 32 tl67.len) ∨ (d_w30_3 = f30 ∧ d_w34_3 = f34 ∧ d_wa20_3 = sl0 ∧ d_wa24_3 = sl1 ∧ d_wa28_3 = sl2 ∧ d_wa2c_3 = sl3 ∧ d_wa30_3 = sl4 ∧ d_wa34_3 = sl5 ∧ d_wa38_3 = sl6 ∧ d_wa3c_3 = sl7 ∧ d_wa40_3 = sl8 ∧ d_wa44_3 = sl9)) ∧
    ∃ n', Steps n0 n' ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        St n'.mem SV n' 0x4EA (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (9 : Fin 32) = x9 ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (21 : Fin 32) = x21 ∧
        reg n' (25 : Fin 32) = x25 ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = d_w30_3 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = d_w34_3 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = ((rem) - BitVec.ofNat 32 (tl8_1.header + tl8_1.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 ∧
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
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = ((cur) + BitVec.ofNat 32 (tl8_1.header + tl8_1.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = ((rem) - BitVec.ofNat 32 (tl8_1.header + tl8_1.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = d_wa20_3 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = d_wa24_3 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = d_wa28_3 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = d_wa2c_3 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = d_wa30_3 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = d_wa34_3 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = d_wa38_3 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = d_wa3c_3 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = d_wa40_3 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = d_wa44_3 ∧
        SvKeepL B n0.mem n'.mem [(0x1020, 0x10), (0x90, 0x8), (0x44, 0x4), (0x325, 0xB), (0x320, 0x4), (0x324, 0x1), (0x1020, 0x8), (0x328, 0x8), (0x48, 0x4), (0x3C, 0x4), (0x38, 0x4), (0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8), (0x34, 0x4), (0x40, 0x4), (0x1380, 0x4), (0x1384, 0x4), (0x1388, 0x4), (0x138C, 0x4), (0x1388, 0x8), (0x1485, 0xB), (0x1484, 0x1), (0x30, 0x4), (0xA20, 0x4), (0xA24, 0x4), (0xA28, 0x4), (0xA2C, 0x4), (0xA30, 0x4), (0xA34, 0x4), (0xA38, 0x4), (0xA3C, 0x4), (0xA40, 0x4), (0xA44, 0x4)]) := by
  rcases sv_x1 F E0 V0 hret hO s0 M0 fM g0_2 g0_9 g0_18 g0_19 g0_21 g0_25 g0_26 g0_27 w0_30 w0_34 w0_40 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_a20 w0_a24 w0_a28 w0_a2c w0_a30 w0_a34 w0_a38 w0_a3c w0_a40 w0_a44 xl_in ea_in hrem with ⟨-, e⟩ | ⟨x1_0, tl8_1, x1_1, op19_1, ol19_1, x1_2, to19_1, x1_3, n1, c1, s1, E1, V1, fR1, r1_2, r1_3, r1_4, r1_8, r1_9, r1_a0, r1_a1, r1_18, r1_19, r1_21, r1_22, r1_24, r1_25, r1_26, r1_27, w1_30, w1_34, w1_40, w1_48, w1_4c, w1_50, w1_54, w1_58, w1_5c, w1_60, w1_64, w1_68, w1_6c, w1_70, w1_74, w1_78, w1_7c, w1_80, w1_84, w1_88, w1_8c, w1_90, w1_94, w1_320, w1_328, w1_32c, w1_a20, w1_a24, w1_a28, w1_a2c, w1_a30, w1_a34, w1_a38, w1_a3c, w1_a40, w1_a44, K1_L⟩
  · exact .inl e
  rcases sv_x2 F E1 V1 hret hO s1 M0 fR1 r1_2 r1_8 r1_9 r1_a0 r1_a1 r1_18 r1_19 r1_21 r1_22 r1_24 r1_25 r1_26 r1_27 w1_30 w1_34 w1_40 w1_4c w1_50 w1_54 w1_58 w1_5c w1_60 w1_64 w1_68 w1_6c w1_70 w1_74 w1_78 w1_7c w1_80 w1_84 w1_88 w1_8c w1_a20 w1_a24 w1_a28 w1_a2c w1_a30 w1_a34 w1_a38 w1_a3c w1_a40 w1_a44 w1_48 w1_90 w1_94 w1_328 w1_32c ((((xl_in).content x1_1).ofNatLen).restW (derOid_ok_elem x1_3)) ((((xl_in).content x1_1).ofNatLen).oidIn x1_2) (ea_in) x1_0 SD0 with e | ⟨x2_w38_2, x2_w3c_2, x2_0, x2_1, n2, c2, s2, E2, V2, fR2, r2_2, r2_3, r2_4, r2_8, r2_9, r2_18, r2_19, r2_21, r2_25, r2_26, r2_27, w2_30, w2_34, w2_38, w2_3c, w2_40, w2_48, w2_4c, w2_50, w2_54, w2_58, w2_5c, w2_60, w2_64, w2_68, w2_6c, w2_70, w2_74, w2_78, w2_7c, w2_80, w2_84, w2_88, w2_8c, w2_90, w2_94, w2_a20, w2_a24, w2_a28, w2_a2c, w2_a30, w2_a34, w2_a38, w2_a3c, w2_a40, w2_a44, K2_L⟩
  · exact .inl (SvErrRet.pre (c1) (by rw [r1_3]) (by rw [r1_4])
      (fun x hx => (fR1 x hx).trans (fM x hx).symm) e)
  rcases sv_d F E2 V2 hret hO s2 M0 fR2 r2_2 r2_8 r2_9 r2_18 r2_19 r2_21 r2_25 r2_26 r2_27 w2_30 w2_34 w2_38 w2_3c w2_40 w2_48 w2_4c w2_50 w2_54 w2_58 w2_5c w2_60 w2_64 w2_68 w2_6c w2_70 w2_74 w2_78 w2_7c w2_80 w2_84 w2_88 w2_8c w2_90 w2_94 w2_a20 w2_a24 w2_a28 w2_a2c w2_a30 w2_a34 w2_a38 w2_a3c w2_a40 w2_a44 x2_1 ((((xl_in).content x1_1).ofNatLen).oidIn x1_2) SD0 with e | ⟨d_w30_3, d_w34_3, d_wa20_3, d_wa24_3, d_wa28_3, d_wa2c_3, d_wa30_3, d_wa34_3, d_wa38_3, d_wa3c_3, d_wa40_3, d_wa44_3, x3_0, n3, c3, fR3, s3, E3, V3, r3_3, r3_4, r3_2, r3_9, r3_18, r3_19, r3_21, r3_25, r3_26, r3_27, w3_30, w3_34, w3_40, w3_4c, w3_50, w3_54, w3_58, w3_5c, w3_60, w3_64, w3_68, w3_6c, w3_70, w3_74, w3_78, w3_7c, w3_80, w3_84, w3_88, w3_8c, w3_90, w3_94, w3_a20, w3_a24, w3_a28, w3_a2c, w3_a30, w3_a34, w3_a38, w3_a3c, w3_a40, w3_a44, K3_L⟩
  · exact .inl (SvErrRet.pre (c1.trans (c2)) (by rw [r2_3, r1_3]) (by rw [r2_4, r1_4])
      (fun x hx => (fR2 x hx).trans (fM x hx).symm) e)
  exact .inr ⟨x1_0, tl8_1, x1_1, op19_1, ol19_1, x1_2, to19_1, x1_3, x2_w38_2, x2_w3c_2, x2_0, x2_1, d_w30_3, d_w34_3, d_wa20_3, d_wa24_3, d_wa28_3, d_wa2c_3, d_wa30_3, d_wa34_3, d_wa38_3, d_wa3c_3, d_wa40_3, d_wa44_3, x3_0, n3, c1.trans (c2.trans (c3)), fR3, s3, E3, V3,
    by rw [r3_3, r2_3, r1_3], by rw [r3_4, r2_4, r1_4], r3_2, r3_9, r3_18, r3_19, r3_21, r3_25, r3_26, r3_27, w3_30, w3_34, w3_40, w3_4c, w3_50, w3_54, w3_58, w3_5c, w3_60, w3_64, w3_68, w3_6c, w3_70, w3_74, w3_78, w3_7c, w3_80, w3_84, w3_88, w3_8c, w3_90, w3_94, w3_a20, w3_a24, w3_a28, w3_a2c, w3_a30, w3_a34, w3_a38, w3_a3c, w3_a40, w3_a44, (((K1_L).trans K2_L).trans K3_L).mono (by decide)⟩

end C3.RV32.Sv
