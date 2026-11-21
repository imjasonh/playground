import C3BootProofs.Proofs.SvSegDku
import C3BootProofs.Proofs.SvSegEku
import C3BootProofs.Proofs.SvSegDbc
import C3BootProofs.Proofs.SvDp0
import C3BootProofs.Proofs.SvDp1
import C3BootProofs.Proofs.SvDp2
import C3BootProofs.Proofs.SvDp3
import C3BootProofs.Proofs.SvDp4
import C3BootProofs.Proofs.SvDp5

/-!
# `sigstore::verify`: An extension by its OID: `KeyUsage`, `ExtKeyUsage`, `BasicConstraints`, a policy OID, or another.

Written by `scripts/gen-sv-segs.py` from `sv_seg_dku`, `sv_seg_eku`, `sv_seg_dbc`, `sv_dp0`, `sv_dp1`, `sv_dp2`, `sv_dp3`, `sv_dp4`, and `sv_dp5`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxHeartbeats 16000000 in
/-- An extension by its OID: `KeyUsage`, `ExtKeyUsage`, `BasicConstraints`, a policy OID, or another. -/
theorem sv_d {B out bp x9 x21 x25 x26 f30 f34 rem p0 L cur sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 sl9 w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c w80 w84 op ol vp vl rest : Word} {v : Nat → Word} {n0 : Machine}
    (F : Fr B 0x3830)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out)
    (s0 : St n0.mem SV n0 0x60E (reg n0))
    (M0 : Word → BitVec 8)
    (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_8 : reg n0 (8 : Fin 32) = op)
    (g0_9 : reg n0 (9 : Fin 32) = x9)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_25 : reg n0 (25 : Fin 32) = x25)
    (g0_26 : reg n0 (26 : Fin 32) = x26)
    (g0_27 : reg n0 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20)
    (w0_30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30)
    (w0_34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34)
    (w0_38 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl)
    (w0_3c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp)
    (w0_40 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem)
    (w0_48 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol)
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
    (w0_94 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest)
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
    (val_in : SvIn B (vp) (vl).toNat)
    (oid_in : SvIn B (op) (ol).toNat)
    (SD0 : SvData M0) :
    SvErrRet B out v n0 ∨
    (∃ d_w30 : Word, ∃ d_w34 : Word, ∃ d_wa20 : Word, ∃ d_wa24 : Word, ∃ d_wa28 : Word, ∃ d_wa2c : Word, ∃ d_wa30 : Word, ∃ d_wa34 : Word, ∃ d_wa38 : Word, ∃ d_wa3c : Word, ∃ d_wa40 : Word, ∃ d_wa44 : Word, ((∃ tl16_1, derElement 0x3 (memBytes M0 (vp) (vl).toNat) = .ok tl16_1 ∧ (2 ≤ (BitVec.ofNat 32 tl16_1.len).toNat) ∧ (BitVec.ofNat 32 (kuUnused (M0 (((((vp) + BitVec.ofNat 32 tl16_1.header)) + ((BitVec.ofNat 32 tl16_1.len))) + BitVec.ofNat 32 0xFFFFFFFF))) = (M0 ((vp) + BitVec.ofNat 32 tl16_1.header)).zeroExtend 32) ∧ (((vl) - BitVec.ofNat 32 (tl16_1.header + tl16_1.len)) = 0) ∧ (¬ (M0 (((vp) + BitVec.ofNat 32 tl16_1.header) + 0x1)).toNat < 0x80) ∧ d_w30 = f30 ∧ d_w34 = BitVec.ofNat 32 0x1 ∧ d_wa20 = sl0 ∧ d_wa24 = sl1 ∧ d_wa28 = sl2 ∧ d_wa2c = sl3 ∧ d_wa30 = sl4 ∧ d_wa34 = sl5 ∧ d_wa38 = sl6 ∧ d_wa3c = sl7 ∧ d_wa40 = sl8 ∧ d_wa44 = sl9) ∨ (∃ tl19_1, derElement 0x30 (memBytes M0 (vp) (vl).toNat) = .ok tl19_1 ∧ ((vl) - BitVec.ofNat 32 (tl19_1.header + tl19_1.len) = 0) ∧ ∃ k_2 found'_2 cp'_2 cl'_2, svChain (sv_ekuStep B out bp x9 x21 x25 x26 f30 f34 rem p0 L cur sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 sl9 w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c w80 w84 rest v M0) k_2 ((BitVec.ofNat 32 0x0), ((vp) + BitVec.ofNat 32 tl19_1.header), (BitVec.ofNat 32 tl19_1.len)) (found'_2, cp'_2, cl'_2) ∧ cl'_2 = 0 ∧ (found'_2 &&& BitVec.ofNat 32 0x1 ≠ 0) ∧ d_w30 = BitVec.ofNat 32 0x1 ∧ d_w34 = f34 ∧ d_wa20 = sl0 ∧ d_wa24 = sl1 ∧ d_wa28 = sl2 ∧ d_wa2c = sl3 ∧ d_wa30 = sl4 ∧ d_wa34 = sl5 ∧ d_wa38 = sl6 ∧ d_wa3c = sl7 ∧ d_wa40 = sl8 ∧ d_wa44 = sl9) ∨ (∃ tl24_1, derElement 0x30 (memBytes M0 (vp) (vl).toNat) = .ok tl24_1 ∧ ((vl) - BitVec.ofNat 32 (tl24_1.header + tl24_1.len) = 0) ∧ ((True) ∨ ((M0 ((vp) + BitVec.ofNat 32 tl24_1.header) ≠ BitVec.ofNat 8 1) ∧ (M0 ((vp) + BitVec.ofNat 32 tl24_1.header) = BitVec.ofNat 8 2) ∧ ∃ ip10 il10, derIntOf (memBytes M0 (((vp) + BitVec.ofNat 32 tl24_1.header)) ((BitVec.ofNat 32 tl24_1.len)).toNat) (((vp) + BitVec.ofNat 32 tl24_1.header)) (derElement 2 (memBytes M0 (((vp) + BitVec.ofNat 32 tl24_1.header)) ((BitVec.ofNat 32 tl24_1.len)).toNat)) = .ok (ip10, il10) ∧ ∃ ti10, derElement 2 (memBytes M0 (((vp) + BitVec.ofNat 32 tl24_1.header)) ((BitVec.ofNat 32 tl24_1.len)).toNat) = .ok ti10 ∧ (((BitVec.ofNat 32 tl24_1.len)) - BitVec.ofNat 32 (ti10.header + ti10.len) = 0))) ∧ d_w30 = f30 ∧ d_w34 = f34 ∧ d_wa20 = sl0 ∧ d_wa24 = sl1 ∧ d_wa28 = sl2 ∧ d_wa2c = sl3 ∧ d_wa30 = sl4 ∧ d_wa34 = sl5 ∧ d_wa38 = sl6 ∧ d_wa3c = sl7 ∧ d_wa40 = sl8 ∧ d_wa44 = sl9) ∨ (∃ tl35, derTlv (memBytes M0 (vp) (vl).toNat) = .ok tl35 ∧ (BitVec.ofNat 8 tl35.tag = BitVec.ofNat 8 0xC) ∧ ((vl) - BitVec.ofNat 32 (tl35.header + tl35.len) = 0) ∧ d_w30 = f30 ∧ d_w34 = f34 ∧ d_wa20 = (vp) + BitVec.ofNat 32 tl35.header ∧ d_wa24 = BitVec.ofNat 32 tl35.len ∧ d_wa28 = sl2 ∧ d_wa2c = sl3 ∧ d_wa30 = sl4 ∧ d_wa34 = sl5 ∧ d_wa38 = sl6 ∧ d_wa3c = sl7 ∧ d_wa40 = sl8 ∧ d_wa44 = sl9) ∨ (∃ tl43, derTlv (memBytes M0 (vp) (vl).toNat) = .ok tl43 ∧ (BitVec.ofNat 8 tl43.tag = BitVec.ofNat 8 0xC) ∧ ((vl) - BitVec.ofNat 32 (tl43.header + tl43.len) = 0) ∧ d_w30 = f30 ∧ d_w34 = f34 ∧ d_wa20 = sl0 ∧ d_wa24 = sl1 ∧ d_wa28 = (vp) + BitVec.ofNat 32 tl43.header ∧ d_wa2c = BitVec.ofNat 32 tl43.len ∧ d_wa30 = sl4 ∧ d_wa34 = sl5 ∧ d_wa38 = sl6 ∧ d_wa3c = sl7 ∧ d_wa40 = sl8 ∧ d_wa44 = sl9) ∨ (∃ tl51, derTlv (memBytes M0 (vp) (vl).toNat) = .ok tl51 ∧ (BitVec.ofNat 8 tl51.tag = BitVec.ofNat 8 0xC) ∧ ((vl) - BitVec.ofNat 32 (tl51.header + tl51.len) = 0) ∧ d_w30 = f30 ∧ d_w34 = f34 ∧ d_wa20 = sl0 ∧ d_wa24 = sl1 ∧ d_wa28 = sl2 ∧ d_wa2c = sl3 ∧ d_wa30 = (vp) + BitVec.ofNat 32 tl51.header ∧ d_wa34 = BitVec.ofNat 32 tl51.len ∧ d_wa38 = sl6 ∧ d_wa3c = sl7 ∧ d_wa40 = sl8 ∧ d_wa44 = sl9) ∨ (∃ tl59, derTlv (memBytes M0 (vp) (vl).toNat) = .ok tl59 ∧ (BitVec.ofNat 8 tl59.tag = BitVec.ofNat 8 0xC) ∧ ((vl) - BitVec.ofNat 32 (tl59.header + tl59.len) = 0) ∧ d_w30 = f30 ∧ d_w34 = f34 ∧ d_wa20 = sl0 ∧ d_wa24 = sl1 ∧ d_wa28 = sl2 ∧ d_wa2c = sl3 ∧ d_wa30 = sl4 ∧ d_wa34 = sl5 ∧ d_wa38 = (vp) + BitVec.ofNat 32 tl59.header ∧ d_wa3c = BitVec.ofNat 32 tl59.len ∧ d_wa40 = sl8 ∧ d_wa44 = sl9) ∨ (∃ tl67, derTlv (memBytes M0 (vp) (vl).toNat) = .ok tl67 ∧ (BitVec.ofNat 8 tl67.tag = BitVec.ofNat 8 0xC) ∧ ((vl) - BitVec.ofNat 32 (tl67.header + tl67.len) = 0) ∧ d_w30 = f30 ∧ d_w34 = f34 ∧ d_wa20 = sl0 ∧ d_wa24 = sl1 ∧ d_wa28 = sl2 ∧ d_wa2c = sl3 ∧ d_wa30 = sl4 ∧ d_wa34 = sl5 ∧ d_wa38 = sl6 ∧ d_wa3c = sl7 ∧ d_wa40 = (vp) + BitVec.ofNat 32 tl67.header ∧ d_wa44 = BitVec.ofNat 32 tl67.len) ∨ (d_w30 = f30 ∧ d_w34 = f34 ∧ d_wa20 = sl0 ∧ d_wa24 = sl1 ∧ d_wa28 = sl2 ∧ d_wa2c = sl3 ∧ d_wa30 = sl4 ∧ d_wa34 = sl5 ∧ d_wa38 = sl6 ∧ d_wa3c = sl7 ∧ d_wa40 = sl8 ∧ d_wa44 = sl9)) ∧
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
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = d_w30 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = d_w34 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rest ∧
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
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = d_wa20 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = d_wa24 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = d_wa28 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = d_wa2c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = d_wa30 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = d_wa34 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = d_wa38 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = d_wa3c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = d_wa40 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = d_wa44 ∧
        SvKeepL B n0.mem n'.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8), (0x34, 0x4), (0x40, 0x4), (0x1380, 0x4), (0x1384, 0x4), (0x1388, 0x4), (0x138C, 0x4), (0x1020, 0x10), (0x1388, 0x8), (0x1485, 0xB), (0x1484, 0x1), (0x1020, 0x8), (0x30, 0x4), (0xA20, 0x4), (0xA24, 0x4), (0xA28, 0x4), (0xA2C, 0x4), (0xA30, 0x4), (0xA34, 0x4), (0xA38, 0x4), (0xA3C, 0x4), (0xA40, 0x4), (0xA44, 0x4)]) := by
  by_cases hb : memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 0x3FCC4889) 3
  · rcases sv_seg_dku (B := B) (out := out) (bp := bp) (x9 := x9) (x21 := x21) (x25 := x25) (x26 := x26) (f30 := f30) (f34 := f34) (rem := rem) (p0 := p0) (L := L) (cur := cur) (sl0 := sl0) (sl1 := sl1) (sl2 := sl2) (sl3 := sl3) (sl4 := sl4) (sl5 := sl5) (sl6 := sl6) (sl7 := sl7) (sl8 := sl8) (sl9 := sl9) (w4c := w4c) (w50 := w50) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w74 := w74) (w78 := w78) (w7c := w7c) (w80 := w80) (w84 := w84) (op := op) (ol := ol) (vp := vp) (vl := vl) (rest := rest) (v := v) (n0 := n0) F E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_9 g0_18 g0_19 g0_21 g0_25 g0_26 g0_27 w0_30 w0_34 w0_38 w0_3c w0_40 w0_48 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_a20 w0_a24 w0_a28 w0_a2c w0_a30 w0_a34 w0_a38 w0_a3c w0_a40 w0_a44 val_in oid_in SD0 hb with e | ⟨tl16_1, h0, h1, h2, h3, h4, rest⟩
    · exact .inl e
    · obtain ⟨n', fc, f_FR, f_ST, f_E, f_V, f_r3, f_r4, f_r2, f_r9, f_r18, f_r19, f_r21, f_r25, f_r26, f_r27, f_w30, f_w34, f_w40, f_w4c, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_wa20, f_wa24, f_wa28, f_wa2c, f_wa30, f_wa34, f_wa38, f_wa3c, f_wa40, f_wa44, f_w38, f_w3c, f_w48, f_w148c, f_KL⟩ := rest
      exact .inr ⟨f30, BitVec.ofNat 32 0x1, sl0, sl1, sl2, sl3, sl4, sl5, sl6, sl7, sl8, sl9, .inl ⟨tl16_1, h0, h1, h2, h3, h4, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨n', fc, f_FR, f_ST, f_E, f_V, f_r3, f_r4, f_r2, f_r9, f_r18, f_r19, f_r21, f_r25, f_r26, f_r27, f_w30, f_w34, f_w40, f_w4c, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_wa20, f_wa24, f_wa28, f_wa2c, f_wa30, f_wa34, f_wa38, f_wa3c, f_wa40, f_wa44, f_KL.mono (by decide)⟩⟩
  · by_cases hb2 : memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 0x3FCC4892) 3
    · rcases sv_seg_eku (B := B) (out := out) (bp := bp) (x9 := x9) (x21 := x21) (x25 := x25) (x26 := x26) (f30 := f30) (f34 := f34) (rem := rem) (p0 := p0) (L := L) (cur := cur) (sl0 := sl0) (sl1 := sl1) (sl2 := sl2) (sl3 := sl3) (sl4 := sl4) (sl5 := sl5) (sl6 := sl6) (sl7 := sl7) (sl8 := sl8) (sl9 := sl9) (w4c := w4c) (w50 := w50) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w74 := w74) (w78 := w78) (w7c := w7c) (w80 := w80) (w84 := w84) (op := op) (ol := ol) (vp := vp) (vl := vl) (rest := rest) (v := v) (n0 := n0) F E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_9 g0_18 g0_19 g0_21 g0_25 g0_26 g0_27 w0_30 w0_34 w0_38 w0_3c w0_40 w0_48 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_a20 w0_a24 w0_a28 w0_a2c w0_a30 w0_a34 w0_a38 w0_a3c w0_a40 w0_a44 val_in oid_in SD0 hb hb2 with e | ⟨tl19_1, h0, h1, k_2, found'_2, cp'_2, cl'_2, h2, h3, h4, rest⟩
      · exact .inl e
      · obtain ⟨n', fc, f_FR, f_ST, f_E, f_V, f_r3, f_r4, f_r2, f_r9, f_r18, f_r19, f_r21, f_r25, f_r26, f_r27, f_w30, f_w34, f_w40, f_w4c, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_wa20, f_wa24, f_wa28, f_wa2c, f_wa30, f_wa34, f_wa38, f_wa3c, f_wa40, f_wa44, f_w38, f_w3c, f_w48, f_KL⟩ := rest
        exact .inr ⟨BitVec.ofNat 32 0x1, f34, sl0, sl1, sl2, sl3, sl4, sl5, sl6, sl7, sl8, sl9, .inr (.inl ⟨tl19_1, h0, h1, k_2, found'_2, cp'_2, cl'_2, h2, h3, h4, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩), ⟨n', fc, f_FR, f_ST, f_E, f_V, f_r3, f_r4, f_r2, f_r9, f_r18, f_r19, f_r21, f_r25, f_r26, f_r27, f_w30, f_w34, f_w40, f_w4c, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_wa20, f_wa24, f_wa28, f_wa2c, f_wa30, f_wa34, f_wa38, f_wa3c, f_wa40, f_wa44, f_KL.mono (by decide)⟩⟩
    · by_cases hb3 : memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 0x3FCC488F) 3
      · rcases sv_seg_dbc (B := B) (out := out) (bp := bp) (x9 := x9) (x21 := x21) (x25 := x25) (x26 := x26) (f30 := f30) (f34 := f34) (rem := rem) (p0 := p0) (L := L) (cur := cur) (sl0 := sl0) (sl1 := sl1) (sl2 := sl2) (sl3 := sl3) (sl4 := sl4) (sl5 := sl5) (sl6 := sl6) (sl7 := sl7) (sl8 := sl8) (sl9 := sl9) (w4c := w4c) (w50 := w50) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w74 := w74) (w78 := w78) (w7c := w7c) (w80 := w80) (w84 := w84) (op := op) (ol := ol) (vp := vp) (vl := vl) (rest := rest) (v := v) (n0 := n0) F E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_9 g0_18 g0_19 g0_21 g0_25 g0_26 g0_27 w0_30 w0_34 w0_38 w0_3c w0_40 w0_48 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_a20 w0_a24 w0_a28 w0_a2c w0_a30 w0_a34 w0_a38 w0_a3c w0_a40 w0_a44 val_in oid_in SD0 hb hb2 hb3 with e | ⟨tl24_1, h0, h1, h2, rest⟩
        · exact .inl e
        · obtain ⟨n', fc, f_FR, f_ST, f_E, f_V, f_r3, f_r4, f_r2, f_r9, f_r18, f_r19, f_r21, f_r25, f_r26, f_r27, f_w30, f_w34, f_w40, f_w4c, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_wa20, f_wa24, f_wa28, f_wa2c, f_wa30, f_wa34, f_wa38, f_wa3c, f_wa40, f_wa44, f_w38, f_w3c, f_w48, f_KL⟩ := rest
          exact .inr ⟨f30, f34, sl0, sl1, sl2, sl3, sl4, sl5, sl6, sl7, sl8, sl9, .inr (.inr (.inl ⟨tl24_1, h0, h1, h2, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)), ⟨n', fc, f_FR, f_ST, f_E, f_V, f_r3, f_r4, f_r2, f_r9, f_r18, f_r19, f_r21, f_r25, f_r26, f_r27, f_w30, f_w34, f_w40, f_w4c, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_wa20, f_wa24, f_wa28, f_wa2c, f_wa30, f_wa34, f_wa38, f_wa3c, f_wa40, f_wa44, f_KL.mono (by decide)⟩⟩
      · by_cases hb4 : memBytes M0 (BitVec.ofNat 32 0x3FCC48B8) 10 = memBytes M0 op ol.toNat
        · rcases sv_dp0 (B := B) (out := out) (bp := bp) (x9 := x9) (x21 := x21) (x25 := x25) (x26 := x26) (f30 := f30) (f34 := f34) (rem := rem) (p0 := p0) (L := L) (cur := cur) (sl0 := sl0) (sl1 := sl1) (sl2 := sl2) (sl3 := sl3) (sl4 := sl4) (sl5 := sl5) (sl6 := sl6) (sl7 := sl7) (sl8 := sl8) (sl9 := sl9) (w4c := w4c) (w50 := w50) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w74 := w74) (w78 := w78) (w7c := w7c) (w80 := w80) (w84 := w84) (op := op) (ol := ol) (vp := vp) (vl := vl) (rest := rest) (v := v) (n0 := n0) F E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_9 g0_18 g0_19 g0_21 g0_25 g0_26 g0_27 w0_30 w0_34 w0_38 w0_3c w0_40 w0_48 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_a20 w0_a24 w0_a28 w0_a2c w0_a30 w0_a34 w0_a38 w0_a3c w0_a40 w0_a44 val_in oid_in SD0 hb hb2 hb3 hb4 with ⟨-, e⟩ | ⟨tl35, h0, h1, h2, rest⟩
          · exact .inl e
          · obtain ⟨n', fc, f_ST, f_E, f_V, f_FR, f_r2, f_r3, f_r4, f_r9, f_r18, f_r19, f_r21, f_r25, f_r26, f_r27, f_w30, f_w34, f_w40, f_w4c, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_wa20, f_wa24, f_wa28, f_wa2c, f_wa30, f_wa34, f_wa38, f_wa3c, f_wa40, f_wa44, f_KL⟩ := rest
            exact .inr ⟨f30, f34, (vp) + BitVec.ofNat 32 tl35.header, BitVec.ofNat 32 tl35.len, sl2, sl3, sl4, sl5, sl6, sl7, sl8, sl9, .inr (.inr (.inr (.inl ⟨tl35, h0, h1, h2, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩))), ⟨n', fc, f_FR, f_ST, f_E, f_V, f_r3, f_r4, f_r2, f_r9, f_r18, f_r19, f_r21, f_r25, f_r26, f_r27, f_w30, f_w34, f_w40, f_w4c, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_wa20, f_wa24, f_wa28, f_wa2c, f_wa30, f_wa34, f_wa38, f_wa3c, f_wa40, f_wa44, f_KL.mono (by decide)⟩⟩
        · by_cases hb5 : memBytes M0 (BitVec.ofNat 32 0x3FCC48C2) 10 = memBytes M0 op ol.toNat
          · rcases sv_dp1 (B := B) (out := out) (bp := bp) (x9 := x9) (x21 := x21) (x25 := x25) (x26 := x26) (f30 := f30) (f34 := f34) (rem := rem) (p0 := p0) (L := L) (cur := cur) (sl0 := sl0) (sl1 := sl1) (sl2 := sl2) (sl3 := sl3) (sl4 := sl4) (sl5 := sl5) (sl6 := sl6) (sl7 := sl7) (sl8 := sl8) (sl9 := sl9) (w4c := w4c) (w50 := w50) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w74 := w74) (w78 := w78) (w7c := w7c) (w80 := w80) (w84 := w84) (op := op) (ol := ol) (vp := vp) (vl := vl) (rest := rest) (v := v) (n0 := n0) F E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_9 g0_18 g0_19 g0_21 g0_25 g0_26 g0_27 w0_30 w0_34 w0_38 w0_3c w0_40 w0_48 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_a20 w0_a24 w0_a28 w0_a2c w0_a30 w0_a34 w0_a38 w0_a3c w0_a40 w0_a44 val_in oid_in SD0 hb hb2 hb3 hb4 hb5 with ⟨-, e⟩ | ⟨tl43, h0, h1, h2, rest⟩
            · exact .inl e
            · obtain ⟨n', fc, f_ST, f_E, f_V, f_FR, f_r2, f_r3, f_r4, f_r9, f_r18, f_r19, f_r21, f_r25, f_r26, f_r27, f_w30, f_w34, f_w40, f_w4c, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_wa20, f_wa24, f_wa28, f_wa2c, f_wa30, f_wa34, f_wa38, f_wa3c, f_wa40, f_wa44, f_KL⟩ := rest
              exact .inr ⟨f30, f34, sl0, sl1, (vp) + BitVec.ofNat 32 tl43.header, BitVec.ofNat 32 tl43.len, sl4, sl5, sl6, sl7, sl8, sl9, .inr (.inr (.inr (.inr (.inl ⟨tl43, h0, h1, h2, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)))), ⟨n', fc, f_FR, f_ST, f_E, f_V, f_r3, f_r4, f_r2, f_r9, f_r18, f_r19, f_r21, f_r25, f_r26, f_r27, f_w30, f_w34, f_w40, f_w4c, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_wa20, f_wa24, f_wa28, f_wa2c, f_wa30, f_wa34, f_wa38, f_wa3c, f_wa40, f_wa44, f_KL.mono (by decide)⟩⟩
          · by_cases hb6 : memBytes M0 (BitVec.ofNat 32 0x3FCC48CC) 10 = memBytes M0 op ol.toNat
            · rcases sv_dp2 (B := B) (out := out) (bp := bp) (x9 := x9) (x21 := x21) (x25 := x25) (x26 := x26) (f30 := f30) (f34 := f34) (rem := rem) (p0 := p0) (L := L) (cur := cur) (sl0 := sl0) (sl1 := sl1) (sl2 := sl2) (sl3 := sl3) (sl4 := sl4) (sl5 := sl5) (sl6 := sl6) (sl7 := sl7) (sl8 := sl8) (sl9 := sl9) (w4c := w4c) (w50 := w50) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w74 := w74) (w78 := w78) (w7c := w7c) (w80 := w80) (w84 := w84) (op := op) (ol := ol) (vp := vp) (vl := vl) (rest := rest) (v := v) (n0 := n0) F E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_9 g0_18 g0_19 g0_21 g0_25 g0_26 g0_27 w0_30 w0_34 w0_38 w0_3c w0_40 w0_48 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_a20 w0_a24 w0_a28 w0_a2c w0_a30 w0_a34 w0_a38 w0_a3c w0_a40 w0_a44 val_in oid_in SD0 hb hb2 hb3 hb4 hb5 hb6 with ⟨-, e⟩ | ⟨tl51, h0, h1, h2, rest⟩
              · exact .inl e
              · obtain ⟨n', fc, f_ST, f_E, f_V, f_FR, f_r2, f_r3, f_r4, f_r9, f_r18, f_r19, f_r21, f_r25, f_r26, f_r27, f_w30, f_w34, f_w40, f_w4c, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_wa20, f_wa24, f_wa28, f_wa2c, f_wa30, f_wa34, f_wa38, f_wa3c, f_wa40, f_wa44, f_KL⟩ := rest
                exact .inr ⟨f30, f34, sl0, sl1, sl2, sl3, (vp) + BitVec.ofNat 32 tl51.header, BitVec.ofNat 32 tl51.len, sl6, sl7, sl8, sl9, .inr (.inr (.inr (.inr (.inr (.inl ⟨tl51, h0, h1, h2, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩))))), ⟨n', fc, f_FR, f_ST, f_E, f_V, f_r3, f_r4, f_r2, f_r9, f_r18, f_r19, f_r21, f_r25, f_r26, f_r27, f_w30, f_w34, f_w40, f_w4c, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_wa20, f_wa24, f_wa28, f_wa2c, f_wa30, f_wa34, f_wa38, f_wa3c, f_wa40, f_wa44, f_KL.mono (by decide)⟩⟩
            · by_cases hb7 : memBytes M0 (BitVec.ofNat 32 0x3FCC48D6) 10 = memBytes M0 op ol.toNat
              · rcases sv_dp3 (B := B) (out := out) (bp := bp) (x9 := x9) (x21 := x21) (x25 := x25) (x26 := x26) (f30 := f30) (f34 := f34) (rem := rem) (p0 := p0) (L := L) (cur := cur) (sl0 := sl0) (sl1 := sl1) (sl2 := sl2) (sl3 := sl3) (sl4 := sl4) (sl5 := sl5) (sl6 := sl6) (sl7 := sl7) (sl8 := sl8) (sl9 := sl9) (w4c := w4c) (w50 := w50) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w74 := w74) (w78 := w78) (w7c := w7c) (w80 := w80) (w84 := w84) (op := op) (ol := ol) (vp := vp) (vl := vl) (rest := rest) (v := v) (n0 := n0) F E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_9 g0_18 g0_19 g0_21 g0_25 g0_26 g0_27 w0_30 w0_34 w0_38 w0_3c w0_40 w0_48 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_a20 w0_a24 w0_a28 w0_a2c w0_a30 w0_a34 w0_a38 w0_a3c w0_a40 w0_a44 val_in oid_in SD0 hb hb2 hb3 hb4 hb5 hb6 hb7 with ⟨-, e⟩ | ⟨tl59, h0, h1, h2, rest⟩
                · exact .inl e
                · obtain ⟨n', fc, f_ST, f_E, f_V, f_FR, f_r2, f_r3, f_r4, f_r9, f_r18, f_r19, f_r21, f_r25, f_r26, f_r27, f_w30, f_w34, f_w40, f_w4c, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_wa20, f_wa24, f_wa28, f_wa2c, f_wa30, f_wa34, f_wa38, f_wa3c, f_wa40, f_wa44, f_KL⟩ := rest
                  exact .inr ⟨f30, f34, sl0, sl1, sl2, sl3, sl4, sl5, (vp) + BitVec.ofNat 32 tl59.header, BitVec.ofNat 32 tl59.len, sl8, sl9, .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨tl59, h0, h1, h2, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)))))), ⟨n', fc, f_FR, f_ST, f_E, f_V, f_r3, f_r4, f_r2, f_r9, f_r18, f_r19, f_r21, f_r25, f_r26, f_r27, f_w30, f_w34, f_w40, f_w4c, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_wa20, f_wa24, f_wa28, f_wa2c, f_wa30, f_wa34, f_wa38, f_wa3c, f_wa40, f_wa44, f_KL.mono (by decide)⟩⟩
              · by_cases hb8 : memBytes M0 (BitVec.ofNat 32 0x3FCC48E0) 10 = memBytes M0 op ol.toNat
                · rcases sv_dp4 (B := B) (out := out) (bp := bp) (x9 := x9) (x21 := x21) (x25 := x25) (x26 := x26) (f30 := f30) (f34 := f34) (rem := rem) (p0 := p0) (L := L) (cur := cur) (sl0 := sl0) (sl1 := sl1) (sl2 := sl2) (sl3 := sl3) (sl4 := sl4) (sl5 := sl5) (sl6 := sl6) (sl7 := sl7) (sl8 := sl8) (sl9 := sl9) (w4c := w4c) (w50 := w50) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w74 := w74) (w78 := w78) (w7c := w7c) (w80 := w80) (w84 := w84) (op := op) (ol := ol) (vp := vp) (vl := vl) (rest := rest) (v := v) (n0 := n0) F E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_9 g0_18 g0_19 g0_21 g0_25 g0_26 g0_27 w0_30 w0_34 w0_38 w0_3c w0_40 w0_48 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_a20 w0_a24 w0_a28 w0_a2c w0_a30 w0_a34 w0_a38 w0_a3c w0_a40 w0_a44 val_in oid_in SD0 hb hb2 hb3 hb4 hb5 hb6 hb7 hb8 with ⟨-, e⟩ | ⟨tl67, h0, h1, h2, rest⟩
                  · exact .inl e
                  · obtain ⟨n', fc, f_ST, f_E, f_V, f_FR, f_r2, f_r3, f_r4, f_r9, f_r18, f_r19, f_r21, f_r25, f_r26, f_r27, f_w30, f_w34, f_w40, f_w4c, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_wa20, f_wa24, f_wa28, f_wa2c, f_wa30, f_wa34, f_wa38, f_wa3c, f_wa40, f_wa44, f_KL⟩ := rest
                    exact .inr ⟨f30, f34, sl0, sl1, sl2, sl3, sl4, sl5, sl6, sl7, (vp) + BitVec.ofNat 32 tl67.header, BitVec.ofNat 32 tl67.len, .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨tl67, h0, h1, h2, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩))))))), ⟨n', fc, f_FR, f_ST, f_E, f_V, f_r3, f_r4, f_r2, f_r9, f_r18, f_r19, f_r21, f_r25, f_r26, f_r27, f_w30, f_w34, f_w40, f_w4c, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_wa20, f_wa24, f_wa28, f_wa2c, f_wa30, f_wa34, f_wa38, f_wa3c, f_wa40, f_wa44, f_KL.mono (by decide)⟩⟩
                · rcases sv_dp5 (B := B) (out := out) (bp := bp) (x9 := x9) (x21 := x21) (x25 := x25) (x26 := x26) (f30 := f30) (f34 := f34) (rem := rem) (p0 := p0) (L := L) (cur := cur) (sl0 := sl0) (sl1 := sl1) (sl2 := sl2) (sl3 := sl3) (sl4 := sl4) (sl5 := sl5) (sl6 := sl6) (sl7 := sl7) (sl8 := sl8) (sl9 := sl9) (w4c := w4c) (w50 := w50) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w74 := w74) (w78 := w78) (w7c := w7c) (w80 := w80) (w84 := w84) (op := op) (ol := ol) (vp := vp) (vl := vl) (rest := rest) (v := v) (n0 := n0) F E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_9 g0_18 g0_19 g0_21 g0_25 g0_26 g0_27 w0_30 w0_34 w0_38 w0_3c w0_40 w0_48 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_a20 w0_a24 w0_a28 w0_a2c w0_a30 w0_a34 w0_a38 w0_a3c w0_a40 w0_a44 val_in oid_in SD0 hb hb2 hb3 hb4 hb5 hb6 hb7 hb8 with ⟨-, e⟩ | rest
                  · exact .inl e
                  · obtain ⟨n', fc, f_ST, f_E, f_V, f_FR, f_r2, f_r3, f_r4, f_r9, f_r18, f_r19, f_r21, f_r25, f_r26, f_r27, f_w30, f_w34, f_w40, f_w4c, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_wa20, f_wa24, f_wa28, f_wa2c, f_wa30, f_wa34, f_wa38, f_wa3c, f_wa40, f_wa44, f_KL⟩ := rest
                    exact .inr ⟨f30, f34, sl0, sl1, sl2, sl3, sl4, sl5, sl6, sl7, sl8, sl9, .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩))))))), ⟨n', fc, f_FR, f_ST, f_E, f_V, f_r3, f_r4, f_r2, f_r9, f_r18, f_r19, f_r21, f_r25, f_r26, f_r27, f_w30, f_w34, f_w40, f_w4c, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_wa20, f_wa24, f_wa28, f_wa2c, f_wa30, f_wa34, f_wa38, f_wa3c, f_wa40, f_wa44, f_KL.mono (by decide)⟩⟩

end C3.RV32.Sv
