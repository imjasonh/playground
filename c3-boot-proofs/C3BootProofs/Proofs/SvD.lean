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
theorem sv_d {B out bp tbp dg rootp ll sgp kp sgl tbl f2c f30 p0 L cur sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 sl9 w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c op ol vp vl rest : Word} {v : Nat → Word} {n0 : Machine} {rem : Word}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out)
    (s0 : St n0.mem SV n0 0x4E2 (reg n0))
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
    (w0_44 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16)
    (val_in : SvIn B vp vl.toNat)
    (oid_in : SvIn B op ol.toNat)
    (SD0 : SvData M0)
    (sl0_or0 : sl0 = 0 ∨ SvIn B sl0 sl1.toNat)
    (sl2_or0 : sl2 = 0 ∨ SvIn B sl2 sl3.toNat)
    (sl4_or0 : sl4 = 0 ∨ SvIn B sl4 sl5.toNat)
    (sl6_or0 : sl6 = 0 ∨ SvIn B sl6 sl7.toNat)
    (sl8_or0 : sl8 = 0 ∨ SvIn B sl8 sl9.toNat) :
    SvErrRet B out v n0 ∨
    (∃ d_w2c : Word, ∃ d_w30 : Word, ∃ d_w80 : Word, ∃ d_w84 : Word, ∃ d_w88 : Word, ∃ d_w8c : Word, ∃ d_w90 : Word, ∃ d_w94 : Word, ∃ d_w98 : Word, ∃ d_w9c : Word, ∃ d_wa0 : Word, ∃ d_wa4 : Word, (((memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress)) 3) ∧ ∃ tl15_1, derElement 0x3 (memBytes M0 (vp) (vl).toNat) = .ok tl15_1 ∧ (2 ≤ (BitVec.ofNat 32 tl15_1.len).toNat) ∧ (BitVec.ofNat 32 (kuUnused (M0 (((((vp) + BitVec.ofNat 32 tl15_1.header)) + ((BitVec.ofNat 32 tl15_1.len))) + BitVec.ofNat 32 0xFFFFFFFF))) = (M0 ((vp) + BitVec.ofNat 32 tl15_1.header)).zeroExtend 32) ∧ (((vl) - BitVec.ofNat 32 (tl15_1.header + tl15_1.len)) = 0) ∧ (¬ (M0 (((vp) + BitVec.ofNat 32 tl15_1.header) + 0x1)).toNat < 0x80) ∧ d_w2c = f2c ∧ d_w30 = BitVec.ofNat 32 0x1 ∧ d_w80 = sl0 ∧ d_w84 = sl1 ∧ d_w88 = sl2 ∧ d_w8c = sl3 ∧ d_w90 = sl4 ∧ d_w94 = sl5 ∧ d_w98 = sl6 ∧ d_w9c = sl7 ∧ d_wa0 = sl8 ∧ d_wa4 = sl9) ∨ ((¬ (memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress)) 3)) ∧ (memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x9)) 3) ∧ ∃ tl21_1, derElement 0x30 (memBytes M0 (vp) (vl).toNat) = .ok tl21_1 ∧ ((vl) - BitVec.ofNat 32 (tl21_1.header + tl21_1.len) = 0) ∧ ∃ k_2 cp'_2 cl'_2 found'_2, svChain (sv_ekuStep B out bp tbp dg rootp ll sgp kp sgl tbl f2c f30 0 p0 L cur sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 sl9 w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c rest v M0) k_2 (((vp) + BitVec.ofNat 32 tl21_1.header), (BitVec.ofNat 32 tl21_1.len), (BitVec.ofNat 32 0x0)) (cp'_2, cl'_2, found'_2) ∧ cl'_2 = 0 ∧ (found'_2 &&& BitVec.ofNat 32 0x1 ≠ 0) ∧ d_w2c = BitVec.ofNat 32 0x1 ∧ d_w30 = f30 ∧ d_w80 = sl0 ∧ d_w84 = sl1 ∧ d_w88 = sl2 ∧ d_w8c = sl3 ∧ d_w90 = sl4 ∧ d_w94 = sl5 ∧ d_w98 = sl6 ∧ d_w9c = sl7 ∧ d_wa0 = sl8 ∧ d_wa4 = sl9) ∨ ((¬ (memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress)) 3)) ∧ (¬ (memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x9)) 3)) ∧ (memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x6)) 3) ∧ ∃ tl27_1, derElement 0x30 (memBytes M0 (vp) (vl).toNat) = .ok tl27_1 ∧ ((vl) - BitVec.ofNat 32 (tl27_1.header + tl27_1.len) = 0) ∧ ((((BitVec.ofNat 32 tl27_1.len) = 0)) ∨ ((¬ ((BitVec.ofNat 32 tl27_1.len) = 0)) ∧ (M0 ((vp) + BitVec.ofNat 32 tl27_1.header) ≠ BitVec.ofNat 8 1) ∧ (M0 ((vp) + BitVec.ofNat 32 tl27_1.header) = BitVec.ofNat 8 2) ∧ ∃ ip10 il10, derIntOf (memBytes M0 (((vp) + BitVec.ofNat 32 tl27_1.header)) ((BitVec.ofNat 32 tl27_1.len)).toNat) (((vp) + BitVec.ofNat 32 tl27_1.header)) (derElement 2 (memBytes M0 (((vp) + BitVec.ofNat 32 tl27_1.header)) ((BitVec.ofNat 32 tl27_1.len)).toNat)) = .ok (ip10, il10) ∧ ∃ ti10, derElement 2 (memBytes M0 (((vp) + BitVec.ofNat 32 tl27_1.header)) ((BitVec.ofNat 32 tl27_1.len)).toNat) = .ok ti10 ∧ (((BitVec.ofNat 32 tl27_1.len)) - BitVec.ofNat 32 (ti10.header + ti10.len) = 0))) ∧ d_w2c = f2c ∧ d_w30 = f30 ∧ d_w80 = sl0 ∧ d_w84 = sl1 ∧ d_w88 = sl2 ∧ d_w8c = sl3 ∧ d_w90 = sl4 ∧ d_w94 = sl5 ∧ d_w98 = sl6 ∧ d_w9c = sl7 ∧ d_wa0 = sl8 ∧ d_wa4 = sl9) ∨ ((¬ (memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress)) 3)) ∧ (¬ (memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x9)) 3)) ∧ (¬ (memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x6)) 3)) ∧ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x2D)) 10 = memBytes M0 op ol.toNat) ∧ ∃ tl43, derTlv (memBytes M0 (vp) (vl).toNat) = .ok tl43 ∧ (BitVec.ofNat 8 tl43.tag = BitVec.ofNat 8 0xC) ∧ ((vl) - BitVec.ofNat 32 (tl43.header + tl43.len) = 0) ∧ d_w2c = f2c ∧ d_w30 = f30 ∧ d_w80 = (vp) + BitVec.ofNat 32 tl43.header ∧ d_w84 = BitVec.ofNat 32 tl43.len ∧ d_w88 = sl2 ∧ d_w8c = sl3 ∧ d_w90 = sl4 ∧ d_w94 = sl5 ∧ d_w98 = sl6 ∧ d_w9c = sl7 ∧ d_wa0 = sl8 ∧ d_wa4 = sl9) ∨ ((¬ (memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress)) 3)) ∧ (¬ (memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x9)) 3)) ∧ (¬ (memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x6)) 3)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x2D)) 10 = memBytes M0 op ol.toNat)) ∧ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x37)) 10 = memBytes M0 op ol.toNat) ∧ ∃ tl56, derTlv (memBytes M0 (vp) (vl).toNat) = .ok tl56 ∧ (BitVec.ofNat 8 tl56.tag = BitVec.ofNat 8 0xC) ∧ ((vl) - BitVec.ofNat 32 (tl56.header + tl56.len) = 0) ∧ d_w2c = f2c ∧ d_w30 = f30 ∧ d_w80 = sl0 ∧ d_w84 = sl1 ∧ d_w88 = (vp) + BitVec.ofNat 32 tl56.header ∧ d_w8c = BitVec.ofNat 32 tl56.len ∧ d_w90 = sl4 ∧ d_w94 = sl5 ∧ d_w98 = sl6 ∧ d_w9c = sl7 ∧ d_wa0 = sl8 ∧ d_wa4 = sl9) ∨ ((¬ (memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress)) 3)) ∧ (¬ (memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x9)) 3)) ∧ (¬ (memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x6)) 3)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x2D)) 10 = memBytes M0 op ol.toNat)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x37)) 10 = memBytes M0 op ol.toNat)) ∧ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x41)) 10 = memBytes M0 op ol.toNat) ∧ ∃ tl69, derTlv (memBytes M0 (vp) (vl).toNat) = .ok tl69 ∧ (BitVec.ofNat 8 tl69.tag = BitVec.ofNat 8 0xC) ∧ ((vl) - BitVec.ofNat 32 (tl69.header + tl69.len) = 0) ∧ d_w2c = f2c ∧ d_w30 = f30 ∧ d_w80 = sl0 ∧ d_w84 = sl1 ∧ d_w88 = sl2 ∧ d_w8c = sl3 ∧ d_w90 = (vp) + BitVec.ofNat 32 tl69.header ∧ d_w94 = BitVec.ofNat 32 tl69.len ∧ d_w98 = sl6 ∧ d_w9c = sl7 ∧ d_wa0 = sl8 ∧ d_wa4 = sl9) ∨ ((¬ (memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress)) 3)) ∧ (¬ (memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x9)) 3)) ∧ (¬ (memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x6)) 3)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x2D)) 10 = memBytes M0 op ol.toNat)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x37)) 10 = memBytes M0 op ol.toNat)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x41)) 10 = memBytes M0 op ol.toNat)) ∧ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x4B)) 10 = memBytes M0 op ol.toNat) ∧ ∃ tl82, derTlv (memBytes M0 (vp) (vl).toNat) = .ok tl82 ∧ (BitVec.ofNat 8 tl82.tag = BitVec.ofNat 8 0xC) ∧ ((vl) - BitVec.ofNat 32 (tl82.header + tl82.len) = 0) ∧ d_w2c = f2c ∧ d_w30 = f30 ∧ d_w80 = sl0 ∧ d_w84 = sl1 ∧ d_w88 = sl2 ∧ d_w8c = sl3 ∧ d_w90 = sl4 ∧ d_w94 = sl5 ∧ d_w98 = (vp) + BitVec.ofNat 32 tl82.header ∧ d_w9c = BitVec.ofNat 32 tl82.len ∧ d_wa0 = sl8 ∧ d_wa4 = sl9) ∨ ((¬ (memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress)) 3)) ∧ (¬ (memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x9)) 3)) ∧ (¬ (memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x6)) 3)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x2D)) 10 = memBytes M0 op ol.toNat)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x37)) 10 = memBytes M0 op ol.toNat)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x41)) 10 = memBytes M0 op ol.toNat)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x4B)) 10 = memBytes M0 op ol.toNat)) ∧ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x55)) 10 = memBytes M0 op ol.toNat) ∧ ∃ tl95, derTlv (memBytes M0 (vp) (vl).toNat) = .ok tl95 ∧ (BitVec.ofNat 8 tl95.tag = BitVec.ofNat 8 0xC) ∧ ((vl) - BitVec.ofNat 32 (tl95.header + tl95.len) = 0) ∧ d_w2c = f2c ∧ d_w30 = f30 ∧ d_w80 = sl0 ∧ d_w84 = sl1 ∧ d_w88 = sl2 ∧ d_w8c = sl3 ∧ d_w90 = sl4 ∧ d_w94 = sl5 ∧ d_w98 = sl6 ∧ d_w9c = sl7 ∧ d_wa0 = (vp) + BitVec.ofNat 32 tl95.header ∧ d_wa4 = BitVec.ofNat 32 tl95.len) ∨ ((¬ (memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress)) 3)) ∧ (¬ (memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x9)) 3)) ∧ (¬ (memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x6)) 3)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x2D)) 10 = memBytes M0 op ol.toNat)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x37)) 10 = memBytes M0 op ol.toNat)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x41)) 10 = memBytes M0 op ol.toNat)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x4B)) 10 = memBytes M0 op ol.toNat)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x55)) 10 = memBytes M0 op ol.toNat)) ∧ d_w2c = f2c ∧ d_w30 = f30 ∧ d_w80 = sl0 ∧ d_w84 = sl1 ∧ d_w88 = sl2 ∧ d_w8c = sl3 ∧ d_w90 = sl4 ∧ d_w94 = sl5 ∧ d_w98 = sl6 ∧ d_w9c = sl7 ∧ d_wa0 = sl8 ∧ d_wa4 = sl9)) ∧ (d_w80 = 0 ∨ SvIn B d_w80 d_w84.toNat) ∧ (d_w88 = 0 ∨ SvIn B d_w88 d_w8c.toNat) ∧ (d_w90 = 0 ∨ SvIn B d_w90 d_w94.toNat) ∧ (d_w98 = 0 ∨ SvIn B d_w98 d_w9c.toNat) ∧ (d_wa0 = 0 ∨ SvIn B d_wa0 d_wa4.toNat) ∧
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
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = d_w2c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = d_w30 ∧
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
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = d_w80 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = d_w84 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = d_w88 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = d_w8c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = d_w90 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = d_w94 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = d_w98 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = d_w9c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = d_wa0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = d_wa4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest ∧
        SvKeepL B n0.mem n'.mem [(0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8), (0x30, 0x4), (0x50, 0x4), (0x1FC, 0x4), (0x200, 0x4), (0x204, 0x4), (0x208, 0x4), (0x420, 0x10), (0x204, 0x8), (0x385, 0xB), (0x384, 0x1), (0x420, 0x8), (0x2C, 0x4), (0x80, 0x4), (0x84, 0x4), (0x88, 0x4), (0x8C, 0x4), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4), (0x9C, 0x4), (0xA0, 0x4), (0xA4, 0x4)]) := by
  by_cases hb : memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress)) 3
  · rcases sv_seg_dku (B := B) (out := out) (bp := bp) (tbp := tbp) (dg := dg) (rootp := rootp) (ll := ll) (sgp := sgp) (kp := kp) (sgl := sgl) (tbl := tbl) (f2c := f2c) (f30 := f30) (p0 := p0) (L := L) (cur := cur) (sl0 := sl0) (sl1 := sl1) (sl2 := sl2) (sl3 := sl3) (sl4 := sl4) (sl5 := sl5) (sl6 := sl6) (sl7 := sl7) (sl8 := sl8) (sl9 := sl9) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w74 := w74) (w78 := w78) (w7c := w7c) (op := op) (ol := ol) (vp := vp) (vl := vl) (rest := rest) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_9 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_27 w0_2c w0_30 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_150 w0_154 w0_34 w0_38 w0_48 w0_4c w0_158 w0_15c w0_44 val_in oid_in SD0 hb with e | ⟨tl15_1, h0, h1, h2, h3, h4, rest⟩
    · exact .inl e
    · obtain ⟨n', fc, f_FR, f_ST, f_E, f_V, f_r3, f_r4, f_r2, f_r8, f_r9, f_r18, f_r19, f_r20, f_r21, f_r22, f_r23, f_r24, f_r25, f_r27, f_w2c, f_w30, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_w98, f_w9c, f_wa0, f_wa4, f_w150, f_w154, f_w158, f_w15c, f_w34, f_w38, f_w48, f_w4c, f_w44, f_w38c, f_KL⟩ := rest
      exact .inr ⟨f2c, BitVec.ofNat 32 0x1, sl0, sl1, sl2, sl3, sl4, sl5, sl6, sl7, sl8, sl9, .inl ⟨hb, tl15_1, h0, h1, h2, h3, h4, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, sl0_or0, sl2_or0, sl4_or0, sl6_or0, sl8_or0, ⟨n', fc, f_FR, f_ST, f_E, f_V, f_r3, f_r4, f_r2, f_r8, f_r9, f_r18, f_r19, f_r20, f_r21, f_r22, f_r23, f_r24, f_r25, f_r27, f_w2c, f_w30, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_w98, f_w9c, f_wa0, f_wa4, f_w150, f_w154, f_w158, f_w15c, f_KL.mono (by decide)⟩⟩
  · by_cases hb2 : memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x9)) 3
    · rcases sv_seg_eku (B := B) (out := out) (bp := bp) (tbp := tbp) (dg := dg) (rootp := rootp) (ll := ll) (sgp := sgp) (kp := kp) (sgl := sgl) (tbl := tbl) (f2c := f2c) (f30 := f30) (p0 := p0) (L := L) (cur := cur) (sl0 := sl0) (sl1 := sl1) (sl2 := sl2) (sl3 := sl3) (sl4 := sl4) (sl5 := sl5) (sl6 := sl6) (sl7 := sl7) (sl8 := sl8) (sl9 := sl9) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w74 := w74) (w78 := w78) (w7c := w7c) (op := op) (ol := ol) (vp := vp) (vl := vl) (rest := rest) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_9 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_27 w0_2c w0_30 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_150 w0_154 w0_34 w0_38 w0_48 w0_4c w0_158 w0_15c w0_44 val_in oid_in SD0 hb hb2 with e | ⟨tl21_1, h0, h1, k_2, cp'_2, cl'_2, found'_2, h2, h3, h4, rest⟩
      · exact .inl e
      · obtain ⟨n', fc, f_FR, f_ST, f_E, f_V, f_r3, f_r4, f_r2, f_r8, f_r9, f_r18, f_r19, f_r20, f_r21, f_r22, f_r23, f_r24, f_r25, f_r27, f_w2c, f_w30, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_w98, f_w9c, f_wa0, f_wa4, f_w150, f_w154, f_w158, f_w15c, f_w34, f_w38, f_w48, f_w4c, f_w44, f_KL⟩ := rest
        exact .inr ⟨BitVec.ofNat 32 0x1, f30, sl0, sl1, sl2, sl3, sl4, sl5, sl6, sl7, sl8, sl9, .inr (.inl ⟨hb, hb2, tl21_1, h0, h1, k_2, cp'_2, cl'_2, found'_2, h2, h3, h4, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩), sl0_or0, sl2_or0, sl4_or0, sl6_or0, sl8_or0, ⟨n', fc, f_FR, f_ST, f_E, f_V, f_r3, f_r4, f_r2, f_r8, f_r9, f_r18, f_r19, f_r20, f_r21, f_r22, f_r23, f_r24, f_r25, f_r27, f_w2c, f_w30, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_w98, f_w9c, f_wa0, f_wa4, f_w150, f_w154, f_w158, f_w15c, f_KL.mono (by decide)⟩⟩
    · by_cases hb3 : memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x6)) 3
      · rcases sv_seg_dbc (B := B) (out := out) (bp := bp) (tbp := tbp) (dg := dg) (rootp := rootp) (ll := ll) (sgp := sgp) (kp := kp) (sgl := sgl) (tbl := tbl) (f2c := f2c) (f30 := f30) (p0 := p0) (L := L) (cur := cur) (sl0 := sl0) (sl1 := sl1) (sl2 := sl2) (sl3 := sl3) (sl4 := sl4) (sl5 := sl5) (sl6 := sl6) (sl7 := sl7) (sl8 := sl8) (sl9 := sl9) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w74 := w74) (w78 := w78) (w7c := w7c) (op := op) (ol := ol) (vp := vp) (vl := vl) (rest := rest) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_9 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_27 w0_2c w0_30 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_150 w0_154 w0_34 w0_38 w0_48 w0_4c w0_158 w0_15c w0_44 val_in oid_in SD0 hb hb2 hb3 with e | ⟨tl27_1, h0, h1, h2, rest⟩
        · exact .inl e
        · obtain ⟨n', fc, f_FR, f_ST, f_E, f_V, f_r3, f_r4, f_r2, f_r8, f_r9, f_r18, f_r19, f_r20, f_r21, f_r22, f_r23, f_r24, f_r25, f_r27, f_w2c, f_w30, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_w98, f_w9c, f_wa0, f_wa4, f_w150, f_w154, f_w158, f_w15c, f_w34, f_w38, f_w48, f_w4c, f_w44, f_KL⟩ := rest
          exact .inr ⟨f2c, f30, sl0, sl1, sl2, sl3, sl4, sl5, sl6, sl7, sl8, sl9, .inr (.inr (.inl ⟨hb, hb2, hb3, tl27_1, h0, h1, h2, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)), sl0_or0, sl2_or0, sl4_or0, sl6_or0, sl8_or0, ⟨n', fc, f_FR, f_ST, f_E, f_V, f_r3, f_r4, f_r2, f_r8, f_r9, f_r18, f_r19, f_r20, f_r21, f_r22, f_r23, f_r24, f_r25, f_r27, f_w2c, f_w30, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_w98, f_w9c, f_wa0, f_wa4, f_w150, f_w154, f_w158, f_w15c, f_KL.mono (by decide)⟩⟩
      · by_cases hb4 : memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x2D)) 10 = memBytes M0 op ol.toNat
        · rcases sv_dp0 (B := B) (out := out) (bp := bp) (tbp := tbp) (dg := dg) (rootp := rootp) (ll := ll) (sgp := sgp) (kp := kp) (sgl := sgl) (tbl := tbl) (f2c := f2c) (f30 := f30) (rem := rem) (p0 := p0) (L := L) (cur := cur) (sl0 := sl0) (sl1 := sl1) (sl2 := sl2) (sl3 := sl3) (sl4 := sl4) (sl5 := sl5) (sl6 := sl6) (sl7 := sl7) (sl8 := sl8) (sl9 := sl9) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w74 := w74) (w78 := w78) (w7c := w7c) (op := op) (ol := ol) (vp := vp) (vl := vl) (rest := rest) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_9 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_27 w0_2c w0_30 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_150 w0_154 w0_34 w0_38 w0_48 w0_4c w0_158 w0_15c w0_44 val_in oid_in SD0 hb hb2 hb3 hb4 with ⟨-, e⟩ | ⟨tl43, h0, h1, h2, rest⟩
          · exact .inl e
          · obtain ⟨n', fc, f_ST, f_E, f_V, f_FR, f_r2, f_r3, f_r4, f_r8, f_r9, f_r18, f_r19, f_r20, f_r21, f_r22, f_r23, f_r24, f_r25, f_r27, f_w2c, f_w30, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_w98, f_w9c, f_wa0, f_wa4, f_w150, f_w154, f_w158, f_w15c, f_KL⟩ := rest
            exact .inr ⟨f2c, f30, (vp) + BitVec.ofNat 32 tl43.header, BitVec.ofNat 32 tl43.len, sl2, sl3, sl4, sl5, sl6, sl7, sl8, sl9, .inr (.inr (.inr (.inl ⟨hb, hb2, hb3, hb4, tl43, h0, h1, h2, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩))), .inr (((val_in).content (derTlv_elem h0)).ofNatLen), sl2_or0, sl4_or0, sl6_or0, sl8_or0, ⟨n', fc, f_FR, f_ST, f_E, f_V, f_r3, f_r4, f_r2, f_r8, f_r9, f_r18, f_r19, f_r20, f_r21, f_r22, f_r23, f_r24, f_r25, f_r27, f_w2c, f_w30, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_w98, f_w9c, f_wa0, f_wa4, f_w150, f_w154, f_w158, f_w15c, f_KL.mono (by decide)⟩⟩
        · by_cases hb5 : memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x37)) 10 = memBytes M0 op ol.toNat
          · rcases sv_dp1 (B := B) (out := out) (bp := bp) (tbp := tbp) (dg := dg) (rootp := rootp) (ll := ll) (sgp := sgp) (kp := kp) (sgl := sgl) (tbl := tbl) (f2c := f2c) (f30 := f30) (rem := rem) (p0 := p0) (L := L) (cur := cur) (sl0 := sl0) (sl1 := sl1) (sl2 := sl2) (sl3 := sl3) (sl4 := sl4) (sl5 := sl5) (sl6 := sl6) (sl7 := sl7) (sl8 := sl8) (sl9 := sl9) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w74 := w74) (w78 := w78) (w7c := w7c) (op := op) (ol := ol) (vp := vp) (vl := vl) (rest := rest) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_9 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_27 w0_2c w0_30 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_150 w0_154 w0_34 w0_38 w0_48 w0_4c w0_158 w0_15c w0_44 val_in oid_in SD0 hb hb2 hb3 hb4 hb5 with ⟨-, e⟩ | ⟨tl56, h0, h1, h2, rest⟩
            · exact .inl e
            · obtain ⟨n', fc, f_ST, f_E, f_V, f_FR, f_r2, f_r3, f_r4, f_r8, f_r9, f_r18, f_r19, f_r20, f_r21, f_r22, f_r23, f_r24, f_r25, f_r27, f_w2c, f_w30, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_w98, f_w9c, f_wa0, f_wa4, f_w150, f_w154, f_w158, f_w15c, f_KL⟩ := rest
              exact .inr ⟨f2c, f30, sl0, sl1, (vp) + BitVec.ofNat 32 tl56.header, BitVec.ofNat 32 tl56.len, sl4, sl5, sl6, sl7, sl8, sl9, .inr (.inr (.inr (.inr (.inl ⟨hb, hb2, hb3, hb4, hb5, tl56, h0, h1, h2, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)))), sl0_or0, .inr (((val_in).content (derTlv_elem h0)).ofNatLen), sl4_or0, sl6_or0, sl8_or0, ⟨n', fc, f_FR, f_ST, f_E, f_V, f_r3, f_r4, f_r2, f_r8, f_r9, f_r18, f_r19, f_r20, f_r21, f_r22, f_r23, f_r24, f_r25, f_r27, f_w2c, f_w30, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_w98, f_w9c, f_wa0, f_wa4, f_w150, f_w154, f_w158, f_w15c, f_KL.mono (by decide)⟩⟩
          · by_cases hb6 : memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x41)) 10 = memBytes M0 op ol.toNat
            · rcases sv_dp2 (B := B) (out := out) (bp := bp) (tbp := tbp) (dg := dg) (rootp := rootp) (ll := ll) (sgp := sgp) (kp := kp) (sgl := sgl) (tbl := tbl) (f2c := f2c) (f30 := f30) (rem := rem) (p0 := p0) (L := L) (cur := cur) (sl0 := sl0) (sl1 := sl1) (sl2 := sl2) (sl3 := sl3) (sl4 := sl4) (sl5 := sl5) (sl6 := sl6) (sl7 := sl7) (sl8 := sl8) (sl9 := sl9) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w74 := w74) (w78 := w78) (w7c := w7c) (op := op) (ol := ol) (vp := vp) (vl := vl) (rest := rest) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_9 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_27 w0_2c w0_30 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_150 w0_154 w0_34 w0_38 w0_48 w0_4c w0_158 w0_15c w0_44 val_in oid_in SD0 hb hb2 hb3 hb4 hb5 hb6 with ⟨-, e⟩ | ⟨tl69, h0, h1, h2, rest⟩
              · exact .inl e
              · obtain ⟨n', fc, f_ST, f_E, f_V, f_FR, f_r2, f_r3, f_r4, f_r8, f_r9, f_r18, f_r19, f_r20, f_r21, f_r22, f_r23, f_r24, f_r25, f_r27, f_w2c, f_w30, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_w98, f_w9c, f_wa0, f_wa4, f_w150, f_w154, f_w158, f_w15c, f_KL⟩ := rest
                exact .inr ⟨f2c, f30, sl0, sl1, sl2, sl3, (vp) + BitVec.ofNat 32 tl69.header, BitVec.ofNat 32 tl69.len, sl6, sl7, sl8, sl9, .inr (.inr (.inr (.inr (.inr (.inl ⟨hb, hb2, hb3, hb4, hb5, hb6, tl69, h0, h1, h2, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩))))), sl0_or0, sl2_or0, .inr (((val_in).content (derTlv_elem h0)).ofNatLen), sl6_or0, sl8_or0, ⟨n', fc, f_FR, f_ST, f_E, f_V, f_r3, f_r4, f_r2, f_r8, f_r9, f_r18, f_r19, f_r20, f_r21, f_r22, f_r23, f_r24, f_r25, f_r27, f_w2c, f_w30, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_w98, f_w9c, f_wa0, f_wa4, f_w150, f_w154, f_w158, f_w15c, f_KL.mono (by decide)⟩⟩
            · by_cases hb7 : memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x4B)) 10 = memBytes M0 op ol.toNat
              · rcases sv_dp3 (B := B) (out := out) (bp := bp) (tbp := tbp) (dg := dg) (rootp := rootp) (ll := ll) (sgp := sgp) (kp := kp) (sgl := sgl) (tbl := tbl) (f2c := f2c) (f30 := f30) (rem := rem) (p0 := p0) (L := L) (cur := cur) (sl0 := sl0) (sl1 := sl1) (sl2 := sl2) (sl3 := sl3) (sl4 := sl4) (sl5 := sl5) (sl6 := sl6) (sl7 := sl7) (sl8 := sl8) (sl9 := sl9) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w74 := w74) (w78 := w78) (w7c := w7c) (op := op) (ol := ol) (vp := vp) (vl := vl) (rest := rest) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_9 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_27 w0_2c w0_30 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_150 w0_154 w0_34 w0_38 w0_48 w0_4c w0_158 w0_15c w0_44 val_in oid_in SD0 hb hb2 hb3 hb4 hb5 hb6 hb7 with ⟨-, e⟩ | ⟨tl82, h0, h1, h2, rest⟩
                · exact .inl e
                · obtain ⟨n', fc, f_ST, f_E, f_V, f_FR, f_r2, f_r3, f_r4, f_r8, f_r9, f_r18, f_r19, f_r20, f_r21, f_r22, f_r23, f_r24, f_r25, f_r27, f_w2c, f_w30, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_w98, f_w9c, f_wa0, f_wa4, f_w150, f_w154, f_w158, f_w15c, f_KL⟩ := rest
                  exact .inr ⟨f2c, f30, sl0, sl1, sl2, sl3, sl4, sl5, (vp) + BitVec.ofNat 32 tl82.header, BitVec.ofNat 32 tl82.len, sl8, sl9, .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨hb, hb2, hb3, hb4, hb5, hb6, hb7, tl82, h0, h1, h2, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)))))), sl0_or0, sl2_or0, sl4_or0, .inr (((val_in).content (derTlv_elem h0)).ofNatLen), sl8_or0, ⟨n', fc, f_FR, f_ST, f_E, f_V, f_r3, f_r4, f_r2, f_r8, f_r9, f_r18, f_r19, f_r20, f_r21, f_r22, f_r23, f_r24, f_r25, f_r27, f_w2c, f_w30, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_w98, f_w9c, f_wa0, f_wa4, f_w150, f_w154, f_w158, f_w15c, f_KL.mono (by decide)⟩⟩
              · by_cases hb8 : memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x55)) 10 = memBytes M0 op ol.toNat
                · rcases sv_dp4 (B := B) (out := out) (bp := bp) (tbp := tbp) (dg := dg) (rootp := rootp) (ll := ll) (sgp := sgp) (kp := kp) (sgl := sgl) (tbl := tbl) (f2c := f2c) (f30 := f30) (rem := rem) (p0 := p0) (L := L) (cur := cur) (sl0 := sl0) (sl1 := sl1) (sl2 := sl2) (sl3 := sl3) (sl4 := sl4) (sl5 := sl5) (sl6 := sl6) (sl7 := sl7) (sl8 := sl8) (sl9 := sl9) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w74 := w74) (w78 := w78) (w7c := w7c) (op := op) (ol := ol) (vp := vp) (vl := vl) (rest := rest) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_9 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_27 w0_2c w0_30 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_150 w0_154 w0_34 w0_38 w0_48 w0_4c w0_158 w0_15c w0_44 val_in oid_in SD0 hb hb2 hb3 hb4 hb5 hb6 hb7 hb8 with ⟨-, e⟩ | ⟨tl95, h0, h1, h2, rest⟩
                  · exact .inl e
                  · obtain ⟨n', fc, f_ST, f_E, f_V, f_FR, f_r2, f_r3, f_r4, f_r8, f_r9, f_r18, f_r19, f_r20, f_r21, f_r22, f_r23, f_r24, f_r25, f_r27, f_w2c, f_w30, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_w98, f_w9c, f_wa0, f_wa4, f_w150, f_w154, f_w158, f_w15c, f_KL⟩ := rest
                    exact .inr ⟨f2c, f30, sl0, sl1, sl2, sl3, sl4, sl5, sl6, sl7, (vp) + BitVec.ofNat 32 tl95.header, BitVec.ofNat 32 tl95.len, .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨hb, hb2, hb3, hb4, hb5, hb6, hb7, hb8, tl95, h0, h1, h2, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩))))))), sl0_or0, sl2_or0, sl4_or0, sl6_or0, .inr (((val_in).content (derTlv_elem h0)).ofNatLen), ⟨n', fc, f_FR, f_ST, f_E, f_V, f_r3, f_r4, f_r2, f_r8, f_r9, f_r18, f_r19, f_r20, f_r21, f_r22, f_r23, f_r24, f_r25, f_r27, f_w2c, f_w30, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_w98, f_w9c, f_wa0, f_wa4, f_w150, f_w154, f_w158, f_w15c, f_KL.mono (by decide)⟩⟩
                · rcases sv_dp5 (B := B) (out := out) (bp := bp) (tbp := tbp) (dg := dg) (rootp := rootp) (ll := ll) (sgp := sgp) (kp := kp) (sgl := sgl) (tbl := tbl) (f2c := f2c) (f30 := f30) (rem := rem) (p0 := p0) (L := L) (cur := cur) (sl0 := sl0) (sl1 := sl1) (sl2 := sl2) (sl3 := sl3) (sl4 := sl4) (sl5 := sl5) (sl6 := sl6) (sl7 := sl7) (sl8 := sl8) (sl9 := sl9) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w74 := w74) (w78 := w78) (w7c := w7c) (op := op) (ol := ol) (vp := vp) (vl := vl) (rest := rest) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_9 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_27 w0_2c w0_30 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_150 w0_154 w0_34 w0_38 w0_48 w0_4c w0_158 w0_15c w0_44 val_in oid_in SD0 hb hb2 hb3 hb4 hb5 hb6 hb7 hb8 with ⟨-, e⟩ | rest
                  · exact .inl e
                  · obtain ⟨n', fc, f_ST, f_E, f_V, f_FR, f_r2, f_r3, f_r4, f_r8, f_r9, f_r18, f_r19, f_r20, f_r21, f_r22, f_r23, f_r24, f_r25, f_r27, f_w2c, f_w30, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_w98, f_w9c, f_wa0, f_wa4, f_w150, f_w154, f_w158, f_w15c, f_KL⟩ := rest
                    exact .inr ⟨f2c, f30, sl0, sl1, sl2, sl3, sl4, sl5, sl6, sl7, sl8, sl9, .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨hb, hb2, hb3, hb4, hb5, hb6, hb7, hb8, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩))))))), sl0_or0, sl2_or0, sl4_or0, sl6_or0, sl8_or0, ⟨n', fc, f_FR, f_ST, f_E, f_V, f_r3, f_r4, f_r2, f_r8, f_r9, f_r18, f_r19, f_r20, f_r21, f_r22, f_r23, f_r24, f_r25, f_r27, f_w2c, f_w30, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_w98, f_w9c, f_wa0, f_wa4, f_w150, f_w154, f_w158, f_w15c, f_KL.mono (by decide)⟩⟩

end C3.RV32.Sv
