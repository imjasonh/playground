import C3BootProofs.Proofs.SvSeg
import C3BootProofs.Proofs.SvDpv
import C3BootProofs.Proofs.SvTs1

/-!
# `sigstore::verify`: The policy, then the signature's DER

Composed from generated stages by `scripts/gen-sv-segs.py`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 100000

set_option maxHeartbeats 64000000 in
/-- **The policy, then the signature's DER**: from 0xDE6 to the P-256 check at 0xFBA, `sv_dpv` and `sv_ts1`. -/
theorem sv_seg_dpv {B out bp x21 x26 pv tsp tsl e0p e0l e1p e1l e2p e2l e3p e3l e4p e4l : Word} {w24 w28 w2c w30 w34 w38 w3c w40 w44 w48 w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w7c w80 w84 w88 w8c w90 w94 w98 w9c wa0 wa4 wa8 wac wb0 wb4 wb8 wbc wc0 wc4 wc8 wcc wd0 wd4 wd8 wdc we0 we4 we8 wec wf0 wf4 wf8 wfc w100 w104 w108 w10c w110 w114 w118 w11c w120 w124 w128 w12c w130 : Word} {v : Nat → Word} {n0 : Machine}
    (F : Fr B 0x3830)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out)
    (s0 : St n0.mem SV n0 0xDE6 (reg n0))
    (M0 : Word → BitVec 8)
    (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_10 : reg n0 a0 = pv)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_26 : reg n0 (26 : Fin 32) = x26)
    (g0_27 : reg n0 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20)
    (w0_24 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24)
    (w0_28 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28)
    (w0_2c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c)
    (w0_30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30)
    (w0_34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34)
    (w0_38 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38)
    (w0_3c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c)
    (w0_40 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40)
    (w0_44 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44)
    (w0_48 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48)
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
    (w0_7c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c)
    (w0_80 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80)
    (w0_84 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84)
    (w0_88 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88)
    (w0_8c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c)
    (w0_90 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90)
    (w0_94 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94)
    (w0_98 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98)
    (w0_9c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c)
    (w0_a0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0)
    (w0_a4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4)
    (w0_a8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8)
    (w0_ac : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac)
    (w0_b0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0)
    (w0_b4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4)
    (w0_b8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8)
    (w0_bc : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc)
    (w0_c0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0)
    (w0_c4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4)
    (w0_c8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8)
    (w0_cc : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc)
    (w0_d0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0)
    (w0_d4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4)
    (w0_d8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8)
    (w0_dc : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc)
    (w0_e0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0)
    (w0_e4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4)
    (w0_e8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8)
    (w0_ec : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec)
    (w0_f0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0)
    (w0_f4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4)
    (w0_f8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8)
    (w0_fc : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc)
    (w0_100 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100)
    (w0_104 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104)
    (w0_108 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108)
    (w0_10c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c)
    (w0_110 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110)
    (w0_114 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114)
    (w0_118 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118)
    (w0_11c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c)
    (w0_120 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120)
    (w0_124 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124)
    (w0_128 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128)
    (w0_12c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c)
    (w0_130 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130)
    (ts_in : SvIn B (tsp) (tsl).toNat)
    (he0p : memLoad32 M0 (w80 + 0x0) = e0p)
    (he0l : memLoad32 M0 (w80 + 0x4) = e0l)
    (he0p_in : SvIn B (w80 + 0x0) 4)
    (he0l_in : SvIn B (w80 + 0x4) 4)
    (ae0p : (w80 + 0x0).toNat % 4 = 0)
    (ae0l : (w80 + 0x4).toNat % 4 = 0)
    (p0_in : SvRo B w48 w34.toNat)
    (e0_in : SvRo B e0p e0l.toNat)
    (he1p : memLoad32 M0 (w80 + 0x8) = e1p)
    (he1l : memLoad32 M0 (w80 + 0xC) = e1l)
    (he1p_in : SvIn B (w80 + 0x8) 4)
    (he1l_in : SvIn B (w80 + 0xC) 4)
    (ae1p : (w80 + 0x8).toNat % 4 = 0)
    (ae1l : (w80 + 0xC).toNat % 4 = 0)
    (p1_in : SvRo B w44 w30.toNat)
    (e1_in : SvRo B e1p e1l.toNat)
    (he2p : memLoad32 M0 (w80 + 0x10) = e2p)
    (he2l : memLoad32 M0 (w80 + 0x14) = e2l)
    (he2p_in : SvIn B (w80 + 0x10) 4)
    (he2l_in : SvIn B (w80 + 0x14) 4)
    (ae2p : (w80 + 0x10).toNat % 4 = 0)
    (ae2l : (w80 + 0x14).toNat % 4 = 0)
    (p2_in : SvRo B w40 w2c.toNat)
    (e2_in : SvRo B e2p e2l.toNat)
    (he3p : memLoad32 M0 (w80 + 0x18) = e3p)
    (he3l : memLoad32 M0 (w80 + 0x1C) = e3l)
    (he3p_in : SvIn B (w80 + 0x18) 4)
    (he3l_in : SvIn B (w80 + 0x1C) 4)
    (ae3p : (w80 + 0x18).toNat % 4 = 0)
    (ae3l : (w80 + 0x1C).toNat % 4 = 0)
    (p3_in : SvRo B w3c w28.toNat)
    (e3_in : SvRo B e3p e3l.toNat)
    (he4p : memLoad32 M0 (w80 + 0x20) = e4p)
    (he4l : memLoad32 M0 (w80 + 0x24) = e4l)
    (he4p_in : SvIn B (w80 + 0x20) 4)
    (he4l_in : SvIn B (w80 + 0x24) 4)
    (ae4p : (w80 + 0x20).toNat % 4 = 0)
    (ae4l : (w80 + 0x24).toNat % 4 = 0)
    (p4_in : SvRo B w38 w24.toNat)
    (e4_in : SvRo B e4p e4l.toNat)
    (htsp : memLoad32 M0 (bp + 0x8) = tsp)
    (htsl : memLoad32 M0 (bp + 0xC) = tsl)
    (htsp_in : SvIn B (bp + 0x8) 4)
    (htsl_in : SvIn B (bp + 0xC) 4)
    (atsp : (bp + 0x8).toNat % 4 = 0)
    (atsl : (bp + 0xC).toNat % 4 = 0) :
    SvErrRet B out v n0 ∨ Panics n0 ∨
    ((pv ≠ 0) ∧
      (memBytes M0 w48 w34.toNat = memBytes M0 e0p e0l.toNat) ∧
      (memBytes M0 w44 w30.toNat = memBytes M0 e1p e1l.toNat) ∧
      (memBytes M0 w40 w2c.toNat = memBytes M0 e2p e2l.toNat) ∧
      (memBytes M0 w3c w28.toNat = memBytes M0 e3p e3l.toNat) ∧
      (memBytes M0 w38 w24.toNat = memBytes M0 e4p e4l.toNat) ∧
      ∃ tl49_1, derElement 0x30 (memBytes M0 (tsp) (tsl).toNat) = .ok tl49_1 ∧
      ((tsl) - BitVec.ofNat 32 (tl49_1.header + tl49_1.len) = 0) ∧
      ∃ bs9_2, derScalarOf 32 (memBytes M0 ((tsp) + BitVec.ofNat 32 tl49_1.header) (BitVec.ofNat 32 tl49_1.len).toNat) ((tsp) + BitVec.ofNat 32 tl49_1.header) (derElement 2 (memBytes M0 ((tsp) + BitVec.ofNat 32 tl49_1.header) (BitVec.ofNat 32 tl49_1.len).toNat)) = .ok bs9_2 ∧
      ∃ te9_2, derElement 2 (memBytes M0 ((tsp) + BitVec.ofNat 32 tl49_1.header) (BitVec.ofNat 32 tl49_1.len).toNat) = .ok te9_2 ∧
      ∃ bs16_2, derScalarOf 32 (memBytes M0 (((tsp) + BitVec.ofNat 32 tl49_1.header) + BitVec.ofNat 32 (te9_2.header + te9_2.len)) ((BitVec.ofNat 32 tl49_1.len) - BitVec.ofNat 32 (te9_2.header + te9_2.len)).toNat) (((tsp) + BitVec.ofNat 32 tl49_1.header) + BitVec.ofNat 32 (te9_2.header + te9_2.len)) (derElement 2 (memBytes M0 (((tsp) + BitVec.ofNat 32 tl49_1.header) + BitVec.ofNat 32 (te9_2.header + te9_2.len)) ((BitVec.ofNat 32 tl49_1.len) - BitVec.ofNat 32 (te9_2.header + te9_2.len)).toNat)) = .ok bs16_2 ∧
      ∃ te16_2, derElement 2 (memBytes M0 (((tsp) + BitVec.ofNat 32 tl49_1.header) + BitVec.ofNat 32 (te9_2.header + te9_2.len)) ((BitVec.ofNat 32 tl49_1.len) - BitVec.ofNat 32 (te9_2.header + te9_2.len)).toNat) = .ok te16_2 ∧
      (((BitVec.ofNat 32 tl49_1.len) - BitVec.ofNat 32 (te9_2.header + te9_2.len)) - BitVec.ofNat 32 (te16_2.header + te16_2.len) = 0) ∧
      ∃ m', Steps n0 m' ∧ (∀ x, SvR B x → m'.mem x = M0 x) ∧ St m'.mem SV m' 0xFBA (reg m') ∧
        SvCode m'.mem ∧ SvSaves B m'.mem v ∧ reg m' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg m' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg m' sp = B + 0x21A0 ∧
        reg m' (8 : Fin 32) = BitVec.ofNat 32 0x1 ∧
        reg m' (9 : Fin 32) = (BitVec.ofNat 8 ((bs16_2).getD 0 0)).zeroExtend 32 ∧
        reg m' (18 : Fin 32) = out ∧
        reg m' (19 : Fin 32) = bp ∧
        reg m' (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 ∧
        reg m' (21 : Fin 32) = x21 ∧
        reg m' (22 : Fin 32) = (BitVec.ofNat 8 ((bs9_2).getD 0 0)).zeroExtend 32 ∧
        reg m' (26 : Fin 32) = x26 ∧
        reg m' (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = tsl ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = tsp ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = (tsp) + BitVec.ofNat 32 tl49_1.header ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = BitVec.ofNat 32 tl49_1.len ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (((tsp) + BitVec.ofNat 32 tl49_1.header) + BitVec.ofNat 32 (te9_2.header + te9_2.len)) + BitVec.ofNat 32 (te16_2.header + te16_2.len) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = ((BitVec.ofNat 32 tl49_1.len) - BitVec.ofNat 32 (te9_2.header + te9_2.len)) - BitVec.ofNat 32 (te16_2.header + te16_2.len) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = tsp ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = tsl ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = (tsp) + BitVec.ofNat 32 (tl49_1.header + tl49_1.len) ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = (tsl) - BitVec.ofNat 32 (tl49_1.header + tl49_1.len) ∧
        m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x138) = BitVec.ofNat 8 ((bs9_2).getD 0 0) ∧
        m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = BitVec.ofNat 8 ((bs16_2).getD 0 0) ∧
        m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) ∧
        m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA21) = BitVec.ofNat 8 ((bs16_2).getD 0 0) ∧
        (∀ j, j < 31 → m'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x139 + j)) = BitVec.ofNat 8 ((bs9_2).getD (1 + j) 0)) ∧
        (∀ j, j < 31 → m'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x159 + j)) = BitVec.ofNat 8 ((bs16_2).getD (1 + j) 0)) ∧
        (∀ j, j < 31 → m'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 ((bs16_2).getD (1 + j) 0)) ∧
        (∀ j, j < 32 → m'.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 ((bs16_2).getD j 0)) ∧
        (∀ j, j < 31 → m'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1020 + j)) = BitVec.ofNat 8 ((bs9_2).getD (1 + j) 0)) ∧
        (∀ j, j < 31 → m'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1380 + j)) = BitVec.ofNat 8 ((bs16_2).getD (1 + j) 0)) ∧
        (∀ j, j < 31 → m'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1480 + j)) = BitVec.ofNat 8 ((bs9_2).getD (1 + j) 0))) := by
  rcases sv_dpv F E0 V0 hret hO s0 M0 fM g0_2 g0_10 g0_18 g0_19 g0_21 g0_26 g0_27 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_3c w0_40 w0_44 w0_48 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_a8 w0_ac w0_b0 w0_b4 w0_b8 w0_bc w0_c0 w0_c4 w0_c8 w0_cc w0_d0 w0_d4 w0_d8 w0_dc w0_e0 w0_e4 w0_e8 w0_ec w0_f0 w0_f4 w0_f8 w0_fc w0_100 w0_104 w0_108 w0_10c w0_110 w0_114 w0_118 w0_11c w0_120 w0_124 w0_128 w0_12c w0_130 ts_in he0p he0l he0p_in he0l_in ae0p ae0l p0_in e0_in he1p he1l he1p_in he1l_in ae1p ae1l p1_in e1_in he2p he2l he2p_in he2l_in ae2p ae2l p2_in e2_in he3p he3l he3p_in he3l_in ae3p ae3l p3_in e3_in he4p he4l he4p_in he4l_in ae4p ae4l p4_in e4_in htsp htsl htsp_in htsl_in atsp atsl with ⟨-, e⟩ | ⟨x1_0, x1_1, x1_2, x1_3, x1_4, x1_5, tl49_1, x1_6, n1, c1, s1, E1, V1, fR1, r1_2, r1_3, r1_4, r1_8, r1_9, r1_18, r1_19, r1_20, r1_21, r1_26, r1_27, w1_24, w1_28, w1_2c, w1_30, w1_34, w1_38, w1_3c, w1_40, w1_44, w1_48, w1_4c, w1_50, w1_54, w1_58, w1_5c, w1_60, w1_64, w1_68, w1_6c, w1_70, w1_7c, w1_80, w1_84, w1_88, w1_8c, w1_90, w1_94, w1_98, w1_9c, w1_a0, w1_a4, w1_a8, w1_ac, w1_b0, w1_b4, w1_b8, w1_bc, w1_c0, w1_c4, w1_c8, w1_cc, w1_d0, w1_d4, w1_d8, w1_dc, w1_e0, w1_e4, w1_e8, w1_ec, w1_f0, w1_f4, w1_f8, w1_fc, w1_100, w1_104, w1_108, w1_10c, w1_110, w1_114, w1_118, w1_11c, w1_120, w1_124, w1_128, w1_12c, w1_130, w1_a20, w1_a24, w1_a28, w1_a2c, w1_1320, w1_1324, w1_1328, w1_132c, b1_a24, K1_L⟩
  · exact .inl e
  rcases sv_ts1 F E1 V1 hret hO s1 M0 fR1 r1_2 r1_8 r1_9 r1_18 r1_19 r1_20 r1_21 r1_26 r1_27 w1_24 w1_28 w1_2c w1_30 w1_34 w1_38 w1_3c w1_40 w1_44 w1_48 w1_4c w1_50 w1_54 w1_58 w1_5c w1_60 w1_64 w1_68 w1_6c w1_70 w1_7c w1_80 w1_84 w1_88 w1_8c w1_90 w1_94 w1_98 w1_9c w1_a0 w1_a4 w1_a8 w1_ac w1_b0 w1_b4 w1_b8 w1_bc w1_c0 w1_c4 w1_c8 w1_cc w1_d0 w1_d4 w1_d8 w1_dc w1_e0 w1_e4 w1_e8 w1_ec w1_f0 w1_f4 w1_f8 w1_fc w1_100 w1_104 w1_108 w1_10c w1_110 w1_114 w1_118 w1_11c w1_120 w1_124 w1_128 w1_12c w1_130 w1_a20 w1_a24 w1_a28 w1_a2c w1_1320 w1_1324 w1_1328 w1_132c b1_a24 (ts_in) x1_6 with ⟨-, e⟩ | ⟨x2_0, bs9_2, x2_1, te9_2, x2_2, bs16_2, x2_3, te16_2, x2_4, x2_5, n2, c2, s2, E2, V2, fR2, r2_2, r2_3, r2_4, r2_8, r2_9, r2_18, r2_19, r2_20, r2_21, r2_22, r2_26, r2_27, w2_24, w2_28, w2_2c, w2_30, w2_34, w2_38, w2_3c, w2_40, w2_44, w2_48, w2_4c, w2_50, w2_54, w2_58, w2_5c, w2_60, w2_64, w2_68, w2_6c, w2_70, w2_7c, w2_80, w2_84, w2_88, w2_8c, w2_90, w2_94, w2_98, w2_9c, w2_a0, w2_a4, w2_a8, w2_ac, w2_b0, w2_b4, w2_b8, w2_bc, w2_c0, w2_c4, w2_c8, w2_cc, w2_d0, w2_d4, w2_d8, w2_dc, w2_e0, w2_e4, w2_e8, w2_ec, w2_f0, w2_f4, w2_f8, w2_fc, w2_100, w2_104, w2_108, w2_10c, w2_110, w2_114, w2_118, w2_11c, w2_120, w2_124, w2_128, w2_12c, w2_130, w2_320, w2_324, w2_328, w2_32c, w2_1320, w2_1324, w2_1328, w2_132c, b2_138, b2_158, b2_a20, b2_a21, q2_139, q2_159, q2_420, q2_a21, q2_1020, q2_1380, q2_1480, K2_L⟩
  · exact .inl (SvErrRet.pre (c1) (by rw [r1_3]) (by rw [r1_4])
      (fun x hx => (fR1 x hx).trans (fM x hx).symm) e)
  exact .inr (.inr ⟨x1_0, x1_1, x1_2, x1_3, x1_4, x1_5, tl49_1, x1_6, x2_0, bs9_2, x2_1, te9_2, x2_2, bs16_2, x2_3, te16_2, x2_4, x2_5, n2, c1.trans (c2), fR2, s2, E2, V2,
    by rw [r2_3, r1_3], by rw [r2_4, r1_4], r2_2, r2_8, r2_9, r2_18, r2_19, r2_20, r2_21, r2_22, r2_26, r2_27, w2_24, w2_28, w2_2c, w2_30, w2_34, w2_38, w2_3c, w2_40, w2_44, w2_48, w2_4c, w2_50, w2_54, w2_58, w2_5c, w2_60, w2_64, w2_68, w2_6c, w2_70, w2_7c, w2_80, w2_84, w2_88, w2_8c, w2_90, w2_94, w2_98, w2_9c, w2_a0, w2_a4, w2_a8, w2_ac, w2_b0, w2_b4, w2_b8, w2_bc, w2_c0, w2_c4, w2_c8, w2_cc, w2_d0, w2_d4, w2_d8, w2_dc, w2_e0, w2_e4, w2_e8, w2_ec, w2_f0, w2_f4, w2_f8, w2_fc, w2_100, w2_104, w2_108, w2_10c, w2_110, w2_114, w2_118, w2_11c, w2_120, w2_124, w2_128, w2_12c, w2_130, w2_320, w2_324, w2_328, w2_32c, w2_1320, w2_1324, w2_1328, w2_132c, b2_138, b2_158, b2_a20, b2_a21, q2_139, q2_159, q2_420, q2_a21, q2_1020, q2_1380, q2_1480⟩)

end C3.RV32.Sv
