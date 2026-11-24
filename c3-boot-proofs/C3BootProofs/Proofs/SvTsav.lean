import C3BootProofs.Proofs.SvTsavct
import C3BootProofs.Proofs.SvTsavmd
import C3BootProofs.Proofs.SvTsavother

/-!
# `sigstore::verify`: One signed attribute's value: the content type, the message digest, or another.

Written by `scripts/gen-sv-segs.py` from `sv_tsavct`, `sv_tsavmd`, and `sv_tsavother`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxHeartbeats 16000000 in
/-- One signed attribute's value: the content type, the message digest, or another. -/
theorem sv_tsav {w78 B out bp x21 x26 dg p0 L0 cp rem op ol vcp vcl x20 w24 w28 w2c w30 w34 w38 w3c w40 w44 w48 w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w7c w80 w84 w88 w8c w90 w94 w98 w9c wa0 wa4 wa8 wac wb0 wb4 wb8 wbc wc0 wc4 wc8 wcc wd0 wd4 wd8 wdc we0 we4 we8 wec wf0 wf4 wf8 wfc w100 w104 w108 w10c w110 w114 w118 w11c w120 w124 w128 w12c w130 : Word} {v : Nat → Word} {n0 : Machine}
    (F : Fr B 0x3830)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out)
    (s0 : St n0.mem SV n0 0x25DA (reg n0))
    (M0 : Word → BitVec 8)
    (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_9 : reg n0 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = x20)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_24 : reg n0 (24 : Fin 32) = dg)
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
    (w0_74 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = p0)
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
    (w0_1320 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = p0)
    (w0_1324 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = L0)
    (w0_1328 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = cp)
    (w0_132c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = rem)
    (w0_1388 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1388) = vcp)
    (w0_138c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x138C) = vcl)
    (cr_in : SvIn B (cp) (rem).toNat)
    (p0_in : SvIn B (p0) (L0).toNat)
    (w0_78 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78)
    (g0_22 : reg n0 (22 : Fin 32) = ol)
    (g0_23 : reg n0 (23 : Fin 32) = op)
    (g0_25 : reg n0 (25 : Fin 32) = L0)
    (oid_in : SvIn B op ol.toNat)
    (vc_in : SvIn B vcp vcl.toNat)
    (dg_or0 : dg = 0 ∨ SvIn B dg 32) :
    SvErrRet B out v n0 ∨
    (∃ tsav_r24 : Word, ∃ tsav_w78 : Word, ∃ tsav_w1388 : Word, ∃ tsav_w138c : Word, (((memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x56)) 9) ∧ ∃ op5 ol5, derContent (vcp) (derOid (memBytes M0 (vcp) (vcl).toNat)) = .ok (op5, ol5) ∧ ∃ to5, derOid (memBytes M0 (vcp) (vcl).toNat) = .ok to5 ∧ (memBytes M0 op5 ol5.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x4A)) 11) ∧ ((vcl) - BitVec.ofNat 32 (to5.header + to5.len) = 0) ∧ tsav_r24 = dg ∧ tsav_w78 = BitVec.ofNat 32 0x1 ∧ tsav_w1388 = (vcp) + BitVec.ofNat 32 (to5.header + to5.len) ∧ tsav_w138c = (vcl) - BitVec.ofNat 32 (to5.header + to5.len)) ∨ ((¬ (memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x56)) 9)) ∧ (memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x5F)) 9) ∧ ∃ vp8 vl8, derContent (vcp) (derElement 4 (memBytes M0 (vcp) (vcl).toNat)) = .ok (vp8, vl8) ∧ ∃ te8, derElement 4 (memBytes M0 (vcp) (vcl).toNat) = .ok te8 ∧ (vl8 = 32) ∧ ((vcl) - BitVec.ofNat 32 (te8.header + te8.len) = 0) ∧ tsav_r24 = vp8 ∧ tsav_w78 = w78 ∧ tsav_w1388 = (vcp) + BitVec.ofNat 32 (te8.header + te8.len) ∧ tsav_w138c = (vcl) - BitVec.ofNat 32 (te8.header + te8.len)) ∨ ((¬ (memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x56)) 9)) ∧ (¬ (memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x5F)) 9)) ∧ tsav_r24 = dg ∧ tsav_w78 = w78 ∧ tsav_w1388 = vcp ∧ tsav_w138c = vcl)) ∧ SvIn B tsav_w1388 tsav_w138c.toNat ∧ (tsav_r24 = 0 ∨ SvIn B tsav_r24 32) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x267A (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = x20 ∧
        reg n' (21 : Fin 32) = x21 ∧
        reg n' (24 : Fin 32) = tsav_r24 ∧
        reg n' (25 : Fin 32) = L0 ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 ∧
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
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = p0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tsav_w78 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = p0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = L0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = cp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = rem ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1388) = tsav_w1388 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x138C) = tsav_w138c ∧
        SvKeepL B n0.mem n'.mem [(0x420, 0x8), (0x1388, 0x8), (0x78, 0x4)]) := by
  by_cases hb : memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x56)) 9
  · rcases sv_tsavct (w78 := w78) (B := B) (out := out) (bp := bp) (x21 := x21) (x26 := x26) (dg := dg) (p0 := p0) (L0 := L0) (cp := cp) (rem := rem) (op := op) (ol := ol) (vcp := vcp) (vcl := vcl) (x20 := x20) (w24 := w24) (w28 := w28) (w2c := w2c) (w30 := w30) (w34 := w34) (w38 := w38) (w3c := w3c) (w40 := w40) (w44 := w44) (w48 := w48) (w4c := w4c) (w50 := w50) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w7c := w7c) (w80 := w80) (w84 := w84) (w88 := w88) (w8c := w8c) (w90 := w90) (w94 := w94) (w98 := w98) (w9c := w9c) (wa0 := wa0) (wa4 := wa4) (wa8 := wa8) (wac := wac) (wb0 := wb0) (wb4 := wb4) (wb8 := wb8) (wbc := wbc) (wc0 := wc0) (wc4 := wc4) (wc8 := wc8) (wcc := wcc) (wd0 := wd0) (wd4 := wd4) (wd8 := wd8) (wdc := wdc) (we0 := we0) (we4 := we4) (we8 := we8) (wec := wec) (wf0 := wf0) (wf4 := wf4) (wf8 := wf8) (wfc := wfc) (w100 := w100) (w104 := w104) (w108 := w108) (w10c := w10c) (w110 := w110) (w114 := w114) (w118 := w118) (w11c := w11c) (w120 := w120) (w124 := w124) (w128 := w128) (w12c := w12c) (w130 := w130) (v := v) (n0 := n0) F E0 V0 hret hO s0 M0 fM g0_2 g0_9 g0_18 g0_19 g0_20 g0_21 g0_24 g0_26 g0_27 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_3c w0_40 w0_44 w0_48 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_a8 w0_ac w0_b0 w0_b4 w0_b8 w0_bc w0_c0 w0_c4 w0_c8 w0_cc w0_d0 w0_d4 w0_d8 w0_dc w0_e0 w0_e4 w0_e8 w0_ec w0_f0 w0_f4 w0_f8 w0_fc w0_100 w0_104 w0_108 w0_10c w0_110 w0_114 w0_118 w0_11c w0_120 w0_124 w0_128 w0_12c w0_130 w0_1320 w0_1324 w0_1328 w0_132c w0_1388 w0_138c cr_in p0_in w0_78 g0_22 g0_23 g0_25 oid_in vc_in hb with ⟨-, e⟩ | ⟨op5, ol5, h0, to5, h1, h2, h3, rest⟩
    · exact .inl e
    · exact .inr ⟨dg, BitVec.ofNat 32 0x1, (vcp) + BitVec.ofNat 32 (to5.header + to5.len), (vcl) - BitVec.ofNat 32 (to5.header + to5.len), .inl ⟨hb, op5, ol5, h0, to5, h1, h2, h3, rfl, rfl, rfl, rfl⟩, (vc_in).restW (derOid_ok_elem h1), dg_or0, rest.imp (fun _ => fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun k => k.mono (by decide)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))⟩
  · by_cases hb2 : memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x5F)) 9
    · rcases sv_tsavmd (w78 := w78) (B := B) (out := out) (bp := bp) (x21 := x21) (x26 := x26) (dg := dg) (p0 := p0) (L0 := L0) (cp := cp) (rem := rem) (op := op) (ol := ol) (vcp := vcp) (vcl := vcl) (x20 := x20) (w24 := w24) (w28 := w28) (w2c := w2c) (w30 := w30) (w34 := w34) (w38 := w38) (w3c := w3c) (w40 := w40) (w44 := w44) (w48 := w48) (w4c := w4c) (w50 := w50) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w7c := w7c) (w80 := w80) (w84 := w84) (w88 := w88) (w8c := w8c) (w90 := w90) (w94 := w94) (w98 := w98) (w9c := w9c) (wa0 := wa0) (wa4 := wa4) (wa8 := wa8) (wac := wac) (wb0 := wb0) (wb4 := wb4) (wb8 := wb8) (wbc := wbc) (wc0 := wc0) (wc4 := wc4) (wc8 := wc8) (wcc := wcc) (wd0 := wd0) (wd4 := wd4) (wd8 := wd8) (wdc := wdc) (we0 := we0) (we4 := we4) (we8 := we8) (wec := wec) (wf0 := wf0) (wf4 := wf4) (wf8 := wf8) (wfc := wfc) (w100 := w100) (w104 := w104) (w108 := w108) (w10c := w10c) (w110 := w110) (w114 := w114) (w118 := w118) (w11c := w11c) (w120 := w120) (w124 := w124) (w128 := w128) (w12c := w12c) (w130 := w130) (v := v) (n0 := n0) F E0 V0 hret hO s0 M0 fM g0_2 g0_9 g0_18 g0_19 g0_20 g0_21 g0_24 g0_26 g0_27 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_3c w0_40 w0_44 w0_48 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_a8 w0_ac w0_b0 w0_b4 w0_b8 w0_bc w0_c0 w0_c4 w0_c8 w0_cc w0_d0 w0_d4 w0_d8 w0_dc w0_e0 w0_e4 w0_e8 w0_ec w0_f0 w0_f4 w0_f8 w0_fc w0_100 w0_104 w0_108 w0_10c w0_110 w0_114 w0_118 w0_11c w0_120 w0_124 w0_128 w0_12c w0_130 w0_1320 w0_1324 w0_1328 w0_132c w0_1388 w0_138c cr_in p0_in w0_78 g0_22 g0_23 g0_25 oid_in vc_in hb hb2 with ⟨-, e⟩ | ⟨vp8, vl8, h0, te8, h1, h2, h3, rest⟩
      · exact .inl e
      · exact .inr ⟨vp8, w78, (vcp) + BitVec.ofNat 32 (te8.header + te8.len), (vcl) - BitVec.ofNat 32 (te8.header + te8.len), .inr (.inl ⟨hb, hb2, vp8, vl8, h0, te8, h1, h2, h3, rfl, rfl, rfl, rfl⟩), (vc_in).restW h1, .inr (by have h := (vc_in).contentIn h0; rw [h2] at h; exact h), rest.imp (fun _ => fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun k => k.mono (by decide)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))⟩
    · rcases sv_tsavother (w78 := w78) (B := B) (out := out) (bp := bp) (x21 := x21) (x26 := x26) (dg := dg) (p0 := p0) (L0 := L0) (cp := cp) (rem := rem) (op := op) (ol := ol) (vcp := vcp) (vcl := vcl) (x20 := x20) (w24 := w24) (w28 := w28) (w2c := w2c) (w30 := w30) (w34 := w34) (w38 := w38) (w3c := w3c) (w40 := w40) (w44 := w44) (w48 := w48) (w4c := w4c) (w50 := w50) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w7c := w7c) (w80 := w80) (w84 := w84) (w88 := w88) (w8c := w8c) (w90 := w90) (w94 := w94) (w98 := w98) (w9c := w9c) (wa0 := wa0) (wa4 := wa4) (wa8 := wa8) (wac := wac) (wb0 := wb0) (wb4 := wb4) (wb8 := wb8) (wbc := wbc) (wc0 := wc0) (wc4 := wc4) (wc8 := wc8) (wcc := wcc) (wd0 := wd0) (wd4 := wd4) (wd8 := wd8) (wdc := wdc) (we0 := we0) (we4 := we4) (we8 := we8) (wec := wec) (wf0 := wf0) (wf4 := wf4) (wf8 := wf8) (wfc := wfc) (w100 := w100) (w104 := w104) (w108 := w108) (w10c := w10c) (w110 := w110) (w114 := w114) (w118 := w118) (w11c := w11c) (w120 := w120) (w124 := w124) (w128 := w128) (w12c := w12c) (w130 := w130) (v := v) (n0 := n0) F E0 V0 hret hO s0 M0 fM g0_2 g0_9 g0_18 g0_19 g0_20 g0_21 g0_24 g0_26 g0_27 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_3c w0_40 w0_44 w0_48 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_a8 w0_ac w0_b0 w0_b4 w0_b8 w0_bc w0_c0 w0_c4 w0_c8 w0_cc w0_d0 w0_d4 w0_d8 w0_dc w0_e0 w0_e4 w0_e8 w0_ec w0_f0 w0_f4 w0_f8 w0_fc w0_100 w0_104 w0_108 w0_10c w0_110 w0_114 w0_118 w0_11c w0_120 w0_124 w0_128 w0_12c w0_130 w0_1320 w0_1324 w0_1328 w0_132c w0_1388 w0_138c cr_in p0_in w0_78 g0_22 g0_23 g0_25 oid_in vc_in hb hb2 with ⟨-, e⟩ | rest
      · exact .inl e
      · exact .inr ⟨dg, w78, vcp, vcl, .inr (.inr ⟨hb, hb2, rfl, rfl, rfl, rfl⟩), vc_in, dg_or0, rest.imp (fun _ => fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun k => k.mono (by decide)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))⟩

end C3.RV32.Sv
