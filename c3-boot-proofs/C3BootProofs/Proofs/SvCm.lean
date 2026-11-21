import C3BootProofs.Proofs.SvCme
import C3BootProofs.Proofs.SvCmdn
import C3BootProofs.Proofs.SvCmdl
import C3BootProofs.Proofs.SvCms
import C3BootProofs.Proofs.SvCmf
import C3BootProofs.Proofs.SvCmx
import C3BootProofs.Proofs.SvCmk
import C3BootProofs.Proofs.SvCmn

/-!
# `sigstore::verify`: The end of a signature line, empty or not.

Written by `scripts/gen-sv-segs.py` from `sv_cme`, `sv_cmdn`, `sv_cmdl`, `sv_cms`, `sv_cmf`, `sv_cmx`, `sv_cmk`, and `sv_cmn`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxHeartbeats 16000000 in
/-- The end of a signature line, empty or not. -/
theorem sv_cm {dp B out bp : Word} {x21 : Word} {x26 dg c q : Word} {rl rp : Word} {sgp : Word} {op ol : Word} {pg gi s0v s5v s7v waa4 : Word} {rt sg : Bytes} {w8 wc w14 w18 w20 w24 w28 w2c w30 w34 w38 w3c w40 w44 w48 w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w78 w7c w80 w84 w88 w8c w90 w94 w98 w9c wa0 wa4 wa8 wac wb0 wb4 wb8 wbc wc0 wc4 wc8 wcc wd0 wd4 wd8 wdc we0 we4 we8 wec wf0 wf4 wf8 wfc w100 w104 w108 w10c w110 w114 w118 w11c w120 w124 w128 w12c w130 wa20 wa24 wa28 wa2c wa30 wa34 wa38 wa3c : Word} {v : Nat → Word} {n0 : Machine}
    (F : Fr B 0x3830)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out)
    (s0 : St n0.mem SV n0 0x2E0C (reg n0))
    (M0 : Word → BitVec 8)
    (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_24 : reg n0 (24 : Fin 32) = dg)
    (g0_25 : reg n0 (25 : Fin 32) = q)
    (g0_26 : reg n0 (26 : Fin 32) = x26)
    (g0_27 : reg n0 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20)
    (w0_8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8)
    (w0_c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc)
    (w0_14 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = w14)
    (w0_18 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = w18)
    (w0_1c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32)
    (w0_20 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = w20)
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
    (w0_78 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78)
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
    (w0_428 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp)
    (w0_a20 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = wa20)
    (w0_a24 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = wa24)
    (w0_a28 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = wa28)
    (w0_a2c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = wa2c)
    (w0_a30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = wa30)
    (w0_a34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = wa34)
    (w0_a38 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = wa38)
    (w0_a3c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = wa3c)
    (w0_aa0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp)
    (w0_aa4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = waa4)
    (q0_320 : ∀ j, j < 31 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0))
    (w0_10 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = (BitVec.ofNat 8 (sg.getD 0 0)).zeroExtend 32)
    (q0_1480 : ∀ j, j < 63 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1480 + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0))
    (g0_10 : reg n0 a0 = pg)
    (g0_22 : reg n0 (22 : Fin 32) = gi)
    (g0_8 : reg n0 (8 : Fin 32) = s0v)
    (g0_21 : reg n0 (21 : Fin 32) = s5v)
    (g0_23 : reg n0 (23 : Fin 32) = s7v)
    (g0_9 : reg n0 (9 : Fin 32) = c)
    (hend : pg = w8)
    (nm_in : SvIn B w28 c.toNat)
    (l_in : SvIn B w48 w44.toNat)
    (CK0 : SvCkCode M0)
    (b_in : SvIn B s7v s0v.toNat) :
    SvErrRet B out v n0 ∨
    (∃ cm_w10 : Word, ∃ cm_w30 : Word, (((False) ∧ cm_w10 = (BitVec.ofNat 8 (sg.getD 0 0)).zeroExtend 32 ∧ cm_w30 = w30) ∨ ((False) ∧ cm_w10 = (BitVec.ofNat 8 (sg.getD 0 0)).zeroExtend 32 ∧ cm_w30 = w30) ∨ (∃ bs, base64Decode (memBytes M0 s7v s0v.toNat) = some bs ∧ (False) ∧ cm_w10 = (BitVec.ofNat 8 (sg.getD 0 0)).zeroExtend 32 ∧ cm_w30 = w30) ∨ (∃ bs, base64Decode (memBytes M0 s7v s0v.toNat) = some bs ∧ cm_w10 = (BitVec.ofNat 8 (sg.getD 0 0)).zeroExtend 32 ∧ cm_w30 = w30) ∨ (∃ bs, base64Decode (memBytes M0 s7v s0v.toNat) = some bs ∧ (w2c = 0) ∧ cm_w10 = (BitVec.ofNat 8 (bs.getD 4 0)).zeroExtend 32 ∧ cm_w30 = BitVec.ofNat 32 0x1) ∨ (∃ bs, base64Decode (memBytes M0 s7v s0v.toNat) = some bs ∧ (False) ∧ cm_w10 = (BitVec.ofNat 8 (sg.getD 0 0)).zeroExtend 32 ∧ cm_w30 = w30) ∨ (∃ bs, base64Decode (memBytes M0 s7v s0v.toNat) = some bs ∧ cm_w10 = (BitVec.ofNat 8 (sg.getD 0 0)).zeroExtend 32 ∧ cm_w30 = w30) ∨ (cm_w10 = (BitVec.ofNat 8 (sg.getD 0 0)).zeroExtend 32 ∧ cm_w30 = w30)) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x2D6E (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (9 : Fin 32) = c ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (21 : Fin 32) = s5v ∧
        reg n' (22 : Fin 32) = gi ∧
        reg n' (23 : Fin 32) = s7v ∧
        reg n' (24 : Fin 32) = dg ∧
        reg n' (25 : Fin 32) = q ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = cm_w10 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = w14 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = w18 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = w20 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = cm_w30 ∧
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
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 ∧
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
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = wa20 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = wa24 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = wa28 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = wa2c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = wa30 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = wa34 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = wa38 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = wa3c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = waa4 ∧
        (∀ j, j < 31 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0)) ∧
        SvKeepL B n0.mem n'.mem [(0x420, 0x60), (0x1380, 0x8), (0x420, 0x60), (0x10, 0x4), (0x1480, 0x3F), (0x30, 0x4)]) := by
  by_cases hb : w40 = s5v
  · rcases sv_cme (dp := dp) (B := B) (out := out) (bp := bp) (x21 := x21) (x26 := x26) (dg := dg) (c := c) (q := q) (rl := rl) (rp := rp) (sgp := sgp) (op := op) (ol := ol) (pg := pg) (gi := gi) (s0v := s0v) (s5v := s5v) (s7v := s7v) (waa4 := waa4) (rt := rt) (sg := sg) (w8 := w8) (wc := wc) (w14 := w14) (w18 := w18) (w20 := w20) (w24 := w24) (w28 := w28) (w2c := w2c) (w30 := w30) (w34 := w34) (w38 := w38) (w3c := w3c) (w40 := w40) (w44 := w44) (w48 := w48) (w4c := w4c) (w50 := w50) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w78 := w78) (w7c := w7c) (w80 := w80) (w84 := w84) (w88 := w88) (w8c := w8c) (w90 := w90) (w94 := w94) (w98 := w98) (w9c := w9c) (wa0 := wa0) (wa4 := wa4) (wa8 := wa8) (wac := wac) (wb0 := wb0) (wb4 := wb4) (wb8 := wb8) (wbc := wbc) (wc0 := wc0) (wc4 := wc4) (wc8 := wc8) (wcc := wcc) (wd0 := wd0) (wd4 := wd4) (wd8 := wd8) (wdc := wdc) (we0 := we0) (we4 := we4) (we8 := we8) (wec := wec) (wf0 := wf0) (wf4 := wf4) (wf8 := wf8) (wfc := wfc) (w100 := w100) (w104 := w104) (w108 := w108) (w10c := w10c) (w110 := w110) (w114 := w114) (w118 := w118) (w11c := w11c) (w120 := w120) (w124 := w124) (w128 := w128) (w12c := w12c) (w130 := w130) (wa20 := wa20) (wa24 := wa24) (wa28 := wa28) (wa2c := wa2c) (wa30 := wa30) (wa34 := wa34) (wa38 := wa38) (wa3c := wa3c) (v := v) (n0 := n0) F E0 V0 hret hO s0 M0 fM g0_2 g0_18 g0_19 g0_24 g0_25 g0_26 g0_27 w0_8 w0_c w0_14 w0_18 w0_1c w0_20 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_3c w0_40 w0_44 w0_48 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_a8 w0_ac w0_b0 w0_b4 w0_b8 w0_bc w0_c0 w0_c4 w0_c8 w0_cc w0_d0 w0_d4 w0_d8 w0_dc w0_e0 w0_e4 w0_e8 w0_ec w0_f0 w0_f4 w0_f8 w0_fc w0_100 w0_104 w0_108 w0_10c w0_110 w0_114 w0_118 w0_11c w0_120 w0_124 w0_128 w0_12c w0_130 w0_428 w0_a20 w0_a24 w0_a28 w0_a2c w0_a30 w0_a34 w0_a38 w0_a3c w0_aa0 w0_aa4 q0_320 w0_10 q0_1480 g0_10 g0_22 g0_8 g0_21 g0_23 g0_9 hend hb with ⟨-, e⟩ | ⟨hf, -⟩
    · exact .inl e
    · exact hf.elim
  · by_cases hb2 : memBytes M0 w28 c.toNat = memBytes M0 w48 w44.toNat
    · by_cases hb3 : base64Decode (memBytes M0 s7v s0v.toNat) = none
      · rcases sv_cmdn (dp := dp) (B := B) (out := out) (bp := bp) (x21 := x21) (x26 := x26) (dg := dg) (c := c) (q := q) (rl := rl) (rp := rp) (sgp := sgp) (op := op) (ol := ol) (pg := pg) (gi := gi) (s0v := s0v) (s5v := s5v) (s7v := s7v) (waa4 := waa4) (rt := rt) (sg := sg) (bs := []) (w8 := w8) (wc := wc) (w14 := w14) (w18 := w18) (w20 := w20) (w24 := w24) (w28 := w28) (w2c := w2c) (w30 := w30) (w34 := w34) (w38 := w38) (w3c := w3c) (w40 := w40) (w44 := w44) (w48 := w48) (w4c := w4c) (w50 := w50) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w78 := w78) (w7c := w7c) (w80 := w80) (w84 := w84) (w88 := w88) (w8c := w8c) (w90 := w90) (w94 := w94) (w98 := w98) (w9c := w9c) (wa0 := wa0) (wa4 := wa4) (wa8 := wa8) (wac := wac) (wb0 := wb0) (wb4 := wb4) (wb8 := wb8) (wbc := wbc) (wc0 := wc0) (wc4 := wc4) (wc8 := wc8) (wcc := wcc) (wd0 := wd0) (wd4 := wd4) (wd8 := wd8) (wdc := wdc) (we0 := we0) (we4 := we4) (we8 := we8) (wec := wec) (wf0 := wf0) (wf4 := wf4) (wf8 := wf8) (wfc := wfc) (w100 := w100) (w104 := w104) (w108 := w108) (w10c := w10c) (w110 := w110) (w114 := w114) (w118 := w118) (w11c := w11c) (w120 := w120) (w124 := w124) (w128 := w128) (w12c := w12c) (w130 := w130) (wa20 := wa20) (wa24 := wa24) (wa28 := wa28) (wa2c := wa2c) (wa30 := wa30) (wa34 := wa34) (wa38 := wa38) (wa3c := wa3c) (v := v) (n0 := n0) F E0 V0 hret hO s0 M0 fM g0_2 g0_18 g0_19 g0_24 g0_25 g0_26 g0_27 w0_8 w0_c w0_14 w0_18 w0_1c w0_20 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_3c w0_40 w0_44 w0_48 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_a8 w0_ac w0_b0 w0_b4 w0_b8 w0_bc w0_c0 w0_c4 w0_c8 w0_cc w0_d0 w0_d4 w0_d8 w0_dc w0_e0 w0_e4 w0_e8 w0_ec w0_f0 w0_f4 w0_f8 w0_fc w0_100 w0_104 w0_108 w0_10c w0_110 w0_114 w0_118 w0_11c w0_120 w0_124 w0_128 w0_12c w0_130 w0_428 w0_a20 w0_a24 w0_a28 w0_a2c w0_a30 w0_a34 w0_a38 w0_a3c w0_aa0 w0_aa4 q0_320 w0_10 q0_1480 g0_10 g0_22 g0_8 g0_21 g0_23 g0_9 hend hb nm_in l_in hb2 CK0 b_in hb3 with ⟨-, e⟩ | ⟨hf, -⟩
        · exact .inl e
        · exact hf.elim
      · obtain ⟨hb3v, hb3w⟩ := Option.ne_none_iff_exists'.mp hb3
        by_cases hb4 : 0x60 < hb3v.length
        · rcases sv_cmdl (dp := dp) (B := B) (out := out) (bp := bp) (x21 := x21) (x26 := x26) (dg := dg) (c := c) (q := q) (rl := rl) (rp := rp) (sgp := sgp) (op := op) (ol := ol) (pg := pg) (gi := gi) (s0v := s0v) (s5v := s5v) (s7v := s7v) (waa4 := waa4) (rt := rt) (sg := sg) (bs := hb3v) (w8 := w8) (wc := wc) (w14 := w14) (w18 := w18) (w20 := w20) (w24 := w24) (w28 := w28) (w2c := w2c) (w30 := w30) (w34 := w34) (w38 := w38) (w3c := w3c) (w40 := w40) (w44 := w44) (w48 := w48) (w4c := w4c) (w50 := w50) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w78 := w78) (w7c := w7c) (w80 := w80) (w84 := w84) (w88 := w88) (w8c := w8c) (w90 := w90) (w94 := w94) (w98 := w98) (w9c := w9c) (wa0 := wa0) (wa4 := wa4) (wa8 := wa8) (wac := wac) (wb0 := wb0) (wb4 := wb4) (wb8 := wb8) (wbc := wbc) (wc0 := wc0) (wc4 := wc4) (wc8 := wc8) (wcc := wcc) (wd0 := wd0) (wd4 := wd4) (wd8 := wd8) (wdc := wdc) (we0 := we0) (we4 := we4) (we8 := we8) (wec := wec) (wf0 := wf0) (wf4 := wf4) (wf8 := wf8) (wfc := wfc) (w100 := w100) (w104 := w104) (w108 := w108) (w10c := w10c) (w110 := w110) (w114 := w114) (w118 := w118) (w11c := w11c) (w120 := w120) (w124 := w124) (w128 := w128) (w12c := w12c) (w130 := w130) (wa20 := wa20) (wa24 := wa24) (wa28 := wa28) (wa2c := wa2c) (wa30 := wa30) (wa34 := wa34) (wa38 := wa38) (wa3c := wa3c) (v := v) (n0 := n0) F E0 V0 hret hO s0 M0 fM g0_2 g0_18 g0_19 g0_24 g0_25 g0_26 g0_27 w0_8 w0_c w0_14 w0_18 w0_1c w0_20 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_3c w0_40 w0_44 w0_48 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_a8 w0_ac w0_b0 w0_b4 w0_b8 w0_bc w0_c0 w0_c4 w0_c8 w0_cc w0_d0 w0_d4 w0_d8 w0_dc w0_e0 w0_e4 w0_e8 w0_ec w0_f0 w0_f4 w0_f8 w0_fc w0_100 w0_104 w0_108 w0_10c w0_110 w0_114 w0_118 w0_11c w0_120 w0_124 w0_128 w0_12c w0_130 w0_428 w0_a20 w0_a24 w0_a28 w0_a2c w0_a30 w0_a34 w0_a38 w0_a3c w0_aa0 w0_aa4 q0_320 w0_10 q0_1480 g0_10 g0_22 g0_8 g0_21 g0_23 g0_9 hend hb nm_in l_in hb2 CK0 b_in hb3w hb4 with ⟨-, e⟩ | ⟨hf, -⟩
          · exact .inl e
          · exact hf.elim
        · by_cases hb6 : hb3v.length < 4
          · rcases sv_cms (dp := dp) (B := B) (out := out) (bp := bp) (x21 := x21) (x26 := x26) (dg := dg) (c := c) (q := q) (rl := rl) (rp := rp) (sgp := sgp) (op := op) (ol := ol) (pg := pg) (gi := gi) (s0v := s0v) (s5v := s5v) (s7v := s7v) (waa4 := waa4) (rt := rt) (sg := sg) (bs := hb3v) (w8 := w8) (wc := wc) (w14 := w14) (w18 := w18) (w20 := w20) (w24 := w24) (w28 := w28) (w2c := w2c) (w30 := w30) (w34 := w34) (w38 := w38) (w3c := w3c) (w40 := w40) (w44 := w44) (w48 := w48) (w4c := w4c) (w50 := w50) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w78 := w78) (w7c := w7c) (w80 := w80) (w84 := w84) (w88 := w88) (w8c := w8c) (w90 := w90) (w94 := w94) (w98 := w98) (w9c := w9c) (wa0 := wa0) (wa4 := wa4) (wa8 := wa8) (wac := wac) (wb0 := wb0) (wb4 := wb4) (wb8 := wb8) (wbc := wbc) (wc0 := wc0) (wc4 := wc4) (wc8 := wc8) (wcc := wcc) (wd0 := wd0) (wd4 := wd4) (wd8 := wd8) (wdc := wdc) (we0 := we0) (we4 := we4) (we8 := we8) (wec := wec) (wf0 := wf0) (wf4 := wf4) (wf8 := wf8) (wfc := wfc) (w100 := w100) (w104 := w104) (w108 := w108) (w10c := w10c) (w110 := w110) (w114 := w114) (w118 := w118) (w11c := w11c) (w120 := w120) (w124 := w124) (w128 := w128) (w12c := w12c) (w130 := w130) (wa20 := wa20) (wa24 := wa24) (wa28 := wa28) (wa2c := wa2c) (wa30 := wa30) (wa34 := wa34) (wa38 := wa38) (wa3c := wa3c) (v := v) (n0 := n0) F E0 V0 hret hO s0 M0 fM g0_2 g0_18 g0_19 g0_24 g0_25 g0_26 g0_27 w0_8 w0_c w0_14 w0_18 w0_1c w0_20 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_3c w0_40 w0_44 w0_48 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_a8 w0_ac w0_b0 w0_b4 w0_b8 w0_bc w0_c0 w0_c4 w0_c8 w0_cc w0_d0 w0_d4 w0_d8 w0_dc w0_e0 w0_e4 w0_e8 w0_ec w0_f0 w0_f4 w0_f8 w0_fc w0_100 w0_104 w0_108 w0_10c w0_110 w0_114 w0_118 w0_11c w0_120 w0_124 w0_128 w0_12c w0_130 w0_428 w0_a20 w0_a24 w0_a28 w0_a2c w0_a30 w0_a34 w0_a38 w0_a3c w0_aa0 w0_aa4 q0_320 w0_10 q0_1480 g0_10 g0_22 g0_8 g0_21 g0_23 g0_9 hend hb nm_in l_in hb2 CK0 b_in hb3w (Nat.not_lt.mp hb4) hb6 with ⟨-, e⟩ | rest
            · exact .inl e
            · obtain ⟨n', fc, f_ST, f_E, f_V, f_FR, f_r2, f_r3, f_r4, f_r9, f_r18, f_r19, f_r21, f_r22, f_r23, f_r24, f_r25, f_r26, f_r27, f_w8, f_wc, f_w10, f_w14, f_w18, f_w1c, f_w20, f_w24, f_w28, f_w2c, f_w30, f_w34, f_w38, f_w3c, f_w40, f_w44, f_w48, f_w4c, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_w98, f_w9c, f_wa0, f_wa4, f_wa8, f_wac, f_wb0, f_wb4, f_wb8, f_wbc, f_wc0, f_wc4, f_wc8, f_wcc, f_wd0, f_wd4, f_wd8, f_wdc, f_we0, f_we4, f_we8, f_wec, f_wf0, f_wf4, f_wf8, f_wfc, f_w100, f_w104, f_w108, f_w10c, f_w110, f_w114, f_w118, f_w11c, f_w120, f_w124, f_w128, f_w12c, f_w130, f_wa20, f_wa24, f_wa28, f_wa2c, f_wa30, f_wa34, f_wa38, f_wa3c, f_waa0, f_waa4, f_w1384, f_q320, f_q1480, f_KL⟩ := rest
              exact .inr ⟨(BitVec.ofNat 8 (sg.getD 0 0)).zeroExtend 32, w30, .inr (.inr (.inr (.inl ⟨hb3v, hb3w, rfl, rfl⟩))), ⟨n', fc, f_ST, f_E, f_V, f_FR, f_r2, f_r3, f_r4, f_r9, f_r18, f_r19, f_r21, f_r22, f_r23, f_r24, f_r25, f_r26, f_r27, f_w8, f_wc, f_w10, f_w14, f_w18, f_w1c, f_w20, f_w24, f_w28, f_w2c, f_w30, f_w34, f_w38, f_w3c, f_w40, f_w44, f_w48, f_w4c, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_w98, f_w9c, f_wa0, f_wa4, f_wa8, f_wac, f_wb0, f_wb4, f_wb8, f_wbc, f_wc0, f_wc4, f_wc8, f_wcc, f_wd0, f_wd4, f_wd8, f_wdc, f_we0, f_we4, f_we8, f_wec, f_wf0, f_wf4, f_wf8, f_wfc, f_w100, f_w104, f_w108, f_w10c, f_w110, f_w114, f_w118, f_w11c, f_w120, f_w124, f_w128, f_w12c, f_w130, f_wa20, f_wa24, f_wa28, f_wa2c, f_wa30, f_wa34, f_wa38, f_wa3c, f_waa0, f_waa4, f_q320, f_KL.mono (by decide)⟩⟩
          · by_cases hb8 : le4 hb3v 0 = w14
            · by_cases hb9 : hb3v.length = 68
              · rcases sv_cmf (dp := dp) (B := B) (out := out) (bp := bp) (x21 := x21) (x26 := x26) (dg := dg) (c := c) (q := q) (rl := rl) (rp := rp) (sgp := sgp) (op := op) (ol := ol) (pg := pg) (gi := gi) (s0v := s0v) (s5v := s5v) (s7v := s7v) (waa4 := waa4) (rt := rt) (sg := sg) (bs := hb3v) (w8 := w8) (wc := wc) (w14 := w14) (w18 := w18) (w20 := w20) (w24 := w24) (w28 := w28) (w2c := w2c) (w30 := w30) (w34 := w34) (w38 := w38) (w3c := w3c) (w40 := w40) (w44 := w44) (w48 := w48) (w4c := w4c) (w50 := w50) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w78 := w78) (w7c := w7c) (w80 := w80) (w84 := w84) (w88 := w88) (w8c := w8c) (w90 := w90) (w94 := w94) (w98 := w98) (w9c := w9c) (wa0 := wa0) (wa4 := wa4) (wa8 := wa8) (wac := wac) (wb0 := wb0) (wb4 := wb4) (wb8 := wb8) (wbc := wbc) (wc0 := wc0) (wc4 := wc4) (wc8 := wc8) (wcc := wcc) (wd0 := wd0) (wd4 := wd4) (wd8 := wd8) (wdc := wdc) (we0 := we0) (we4 := we4) (we8 := we8) (wec := wec) (wf0 := wf0) (wf4 := wf4) (wf8 := wf8) (wfc := wfc) (w100 := w100) (w104 := w104) (w108 := w108) (w10c := w10c) (w110 := w110) (w114 := w114) (w118 := w118) (w11c := w11c) (w120 := w120) (w124 := w124) (w128 := w128) (w12c := w12c) (w130 := w130) (wa20 := wa20) (wa24 := wa24) (wa28 := wa28) (wa2c := wa2c) (wa30 := wa30) (wa34 := wa34) (wa38 := wa38) (wa3c := wa3c) (v := v) (n0 := n0) F E0 V0 hret hO s0 M0 fM g0_2 g0_18 g0_19 g0_24 g0_25 g0_26 g0_27 w0_8 w0_c w0_14 w0_18 w0_1c w0_20 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_3c w0_40 w0_44 w0_48 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_a8 w0_ac w0_b0 w0_b4 w0_b8 w0_bc w0_c0 w0_c4 w0_c8 w0_cc w0_d0 w0_d4 w0_d8 w0_dc w0_e0 w0_e4 w0_e8 w0_ec w0_f0 w0_f4 w0_f8 w0_fc w0_100 w0_104 w0_108 w0_10c w0_110 w0_114 w0_118 w0_11c w0_120 w0_124 w0_128 w0_12c w0_130 w0_428 w0_a20 w0_a24 w0_a28 w0_a2c w0_a30 w0_a34 w0_a38 w0_a3c w0_aa0 w0_aa4 q0_320 w0_10 q0_1480 g0_10 g0_22 g0_8 g0_21 g0_23 g0_9 hend hb nm_in l_in hb2 CK0 b_in hb3w (Nat.not_lt.mp hb4) (Nat.not_lt.mp hb6) hb8 hb9 with ⟨-, e⟩ | ⟨h0, rest⟩
                · exact .inl e
                · obtain ⟨n', fc, f_ST, f_E, f_V, f_FR, f_r2, f_r3, f_r4, f_r9, f_r18, f_r19, f_r21, f_r22, f_r23, f_r24, f_r25, f_r26, f_r27, f_w8, f_wc, f_w10, f_w14, f_w18, f_w1c, f_w20, f_w24, f_w28, f_w2c, f_w30, f_w34, f_w38, f_w3c, f_w40, f_w44, f_w48, f_w4c, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_w98, f_w9c, f_wa0, f_wa4, f_wa8, f_wac, f_wb0, f_wb4, f_wb8, f_wbc, f_wc0, f_wc4, f_wc8, f_wcc, f_wd0, f_wd4, f_wd8, f_wdc, f_we0, f_we4, f_we8, f_wec, f_wf0, f_wf4, f_wf8, f_wfc, f_w100, f_w104, f_w108, f_w10c, f_w110, f_w114, f_w118, f_w11c, f_w120, f_w124, f_w128, f_w12c, f_w130, f_wa20, f_wa24, f_wa28, f_wa2c, f_wa30, f_wa34, f_wa38, f_wa3c, f_waa0, f_waa4, f_w1384, f_q320, f_q420, f_q1480, f_KL⟩ := rest
                  exact .inr ⟨(BitVec.ofNat 8 (hb3v.getD 4 0)).zeroExtend 32, BitVec.ofNat 32 0x1, .inr (.inr (.inr (.inr (.inl ⟨hb3v, hb3w, h0, rfl, rfl⟩)))), ⟨n', fc, f_ST, f_E, f_V, f_FR, f_r2, f_r3, f_r4, f_r9, f_r18, f_r19, f_r21, f_r22, f_r23, f_r24, f_r25, f_r26, f_r27, f_w8, f_wc, f_w10, f_w14, f_w18, f_w1c, f_w20, f_w24, f_w28, f_w2c, f_w30, f_w34, f_w38, f_w3c, f_w40, f_w44, f_w48, f_w4c, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_w98, f_w9c, f_wa0, f_wa4, f_wa8, f_wac, f_wb0, f_wb4, f_wb8, f_wbc, f_wc0, f_wc4, f_wc8, f_wcc, f_wd0, f_wd4, f_wd8, f_wdc, f_we0, f_we4, f_we8, f_wec, f_wf0, f_wf4, f_wf8, f_wfc, f_w100, f_w104, f_w108, f_w10c, f_w110, f_w114, f_w118, f_w11c, f_w120, f_w124, f_w128, f_w12c, f_w130, f_wa20, f_wa24, f_wa28, f_wa2c, f_wa30, f_wa34, f_wa38, f_wa3c, f_waa0, f_waa4, f_q320, f_KL.mono (by decide)⟩⟩
              · rcases sv_cmx (dp := dp) (B := B) (out := out) (bp := bp) (x21 := x21) (x26 := x26) (dg := dg) (c := c) (q := q) (rl := rl) (rp := rp) (sgp := sgp) (op := op) (ol := ol) (pg := pg) (gi := gi) (s0v := s0v) (s5v := s5v) (s7v := s7v) (waa4 := waa4) (rt := rt) (sg := sg) (bs := hb3v) (w8 := w8) (wc := wc) (w14 := w14) (w18 := w18) (w20 := w20) (w24 := w24) (w28 := w28) (w2c := w2c) (w30 := w30) (w34 := w34) (w38 := w38) (w3c := w3c) (w40 := w40) (w44 := w44) (w48 := w48) (w4c := w4c) (w50 := w50) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w78 := w78) (w7c := w7c) (w80 := w80) (w84 := w84) (w88 := w88) (w8c := w8c) (w90 := w90) (w94 := w94) (w98 := w98) (w9c := w9c) (wa0 := wa0) (wa4 := wa4) (wa8 := wa8) (wac := wac) (wb0 := wb0) (wb4 := wb4) (wb8 := wb8) (wbc := wbc) (wc0 := wc0) (wc4 := wc4) (wc8 := wc8) (wcc := wcc) (wd0 := wd0) (wd4 := wd4) (wd8 := wd8) (wdc := wdc) (we0 := we0) (we4 := we4) (we8 := we8) (wec := wec) (wf0 := wf0) (wf4 := wf4) (wf8 := wf8) (wfc := wfc) (w100 := w100) (w104 := w104) (w108 := w108) (w10c := w10c) (w110 := w110) (w114 := w114) (w118 := w118) (w11c := w11c) (w120 := w120) (w124 := w124) (w128 := w128) (w12c := w12c) (w130 := w130) (wa20 := wa20) (wa24 := wa24) (wa28 := wa28) (wa2c := wa2c) (wa30 := wa30) (wa34 := wa34) (wa38 := wa38) (wa3c := wa3c) (v := v) (n0 := n0) F E0 V0 hret hO s0 M0 fM g0_2 g0_18 g0_19 g0_24 g0_25 g0_26 g0_27 w0_8 w0_c w0_14 w0_18 w0_1c w0_20 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_3c w0_40 w0_44 w0_48 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_a8 w0_ac w0_b0 w0_b4 w0_b8 w0_bc w0_c0 w0_c4 w0_c8 w0_cc w0_d0 w0_d4 w0_d8 w0_dc w0_e0 w0_e4 w0_e8 w0_ec w0_f0 w0_f4 w0_f8 w0_fc w0_100 w0_104 w0_108 w0_10c w0_110 w0_114 w0_118 w0_11c w0_120 w0_124 w0_128 w0_12c w0_130 w0_428 w0_a20 w0_a24 w0_a28 w0_a2c w0_a30 w0_a34 w0_a38 w0_a3c w0_aa0 w0_aa4 q0_320 w0_10 q0_1480 g0_10 g0_22 g0_8 g0_21 g0_23 g0_9 hend hb nm_in l_in hb2 CK0 b_in hb3w (Nat.not_lt.mp hb4) (Nat.not_lt.mp hb6) hb8 hb9 with ⟨-, e⟩ | ⟨hf, -⟩
                · exact .inl e
                · exact hf.elim
            · rcases sv_cmk (dp := dp) (B := B) (out := out) (bp := bp) (x21 := x21) (x26 := x26) (dg := dg) (c := c) (q := q) (rl := rl) (rp := rp) (sgp := sgp) (op := op) (ol := ol) (pg := pg) (gi := gi) (s0v := s0v) (s5v := s5v) (s7v := s7v) (waa4 := waa4) (rt := rt) (sg := sg) (bs := hb3v) (w8 := w8) (wc := wc) (w14 := w14) (w18 := w18) (w20 := w20) (w24 := w24) (w28 := w28) (w2c := w2c) (w30 := w30) (w34 := w34) (w38 := w38) (w3c := w3c) (w40 := w40) (w44 := w44) (w48 := w48) (w4c := w4c) (w50 := w50) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w78 := w78) (w7c := w7c) (w80 := w80) (w84 := w84) (w88 := w88) (w8c := w8c) (w90 := w90) (w94 := w94) (w98 := w98) (w9c := w9c) (wa0 := wa0) (wa4 := wa4) (wa8 := wa8) (wac := wac) (wb0 := wb0) (wb4 := wb4) (wb8 := wb8) (wbc := wbc) (wc0 := wc0) (wc4 := wc4) (wc8 := wc8) (wcc := wcc) (wd0 := wd0) (wd4 := wd4) (wd8 := wd8) (wdc := wdc) (we0 := we0) (we4 := we4) (we8 := we8) (wec := wec) (wf0 := wf0) (wf4 := wf4) (wf8 := wf8) (wfc := wfc) (w100 := w100) (w104 := w104) (w108 := w108) (w10c := w10c) (w110 := w110) (w114 := w114) (w118 := w118) (w11c := w11c) (w120 := w120) (w124 := w124) (w128 := w128) (w12c := w12c) (w130 := w130) (wa20 := wa20) (wa24 := wa24) (wa28 := wa28) (wa2c := wa2c) (wa30 := wa30) (wa34 := wa34) (wa38 := wa38) (wa3c := wa3c) (v := v) (n0 := n0) F E0 V0 hret hO s0 M0 fM g0_2 g0_18 g0_19 g0_24 g0_25 g0_26 g0_27 w0_8 w0_c w0_14 w0_18 w0_1c w0_20 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_3c w0_40 w0_44 w0_48 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_a8 w0_ac w0_b0 w0_b4 w0_b8 w0_bc w0_c0 w0_c4 w0_c8 w0_cc w0_d0 w0_d4 w0_d8 w0_dc w0_e0 w0_e4 w0_e8 w0_ec w0_f0 w0_f4 w0_f8 w0_fc w0_100 w0_104 w0_108 w0_10c w0_110 w0_114 w0_118 w0_11c w0_120 w0_124 w0_128 w0_12c w0_130 w0_428 w0_a20 w0_a24 w0_a28 w0_a2c w0_a30 w0_a34 w0_a38 w0_a3c w0_aa0 w0_aa4 q0_320 w0_10 q0_1480 g0_10 g0_22 g0_8 g0_21 g0_23 g0_9 hend hb nm_in l_in hb2 CK0 b_in hb3w (Nat.not_lt.mp hb4) (Nat.not_lt.mp hb6) hb8 with ⟨-, e⟩ | rest
              · exact .inl e
              · obtain ⟨n', fc, f_ST, f_E, f_V, f_FR, f_r2, f_r3, f_r4, f_r9, f_r18, f_r19, f_r21, f_r22, f_r23, f_r24, f_r25, f_r26, f_r27, f_w8, f_wc, f_w10, f_w14, f_w18, f_w1c, f_w20, f_w24, f_w28, f_w2c, f_w30, f_w34, f_w38, f_w3c, f_w40, f_w44, f_w48, f_w4c, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_w98, f_w9c, f_wa0, f_wa4, f_wa8, f_wac, f_wb0, f_wb4, f_wb8, f_wbc, f_wc0, f_wc4, f_wc8, f_wcc, f_wd0, f_wd4, f_wd8, f_wdc, f_we0, f_we4, f_we8, f_wec, f_wf0, f_wf4, f_wf8, f_wfc, f_w100, f_w104, f_w108, f_w10c, f_w110, f_w114, f_w118, f_w11c, f_w120, f_w124, f_w128, f_w12c, f_w130, f_wa20, f_wa24, f_wa28, f_wa2c, f_wa30, f_wa34, f_wa38, f_wa3c, f_waa0, f_waa4, f_w1384, f_q320, f_q1480, f_KL⟩ := rest
                exact .inr ⟨(BitVec.ofNat 8 (sg.getD 0 0)).zeroExtend 32, w30, .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨hb3v, hb3w, rfl, rfl⟩)))))), ⟨n', fc, f_ST, f_E, f_V, f_FR, f_r2, f_r3, f_r4, f_r9, f_r18, f_r19, f_r21, f_r22, f_r23, f_r24, f_r25, f_r26, f_r27, f_w8, f_wc, f_w10, f_w14, f_w18, f_w1c, f_w20, f_w24, f_w28, f_w2c, f_w30, f_w34, f_w38, f_w3c, f_w40, f_w44, f_w48, f_w4c, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_w98, f_w9c, f_wa0, f_wa4, f_wa8, f_wac, f_wb0, f_wb4, f_wb8, f_wbc, f_wc0, f_wc4, f_wc8, f_wcc, f_wd0, f_wd4, f_wd8, f_wdc, f_we0, f_we4, f_we8, f_wec, f_wf0, f_wf4, f_wf8, f_wfc, f_w100, f_w104, f_w108, f_w10c, f_w110, f_w114, f_w118, f_w11c, f_w120, f_w124, f_w128, f_w12c, f_w130, f_wa20, f_wa24, f_wa28, f_wa2c, f_wa30, f_wa34, f_wa38, f_wa3c, f_waa0, f_waa4, f_q320, f_KL.mono (by decide)⟩⟩
    · rcases sv_cmn (dp := dp) (B := B) (out := out) (bp := bp) (x21 := x21) (x26 := x26) (dg := dg) (c := c) (q := q) (rl := rl) (rp := rp) (sgp := sgp) (op := op) (ol := ol) (pg := pg) (gi := gi) (s0v := s0v) (s5v := s5v) (s7v := s7v) (waa4 := waa4) (rt := rt) (sg := sg) (bs := []) (w8 := w8) (wc := wc) (w14 := w14) (w18 := w18) (w20 := w20) (w24 := w24) (w28 := w28) (w2c := w2c) (w30 := w30) (w34 := w34) (w38 := w38) (w3c := w3c) (w40 := w40) (w44 := w44) (w48 := w48) (w4c := w4c) (w50 := w50) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w78 := w78) (w7c := w7c) (w80 := w80) (w84 := w84) (w88 := w88) (w8c := w8c) (w90 := w90) (w94 := w94) (w98 := w98) (w9c := w9c) (wa0 := wa0) (wa4 := wa4) (wa8 := wa8) (wac := wac) (wb0 := wb0) (wb4 := wb4) (wb8 := wb8) (wbc := wbc) (wc0 := wc0) (wc4 := wc4) (wc8 := wc8) (wcc := wcc) (wd0 := wd0) (wd4 := wd4) (wd8 := wd8) (wdc := wdc) (we0 := we0) (we4 := we4) (we8 := we8) (wec := wec) (wf0 := wf0) (wf4 := wf4) (wf8 := wf8) (wfc := wfc) (w100 := w100) (w104 := w104) (w108 := w108) (w10c := w10c) (w110 := w110) (w114 := w114) (w118 := w118) (w11c := w11c) (w120 := w120) (w124 := w124) (w128 := w128) (w12c := w12c) (w130 := w130) (wa20 := wa20) (wa24 := wa24) (wa28 := wa28) (wa2c := wa2c) (wa30 := wa30) (wa34 := wa34) (wa38 := wa38) (wa3c := wa3c) (v := v) (n0 := n0) F E0 V0 hret hO s0 M0 fM g0_2 g0_18 g0_19 g0_24 g0_25 g0_26 g0_27 w0_8 w0_c w0_14 w0_18 w0_1c w0_20 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_3c w0_40 w0_44 w0_48 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_a8 w0_ac w0_b0 w0_b4 w0_b8 w0_bc w0_c0 w0_c4 w0_c8 w0_cc w0_d0 w0_d4 w0_d8 w0_dc w0_e0 w0_e4 w0_e8 w0_ec w0_f0 w0_f4 w0_f8 w0_fc w0_100 w0_104 w0_108 w0_10c w0_110 w0_114 w0_118 w0_11c w0_120 w0_124 w0_128 w0_12c w0_130 w0_428 w0_a20 w0_a24 w0_a28 w0_a2c w0_a30 w0_a34 w0_a38 w0_a3c w0_aa0 w0_aa4 q0_320 w0_10 q0_1480 g0_10 g0_22 g0_8 g0_21 g0_23 g0_9 hend hb nm_in l_in hb2 with ⟨-, e⟩ | rest
      · exact .inl e
      · obtain ⟨n', fc, f_ST, f_E, f_V, f_FR, f_r2, f_r3, f_r4, f_r9, f_r18, f_r19, f_r21, f_r22, f_r23, f_r24, f_r25, f_r26, f_r27, f_w8, f_wc, f_w10, f_w14, f_w18, f_w1c, f_w20, f_w24, f_w28, f_w2c, f_w30, f_w34, f_w38, f_w3c, f_w40, f_w44, f_w48, f_w4c, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_w98, f_w9c, f_wa0, f_wa4, f_wa8, f_wac, f_wb0, f_wb4, f_wb8, f_wbc, f_wc0, f_wc4, f_wc8, f_wcc, f_wd0, f_wd4, f_wd8, f_wdc, f_we0, f_we4, f_we8, f_wec, f_wf0, f_wf4, f_wf8, f_wfc, f_w100, f_w104, f_w108, f_w10c, f_w110, f_w114, f_w118, f_w11c, f_w120, f_w124, f_w128, f_w12c, f_w130, f_wa20, f_wa24, f_wa28, f_wa2c, f_wa30, f_wa34, f_wa38, f_wa3c, f_waa0, f_waa4, f_q320, f_q1480, f_KL⟩ := rest
        exact .inr ⟨(BitVec.ofNat 8 (sg.getD 0 0)).zeroExtend 32, w30, .inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨rfl, rfl⟩)))))), ⟨n', fc, f_ST, f_E, f_V, f_FR, f_r2, f_r3, f_r4, f_r9, f_r18, f_r19, f_r21, f_r22, f_r23, f_r24, f_r25, f_r26, f_r27, f_w8, f_wc, f_w10, f_w14, f_w18, f_w1c, f_w20, f_w24, f_w28, f_w2c, f_w30, f_w34, f_w38, f_w3c, f_w40, f_w44, f_w48, f_w4c, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_w98, f_w9c, f_wa0, f_wa4, f_wa8, f_wac, f_wb0, f_wb4, f_wb8, f_wbc, f_wc0, f_wc4, f_wc8, f_wcc, f_wd0, f_wd4, f_wd8, f_wdc, f_we0, f_we4, f_we8, f_wec, f_wf0, f_wf4, f_wf8, f_wfc, f_w100, f_w104, f_w108, f_w10c, f_w110, f_w114, f_w118, f_w11c, f_w120, f_w124, f_w128, f_w12c, f_w130, f_wa20, f_wa24, f_wa28, f_wa2c, f_wa30, f_wa34, f_wa38, f_wa3c, f_waa0, f_waa4, f_q320, f_KL.mono (by decide)⟩⟩

end C3.RV32.Sv
