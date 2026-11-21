import C3BootProofs.Proofs.SvSeg
import C3BootProofs.Proofs.SvRl
import C3BootProofs.Proofs.SvRm
import C3BootProofs.Proofs.SvWin0
import C3BootProofs.Proofs.SvWin1
import C3BootProofs.Proofs.SvWin2
import C3BootProofs.Proofs.SvWin3
import C3BootProofs.Proofs.SvWin4
import C3BootProofs.Proofs.SvWin5
import C3BootProofs.Proofs.SvWin6
import C3BootProofs.Proofs.SvWin7

/-!
# `sigstore::verify`: The validity windows

Composed from generated stages by `scripts/gen-sv-segs.py`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 100000

set_option maxHeartbeats 64000000 in
/-- **The validity windows**: from 0x300E to the successful exit at 0x3264, `sv_rl`, `sv_rm`, and the eight window checks. -/
theorem sv_seg_win {B out bp x21 x26 dg c rl sgp lih lil : Word} {rt sg : Bytes} {w8 wc w14 w18 w20 w24 w28 w2c w30 w34 w38 w3c w40 w44 w48 w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c w80 w84 w88 w8c w90 w94 w98 w9c wa0 wa4 wa8 wac wb0 wb4 wb8 wbc wc0 wc4 wc8 wcc wd0 wd4 wd8 wdc we0 we4 we8 wec wf0 wf4 wf8 wfc w100 w104 w108 w10c w110 w114 w118 w11c w120 w124 w128 w12c w130 : Word} {v : Nat → Word} {n0 : Machine} {k28 k2c k30 k34 : Word}
    (F : Fr B 0x3830)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out)
    (s0 : St n0.mem SV n0 0x300E (reg n0))
    (M0 : Word → BitVec 8)
    (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_9 : reg n0 (9 : Fin 32) = c)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_22 : reg n0 (22 : Fin 32) = rl)
    (g0_24 : reg n0 (24 : Fin 32) = dg)
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
    (w0_a20 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70)
    (w0_a24 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21)
    (w0_a28 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c)
    (w0_a2c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48)
    (w0_a30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44)
    (w0_a34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60)
    (w0_a38 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c)
    (w0_a3c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78)
    (w0_aa0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp)
    (w0_aa4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg)
    (q0_320 : ∀ j, j < 31 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0))
    (w0_10 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = (BitVec.ofNat 8 (sg.getD 0 0)).zeroExtend 32)
    (q0_1480 : ∀ j, j < 63 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1480 + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0))
    (w0_74 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74)
    (g0_23 : reg n0 (23 : Fin 32) = lih)
    (g0_25 : reg n0 (25 : Fin 32) = lil)
    (g0_8 : reg n0 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1020)
    (b0_1048 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1048) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8)
    (q0_1049 : ∀ j, j < 31 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1049 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0))
    (S2 : SvSha2Code M0)
    (KS : SvK2Sep B)
    (RS : SvRoSep B)
    (RK0 : SvRkCode M0)
    (dgi_in : SvIn B w84 32)
    (sig_in : SvIn B w68 w64.toNat)
    (crt_in : SvIn B w6c x26.toNat)
    (pp_in4 : SvIn B (bp + 0x10) 4)
    (pl_in4 : SvIn B (bp + 0x14) 4)
    (a_pp : (bp + 0x10).toNat % 4 = 0)
    (a_pl : (bp + 0x14).toNat % 4 = 0)
    (pp_in : SvIn B (memLoad32 M0 (bp + 0x10)) (memLoad32 M0 (bp + 0x14)).toNat)
    (w0_1028 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = k28)
    (w0_102c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = k2c)
    (w0_1030 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = k30)
    (w0_1034 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1034) = k34)
    (ii2h : SvIn B (w7c + 0xFFFFFFE8) 4)
    (ai2h : (w7c + 0xFFFFFFE8).toNat % 4 = 0)
    (ii2l : SvIn B (w7c + 0xFFFFFFE4) 4)
    (ai2l : (w7c + 0xFFFFFFE4).toNat % 4 = 0)
    (ii3h : SvIn B (w7c + 0xFFFFFFF0) 4)
    (ai3h : (w7c + 0xFFFFFFF0).toNat % 4 = 0)
    (ii3l : SvIn B (w7c + 0xFFFFFFEC) 4)
    (ai3l : (w7c + 0xFFFFFFEC).toNat % 4 = 0)
    (it4h : SvIn B (w74 + 0xC) 4)
    (at4h : (w74 + 0xC).toNat % 4 = 0)
    (it4l : SvIn B (w74 + 0x8) 4)
    (at4l : (w74 + 0x8).toNat % 4 = 0)
    (it5h : SvIn B (w74 + 0x14) 4)
    (at5h : (w74 + 0x14).toNat % 4 = 0)
    (it5l : SvIn B (w74 + 0x10) 4)
    (at5l : (w74 + 0x10).toNat % 4 = 0) :
    SvErrRet B out v n0 ∨ Panics n0 ∨
    (∃ root6_2, rootFromInclusion (pair64 (lil) (lih)) (pair64 (w60) (w70)) ((sha256 ([] ++ memBytes M0 (BitVec.ofNat 32 0x3FCC4106) (0x1) ++ memBytes M0 (BitVec.ofNat 32 0x3FCC46F0) (0x71) ++ base64Encode (memBytes M0 (w84) (32)) ++ memBytes M0 (BitVec.ofNat 32 0x3FCC4761) (0x1B) ++ base64Encode (memBytes M0 (w68) ((w64).toNat)) ++ memBytes M0 (BitVec.ofNat 32 0x3FCC477C) (0x54) ++ base64Encode (memBytes M0 (w6c) ((x26).toNat)) ++ memBytes M0 (BitVec.ofNat 32 0x3FCC47D0) (0x7)))) (memBytes M0 ((memLoad32 M0 (bp + 0x10))) (((memLoad32 M0 (bp + 0x14))).toNat)) = some root6_2 ∧
      (b32 root6_2 = b32 rt) ∧
      (((aluEval .sltu (w3c) (w58) = 0)) ∨ ((aluEval .sltu (w78) (w54) = 0))) ∧
      (((aluEval .sltu (w50) (w3c) = 0)) ∨ ((aluEval .sltu (w4c) (w78) = 0))) ∧
      (((aluEval .sltu (w3c) ((memLoad32 M0 (w7c + 0xFFFFFFE4))) = 0)) ∨ ((aluEval .sltu (w78) ((memLoad32 M0 (w7c + 0xFFFFFFE8))) = 0))) ∧
      (((aluEval .sltu ((memLoad32 M0 (w7c + 0xFFFFFFEC))) (w3c) = 0)) ∨ ((aluEval .sltu ((memLoad32 M0 (w7c + 0xFFFFFFF0))) (w78) = 0))) ∧
      (((aluEval .sltu (w3c) ((memLoad32 M0 (w74 + 0x8))) = 0)) ∨ ((aluEval .sltu (w78) ((memLoad32 M0 (w74 + 0xC))) = 0))) ∧
      (((aluEval .sltu ((memLoad32 M0 (w74 + 0x10))) (w3c) = 0)) ∨ ((aluEval .sltu ((memLoad32 M0 (w74 + 0x14))) (w78) = 0))) ∧
      (((aluEval .sltu (w3c) (k28) = 0)) ∨ ((aluEval .sltu (w78) (k2c) = 0))) ∧
      (((aluEval .sltu (k30) (w3c) = 0)) ∨ ((aluEval .sltu (k34) (w78) = 0))) ∧
      ∃ m', Steps n0 m' ∧ (∀ x, SvR B x → m'.mem x = M0 x) ∧ St m'.mem SV m' 0x3264 (reg m') ∧
        SvCode m'.mem ∧ SvSaves B m'.mem v ∧ reg m' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg m' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg m' sp = B + 0x21A0 ∧
        reg m' (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1048 ∧
        reg m' (9 : Fin 32) = ((BitVec.ofNat 8 (root6_2.getD 0 0)).zeroExtend 32) ∧
        reg m' (18 : Fin 32) = out ∧
        reg m' (19 : Fin 32) = bp ∧
        reg m' (21 : Fin 32) = x21 ∧
        reg m' (22 : Fin 32) = rl ∧
        reg m' (23 : Fin 32) = lih ∧
        reg m' (24 : Fin 32) = dg ∧
        reg m' (25 : Fin 32) = lil ∧
        reg m' (26 : Fin 32) = x26 ∧
        reg m' (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = (BitVec.ofNat 8 (sg.getD 0 0)).zeroExtend 32 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = w14 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = w18 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = w20 ∧
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
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 ∧
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
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = w3c ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = w78 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = dp ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = k28 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = k2c ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = k30 ∧
        memLoad32 m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1034) = k34 ∧
        m'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1048) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 ∧
        (∀ j, j < 31 → m'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0)) ∧
        (∀ j, j < 31 → m'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1049 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0))) := by
  rcases sv_rl (q := 0) (rp := 0) (op := 0) (ol := 0) F E0 V0 hret hO s0 M0 fM g0_2 g0_9 g0_18 g0_19 g0_21 g0_22 g0_24 g0_26 g0_27 w0_8 w0_c w0_14 w0_18 w0_1c w0_20 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_3c w0_40 w0_44 w0_48 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_a8 w0_ac w0_b0 w0_b4 w0_b8 w0_bc w0_c0 w0_c4 w0_c8 w0_cc w0_d0 w0_d4 w0_d8 w0_dc w0_e0 w0_e4 w0_e8 w0_ec w0_f0 w0_f4 w0_f8 w0_fc w0_100 w0_104 w0_108 w0_10c w0_110 w0_114 w0_118 w0_11c w0_120 w0_124 w0_128 w0_12c w0_130 w0_428 w0_a20 w0_a24 w0_a28 w0_a2c w0_a30 w0_a34 w0_a38 w0_a3c w0_aa0 w0_aa4 q0_320 w0_10 q0_1480 w0_74 g0_23 g0_25 g0_8 b0_1048 q0_1049 S2 KS RS RK0 dgi_in sig_in crt_in with ⟨-, e⟩ | ⟨n1, c1, s1, E1, V1, fR1, r1_2, r1_3, r1_4, r1_8, r1_9, r1_18, r1_19, r1_21, r1_22, r1_23, r1_24, r1_25, r1_26, r1_27, w1_8, w1_c, w1_10, w1_14, w1_18, w1_1c, w1_20, w1_24, w1_28, w1_2c, w1_30, w1_34, w1_38, w1_3c, w1_40, w1_44, w1_48, w1_4c, w1_50, w1_54, w1_58, w1_5c, w1_60, w1_64, w1_68, w1_6c, w1_70, w1_74, w1_78, w1_7c, w1_80, w1_84, w1_88, w1_8c, w1_90, w1_94, w1_98, w1_9c, w1_a0, w1_a4, w1_a8, w1_ac, w1_b0, w1_b4, w1_b8, w1_bc, w1_c0, w1_c4, w1_c8, w1_cc, w1_d0, w1_d4, w1_d8, w1_dc, w1_e0, w1_e4, w1_e8, w1_ec, w1_f0, w1_f4, w1_f8, w1_fc, w1_100, w1_104, w1_108, w1_10c, w1_110, w1_114, w1_118, w1_11c, w1_120, w1_124, w1_128, w1_12c, w1_130, w1_a20, w1_a24, w1_a28, w1_a2c, w1_a30, w1_a34, w1_a38, w1_a3c, w1_aa0, w1_aa4, b1_1048, q1_320, q1_1049, q1_1480, mb1_1380, K1_L⟩
  · exact .inl e
  rcases sv_rm (q := 0) (rp := 0) (op := 0) (ol := 0) F E1 V1 hret hO s1 M0 fR1 r1_2 r1_9 r1_18 r1_19 r1_21 r1_22 r1_24 r1_26 r1_27 w1_8 w1_c w1_14 w1_18 w1_1c w1_20 w1_24 w1_28 w1_2c w1_30 w1_34 w1_38 w1_3c w1_40 w1_44 w1_48 w1_4c w1_50 w1_54 w1_58 w1_5c w1_60 w1_64 w1_68 w1_6c w1_70 w1_78 w1_7c w1_80 w1_84 w1_88 w1_8c w1_90 w1_94 w1_98 w1_9c w1_a0 w1_a4 w1_a8 w1_ac w1_b0 w1_b4 w1_b8 w1_bc w1_c0 w1_c4 w1_c8 w1_cc w1_d0 w1_d4 w1_d8 w1_dc w1_e0 w1_e4 w1_e8 w1_ec w1_f0 w1_f4 w1_f8 w1_fc w1_100 w1_104 w1_108 w1_10c w1_110 w1_114 w1_118 w1_11c w1_120 w1_124 w1_128 w1_12c w1_130 rfl w1_a20 w1_a24 w1_a28 w1_a2c w1_a30 w1_a34 w1_a38 w1_a3c w1_aa0 w1_aa4 q1_320 w1_10 q1_1480 w1_74 r1_23 r1_25 r1_8 b1_1048 q1_1049 S2 KS RS RK0 mb1_1380 rfl rfl pp_in4 pl_in4 a_pp a_pl pp_in with ⟨-, e⟩ | ⟨root6_2, x2_0, x2_1, n2, c2, s2, E2, V2, fR2, r2_2, r2_3, r2_4, r2_8, r2_9, r2_18, r2_19, r2_21, r2_22, r2_23, r2_24, r2_25, r2_26, r2_27, w2_8, w2_c, w2_10, w2_14, w2_18, w2_1c, w2_20, w2_24, w2_28, w2_2c, w2_30, w2_34, w2_38, w2_3c, w2_40, w2_44, w2_48, w2_4c, w2_50, w2_54, w2_58, w2_5c, w2_60, w2_64, w2_68, w2_6c, w2_70, w2_74, w2_78, w2_7c, w2_80, w2_84, w2_88, w2_8c, w2_90, w2_94, w2_98, w2_9c, w2_a0, w2_a4, w2_a8, w2_ac, w2_b0, w2_b4, w2_b8, w2_bc, w2_c0, w2_c4, w2_c8, w2_cc, w2_d0, w2_d4, w2_d8, w2_dc, w2_e0, w2_e4, w2_e8, w2_ec, w2_f0, w2_f4, w2_f8, w2_fc, w2_100, w2_104, w2_108, w2_10c, w2_110, w2_114, w2_118, w2_11c, w2_120, w2_124, w2_128, w2_12c, w2_130, w2_a20, w2_a24, w2_a28, w2_a2c, w2_a30, w2_a34, w2_a38, w2_a3c, w2_aa0, w2_aa4, b2_420, b2_421, b2_1048, b2_1480, q2_320, q2_421, q2_1049, q2_1481, K2_L⟩
  · exact .inl (SvErrRet.pre (c1) (by rw [r1_3]) (by rw [r1_4])
      (fun x hx => (fR1 x hx).trans (fM x hx).symm) e)
  rcases sv_win0 (q := 0) (rp := 0) (op := 0) (ol := 0) (i2h := 0) (i2l := 0) (i3h := 0) (i3l := 0) (t4h := 0) (t4l := 0) (t5h := 0) (t5l := 0) F E2 V2 hret hO s2 M0 fR2 r2_2 r2_9 r2_18 r2_19 r2_21 r2_22 r2_24 r2_26 r2_27 w2_8 w2_c w2_14 w2_18 w2_1c w2_20 w2_24 w2_28 w2_2c w2_30 w2_34 w2_38 w2_3c w2_40 w2_44 w2_48 w2_4c w2_50 w2_54 w2_58 w2_5c w2_60 w2_64 w2_68 w2_6c w2_70 w2_78 w2_7c w2_80 w2_84 w2_88 w2_8c w2_90 w2_94 w2_98 w2_9c w2_a0 w2_a4 w2_a8 w2_ac w2_b0 w2_b4 w2_b8 w2_bc w2_c0 w2_c4 w2_c8 w2_cc w2_d0 w2_d4 w2_d8 w2_dc w2_e0 w2_e4 w2_e8 w2_ec w2_f0 w2_f4 w2_f8 w2_fc w2_100 w2_104 w2_108 w2_10c w2_110 w2_114 w2_118 w2_11c w2_120 w2_124 w2_128 w2_12c w2_130 rfl w2_a20 w2_a24 w2_a28 w2_a2c w2_a30 w2_a34 w2_a38 w2_a3c w2_aa0 w2_aa4 q2_320 w2_10 w2_74 r2_23 r2_25 r2_8 b2_1048 q2_1049 S2 KS RS RK0 ((K2_L.w32 (by decide) (by decide)).trans ((K1_L.w32 (by decide) (by decide)).trans w0_1028)) ((K2_L.w32 (by decide) (by decide)).trans ((K1_L.w32 (by decide) (by decide)).trans w0_102c)) ((K2_L.w32 (by decide) (by decide)).trans ((K1_L.w32 (by decide) (by decide)).trans w0_1030)) ((K2_L.w32 (by decide) (by decide)).trans ((K1_L.w32 (by decide) (by decide)).trans w0_1034)) with e | ⟨x3_0, n3, c3, s3, E3, V3, fR3, r3_2, r3_3, r3_4, r3_8, r3_9, r3_18, r3_19, r3_21, r3_22, r3_23, r3_24, r3_25, r3_26, r3_27, w3_8, w3_c, w3_10, w3_14, w3_18, w3_1c, w3_20, w3_24, w3_28, w3_2c, w3_30, w3_34, w3_38, w3_3c, w3_40, w3_44, w3_48, w3_4c, w3_50, w3_54, w3_58, w3_5c, w3_60, w3_64, w3_68, w3_6c, w3_70, w3_74, w3_78, w3_7c, w3_80, w3_84, w3_88, w3_8c, w3_90, w3_94, w3_98, w3_9c, w3_a0, w3_a4, w3_a8, w3_ac, w3_b0, w3_b4, w3_b8, w3_bc, w3_c0, w3_c4, w3_c8, w3_cc, w3_d0, w3_d4, w3_d8, w3_dc, w3_e0, w3_e4, w3_e8, w3_ec, w3_f0, w3_f4, w3_f8, w3_fc, w3_100, w3_104, w3_108, w3_10c, w3_110, w3_114, w3_118, w3_11c, w3_120, w3_124, w3_128, w3_12c, w3_130, w3_428, w3_a20, w3_a24, w3_a28, w3_a2c, w3_a30, w3_a34, w3_a38, w3_a3c, w3_aa0, w3_aa4, w3_1028, w3_102c, w3_1030, w3_1034, b3_1048, q3_320, q3_1049, K3_L⟩
  · exact .inl (SvErrRet.pre (c1.trans (c2)) (by rw [r2_3, r1_3]) (by rw [r2_4, r1_4])
      (fun x hx => (fR2 x hx).trans (fM x hx).symm) e)
  rcases sv_win1 (q := 0) (rp := 0) (op := 0) (ol := 0) (i2h := 0) (i2l := 0) (i3h := 0) (i3l := 0) (t4h := 0) (t4l := 0) (t5h := 0) (t5l := 0) F E3 V3 hret hO s3 M0 fR3 r3_2 r3_9 r3_18 r3_19 r3_21 r3_22 r3_24 r3_26 r3_27 w3_8 w3_c w3_14 w3_18 w3_1c w3_20 w3_24 w3_28 w3_2c w3_30 w3_34 w3_38 w3_3c w3_40 w3_44 w3_48 w3_4c w3_50 w3_54 w3_58 w3_5c w3_60 w3_64 w3_68 w3_6c w3_70 w3_78 w3_7c w3_80 w3_84 w3_88 w3_8c w3_90 w3_94 w3_98 w3_9c w3_a0 w3_a4 w3_a8 w3_ac w3_b0 w3_b4 w3_b8 w3_bc w3_c0 w3_c4 w3_c8 w3_cc w3_d0 w3_d4 w3_d8 w3_dc w3_e0 w3_e4 w3_e8 w3_ec w3_f0 w3_f4 w3_f8 w3_fc w3_100 w3_104 w3_108 w3_10c w3_110 w3_114 w3_118 w3_11c w3_120 w3_124 w3_128 w3_12c w3_130 w3_428 w3_a20 w3_a24 w3_a28 w3_a2c w3_a30 w3_a34 w3_a38 w3_a3c w3_aa0 w3_aa4 q3_320 w3_10 w3_74 r3_23 r3_25 r3_8 b3_1048 q3_1049 S2 KS RS RK0 w3_1028 w3_102c w3_1030 w3_1034 with e | ⟨x4_0, n4, c4, s4, E4, V4, fR4, r4_2, r4_3, r4_4, r4_8, r4_9, r4_18, r4_19, r4_21, r4_22, r4_23, r4_24, r4_25, r4_26, r4_27, w4_8, w4_c, w4_10, w4_14, w4_18, w4_1c, w4_20, w4_24, w4_28, w4_2c, w4_30, w4_34, w4_38, w4_3c, w4_40, w4_44, w4_48, w4_4c, w4_50, w4_54, w4_58, w4_5c, w4_60, w4_64, w4_68, w4_6c, w4_70, w4_74, w4_78, w4_7c, w4_80, w4_84, w4_88, w4_8c, w4_90, w4_94, w4_98, w4_9c, w4_a0, w4_a4, w4_a8, w4_ac, w4_b0, w4_b4, w4_b8, w4_bc, w4_c0, w4_c4, w4_c8, w4_cc, w4_d0, w4_d4, w4_d8, w4_dc, w4_e0, w4_e4, w4_e8, w4_ec, w4_f0, w4_f4, w4_f8, w4_fc, w4_100, w4_104, w4_108, w4_10c, w4_110, w4_114, w4_118, w4_11c, w4_120, w4_124, w4_128, w4_12c, w4_130, w4_428, w4_a20, w4_a24, w4_a28, w4_a2c, w4_a30, w4_a34, w4_a38, w4_a3c, w4_aa0, w4_aa4, w4_1028, w4_102c, w4_1030, w4_1034, b4_1048, q4_320, q4_1049, K4_L⟩
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3))) (by rw [r3_3, r2_3, r1_3]) (by rw [r3_4, r2_4, r1_4])
      (fun x hx => (fR3 x hx).trans (fM x hx).symm) e)
  rcases sv_win2 (q := 0) (rp := 0) (op := 0) (ol := 0) (i3h := 0) (i3l := 0) (t4h := 0) (t4l := 0) (t5h := 0) (t5l := 0) F E4 V4 hret hO s4 M0 fR4 r4_2 r4_9 r4_18 r4_19 r4_21 r4_22 r4_24 r4_26 r4_27 w4_8 w4_c w4_14 w4_18 w4_1c w4_20 w4_24 w4_28 w4_2c w4_30 w4_34 w4_38 w4_3c w4_40 w4_44 w4_48 w4_4c w4_50 w4_54 w4_58 w4_5c w4_60 w4_64 w4_68 w4_6c w4_70 w4_78 w4_7c w4_80 w4_84 w4_88 w4_8c w4_90 w4_94 w4_98 w4_9c w4_a0 w4_a4 w4_a8 w4_ac w4_b0 w4_b4 w4_b8 w4_bc w4_c0 w4_c4 w4_c8 w4_cc w4_d0 w4_d4 w4_d8 w4_dc w4_e0 w4_e4 w4_e8 w4_ec w4_f0 w4_f4 w4_f8 w4_fc w4_100 w4_104 w4_108 w4_10c w4_110 w4_114 w4_118 w4_11c w4_120 w4_124 w4_128 w4_12c w4_130 w4_428 w4_a20 w4_a24 w4_a28 w4_a2c w4_a30 w4_a34 w4_a38 w4_a3c w4_aa0 w4_aa4 q4_320 w4_10 w4_74 r4_23 r4_25 r4_8 b4_1048 q4_1049 S2 KS RS RK0 w4_1028 w4_102c w4_1030 w4_1034 rfl ii2h ai2h rfl ii2l ai2l with e | ⟨x5_0, n5, c5, s5, E5, V5, fR5, r5_2, r5_3, r5_4, r5_8, r5_9, r5_18, r5_19, r5_21, r5_22, r5_23, r5_24, r5_25, r5_26, r5_27, w5_8, w5_c, w5_10, w5_14, w5_18, w5_1c, w5_20, w5_24, w5_28, w5_2c, w5_30, w5_34, w5_38, w5_3c, w5_40, w5_44, w5_48, w5_4c, w5_50, w5_54, w5_58, w5_5c, w5_60, w5_64, w5_68, w5_6c, w5_70, w5_74, w5_78, w5_7c, w5_80, w5_84, w5_88, w5_8c, w5_90, w5_94, w5_98, w5_9c, w5_a0, w5_a4, w5_a8, w5_ac, w5_b0, w5_b4, w5_b8, w5_bc, w5_c0, w5_c4, w5_c8, w5_cc, w5_d0, w5_d4, w5_d8, w5_dc, w5_e0, w5_e4, w5_e8, w5_ec, w5_f0, w5_f4, w5_f8, w5_fc, w5_100, w5_104, w5_108, w5_10c, w5_110, w5_114, w5_118, w5_11c, w5_120, w5_124, w5_128, w5_12c, w5_130, w5_428, w5_a20, w5_a24, w5_a28, w5_a2c, w5_a30, w5_a34, w5_a38, w5_a3c, w5_aa0, w5_aa4, w5_1028, w5_102c, w5_1030, w5_1034, b5_1048, q5_320, q5_1049, K5_L⟩
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3.trans (c4)))) (by rw [r4_3, r3_3, r2_3, r1_3]) (by rw [r4_4, r3_4, r2_4, r1_4])
      (fun x hx => (fR4 x hx).trans (fM x hx).symm) e)
  rcases sv_win3 (q := 0) (rp := 0) (op := 0) (ol := 0) (i2h := 0) (i2l := 0) (t4h := 0) (t4l := 0) (t5h := 0) (t5l := 0) F E5 V5 hret hO s5 M0 fR5 r5_2 r5_9 r5_18 r5_19 r5_21 r5_22 r5_24 r5_26 r5_27 w5_8 w5_c w5_14 w5_18 w5_1c w5_20 w5_24 w5_28 w5_2c w5_30 w5_34 w5_38 w5_3c w5_40 w5_44 w5_48 w5_4c w5_50 w5_54 w5_58 w5_5c w5_60 w5_64 w5_68 w5_6c w5_70 w5_78 w5_7c w5_80 w5_84 w5_88 w5_8c w5_90 w5_94 w5_98 w5_9c w5_a0 w5_a4 w5_a8 w5_ac w5_b0 w5_b4 w5_b8 w5_bc w5_c0 w5_c4 w5_c8 w5_cc w5_d0 w5_d4 w5_d8 w5_dc w5_e0 w5_e4 w5_e8 w5_ec w5_f0 w5_f4 w5_f8 w5_fc w5_100 w5_104 w5_108 w5_10c w5_110 w5_114 w5_118 w5_11c w5_120 w5_124 w5_128 w5_12c w5_130 w5_428 w5_a20 w5_a24 w5_a28 w5_a2c w5_a30 w5_a34 w5_a38 w5_a3c w5_aa0 w5_aa4 q5_320 w5_10 w5_74 r5_23 r5_25 r5_8 b5_1048 q5_1049 S2 KS RS RK0 w5_1028 w5_102c w5_1030 w5_1034 rfl ii3h ai3h rfl ii3l ai3l with e | ⟨x6_0, n6, c6, s6, E6, V6, fR6, r6_2, r6_3, r6_4, r6_8, r6_9, r6_18, r6_19, r6_21, r6_22, r6_23, r6_24, r6_25, r6_26, r6_27, w6_8, w6_c, w6_10, w6_14, w6_18, w6_1c, w6_20, w6_24, w6_28, w6_2c, w6_30, w6_34, w6_38, w6_3c, w6_40, w6_44, w6_48, w6_4c, w6_50, w6_54, w6_58, w6_5c, w6_60, w6_64, w6_68, w6_6c, w6_70, w6_74, w6_78, w6_7c, w6_80, w6_84, w6_88, w6_8c, w6_90, w6_94, w6_98, w6_9c, w6_a0, w6_a4, w6_a8, w6_ac, w6_b0, w6_b4, w6_b8, w6_bc, w6_c0, w6_c4, w6_c8, w6_cc, w6_d0, w6_d4, w6_d8, w6_dc, w6_e0, w6_e4, w6_e8, w6_ec, w6_f0, w6_f4, w6_f8, w6_fc, w6_100, w6_104, w6_108, w6_10c, w6_110, w6_114, w6_118, w6_11c, w6_120, w6_124, w6_128, w6_12c, w6_130, w6_428, w6_a20, w6_a24, w6_a28, w6_a2c, w6_a30, w6_a34, w6_a38, w6_a3c, w6_aa0, w6_aa4, w6_1028, w6_102c, w6_1030, w6_1034, b6_1048, q6_320, q6_1049, K6_L⟩
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3.trans (c4.trans (c5))))) (by rw [r5_3, r4_3, r3_3, r2_3, r1_3]) (by rw [r5_4, r4_4, r3_4, r2_4, r1_4])
      (fun x hx => (fR5 x hx).trans (fM x hx).symm) e)
  rcases sv_win4 (q := 0) (rp := 0) (op := 0) (ol := 0) (i2h := 0) (i2l := 0) (i3h := 0) (i3l := 0) (t5h := 0) (t5l := 0) F E6 V6 hret hO s6 M0 fR6 r6_2 r6_9 r6_18 r6_19 r6_21 r6_22 r6_24 r6_26 r6_27 w6_8 w6_c w6_14 w6_18 w6_1c w6_20 w6_24 w6_28 w6_2c w6_30 w6_34 w6_38 w6_3c w6_40 w6_44 w6_48 w6_4c w6_50 w6_54 w6_58 w6_5c w6_60 w6_64 w6_68 w6_6c w6_70 w6_78 w6_7c w6_80 w6_84 w6_88 w6_8c w6_90 w6_94 w6_98 w6_9c w6_a0 w6_a4 w6_a8 w6_ac w6_b0 w6_b4 w6_b8 w6_bc w6_c0 w6_c4 w6_c8 w6_cc w6_d0 w6_d4 w6_d8 w6_dc w6_e0 w6_e4 w6_e8 w6_ec w6_f0 w6_f4 w6_f8 w6_fc w6_100 w6_104 w6_108 w6_10c w6_110 w6_114 w6_118 w6_11c w6_120 w6_124 w6_128 w6_12c w6_130 w6_428 w6_a20 w6_a24 w6_a28 w6_a2c w6_a30 w6_a34 w6_a38 w6_a3c w6_aa0 w6_aa4 q6_320 w6_10 w6_74 r6_23 r6_25 r6_8 b6_1048 q6_1049 S2 KS RS RK0 w6_1028 w6_102c w6_1030 w6_1034 rfl it4h at4h rfl it4l at4l with e | ⟨x7_0, n7, c7, s7, E7, V7, fR7, r7_2, r7_3, r7_4, r7_8, r7_9, r7_18, r7_19, r7_21, r7_22, r7_23, r7_24, r7_25, r7_26, r7_27, w7_8, w7_c, w7_10, w7_14, w7_18, w7_1c, w7_20, w7_24, w7_28, w7_2c, w7_30, w7_34, w7_38, w7_3c, w7_40, w7_44, w7_48, w7_4c, w7_50, w7_54, w7_58, w7_5c, w7_60, w7_64, w7_68, w7_6c, w7_70, w7_74, w7_78, w7_7c, w7_80, w7_84, w7_88, w7_8c, w7_90, w7_94, w7_98, w7_9c, w7_a0, w7_a4, w7_a8, w7_ac, w7_b0, w7_b4, w7_b8, w7_bc, w7_c0, w7_c4, w7_c8, w7_cc, w7_d0, w7_d4, w7_d8, w7_dc, w7_e0, w7_e4, w7_e8, w7_ec, w7_f0, w7_f4, w7_f8, w7_fc, w7_100, w7_104, w7_108, w7_10c, w7_110, w7_114, w7_118, w7_11c, w7_120, w7_124, w7_128, w7_12c, w7_130, w7_428, w7_a20, w7_a24, w7_a28, w7_a2c, w7_a30, w7_a34, w7_a38, w7_a3c, w7_aa0, w7_aa4, w7_1028, w7_102c, w7_1030, w7_1034, b7_1048, q7_320, q7_1049, K7_L⟩
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6)))))) (by rw [r6_3, r5_3, r4_3, r3_3, r2_3, r1_3]) (by rw [r6_4, r5_4, r4_4, r3_4, r2_4, r1_4])
      (fun x hx => (fR6 x hx).trans (fM x hx).symm) e)
  rcases sv_win5 (q := 0) (rp := 0) (op := 0) (ol := 0) (i2h := 0) (i2l := 0) (i3h := 0) (i3l := 0) (t4h := 0) (t4l := 0) F E7 V7 hret hO s7 M0 fR7 r7_2 r7_9 r7_18 r7_19 r7_21 r7_22 r7_24 r7_26 r7_27 w7_8 w7_c w7_14 w7_18 w7_1c w7_20 w7_24 w7_28 w7_2c w7_30 w7_34 w7_38 w7_3c w7_40 w7_44 w7_48 w7_4c w7_50 w7_54 w7_58 w7_5c w7_60 w7_64 w7_68 w7_6c w7_70 w7_78 w7_7c w7_80 w7_84 w7_88 w7_8c w7_90 w7_94 w7_98 w7_9c w7_a0 w7_a4 w7_a8 w7_ac w7_b0 w7_b4 w7_b8 w7_bc w7_c0 w7_c4 w7_c8 w7_cc w7_d0 w7_d4 w7_d8 w7_dc w7_e0 w7_e4 w7_e8 w7_ec w7_f0 w7_f4 w7_f8 w7_fc w7_100 w7_104 w7_108 w7_10c w7_110 w7_114 w7_118 w7_11c w7_120 w7_124 w7_128 w7_12c w7_130 w7_428 w7_a20 w7_a24 w7_a28 w7_a2c w7_a30 w7_a34 w7_a38 w7_a3c w7_aa0 w7_aa4 q7_320 w7_10 w7_74 r7_23 r7_25 r7_8 b7_1048 q7_1049 S2 KS RS RK0 w7_1028 w7_102c w7_1030 w7_1034 rfl it5h at5h rfl it5l at5l with e | ⟨x8_0, n8, c8, s8, E8, V8, fR8, r8_2, r8_3, r8_4, r8_8, r8_9, r8_18, r8_19, r8_21, r8_22, r8_23, r8_24, r8_25, r8_26, r8_27, w8_8, w8_c, w8_10, w8_14, w8_18, w8_1c, w8_20, w8_24, w8_28, w8_2c, w8_30, w8_34, w8_38, w8_3c, w8_40, w8_44, w8_48, w8_4c, w8_50, w8_54, w8_58, w8_5c, w8_60, w8_64, w8_68, w8_6c, w8_70, w8_74, w8_78, w8_7c, w8_80, w8_84, w8_88, w8_8c, w8_90, w8_94, w8_98, w8_9c, w8_a0, w8_a4, w8_a8, w8_ac, w8_b0, w8_b4, w8_b8, w8_bc, w8_c0, w8_c4, w8_c8, w8_cc, w8_d0, w8_d4, w8_d8, w8_dc, w8_e0, w8_e4, w8_e8, w8_ec, w8_f0, w8_f4, w8_f8, w8_fc, w8_100, w8_104, w8_108, w8_10c, w8_110, w8_114, w8_118, w8_11c, w8_120, w8_124, w8_128, w8_12c, w8_130, w8_428, w8_a20, w8_a24, w8_a28, w8_a2c, w8_a30, w8_a34, w8_a38, w8_a3c, w8_aa0, w8_aa4, w8_1028, w8_102c, w8_1030, w8_1034, b8_1048, q8_320, q8_1049, K8_L⟩
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7))))))) (by rw [r7_3, r6_3, r5_3, r4_3, r3_3, r2_3, r1_3]) (by rw [r7_4, r6_4, r5_4, r4_4, r3_4, r2_4, r1_4])
      (fun x hx => (fR7 x hx).trans (fM x hx).symm) e)
  rcases sv_win6 (q := 0) (rp := 0) (op := 0) (ol := 0) (i2h := 0) (i2l := 0) (i3h := 0) (i3l := 0) (t4h := 0) (t4l := 0) (t5h := 0) (t5l := 0) F E8 V8 hret hO s8 M0 fR8 r8_2 r8_9 r8_18 r8_19 r8_21 r8_22 r8_24 r8_26 r8_27 w8_8 w8_c w8_14 w8_18 w8_1c w8_20 w8_24 w8_28 w8_2c w8_30 w8_34 w8_38 w8_3c w8_40 w8_44 w8_48 w8_4c w8_50 w8_54 w8_58 w8_5c w8_60 w8_64 w8_68 w8_6c w8_70 w8_78 w8_7c w8_80 w8_84 w8_88 w8_8c w8_90 w8_94 w8_98 w8_9c w8_a0 w8_a4 w8_a8 w8_ac w8_b0 w8_b4 w8_b8 w8_bc w8_c0 w8_c4 w8_c8 w8_cc w8_d0 w8_d4 w8_d8 w8_dc w8_e0 w8_e4 w8_e8 w8_ec w8_f0 w8_f4 w8_f8 w8_fc w8_100 w8_104 w8_108 w8_10c w8_110 w8_114 w8_118 w8_11c w8_120 w8_124 w8_128 w8_12c w8_130 w8_428 w8_a20 w8_a24 w8_a28 w8_a2c w8_a30 w8_a34 w8_a38 w8_a3c w8_aa0 w8_aa4 q8_320 w8_10 w8_74 r8_23 r8_25 r8_8 b8_1048 q8_1049 S2 KS RS RK0 w8_1028 w8_102c w8_1030 w8_1034 with e | ⟨x9_0, n9, c9, s9, E9, V9, fR9, r9_2, r9_3, r9_4, r9_8, r9_9, r9_18, r9_19, r9_21, r9_22, r9_23, r9_24, r9_25, r9_26, r9_27, w9_8, w9_c, w9_10, w9_14, w9_18, w9_1c, w9_20, w9_24, w9_28, w9_2c, w9_30, w9_34, w9_38, w9_3c, w9_40, w9_44, w9_48, w9_4c, w9_50, w9_54, w9_58, w9_5c, w9_60, w9_64, w9_68, w9_6c, w9_70, w9_74, w9_78, w9_7c, w9_80, w9_84, w9_88, w9_8c, w9_90, w9_94, w9_98, w9_9c, w9_a0, w9_a4, w9_a8, w9_ac, w9_b0, w9_b4, w9_b8, w9_bc, w9_c0, w9_c4, w9_c8, w9_cc, w9_d0, w9_d4, w9_d8, w9_dc, w9_e0, w9_e4, w9_e8, w9_ec, w9_f0, w9_f4, w9_f8, w9_fc, w9_100, w9_104, w9_108, w9_10c, w9_110, w9_114, w9_118, w9_11c, w9_120, w9_124, w9_128, w9_12c, w9_130, w9_428, w9_a20, w9_a24, w9_a28, w9_a2c, w9_a30, w9_a34, w9_a38, w9_a3c, w9_aa0, w9_aa4, w9_1028, w9_102c, w9_1030, w9_1034, b9_1048, q9_320, q9_1049, K9_L⟩
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8)))))))) (by rw [r8_3, r7_3, r6_3, r5_3, r4_3, r3_3, r2_3, r1_3]) (by rw [r8_4, r7_4, r6_4, r5_4, r4_4, r3_4, r2_4, r1_4])
      (fun x hx => (fR8 x hx).trans (fM x hx).symm) e)
  rcases sv_win7 (q := 0) (rp := 0) (op := 0) (ol := 0) (i2h := 0) (i2l := 0) (i3h := 0) (i3l := 0) (t4h := 0) (t4l := 0) (t5h := 0) (t5l := 0) F E9 V9 hret hO s9 M0 fR9 r9_2 r9_9 r9_18 r9_19 r9_21 r9_22 r9_24 r9_26 r9_27 w9_8 w9_c w9_14 w9_18 w9_1c w9_20 w9_24 w9_28 w9_2c w9_30 w9_34 w9_38 w9_3c w9_40 w9_44 w9_48 w9_4c w9_50 w9_54 w9_58 w9_5c w9_60 w9_64 w9_68 w9_6c w9_70 w9_78 w9_7c w9_80 w9_84 w9_88 w9_8c w9_90 w9_94 w9_98 w9_9c w9_a0 w9_a4 w9_a8 w9_ac w9_b0 w9_b4 w9_b8 w9_bc w9_c0 w9_c4 w9_c8 w9_cc w9_d0 w9_d4 w9_d8 w9_dc w9_e0 w9_e4 w9_e8 w9_ec w9_f0 w9_f4 w9_f8 w9_fc w9_100 w9_104 w9_108 w9_10c w9_110 w9_114 w9_118 w9_11c w9_120 w9_124 w9_128 w9_12c w9_130 w9_428 w9_a20 w9_a24 w9_a28 w9_a2c w9_a30 w9_a34 w9_a38 w9_a3c w9_aa0 w9_aa4 q9_320 w9_10 w9_74 r9_23 r9_25 r9_8 b9_1048 q9_1049 S2 KS RS RK0 w9_1028 w9_102c w9_1030 w9_1034 with e | ⟨x10_0, n10, c10, s10, E10, V10, fR10, r10_2, r10_3, r10_4, r10_8, r10_9, r10_18, r10_19, r10_21, r10_22, r10_23, r10_24, r10_25, r10_26, r10_27, w10_8, w10_c, w10_10, w10_14, w10_18, w10_1c, w10_20, w10_24, w10_28, w10_2c, w10_30, w10_34, w10_38, w10_3c, w10_40, w10_44, w10_48, w10_4c, w10_50, w10_54, w10_58, w10_5c, w10_60, w10_64, w10_68, w10_6c, w10_70, w10_74, w10_78, w10_7c, w10_80, w10_84, w10_88, w10_8c, w10_90, w10_94, w10_98, w10_9c, w10_a0, w10_a4, w10_a8, w10_ac, w10_b0, w10_b4, w10_b8, w10_bc, w10_c0, w10_c4, w10_c8, w10_cc, w10_d0, w10_d4, w10_d8, w10_dc, w10_e0, w10_e4, w10_e8, w10_ec, w10_f0, w10_f4, w10_f8, w10_fc, w10_100, w10_104, w10_108, w10_10c, w10_110, w10_114, w10_118, w10_11c, w10_120, w10_124, w10_128, w10_12c, w10_130, w10_428, w10_a20, w10_a24, w10_a28, w10_a2c, w10_a30, w10_a34, w10_a38, w10_a3c, w10_aa0, w10_aa4, w10_1028, w10_102c, w10_1030, w10_1034, b10_1048, q10_320, q10_1049, K10_L⟩
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (c9))))))))) (by rw [r9_3, r8_3, r7_3, r6_3, r5_3, r4_3, r3_3, r2_3, r1_3]) (by rw [r9_4, r8_4, r7_4, r6_4, r5_4, r4_4, r3_4, r2_4, r1_4])
      (fun x hx => (fR9 x hx).trans (fM x hx).symm) e)
  exact .inr (.inr ⟨root6_2, x2_0, x2_1, x3_0, x4_0, x5_0, x6_0, x7_0, x8_0, x9_0, x10_0, n10, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans (c10))))))))), fR10, s10, E10, V10,
    by rw [r10_3, r9_3, r8_3, r7_3, r6_3, r5_3, r4_3, r3_3, r2_3, r1_3], by rw [r10_4, r9_4, r8_4, r7_4, r6_4, r5_4, r4_4, r3_4, r2_4, r1_4], r10_2, r10_8, r10_9, r10_18, r10_19, r10_21, r10_22, r10_23, r10_24, r10_25, r10_26, r10_27, w10_8, w10_c, w10_10, w10_14, w10_18, w10_1c, w10_20, w10_24, w10_28, w10_2c, w10_30, w10_34, w10_38, w10_3c, w10_40, w10_44, w10_48, w10_4c, w10_50, w10_54, w10_58, w10_5c, w10_60, w10_64, w10_68, w10_6c, w10_70, w10_74, w10_78, w10_7c, w10_80, w10_84, w10_88, w10_8c, w10_90, w10_94, w10_98, w10_9c, w10_a0, w10_a4, w10_a8, w10_ac, w10_b0, w10_b4, w10_b8, w10_bc, w10_c0, w10_c4, w10_c8, w10_cc, w10_d0, w10_d4, w10_d8, w10_dc, w10_e0, w10_e4, w10_e8, w10_ec, w10_f0, w10_f4, w10_f8, w10_fc, w10_100, w10_104, w10_108, w10_10c, w10_110, w10_114, w10_118, w10_11c, w10_120, w10_124, w10_128, w10_12c, w10_130, w10_a20, w10_a24, w10_a28, w10_a2c, w10_a30, w10_a34, w10_a38, w10_a3c, w10_aa0, w10_aa4, w10_1028, w10_102c, w10_1030, w10_1034, b10_1048, q10_320, q10_1049⟩)

end C3.RV32.Sv
