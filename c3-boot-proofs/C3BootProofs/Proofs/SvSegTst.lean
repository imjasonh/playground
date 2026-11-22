import C3BootProofs.Proofs.SvSegCk
import C3BootProofs.Proofs.SvTst1
import C3BootProofs.Proofs.SvTst2
import C3BootProofs.Proofs.SvTst3
import C3BootProofs.Proofs.SvTst4
import C3BootProofs.Proofs.SvTst5
import C3BootProofs.Proofs.SvTst6
import C3BootProofs.Proofs.SvTsv

/-!
# `sigstore::verify`: The `TSTInfo` and the timestamp's signature

Composed from generated stages by `scripts/gen-sv-segs.py`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 100000

set_option maxHeartbeats 64000000 in
/-- **The `TSTInfo` and the timestamp's signature**: from 0x2704 to the TSA search at 0x2A40, `sv_tst1` to `sv_tsv`. -/
theorem sv_seg_tst {B out bp x21 x26 dg sip sil : Word} {sr ss : Bytes} {w24 w28 w2c w30 w34 w38 w3c w40 w44 w48 w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w7c w80 w84 w88 w8c w90 w94 w98 w9c wa0 wa4 wa8 wac wb0 wb4 wb8 wbc wc0 wc4 wc8 wcc wd0 wd4 wd8 wdc we0 we4 we8 wec wf0 wf4 wf8 wfc w100 w104 w108 w10c w110 w114 w118 w11c w120 w124 w128 w12c w130 : Word} {v : Nat → Word} {n0 : Machine} {w78 : Word}
    (F : Fr B 0x3830)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out)
    (s0 : St n0.mem SV n0 0x2704 (reg n0))
    (M0 : Word → BitVec 8)
    (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_24 : reg n0 (24 : Fin 32) = dg)
    (g0_25 : reg n0 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32)
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
    (w0_208 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x208) = sip)
    (w0_20c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x20C) = sil)
    (tst_in : SvIn B (w70) (x21).toNat)
    (D0 : SvData M0)
    (q0_421 : ∀ j, j < 48 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x421 + j)) = BitVec.ofNat 8 (sr.getD j 0))
    (q0_451 : ∀ j, j < 48 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x451 + j)) = BitVec.ofNat 8 (ss.getD j 0))
    (w0_78 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78) :
    SvErrRet B out v n0 ∨
    ((sil = 0) ∧
      ∃ tl13_1, derElement 0x30 (memBytes M0 (w70) (x21).toNat) = .ok tl13_1 ∧
      ((x21) - BitVec.ofNat 32 (tl13_1.header + tl13_1.len) = 0) ∧
      derIntIsOf M0 (memBytes M0 ((w70) + BitVec.ofNat 32 tl13_1.header) (BitVec.ofNat 32 tl13_1.len).toNat) ((w70) + BitVec.ofNat 32 tl13_1.header) (derElement 2 (memBytes M0 ((w70) + BitVec.ofNat 32 tl13_1.header) (BitVec.ofNat 32 tl13_1.len).toNat)) ((BitVec.ofNat 32 0x1).extractLsb' 0 8) = .ok true ∧
      ∃ te26_1, derElement 2 (memBytes M0 ((w70) + BitVec.ofNat 32 tl13_1.header) (BitVec.ofNat 32 tl13_1.len).toNat) = .ok te26_1 ∧
      ∃ op32_1 ol32_1, derContent (((w70) + BitVec.ofNat 32 tl13_1.header) + BitVec.ofNat 32 (te26_1.header + te26_1.len)) (derOid (memBytes M0 (((w70) + BitVec.ofNat 32 tl13_1.header) + BitVec.ofNat 32 (te26_1.header + te26_1.len)) ((BitVec.ofNat 32 tl13_1.len) - BitVec.ofNat 32 (te26_1.header + te26_1.len)).toNat)) = .ok (op32_1, ol32_1) ∧
      ∃ to32_1, derOid (memBytes M0 (((w70) + BitVec.ofNat 32 tl13_1.header) + BitVec.ofNat 32 (te26_1.header + te26_1.len)) ((BitVec.ofNat 32 tl13_1.len) - BitVec.ofNat 32 (te26_1.header + te26_1.len)).toNat) = .ok to32_1 ∧
      ∃ tl36_1, derElement 0x30 (memBytes M0 ((((w70) + BitVec.ofNat 32 tl13_1.header) + BitVec.ofNat 32 (te26_1.header + te26_1.len)) + BitVec.ofNat 32 (to32_1.header + to32_1.len)) (((BitVec.ofNat 32 tl13_1.len) - BitVec.ofNat 32 (te26_1.header + te26_1.len)) - BitVec.ofNat 32 (to32_1.header + to32_1.len)).toNat) = .ok tl36_1 ∧
      isSha256Of M0 (((((w70) + BitVec.ofNat 32 tl13_1.header) + BitVec.ofNat 32 (te26_1.header + te26_1.len)) + BitVec.ofNat 32 (to32_1.header + to32_1.len)) + BitVec.ofNat 32 tl36_1.header) (BitVec.ofNat 32 tl36_1.len).toNat = .ok true ∧
      ∃ te45_1, derElement 0x30 (memBytes M0 (((((w70) + BitVec.ofNat 32 tl13_1.header) + BitVec.ofNat 32 (te26_1.header + te26_1.len)) + BitVec.ofNat 32 (to32_1.header + to32_1.len)) + BitVec.ofNat 32 tl36_1.header) (BitVec.ofNat 32 tl36_1.len).toNat) = .ok te45_1 ∧
      ∃ vp51_1 vl51_1, derContent ((((((w70) + BitVec.ofNat 32 tl13_1.header) + BitVec.ofNat 32 (te26_1.header + te26_1.len)) + BitVec.ofNat 32 (to32_1.header + to32_1.len)) + BitVec.ofNat 32 tl36_1.header) + BitVec.ofNat 32 (te45_1.header + te45_1.len)) (derElement 4 (memBytes M0 ((((((w70) + BitVec.ofNat 32 tl13_1.header) + BitVec.ofNat 32 (te26_1.header + te26_1.len)) + BitVec.ofNat 32 (to32_1.header + to32_1.len)) + BitVec.ofNat 32 tl36_1.header) + BitVec.ofNat 32 (te45_1.header + te45_1.len)) ((BitVec.ofNat 32 tl36_1.len) - BitVec.ofNat 32 (te45_1.header + te45_1.len)).toNat)) = .ok (vp51_1, vl51_1) ∧
      ∃ te51_1, derElement 4 (memBytes M0 ((((((w70) + BitVec.ofNat 32 tl13_1.header) + BitVec.ofNat 32 (te26_1.header + te26_1.len)) + BitVec.ofNat 32 (to32_1.header + to32_1.len)) + BitVec.ofNat 32 tl36_1.header) + BitVec.ofNat 32 (te45_1.header + te45_1.len)) ((BitVec.ofNat 32 tl36_1.len) - BitVec.ofNat 32 (te45_1.header + te45_1.len)).toNat) = .ok te51_1 ∧
      (vl51_1 = 32) ∧
      (((BitVec.ofNat 32 tl36_1.len) - BitVec.ofNat 32 (te45_1.header + te45_1.len)) - BitVec.ofNat 32 (te51_1.header + te51_1.len) = 0) ∧
      ∃ tl2_2, derElement 2 (memBytes M0 ((((((w70) + BitVec.ofNat 32 tl13_1.header) + BitVec.ofNat 32 (te26_1.header + te26_1.len)) + BitVec.ofNat 32 (to32_1.header + to32_1.len)) + BitVec.ofNat 32 (tl36_1.header + tl36_1.len))) (((((BitVec.ofNat 32 tl13_1.len) - BitVec.ofNat 32 (te26_1.header + te26_1.len)) - BitVec.ofNat 32 (to32_1.header + to32_1.len)) - BitVec.ofNat 32 (tl36_1.header + tl36_1.len))).toNat) = .ok tl2_2 ∧
      ∃ ip2_2 il2_2, derPosIntOf (memBytes M0 ((((((w70) + BitVec.ofNat 32 tl13_1.header) + BitVec.ofNat 32 (te26_1.header + te26_1.len)) + BitVec.ofNat 32 (to32_1.header + to32_1.len)) + BitVec.ofNat 32 (tl36_1.header + tl36_1.len))) (((((BitVec.ofNat 32 tl13_1.len) - BitVec.ofNat 32 (te26_1.header + te26_1.len)) - BitVec.ofNat 32 (to32_1.header + to32_1.len)) - BitVec.ofNat 32 (tl36_1.header + tl36_1.len))).toNat) ((((((w70) + BitVec.ofNat 32 tl13_1.header) + BitVec.ofNat 32 (te26_1.header + te26_1.len)) + BitVec.ofNat 32 (to32_1.header + to32_1.len)) + BitVec.ofNat 32 (tl36_1.header + tl36_1.len))) (.ok tl2_2) = .ok (ip2_2, il2_2) ∧
      (((il2_2) - (aluEval .sltu ((M0 (ip2_2)).zeroExtend 32) 1)).toNat ≤ 20) ∧
      ∃ tl13_2, derElement 0x18 (memBytes M0 (((((((w70) + BitVec.ofNat 32 tl13_1.header) + BitVec.ofNat 32 (te26_1.header + te26_1.len)) + BitVec.ofNat 32 (to32_1.header + to32_1.len)) + BitVec.ofNat 32 (tl36_1.header + tl36_1.len))) + BitVec.ofNat 32 (tl2_2.header + tl2_2.len)) ((((((BitVec.ofNat 32 tl13_1.len) - BitVec.ofNat 32 (te26_1.header + te26_1.len)) - BitVec.ofNat 32 (to32_1.header + to32_1.len)) - BitVec.ofNat 32 (tl36_1.header + tl36_1.len))) - BitVec.ofNat 32 (tl2_2.header + tl2_2.len)).toNat) = .ok tl13_2 ∧
      ∃ tm18_2, generalizedTime (memBytes M0 ((((((((w70) + BitVec.ofNat 32 tl13_1.header) + BitVec.ofNat 32 (te26_1.header + te26_1.len)) + BitVec.ofNat 32 (to32_1.header + to32_1.len)) + BitVec.ofNat 32 (tl36_1.header + tl36_1.len))) + BitVec.ofNat 32 (tl2_2.header + tl2_2.len)) + BitVec.ofNat 32 tl13_2.header) ((BitVec.ofNat 32 tl13_2.len).toNat)) = some tm18_2 ∧
      ∃ tst3_w1328_3 : Word, ∃ tst3_w132c_3 : Word, ((tst3_w1328_3 = ((((((((w70) + BitVec.ofNat 32 tl13_1.header) + BitVec.ofNat 32 (te26_1.header + te26_1.len)) + BitVec.ofNat 32 (to32_1.header + to32_1.len)) + BitVec.ofNat 32 (tl36_1.header + tl36_1.len))) + BitVec.ofNat 32 (tl2_2.header + tl2_2.len)) + BitVec.ofNat 32 (tl13_2.header + tl13_2.len)) ∧ tst3_w132c_3 = (((((((BitVec.ofNat 32 tl13_1.len) - BitVec.ofNat 32 (te26_1.header + te26_1.len)) - BitVec.ofNat 32 (to32_1.header + to32_1.len)) - BitVec.ofNat 32 (tl36_1.header + tl36_1.len))) - BitVec.ofNat 32 (tl2_2.header + tl2_2.len)) - BitVec.ofNat 32 (tl13_2.header + tl13_2.len))) ∨ (∃ tl2, derOptRes 0x30 (memBytes M0 (((((((((w70) + BitVec.ofNat 32 tl13_1.header) + BitVec.ofNat 32 (te26_1.header + te26_1.len)) + BitVec.ofNat 32 (to32_1.header + to32_1.len)) + BitVec.ofNat 32 (tl36_1.header + tl36_1.len))) + BitVec.ofNat 32 (tl2_2.header + tl2_2.len)) + BitVec.ofNat 32 (tl13_2.header + tl13_2.len))) ((((((((BitVec.ofNat 32 tl13_1.len) - BitVec.ofNat 32 (te26_1.header + te26_1.len)) - BitVec.ofNat 32 (to32_1.header + to32_1.len)) - BitVec.ofNat 32 (tl36_1.header + tl36_1.len))) - BitVec.ofNat 32 (tl2_2.header + tl2_2.len)) - BitVec.ofNat 32 (tl13_2.header + tl13_2.len))).toNat) = some (.ok tl2) ∧ tst3_w1328_3 = (((((((((w70) + BitVec.ofNat 32 tl13_1.header) + BitVec.ofNat 32 (te26_1.header + te26_1.len)) + BitVec.ofNat 32 (to32_1.header + to32_1.len)) + BitVec.ofNat 32 (tl36_1.header + tl36_1.len))) + BitVec.ofNat 32 (tl2_2.header + tl2_2.len)) + BitVec.ofNat 32 (tl13_2.header + tl13_2.len))) + BitVec.ofNat 32 (tl2.header + tl2.len) ∧ tst3_w132c_3 = ((((((((BitVec.ofNat 32 tl13_1.len) - BitVec.ofNat 32 (te26_1.header + te26_1.len)) - BitVec.ofNat 32 (to32_1.header + to32_1.len)) - BitVec.ofNat 32 (tl36_1.header + tl36_1.len))) - BitVec.ofNat 32 (tl2_2.header + tl2_2.len)) - BitVec.ofNat 32 (tl13_2.header + tl13_2.len))) - BitVec.ofNat 32 (tl2.header + tl2.len))) ∧ SvIn B tst3_w1328_3 tst3_w132c_3.toNat ∧
      ∃ tst4_r8_4 : Word, ∃ tst4_w1328_4 : Word, ∃ tst4_w132c_4 : Word, ((tst4_r8_4 = BitVec.ofNat 32 0x18 ∧ tst4_w1328_4 = tst3_w1328_3 ∧ tst4_w132c_4 = tst3_w132c_3) ∨ (derBoolOf (memBytes M0 (tst3_w1328_3) (tst3_w132c_3).toNat) (derElement 1 (memBytes M0 (tst3_w1328_3) (tst3_w132c_3).toNat)) = .ok () ∧ ∃ tb10_1, derElement 1 (memBytes M0 (tst3_w1328_3) (tst3_w132c_3).toNat) = .ok tb10_1 ∧ ∃ tst4b_w1328_2 : Word, ∃ tst4b_w132c_2 : Word, ((tst4b_w1328_2 = ((tst3_w1328_3) + BitVec.ofNat 32 (tb10_1.header + tb10_1.len)) ∧ tst4b_w132c_2 = ((tst3_w132c_3) - BitVec.ofNat 32 (tb10_1.header + tb10_1.len))) ∨ (∃ tst4n_w1328_2 : Word, ∃ tst4n_w132c_2 : Word, ((∃ ip4 il4, derIntOf (memBytes M0 (((tst3_w1328_3) + BitVec.ofNat 32 (tb10_1.header + tb10_1.len))) (((tst3_w132c_3) - BitVec.ofNat 32 (tb10_1.header + tb10_1.len))).toNat) (((tst3_w1328_3) + BitVec.ofNat 32 (tb10_1.header + tb10_1.len))) (derElement 2 (memBytes M0 (((tst3_w1328_3) + BitVec.ofNat 32 (tb10_1.header + tb10_1.len))) (((tst3_w132c_3) - BitVec.ofNat 32 (tb10_1.header + tb10_1.len))).toNat)) = .ok (ip4, il4) ∧ ∃ ti4, derElement 2 (memBytes M0 (((tst3_w1328_3) + BitVec.ofNat 32 (tb10_1.header + tb10_1.len))) (((tst3_w132c_3) - BitVec.ofNat 32 (tb10_1.header + tb10_1.len))).toNat) = .ok ti4 ∧ tst4n_w1328_2 = (((tst3_w1328_3) + BitVec.ofNat 32 (tb10_1.header + tb10_1.len))) + BitVec.ofNat 32 (ti4.header + ti4.len) ∧ tst4n_w132c_2 = (((tst3_w132c_3) - BitVec.ofNat 32 (tb10_1.header + tb10_1.len))) - BitVec.ofNat 32 (ti4.header + ti4.len)) ∨ (tst4n_w1328_2 = ((tst3_w1328_3) + BitVec.ofNat 32 (tb10_1.header + tb10_1.len)) ∧ tst4n_w132c_2 = ((tst3_w132c_3) - BitVec.ofNat 32 (tb10_1.header + tb10_1.len)))) ∧ SvIn B tst4n_w1328_2 tst4n_w132c_2.toNat ∧ tst4b_w1328_2 = tst4n_w1328_2 ∧ tst4b_w132c_2 = tst4n_w132c_2)) ∧ SvIn B tst4b_w1328_2 tst4b_w132c_2.toNat ∧ tst4_r8_4 = (BitVec.ofNat 32 0xFFFFFFFF) ∧ tst4_w1328_4 = tst4b_w1328_2 ∧ tst4_w132c_4 = tst4b_w132c_2) ∨ (∃ tst4n_w1328_2 : Word, ∃ tst4n_w132c_2 : Word, ((∃ ip4 il4, derIntOf (memBytes M0 (tst3_w1328_3) (tst3_w132c_3).toNat) (tst3_w1328_3) (derElement 2 (memBytes M0 (tst3_w1328_3) (tst3_w132c_3).toNat)) = .ok (ip4, il4) ∧ ∃ ti4, derElement 2 (memBytes M0 (tst3_w1328_3) (tst3_w132c_3).toNat) = .ok ti4 ∧ tst4n_w1328_2 = (tst3_w1328_3) + BitVec.ofNat 32 (ti4.header + ti4.len) ∧ tst4n_w132c_2 = (tst3_w132c_3) - BitVec.ofNat 32 (ti4.header + ti4.len)) ∨ (tst4n_w1328_2 = tst3_w1328_3 ∧ tst4n_w132c_2 = tst3_w132c_3)) ∧ SvIn B tst4n_w1328_2 tst4n_w132c_2.toNat ∧ tst4_r8_4 = (BitVec.ofNat 32 0x18) ∧ tst4_w1328_4 = tst4n_w1328_2 ∧ tst4_w132c_4 = tst4n_w132c_2)) ∧ SvIn B tst4_w1328_4 tst4_w132c_4.toNat ∧
      ∃ tst5_w1328_5 : Word, ∃ tst5_w132c_5 : Word, ((tst5_w1328_5 = tst4_w1328_4 ∧ tst5_w132c_5 = tst4_w132c_4) ∨ (∃ tl2, derOptRes 0xA0 (memBytes M0 (tst4_w1328_4) (tst4_w132c_4).toNat) = some (.ok tl2) ∧ tst5_w1328_5 = (tst4_w1328_4) + BitVec.ofNat 32 (tl2.header + tl2.len) ∧ tst5_w132c_5 = (tst4_w132c_4) - BitVec.ofNat 32 (tl2.header + tl2.len))) ∧ SvIn B tst5_w1328_5 tst5_w132c_5.toNat ∧
      ∃ tst6_w1328_6 : Word, ∃ tst6_w132c_6 : Word, (((tst5_w132c_5 = 0) ∧ tst6_w1328_6 = tst5_w1328_5 ∧ tst6_w132c_6 = tst5_w132c_5) ∨ (∃ tl2, derOptRes 0xA1 (memBytes M0 (tst5_w1328_5) (tst5_w132c_5).toNat) = some (.ok tl2) ∧ ((tst5_w132c_5) - BitVec.ofNat 32 (tl2.header + tl2.len) = 0) ∧ tst6_w1328_6 = (tst5_w1328_5) + BitVec.ofNat 32 (tl2.header + tl2.len) ∧ tst6_w132c_6 = (tst5_w132c_5) - BitVec.ofNat 32 (tl2.header + tl2.len))) ∧ SvIn B tst6_w1328_6 tst6_w132c_6.toNat ∧
    ∃ n', Steps n0 n' ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        St n'.mem SV n' 0x2A40 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (9 : Fin 32) = BitVec.ofNat 32 0x80 ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (21 : Fin 32) = x21 ∧
        reg n' (22 : Fin 32) = vp51_1 ∧
        reg n' (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 ∧
        reg n' (24 : Fin 32) = dg ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = (BitVec.ofNat 32 (tm18_2 % 2 ^ 32)) ∧
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
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = (w80) + BitVec.ofNat 32 0x198 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = (BitVec.ofNat 32 (tm18_2 / 2 ^ 32)) ∧
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
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = w70 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = x21 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = w5c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = w48 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = w44 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = w60 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = (BitVec.ofNat 32 (tm18_2 % 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = (BitVec.ofNat 32 (tm18_2 / 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = vp51_1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 8 (sr.getD 0 0) ∧
        (∀ j, j < 47 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA41 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0)) ∧
        (∀ j, j < 48 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA70 + j)) = BitVec.ofNat 8 (ss.getD j 0)) ∧
        (∀ j, j < 47 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1020 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0)) ∧
        (∀ j, j < 48 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x104F + j)) = BitVec.ofNat 8 (ss.getD j 0)) ∧
        (∀ j, j < 47 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1480 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0)) ∧
        (∀ j, j < 48 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x14AF + j)) = BitVec.ofNat 8 (ss.getD j 0)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x208) = sip ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x20C) = sil ∧
        (∀ j, j < 48 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x451 + j)) = BitVec.ofNat 8 (ss.getD j 0)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) = w70 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x244) = x21 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x248) = (w70) + BitVec.ofNat 32 (tl13_1.header + tl13_1.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24C) = (x21) - BitVec.ofNat 32 (tl13_1.header + tl13_1.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ((((w70) + BitVec.ofNat 32 tl13_1.header) + BitVec.ofNat 32 (te26_1.header + te26_1.len)) + BitVec.ofNat 32 (to32_1.header + to32_1.len)) + BitVec.ofNat 32 tl36_1.header ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = BitVec.ofNat 32 tl36_1.len ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = ((((((w70) + BitVec.ofNat 32 tl13_1.header) + BitVec.ofNat 32 (te26_1.header + te26_1.len)) + BitVec.ofNat 32 (to32_1.header + to32_1.len)) + BitVec.ofNat 32 tl36_1.header) + BitVec.ofNat 32 (te45_1.header + te45_1.len)) + BitVec.ofNat 32 (te51_1.header + te51_1.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = ((BitVec.ofNat 32 tl36_1.len) - BitVec.ofNat 32 (te45_1.header + te45_1.len)) - BitVec.ofNat 32 (te51_1.header + te51_1.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (w70) + BitVec.ofNat 32 tl13_1.header ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl13_1.len ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = tst6_w1328_6 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = tst6_w132c_6 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1388) = BitVec.ofNat 32 (tm18_2 % 2 ^ 32) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x138C) = BitVec.ofNat 32 (tm18_2 / 2 ^ 32) ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) = (0 : BitVec 8) ∧
        SvKeepL B n0.mem n'.mem [(0x1020, 0x5F), (0x240, 0x4), (0x244, 0x4), (0x248, 0x4), (0x24C, 0x4), (0x420, 0x10), (0x248, 0x8), (0x1325, 0xB), (0x1320, 0x4), (0x1324, 0x1), (0x1328, 0x8), (0x420, 0x8), (0x1328, 0x8), (0x420, 0x10), (0x1328, 0x8), (0x325, 0xB), (0x320, 0x4), (0x324, 0x1), (0x328, 0x8), (0x420, 0x8), (0x328, 0x8), (0x420, 0x11), (0x1380, 0x10), (0x3C, 0x4), (0x78, 0x4), (0x420, 0x18), (0x1480, 0x5F), (0xA25, 0x1), (0xA26, 0x1), (0xA27, 0x1), (0xA28, 0x4), (0xA2C, 0x4), (0xA30, 0x4), (0xA34, 0x4), (0xA40, 0x1), (0xA41, 0x5F), (0xAA0, 0x4), (0xAA4, 0x4), (0xA20, 0x4), (0xA24, 0x1), (0xA38, 0x4), (0xA3C, 0x4), (0x74, 0x4)]) := by
  rcases sv_tst1 F E0 V0 hret hO s0 M0 fM g0_2 g0_18 g0_19 g0_21 g0_24 g0_25 g0_26 g0_27 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_3c w0_40 w0_44 w0_48 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_a8 w0_ac w0_b0 w0_b4 w0_b8 w0_bc w0_c0 w0_c4 w0_c8 w0_cc w0_d0 w0_d4 w0_d8 w0_dc w0_e0 w0_e4 w0_e8 w0_ec w0_f0 w0_f4 w0_f8 w0_fc w0_100 w0_104 w0_108 w0_10c w0_110 w0_114 w0_118 w0_11c w0_120 w0_124 w0_128 w0_12c w0_130 w0_208 w0_20c tst_in D0 q0_421 q0_451 with ⟨-, e⟩ | ⟨x1_0, tl13_1, x1_1, x1_2, x1_3, te26_1, x1_4, op32_1, ol32_1, x1_5, to32_1, x1_6, tl36_1, x1_7, x1_8, te45_1, x1_9, vp51_1, vl51_1, x1_10, te51_1, x1_11, x1_12, x1_13, n1, c1, s1, E1, V1, fR1, r1_2, r1_3, r1_4, r1_8, r1_18, r1_19, r1_20, r1_21, r1_22, r1_24, r1_25, r1_26, r1_27, w1_24, w1_28, w1_2c, w1_30, w1_34, w1_38, w1_3c, w1_40, w1_44, w1_48, w1_4c, w1_50, w1_54, w1_58, w1_5c, w1_60, w1_64, w1_68, w1_6c, w1_70, w1_7c, w1_80, w1_84, w1_88, w1_8c, w1_90, w1_94, w1_98, w1_9c, w1_a0, w1_a4, w1_a8, w1_ac, w1_b0, w1_b4, w1_b8, w1_bc, w1_c0, w1_c4, w1_c8, w1_cc, w1_d0, w1_d4, w1_d8, w1_dc, w1_e0, w1_e4, w1_e8, w1_ec, w1_f0, w1_f4, w1_f8, w1_fc, w1_100, w1_104, w1_108, w1_10c, w1_110, w1_114, w1_118, w1_11c, w1_120, w1_124, w1_128, w1_12c, w1_130, w1_208, w1_20c, w1_240, w1_244, w1_248, w1_24c, w1_320, w1_324, w1_328, w1_32c, w1_420, w1_424, w1_428, w1_42c, w1_1320, w1_1324, w1_1328, w1_132c, q1_451, q1_1020, q1_104f, K1_L⟩
  · exact .inl e
  rcases sv_tst2 (x8 := 0) F E1 V1 hret hO s1 M0 fR1 r1_2 r1_8 r1_18 r1_19 r1_20 r1_21 r1_22 r1_24 r1_25 r1_26 r1_27 w1_24 w1_28 w1_2c w1_30 w1_34 w1_38 w1_3c w1_40 w1_44 w1_48 w1_4c w1_50 w1_54 w1_58 w1_5c w1_60 w1_64 w1_68 w1_6c w1_70 ((K1_L.w32 (by decide) (by decide)).trans w0_78) w1_7c w1_80 w1_84 w1_88 w1_8c w1_90 w1_94 w1_98 w1_9c w1_a0 w1_a4 w1_a8 w1_ac w1_b0 w1_b4 w1_b8 w1_bc w1_c0 w1_c4 w1_c8 w1_cc w1_d0 w1_d4 w1_d8 w1_dc w1_e0 w1_e4 w1_e8 w1_ec w1_f0 w1_f4 w1_f8 w1_fc w1_100 w1_104 w1_108 w1_10c w1_110 w1_114 w1_118 w1_11c w1_120 w1_124 w1_128 w1_12c w1_130 w1_1328 w1_132c ((((((tst_in).content x1_1).ofNatLen).restW x1_4).restW (derOid_ok_elem x1_6)).restW x1_7) D0 q1_1020 q1_104f with ⟨-, e⟩ | ⟨tl2_2, x2_0, ip2_2, il2_2, x2_1, x2_2, tl13_2, x2_3, tm18_2, x2_4, n2, c2, s2, E2, V2, fR2, r2_2, r2_3, r2_4, r2_8, r2_18, r2_19, r2_20, r2_21, r2_22, r2_24, r2_25, r2_26, r2_27, w2_24, w2_28, w2_2c, w2_30, w2_34, w2_38, w2_3c, w2_40, w2_44, w2_48, w2_4c, w2_50, w2_54, w2_58, w2_5c, w2_60, w2_64, w2_68, w2_6c, w2_70, w2_78, w2_7c, w2_80, w2_84, w2_88, w2_8c, w2_90, w2_94, w2_98, w2_9c, w2_a0, w2_a4, w2_a8, w2_ac, w2_b0, w2_b4, w2_b8, w2_bc, w2_c0, w2_c4, w2_c8, w2_cc, w2_d0, w2_d4, w2_d8, w2_dc, w2_e0, w2_e4, w2_e8, w2_ec, w2_f0, w2_f4, w2_f8, w2_fc, w2_100, w2_104, w2_108, w2_10c, w2_110, w2_114, w2_118, w2_11c, w2_120, w2_124, w2_128, w2_12c, w2_130, w2_420, w2_424, w2_428, w2_42c, w2_1328, w2_132c, w2_1388, w2_138c, b2_430, b2_1380, q2_1020, q2_104f, K2_L⟩
  · exact .inl (SvErrRet.pre (c1) (by rw [r1_3]) (by rw [r1_4])
      (fun x hx => (fR1 x hx).trans (fM x hx).symm) e)
  rcases sv_tst3 (x8 := 0) F E2 V2 hret hO s2 M0 fR2 r2_2 r2_8 r2_18 r2_19 r2_20 r2_21 r2_22 r2_24 r2_25 r2_26 r2_27 w2_24 w2_28 w2_2c w2_30 w2_34 w2_38 w2_3c w2_40 w2_44 w2_48 w2_4c w2_50 w2_54 w2_58 w2_5c w2_60 w2_64 w2_68 w2_6c w2_70 w2_78 w2_7c w2_80 w2_84 w2_88 w2_8c w2_90 w2_94 w2_98 w2_9c w2_a0 w2_a4 w2_a8 w2_ac w2_b0 w2_b4 w2_b8 w2_bc w2_c0 w2_c4 w2_c8 w2_cc w2_d0 w2_d4 w2_d8 w2_dc w2_e0 w2_e4 w2_e8 w2_ec w2_f0 w2_f4 w2_f8 w2_fc w2_100 w2_104 w2_108 w2_10c w2_110 w2_114 w2_118 w2_11c w2_120 w2_124 w2_128 w2_12c w2_130 w2_1328 w2_132c ((((((((tst_in).content x1_1).ofNatLen).restW x1_4).restW (derOid_ok_elem x1_6)).restW x1_7).restW x2_0).restW x2_3) D0 q2_1020 q2_104f with e | ⟨tst3_w1328_3, tst3_w132c_3, x3_0, x3_1, n3, c3, s3, E3, V3, fR3, r3_2, r3_3, r3_4, r3_8, r3_18, r3_19, r3_20, r3_21, r3_22, r3_24, r3_25, r3_26, r3_27, w3_24, w3_28, w3_2c, w3_30, w3_34, w3_38, w3_3c, w3_40, w3_44, w3_48, w3_4c, w3_50, w3_54, w3_58, w3_5c, w3_60, w3_64, w3_68, w3_6c, w3_70, w3_78, w3_7c, w3_80, w3_84, w3_88, w3_8c, w3_90, w3_94, w3_98, w3_9c, w3_a0, w3_a4, w3_a8, w3_ac, w3_b0, w3_b4, w3_b8, w3_bc, w3_c0, w3_c4, w3_c8, w3_cc, w3_d0, w3_d4, w3_d8, w3_dc, w3_e0, w3_e4, w3_e8, w3_ec, w3_f0, w3_f4, w3_f8, w3_fc, w3_100, w3_104, w3_108, w3_10c, w3_110, w3_114, w3_118, w3_11c, w3_120, w3_124, w3_128, w3_12c, w3_130, w3_1328, w3_132c, q3_1020, q3_104f, K3_L⟩
  · exact .inl (SvErrRet.pre (c1.trans (c2)) (by rw [r2_3, r1_3]) (by rw [r2_4, r1_4])
      (fun x hx => (fR2 x hx).trans (fM x hx).symm) e)
  rcases sv_tst4 (x8 := 0) F E3 V3 hret hO s3 M0 fR3 r3_2 r3_8 r3_18 r3_19 r3_20 r3_21 r3_22 r3_24 r3_25 r3_26 r3_27 w3_24 w3_28 w3_2c w3_30 w3_34 w3_38 w3_3c w3_40 w3_44 w3_48 w3_4c w3_50 w3_54 w3_58 w3_5c w3_60 w3_64 w3_68 w3_6c w3_70 w3_78 w3_7c w3_80 w3_84 w3_88 w3_8c w3_90 w3_94 w3_98 w3_9c w3_a0 w3_a4 w3_a8 w3_ac w3_b0 w3_b4 w3_b8 w3_bc w3_c0 w3_c4 w3_c8 w3_cc w3_d0 w3_d4 w3_d8 w3_dc w3_e0 w3_e4 w3_e8 w3_ec w3_f0 w3_f4 w3_f8 w3_fc w3_100 w3_104 w3_108 w3_10c w3_110 w3_114 w3_118 w3_11c w3_120 w3_124 w3_128 w3_12c w3_130 w3_1328 w3_132c x3_1 D0 q3_1020 q3_104f with e | ⟨tst4_r8_4, tst4_w1328_4, tst4_w132c_4, x4_0, x4_1, n4, c4, s4, E4, V4, fR4, r4_2, r4_3, r4_4, r4_8, r4_18, r4_19, r4_20, r4_21, r4_22, r4_24, r4_25, r4_26, r4_27, w4_24, w4_28, w4_2c, w4_30, w4_34, w4_38, w4_3c, w4_40, w4_44, w4_48, w4_4c, w4_50, w4_54, w4_58, w4_5c, w4_60, w4_64, w4_68, w4_6c, w4_70, w4_78, w4_7c, w4_80, w4_84, w4_88, w4_8c, w4_90, w4_94, w4_98, w4_9c, w4_a0, w4_a4, w4_a8, w4_ac, w4_b0, w4_b4, w4_b8, w4_bc, w4_c0, w4_c4, w4_c8, w4_cc, w4_d0, w4_d4, w4_d8, w4_dc, w4_e0, w4_e4, w4_e8, w4_ec, w4_f0, w4_f4, w4_f8, w4_fc, w4_100, w4_104, w4_108, w4_10c, w4_110, w4_114, w4_118, w4_11c, w4_120, w4_124, w4_128, w4_12c, w4_130, w4_1328, w4_132c, q4_1020, q4_104f, K4_L⟩
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3))) (by rw [r3_3, r2_3, r1_3]) (by rw [r3_4, r2_4, r1_4])
      (fun x hx => (fR3 x hx).trans (fM x hx).symm) e)
  rcases sv_tst5 F E4 V4 hret hO s4 M0 fR4 r4_2 r4_8 r4_18 r4_19 r4_20 r4_21 r4_22 r4_24 r4_25 r4_26 r4_27 w4_24 w4_28 w4_2c w4_30 w4_34 w4_38 w4_3c w4_40 w4_44 w4_48 w4_4c w4_50 w4_54 w4_58 w4_5c w4_60 w4_64 w4_68 w4_6c w4_70 w4_78 w4_7c w4_80 w4_84 w4_88 w4_8c w4_90 w4_94 w4_98 w4_9c w4_a0 w4_a4 w4_a8 w4_ac w4_b0 w4_b4 w4_b8 w4_bc w4_c0 w4_c4 w4_c8 w4_cc w4_d0 w4_d4 w4_d8 w4_dc w4_e0 w4_e4 w4_e8 w4_ec w4_f0 w4_f4 w4_f8 w4_fc w4_100 w4_104 w4_108 w4_10c w4_110 w4_114 w4_118 w4_11c w4_120 w4_124 w4_128 w4_12c w4_130 w4_1328 w4_132c x4_1 D0 q4_1020 q4_104f with e | ⟨tst5_w1328_5, tst5_w132c_5, x5_0, x5_1, n5, c5, s5, E5, V5, fR5, r5_2, r5_3, r5_4, r5_8, r5_18, r5_19, r5_20, r5_21, r5_22, r5_24, r5_25, r5_26, r5_27, w5_24, w5_28, w5_2c, w5_30, w5_34, w5_38, w5_3c, w5_40, w5_44, w5_48, w5_4c, w5_50, w5_54, w5_58, w5_5c, w5_60, w5_64, w5_68, w5_6c, w5_70, w5_78, w5_7c, w5_80, w5_84, w5_88, w5_8c, w5_90, w5_94, w5_98, w5_9c, w5_a0, w5_a4, w5_a8, w5_ac, w5_b0, w5_b4, w5_b8, w5_bc, w5_c0, w5_c4, w5_c8, w5_cc, w5_d0, w5_d4, w5_d8, w5_dc, w5_e0, w5_e4, w5_e8, w5_ec, w5_f0, w5_f4, w5_f8, w5_fc, w5_100, w5_104, w5_108, w5_10c, w5_110, w5_114, w5_118, w5_11c, w5_120, w5_124, w5_128, w5_12c, w5_130, w5_1328, w5_132c, q5_1020, q5_104f, K5_L⟩
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3.trans (c4)))) (by rw [r4_3, r3_3, r2_3, r1_3]) (by rw [r4_4, r3_4, r2_4, r1_4])
      (fun x hx => (fR4 x hx).trans (fM x hx).symm) e)
  rcases sv_tst6 F E5 V5 hret hO s5 M0 fR5 r5_2 r5_8 r5_18 r5_19 r5_20 r5_21 r5_22 r5_24 r5_25 r5_26 r5_27 w5_24 w5_28 w5_2c w5_30 w5_34 w5_38 w5_3c w5_40 w5_44 w5_48 w5_4c w5_50 w5_54 w5_58 w5_5c w5_60 w5_64 w5_68 w5_6c w5_70 w5_78 w5_7c w5_80 w5_84 w5_88 w5_8c w5_90 w5_94 w5_98 w5_9c w5_a0 w5_a4 w5_a8 w5_ac w5_b0 w5_b4 w5_b8 w5_bc w5_c0 w5_c4 w5_c8 w5_cc w5_d0 w5_d4 w5_d8 w5_dc w5_e0 w5_e4 w5_e8 w5_ec w5_f0 w5_f4 w5_f8 w5_fc w5_100 w5_104 w5_108 w5_10c w5_110 w5_114 w5_118 w5_11c w5_120 w5_124 w5_128 w5_12c w5_130 w5_1328 w5_132c x5_1 D0 q5_1020 q5_104f with e | ⟨tst6_w1328_6, tst6_w132c_6, x6_0, x6_1, n6, c6, s6, E6, V6, fR6, r6_2, r6_3, r6_4, r6_8, r6_18, r6_19, r6_20, r6_21, r6_22, r6_24, r6_25, r6_26, r6_27, w6_24, w6_28, w6_2c, w6_30, w6_34, w6_38, w6_3c, w6_40, w6_44, w6_48, w6_4c, w6_50, w6_54, w6_58, w6_5c, w6_60, w6_64, w6_68, w6_6c, w6_70, w6_78, w6_7c, w6_80, w6_84, w6_88, w6_8c, w6_90, w6_94, w6_98, w6_9c, w6_a0, w6_a4, w6_a8, w6_ac, w6_b0, w6_b4, w6_b8, w6_bc, w6_c0, w6_c4, w6_c8, w6_cc, w6_d0, w6_d4, w6_d8, w6_dc, w6_e0, w6_e4, w6_e8, w6_ec, w6_f0, w6_f4, w6_f8, w6_fc, w6_100, w6_104, w6_108, w6_10c, w6_110, w6_114, w6_118, w6_11c, w6_120, w6_124, w6_128, w6_12c, w6_130, w6_1328, w6_132c, q6_1020, q6_104f, K6_L⟩
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3.trans (c4.trans (c5))))) (by rw [r5_3, r4_3, r3_3, r2_3, r1_3]) (by rw [r5_4, r4_4, r3_4, r2_4, r1_4])
      (fun x hx => (fR5 x hx).trans (fM x hx).symm) e)
  rcases sv_tsv F E6 V6 hret hO s6 M0 fR6 r6_2 r6_8 r6_18 r6_19 r6_20 r6_21 r6_22 r6_24 r6_25 r6_26 r6_27 w6_24 w6_28 w6_2c w6_30 w6_34 w6_38 w6_3c w6_40 w6_44 w6_48 w6_4c w6_50 w6_54 w6_58 w6_5c w6_60 w6_64 w6_68 w6_6c w6_70 w6_78 w6_7c w6_80 w6_84 w6_88 w6_8c w6_90 w6_94 w6_98 w6_9c w6_a0 w6_a4 w6_a8 w6_ac w6_b0 w6_b4 w6_b8 w6_bc w6_c0 w6_c4 w6_c8 w6_cc w6_d0 w6_d4 w6_d8 w6_dc w6_e0 w6_e4 w6_e8 w6_ec w6_f0 w6_f4 w6_f8 w6_fc w6_100 w6_104 w6_108 w6_10c w6_110 w6_114 w6_118 w6_11c w6_120 w6_124 w6_128 w6_12c w6_130 q6_1020 q6_104f ((tst_in).pos_ne) with ⟨-, e⟩ | ⟨n7, c7, s7, E7, V7, fR7, r7_2, r7_3, r7_4, r7_9, r7_18, r7_19, r7_21, r7_22, r7_23, r7_24, r7_26, r7_27, w7_24, w7_28, w7_2c, w7_30, w7_34, w7_38, w7_3c, w7_40, w7_44, w7_48, w7_4c, w7_50, w7_54, w7_58, w7_5c, w7_60, w7_64, w7_68, w7_6c, w7_70, w7_74, w7_78, w7_7c, w7_80, w7_84, w7_88, w7_8c, w7_90, w7_94, w7_98, w7_9c, w7_a0, w7_a4, w7_a8, w7_ac, w7_b0, w7_b4, w7_b8, w7_bc, w7_c0, w7_c4, w7_c8, w7_cc, w7_d0, w7_d4, w7_d8, w7_dc, w7_e0, w7_e4, w7_e8, w7_ec, w7_f0, w7_f4, w7_f8, w7_fc, w7_100, w7_104, w7_108, w7_10c, w7_110, w7_114, w7_118, w7_11c, w7_120, w7_124, w7_128, w7_12c, w7_130, w7_a20, w7_a24, w7_a28, w7_a2c, w7_a30, w7_a34, w7_a38, w7_a3c, w7_aa0, w7_aa4, b7_a40, q7_a41, q7_a70, q7_1020, q7_104f, q7_1480, q7_14af, K7_L⟩
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6)))))) (by rw [r6_3, r5_3, r4_3, r3_3, r2_3, r1_3]) (by rw [r6_4, r5_4, r4_4, r3_4, r2_4, r1_4])
      (fun x hx => (fR6 x hx).trans (fM x hx).symm) e)
  exact .inr ⟨x1_0, tl13_1, x1_1, x1_2, x1_3, te26_1, x1_4, op32_1, ol32_1, x1_5, to32_1, x1_6, tl36_1, x1_7, x1_8, te45_1, x1_9, vp51_1, vl51_1, x1_10, te51_1, x1_11, x1_12, x1_13, tl2_2, x2_0, ip2_2, il2_2, x2_1, x2_2, tl13_2, x2_3, tm18_2, x2_4, tst3_w1328_3, tst3_w132c_3, x3_0, x3_1, tst4_r8_4, tst4_w1328_4, tst4_w132c_4, x4_0, x4_1, tst5_w1328_5, tst5_w132c_5, x5_0, x5_1, tst6_w1328_6, tst6_w132c_6, x6_0, x6_1, n7, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7)))))), fR7, s7, E7, V7,
    by rw [r7_3, r6_3, r5_3, r4_3, r3_3, r2_3, r1_3], by rw [r7_4, r6_4, r5_4, r4_4, r3_4, r2_4, r1_4], r7_2, r7_9, r7_18, r7_19, r7_21, r7_22, r7_23, r7_24, r7_26, r7_27, w7_24, w7_28, w7_2c, w7_30, w7_34, w7_38, w7_3c, w7_40, w7_44, w7_48, w7_4c, w7_50, w7_54, w7_58, w7_5c, w7_60, w7_64, w7_68, w7_6c, w7_70, w7_74, w7_78, w7_7c, w7_80, w7_84, w7_88, w7_8c, w7_90, w7_94, w7_98, w7_9c, w7_a0, w7_a4, w7_a8, w7_ac, w7_b0, w7_b4, w7_b8, w7_bc, w7_c0, w7_c4, w7_c8, w7_cc, w7_d0, w7_d4, w7_d8, w7_dc, w7_e0, w7_e4, w7_e8, w7_ec, w7_f0, w7_f4, w7_f8, w7_fc, w7_100, w7_104, w7_108, w7_10c, w7_110, w7_114, w7_118, w7_11c, w7_120, w7_124, w7_128, w7_12c, w7_130, w7_a20, w7_a24, w7_a28, w7_a2c, w7_a30, w7_a34, w7_a38, w7_a3c, w7_aa0, w7_aa4, b7_a40, q7_a41, q7_a70, q7_1020, q7_104f, q7_1480, q7_14af, ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_208)))))), ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_20c)))))), (fun j hj => (K7_L.range (by decide) (by decide) j hj).trans ((fun j hj => (K6_L.range (by decide) (by decide) j hj).trans ((fun j hj => (K5_L.range (by decide) (by decide) j hj).trans ((fun j hj => (K4_L.range (by decide) (by decide) j hj).trans ((fun j hj => (K3_L.range (by decide) (by decide) j hj).trans ((fun j hj => (K2_L.range (by decide) (by decide) j hj).trans (q1_451 j hj)) j hj)) j hj)) j hj)) j hj)) j hj)), ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_240)))))), ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_244)))))), ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_248)))))), ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_24c)))))), ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_320)))))), ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_324)))))), ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_328)))))), ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_32c)))))), ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_1320)))))), ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_1324)))))), ((K7_L.w32 (by decide) (by decide)).trans w6_1328), ((K7_L.w32 (by decide) (by decide)).trans w6_132c), ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans w2_1388))))), ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans w2_138c))))), ((K7_L.b8 (by decide) (by decide)).trans ((K6_L.b8 (by decide) (by decide)).trans ((K5_L.b8 (by decide) (by decide)).trans ((K4_L.b8 (by decide) (by decide)).trans ((K3_L.b8 (by decide) (by decide)).trans b2_1380))))), (((((((K1_L).trans K2_L).trans K3_L).trans K4_L).trans K5_L).trans K6_L).trans K7_L).mono (by decide)⟩

end C3.RV32.Sv
