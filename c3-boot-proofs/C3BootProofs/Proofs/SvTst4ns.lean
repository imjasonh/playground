import C3BootProofs.Proofs.SvGt

/-!
# `sigstore::verify`: the TSTInfo's nonce

From 0x2932 to 0x2952: the next field is an `INTEGER` nonce.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svTst4ns2932 : List BInstr :=
  [.aluImm .add a1 x0 0x2]
theorem svTst4ns2932_end : blockEnd sigstoreVerifyCode 0x2932 svTst4ns2932 = some 0x2934 := by
  simp only [svTst4ns2932]
  rw [blockEnd, sv_at_2932]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTst4ns2938 : List BInstr :=
  [.aluImm .add a0 sp 0x420, .lui a1 0x1000, .aluImm .add a1 a1 0x320, .alu .add a1 a1 sp]
theorem svTst4ns2938_end : blockEnd sigstoreVerifyCode 0x2938 svTst4ns2938 = some 0x2944 := by
  simp only [svTst4ns2938]
  rw [blockEnd, sv_at_2938]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_293c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_293e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_2942]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_tst4ns {B out bp x21 x26 dg dp rp rl x8 : Word} {sr ss : Bytes} {w24 w28 w2c w30 w34 w38 w3c w40 w44 w48 w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w78 w7c w80 w84 w88 w8c w90 w94 w98 w9c wa0 wa4 wa8 wac wb0 wb4 wb8 wbc wc0 wc4 wc8 wcc wd0 wd4 wd8 wdc we0 we4 we8 wec wf0 wf4 wf8 wfc w100 w104 w108 w10c w110 w114 w118 w11c w120 w124 w128 w12c w130 : Word} {v : Nat → Word} {n0 : Machine}
    (F : Fr B 0x3830) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x2932 (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_10 : reg n0 a0 = (M0 rp).zeroExtend 32)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_8 : reg n0 (8 : Fin 32) = x8)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_22 : reg n0 (22 : Fin 32) = dp)
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
    (w0_1328 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = rp)
    (w0_132c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = rl)
    (rd_in : SvIn B (rp) (rl).toNat)
    (D0 : SvData M0)
    (q0_1020 : ∀ j, j < 47 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1020 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0))
    (q0_104f : ∀ j, j < 48 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x104F + j)) = BitVec.ofNat 8 (ss.getD j 0))
    (hrl : rl ≠ 0)
    (hb2 : M0 rp = BitVec.ofNat 8 2) :
    (¬ (∃ ip4 il4, derIntOf (memBytes M0 (rp) (rl).toNat) (rp) (derElement 2 (memBytes M0 (rp) (rl).toNat)) = .ok (ip4, il4) ∧ ∃ ti4, derElement 2 (memBytes M0 (rp) (rl).toNat) = .ok ti4 ∧ True) ∧ SvErrRet B out v n0) ∨
    (∃ ip4 il4, derIntOf (memBytes M0 (rp) (rl).toNat) (rp) (derElement 2 (memBytes M0 (rp) (rl).toNat)) = .ok (ip4, il4) ∧
    ∃ ti4, derElement 2 (memBytes M0 (rp) (rl).toNat) = .ok ti4 ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x2952 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = x8 ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 ∧
        reg n' (21 : Fin 32) = x21 ∧
        reg n' (22 : Fin 32) = dp ∧
        reg n' (24 : Fin 32) = dg ∧
        reg n' (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 ∧
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
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = (rp) + BitVec.ofNat 32 (ti4.header + ti4.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = (rl) - BitVec.ofNat 32 (ti4.header + ti4.len) ∧
        (∀ j, j < 47 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1020 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0)) ∧
        (∀ j, j < 48 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x104F + j)) = BitVec.ofNat 8 (ss.getD j 0)) ∧
        SvKeepL B n0.mem n'.mem [(0x420, 0x8), (0x1328, 0x8)]) := by
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x2932
  obtain ⟨n1, c1, u1⟩ := s0.block svTst4ns2932 E0.self svTst4ns2932_end
    ⟨trivial, trivial⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have s1 : St n1.mem SV n1 0x2934 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have rb1 : ∀ q, reg n1 q = (runBlock svTst4ns2932 (n0.mem, reg n0)).2 q := fun q => by rw [u1.regs]
  have fr1 : ∀ x, SvR B x → n1.mem x = n0.mem x := fun x _ => by rw [m1]
  have t1 : Steps n0 n1 := t0.trans c1
  have fR1 : ∀ x, SvR B x → n1.mem x = M0 x := fun x hx => (fr1 x hx).trans (fR0 x hx)
  have E1 : SvCode n1.mem := E0.fr F fr1
  have V1 : SvSaves B n1.mem v := V0.same m1
  have g1_2 : reg n1 sp = B + 0x21A0 := by
    rw [rb1, runBlock_reg _ _ _ sp s0.zero (by decide), g0_2]
  have g1_3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb1, runBlock_reg _ _ _ (3 : Fin 32) s0.zero (by decide), g0_3]
  have g1_4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb1, runBlock_reg _ _ _ (4 : Fin 32) s0.zero (by decide), g0_4]
  have g1_8 : reg n1 (8 : Fin 32) = x8 := by
    rw [rb1, runBlock_reg _ _ _ (8 : Fin 32) s0.zero (by decide), g0_8]
  have g1_10 : reg n1 a0 = (M0 rp).zeroExtend 32 := by
    rw [rb1, runBlock_reg _ _ _ a0 s0.zero (by decide), g0_10]
  have g1_18 : reg n1 (18 : Fin 32) = out := by
    rw [rb1, runBlock_reg _ _ _ (18 : Fin 32) s0.zero (by decide), g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = bp := by
    rw [rb1, runBlock_reg _ _ _ (19 : Fin 32) s0.zero (by decide), g0_19]
  have g1_20 : reg n1 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
    rw [rb1, runBlock_reg _ _ _ (20 : Fin 32) s0.zero (by decide), g0_20]
  have g1_21 : reg n1 (21 : Fin 32) = x21 := by
    rw [rb1, runBlock_reg _ _ _ (21 : Fin 32) s0.zero (by decide), g0_21]
  have g1_22 : reg n1 (22 : Fin 32) = dp := by
    rw [rb1, runBlock_reg _ _ _ (22 : Fin 32) s0.zero (by decide), g0_22]
  have g1_24 : reg n1 (24 : Fin 32) = dg := by
    rw [rb1, runBlock_reg _ _ _ (24 : Fin 32) s0.zero (by decide), g0_24]
  have g1_25 : reg n1 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by
    rw [rb1, runBlock_reg _ _ _ (25 : Fin 32) s0.zero (by decide), g0_25]
  have g1_26 : reg n1 (26 : Fin 32) = x26 := by
    rw [rb1, runBlock_reg _ _ _ (26 : Fin 32) s0.zero (by decide), g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb1, runBlock_reg _ _ _ (27 : Fin 32) s0.zero (by decide), g0_27]
  have g1_11 : reg n1 a1 = BitVec.ofNat 32 0x2 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svTst4ns2932, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_8, g0_10, g0_18, g0_19, g0_20, g0_21, g0_22, g0_24, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk1 : SvKeepL B n0.mem n1.mem [] := by rw [m1]; exact (SvKeepL.refl : SvKeepL B n0.mem n0.mem [])
  have w1_24 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m1]; exact w0_24
  have w1_28 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m1]; exact w0_28
  have w1_2c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m1]; exact w0_2c
  have w1_30 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m1]; exact w0_30
  have w1_34 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m1]; exact w0_34
  have w1_38 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m1]; exact w0_38
  have w1_3c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m1]; exact w0_3c
  have w1_40 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m1]; exact w0_40
  have w1_44 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m1]; exact w0_44
  have w1_48 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m1]; exact w0_48
  have w1_4c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m1]; exact w0_4c
  have w1_50 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m1]; exact w0_50
  have w1_54 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m1]; exact w0_54
  have w1_58 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m1]; exact w0_58
  have w1_5c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m1]; exact w0_5c
  have w1_60 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m1]; exact w0_60
  have w1_64 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m1]; exact w0_64
  have w1_68 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m1]; exact w0_68
  have w1_6c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m1]; exact w0_6c
  have w1_70 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m1]; exact w0_70
  have w1_78 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m1]; exact w0_78
  have w1_7c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m1]; exact w0_7c
  have w1_80 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m1]; exact w0_80
  have w1_84 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m1]; exact w0_84
  have w1_88 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m1]; exact w0_88
  have w1_8c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m1]; exact w0_8c
  have w1_90 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m1]; exact w0_90
  have w1_94 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m1]; exact w0_94
  have w1_98 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m1]; exact w0_98
  have w1_9c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m1]; exact w0_9c
  have w1_a0 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m1]; exact w0_a0
  have w1_a4 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m1]; exact w0_a4
  have w1_a8 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m1]; exact w0_a8
  have w1_ac : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m1]; exact w0_ac
  have w1_b0 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m1]; exact w0_b0
  have w1_b4 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m1]; exact w0_b4
  have w1_b8 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m1]; exact w0_b8
  have w1_bc : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m1]; exact w0_bc
  have w1_c0 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m1]; exact w0_c0
  have w1_c4 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m1]; exact w0_c4
  have w1_c8 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m1]; exact w0_c8
  have w1_cc : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m1]; exact w0_cc
  have w1_d0 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m1]; exact w0_d0
  have w1_d4 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m1]; exact w0_d4
  have w1_d8 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m1]; exact w0_d8
  have w1_dc : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m1]; exact w0_dc
  have w1_e0 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m1]; exact w0_e0
  have w1_e4 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m1]; exact w0_e4
  have w1_e8 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m1]; exact w0_e8
  have w1_ec : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m1]; exact w0_ec
  have w1_f0 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m1]; exact w0_f0
  have w1_f4 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m1]; exact w0_f4
  have w1_f8 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m1]; exact w0_f8
  have w1_fc : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m1]; exact w0_fc
  have w1_100 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m1]; exact w0_100
  have w1_104 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m1]; exact w0_104
  have w1_108 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m1]; exact w0_108
  have w1_10c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m1]; exact w0_10c
  have w1_110 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m1]; exact w0_110
  have w1_114 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m1]; exact w0_114
  have w1_118 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m1]; exact w0_118
  have w1_11c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m1]; exact w0_11c
  have w1_120 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m1]; exact w0_120
  have w1_124 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m1]; exact w0_124
  have w1_128 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m1]; exact w0_128
  have w1_12c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m1]; exact w0_12c
  have w1_130 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m1]; exact w0_130
  have w1_1328 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = rp := by rw [m1]; exact w0_1328
  have w1_132c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = rl := by rw [m1]; exact w0_132c
  have q1_1020 : ∀ j, j < 47 → n1.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1020 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m1]; exact q0_1020 j hj
  have q1_104f : ∀ j, j < 48 → n1.mem (B + 0x21A0 + BitVec.ofNat 32 (0x104F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m1]; exact q0_104f j hj
  -- 0x2934: branch, not taken
  obtain ⟨n2, d2, u2⟩ := s1.notTaken E1.self 0x2938 sv_at_2934
    (by decide) (by rw [g1_10, g1_11]; exact br_bne_byte_f (by decide) hb2)
  have s2 : St n2.mem SV n2 0x2938 (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
  have m2 : n2.mem = n1.mem := u2.mem
  have fr2 : ∀ x, SvR B x → n2.mem x = n1.mem x := fun x _ => by rw [m2]
  have t2 : Steps n0 n2 := t1.trans (.single d2)
  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.same m2
  have g2_2 : reg n2 sp = B + 0x21A0 := by rw [u2.regs, g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u2.regs, g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u2.regs, g1_4]
  have g2_8 : reg n2 (8 : Fin 32) = x8 := by rw [u2.regs, g1_8]
  have g2_10 : reg n2 a0 = (M0 rp).zeroExtend 32 := by rw [u2.regs, g1_10]
  have g2_11 : reg n2 a1 = BitVec.ofNat 32 0x2 := by rw [u2.regs, g1_11]
  have g2_18 : reg n2 (18 : Fin 32) = out := by rw [u2.regs, g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [u2.regs, g1_19]
  have g2_20 : reg n2 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u2.regs, g1_20]
  have g2_21 : reg n2 (21 : Fin 32) = x21 := by rw [u2.regs, g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = dp := by rw [u2.regs, g1_22]
  have g2_24 : reg n2 (24 : Fin 32) = dg := by rw [u2.regs, g1_24]
  have g2_25 : reg n2 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [u2.regs, g1_25]
  have g2_26 : reg n2 (26 : Fin 32) = x26 := by rw [u2.regs, g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u2.regs, g1_27]
  have keep_kk2 : SvKeepL B n0.mem n2.mem [] := by rw [m2]; exact keep_kk1
  clear keep_kk1
  have w2_24 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m2]; exact w1_24
  have w2_28 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m2]; exact w1_28
  have w2_2c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m2]; exact w1_2c
  have w2_30 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m2]; exact w1_30
  have w2_34 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m2]; exact w1_34
  have w2_38 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m2]; exact w1_38
  have w2_3c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m2]; exact w1_3c
  have w2_40 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m2]; exact w1_40
  have w2_44 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m2]; exact w1_44
  have w2_48 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m2]; exact w1_48
  have w2_4c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m2]; exact w1_4c
  have w2_50 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m2]; exact w1_50
  have w2_54 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m2]; exact w1_54
  have w2_58 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m2]; exact w1_58
  have w2_5c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m2]; exact w1_5c
  have w2_60 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m2]; exact w1_60
  have w2_64 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m2]; exact w1_64
  have w2_68 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m2]; exact w1_68
  have w2_6c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m2]; exact w1_6c
  have w2_70 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m2]; exact w1_70
  have w2_78 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m2]; exact w1_78
  have w2_7c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m2]; exact w1_7c
  have w2_80 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m2]; exact w1_80
  have w2_84 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m2]; exact w1_84
  have w2_88 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m2]; exact w1_88
  have w2_8c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m2]; exact w1_8c
  have w2_90 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m2]; exact w1_90
  have w2_94 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m2]; exact w1_94
  have w2_98 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m2]; exact w1_98
  have w2_9c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m2]; exact w1_9c
  have w2_a0 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m2]; exact w1_a0
  have w2_a4 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m2]; exact w1_a4
  have w2_a8 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m2]; exact w1_a8
  have w2_ac : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m2]; exact w1_ac
  have w2_b0 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m2]; exact w1_b0
  have w2_b4 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m2]; exact w1_b4
  have w2_b8 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m2]; exact w1_b8
  have w2_bc : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m2]; exact w1_bc
  have w2_c0 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m2]; exact w1_c0
  have w2_c4 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m2]; exact w1_c4
  have w2_c8 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m2]; exact w1_c8
  have w2_cc : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m2]; exact w1_cc
  have w2_d0 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m2]; exact w1_d0
  have w2_d4 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m2]; exact w1_d4
  have w2_d8 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m2]; exact w1_d8
  have w2_dc : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m2]; exact w1_dc
  have w2_e0 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m2]; exact w1_e0
  have w2_e4 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m2]; exact w1_e4
  have w2_e8 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m2]; exact w1_e8
  have w2_ec : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m2]; exact w1_ec
  have w2_f0 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m2]; exact w1_f0
  have w2_f4 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m2]; exact w1_f4
  have w2_f8 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m2]; exact w1_f8
  have w2_fc : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m2]; exact w1_fc
  have w2_100 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m2]; exact w1_100
  have w2_104 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m2]; exact w1_104
  have w2_108 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m2]; exact w1_108
  have w2_10c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m2]; exact w1_10c
  have w2_110 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m2]; exact w1_110
  have w2_114 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m2]; exact w1_114
  have w2_118 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m2]; exact w1_118
  have w2_11c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m2]; exact w1_11c
  have w2_120 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m2]; exact w1_120
  have w2_124 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m2]; exact w1_124
  have w2_128 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m2]; exact w1_128
  have w2_12c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m2]; exact w1_12c
  have w2_130 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m2]; exact w1_130
  have w2_1328 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = rp := by rw [m2]; exact w1_1328
  have w2_132c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = rl := by rw [m2]; exact w1_132c
  have q2_1020 : ∀ j, j < 47 → n2.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1020 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m2]; exact q1_1020 j hj
  have q2_104f : ∀ j, j < 48 → n2.mem (B + 0x21A0 + BitVec.ofNat 32 (0x104F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m2]; exact q1_104f j hj
  clear q1_104f q1_1020 w1_132c w1_1328 w1_130 w1_12c w1_128 w1_124 w1_120 w1_11c w1_118 w1_114 w1_110 w1_10c w1_108 w1_104 w1_100 w1_fc w1_f8 w1_f4 w1_f0 w1_ec w1_e8 w1_e4 w1_e0 w1_dc w1_d8 w1_d4 w1_d0 w1_cc w1_c8 w1_c4 w1_c0 w1_bc w1_b8 w1_b4 w1_b0 w1_ac w1_a8 w1_a4 w1_a0 w1_9c w1_98 w1_94 w1_90 w1_8c w1_88 w1_84 w1_80 w1_7c w1_78 w1_70 w1_6c w1_68 w1_64 w1_60 w1_5c w1_58 w1_54 w1_50 w1_4c w1_48 w1_44 w1_40 w1_3c w1_38 w1_34 w1_30 w1_2c w1_28 w1_24 g1_11 g1_27 g1_26 g1_25 g1_24 g1_22 g1_21 g1_20 g1_19 g1_18 g1_10 g1_8 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
  -- 0x2938
  obtain ⟨n3, c3, u3⟩ := s2.block svTst4ns2938 E2.self svTst4ns2938_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have s3 : St n3.mem SV n3 0x2944 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have rb3 : ∀ q, reg n3 q = (runBlock svTst4ns2938 (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
  have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
  have t3 : Steps n0 n3 := t2.trans c3
  have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : SvCode n3.mem := E2.fr F fr3
  have V3 : SvSaves B n3.mem v := V2.same m3
  have g3_2 : reg n3 sp = B + 0x21A0 := by
    rw [rb3, runBlock_reg _ _ _ sp s2.zero (by decide), g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb3, runBlock_reg _ _ _ (3 : Fin 32) s2.zero (by decide), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb3, runBlock_reg _ _ _ (4 : Fin 32) s2.zero (by decide), g2_4]
  have g3_8 : reg n3 (8 : Fin 32) = x8 := by
    rw [rb3, runBlock_reg _ _ _ (8 : Fin 32) s2.zero (by decide), g2_8]
  have g3_18 : reg n3 (18 : Fin 32) = out := by
    rw [rb3, runBlock_reg _ _ _ (18 : Fin 32) s2.zero (by decide), g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = bp := by
    rw [rb3, runBlock_reg _ _ _ (19 : Fin 32) s2.zero (by decide), g2_19]
  have g3_20 : reg n3 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
    rw [rb3, runBlock_reg _ _ _ (20 : Fin 32) s2.zero (by decide), g2_20]
  have g3_21 : reg n3 (21 : Fin 32) = x21 := by
    rw [rb3, runBlock_reg _ _ _ (21 : Fin 32) s2.zero (by decide), g2_21]
  have g3_22 : reg n3 (22 : Fin 32) = dp := by
    rw [rb3, runBlock_reg _ _ _ (22 : Fin 32) s2.zero (by decide), g2_22]
  have g3_24 : reg n3 (24 : Fin 32) = dg := by
    rw [rb3, runBlock_reg _ _ _ (24 : Fin 32) s2.zero (by decide), g2_24]
  have g3_25 : reg n3 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by
    rw [rb3, runBlock_reg _ _ _ (25 : Fin 32) s2.zero (by decide), g2_25]
  have g3_26 : reg n3 (26 : Fin 32) = x26 := by
    rw [rb3, runBlock_reg _ _ _ (26 : Fin 32) s2.zero (by decide), g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb3, runBlock_reg _ _ _ (27 : Fin 32) s2.zero (by decide), g2_27]
  have g3_10 : reg n3 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb3]; simp +decide only [runBlock, BInstr.run, svTst4ns2938, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g2_2, g2_3, g2_4, g2_8, g2_10, g2_11, g2_18, g2_19, g2_20, g2_21, g2_22, g2_24, g2_25, g2_26, g2_27, s2.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g3_11 : reg n3 a1 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
    rw [rb3]; simp +decide only [runBlock, BInstr.run, svTst4ns2938, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g2_2, g2_3, g2_4, g2_8, g2_10, g2_11, g2_18, g2_19, g2_20, g2_21, g2_22, g2_24, g2_25, g2_26, g2_27, s2.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk3 : SvKeepL B n0.mem n3.mem [] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have w3_24 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m3]; exact w2_24
  have w3_28 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m3]; exact w2_28
  have w3_2c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m3]; exact w2_2c
  have w3_30 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m3]; exact w2_30
  have w3_34 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m3]; exact w2_34
  have w3_38 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m3]; exact w2_38
  have w3_3c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m3]; exact w2_3c
  have w3_40 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m3]; exact w2_40
  have w3_44 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m3]; exact w2_44
  have w3_48 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m3]; exact w2_48
  have w3_4c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m3]; exact w2_4c
  have w3_50 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m3]; exact w2_50
  have w3_54 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m3]; exact w2_54
  have w3_58 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m3]; exact w2_58
  have w3_5c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m3]; exact w2_5c
  have w3_60 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m3]; exact w2_60
  have w3_64 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m3]; exact w2_64
  have w3_68 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m3]; exact w2_68
  have w3_6c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m3]; exact w2_6c
  have w3_70 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m3]; exact w2_70
  have w3_78 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m3]; exact w2_78
  have w3_7c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m3]; exact w2_7c
  have w3_80 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m3]; exact w2_80
  have w3_84 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m3]; exact w2_84
  have w3_88 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m3]; exact w2_88
  have w3_8c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m3]; exact w2_8c
  have w3_90 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m3]; exact w2_90
  have w3_94 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m3]; exact w2_94
  have w3_98 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m3]; exact w2_98
  have w3_9c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m3]; exact w2_9c
  have w3_a0 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m3]; exact w2_a0
  have w3_a4 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m3]; exact w2_a4
  have w3_a8 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m3]; exact w2_a8
  have w3_ac : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m3]; exact w2_ac
  have w3_b0 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m3]; exact w2_b0
  have w3_b4 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m3]; exact w2_b4
  have w3_b8 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m3]; exact w2_b8
  have w3_bc : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m3]; exact w2_bc
  have w3_c0 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m3]; exact w2_c0
  have w3_c4 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m3]; exact w2_c4
  have w3_c8 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m3]; exact w2_c8
  have w3_cc : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m3]; exact w2_cc
  have w3_d0 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m3]; exact w2_d0
  have w3_d4 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m3]; exact w2_d4
  have w3_d8 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m3]; exact w2_d8
  have w3_dc : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m3]; exact w2_dc
  have w3_e0 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m3]; exact w2_e0
  have w3_e4 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m3]; exact w2_e4
  have w3_e8 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m3]; exact w2_e8
  have w3_ec : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m3]; exact w2_ec
  have w3_f0 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m3]; exact w2_f0
  have w3_f4 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m3]; exact w2_f4
  have w3_f8 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m3]; exact w2_f8
  have w3_fc : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m3]; exact w2_fc
  have w3_100 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m3]; exact w2_100
  have w3_104 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m3]; exact w2_104
  have w3_108 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m3]; exact w2_108
  have w3_10c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m3]; exact w2_10c
  have w3_110 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m3]; exact w2_110
  have w3_114 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m3]; exact w2_114
  have w3_118 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m3]; exact w2_118
  have w3_11c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m3]; exact w2_11c
  have w3_120 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m3]; exact w2_120
  have w3_124 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m3]; exact w2_124
  have w3_128 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m3]; exact w2_128
  have w3_12c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m3]; exact w2_12c
  have w3_130 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m3]; exact w2_130
  have w3_1328 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = rp := by rw [m3]; exact w2_1328
  have w3_132c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = rl := by rw [m3]; exact w2_132c
  have q3_1020 : ∀ j, j < 47 → n3.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1020 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m3]; exact q2_1020 j hj
  have q3_104f : ∀ j, j < 48 → n3.mem (B + 0x21A0 + BitVec.ofNat 32 (0x104F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m3]; exact q2_104f j hj
  clear q2_104f q2_1020 w2_132c w2_1328 w2_130 w2_12c w2_128 w2_124 w2_120 w2_11c w2_118 w2_114 w2_110 w2_10c w2_108 w2_104 w2_100 w2_fc w2_f8 w2_f4 w2_f0 w2_ec w2_e8 w2_e4 w2_e0 w2_dc w2_d8 w2_d4 w2_d0 w2_cc w2_c8 w2_c4 w2_c0 w2_bc w2_b8 w2_b4 w2_b0 w2_ac w2_a8 w2_a4 w2_a0 w2_9c w2_98 w2_94 w2_90 w2_8c w2_88 w2_84 w2_80 w2_7c w2_78 w2_70 w2_6c w2_68 w2_64 w2_60 w2_5c w2_58 w2_54 w2_50 w2_4c w2_48 w2_44 w2_40 w2_3c w2_38 w2_34 w2_30 w2_2c w2_28 w2_24 g2_27 g2_26 g2_25 g2_24 g2_22 g2_21 g2_20 g2_19 g2_18 g2_11 g2_10 g2_8 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 m2 s2 u2 d2
  -- 0x2944: sv_intF
  obtain ⟨n4, c4, s4, sp4, rk4, K4, A4, Ok4, Er4, fr4⟩ := sv_intF (oc := 0x420) (dc := 0x1320)
    F E3 s3 sv_at_2944 sv_at_2948 (by decide) (by decide) g3_2 g3_10 g3_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w3_1328 w3_132c rd_in
  have t4 : Steps n0 n4 := t3.trans c4
  have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : SvCode n4.mem := E3.fr F fr4
  have V4 : SvSaves B n4.mem v := V3.keepL K4 (by decide)
  rw [sv_mb fR3 rd_in] at A4 Ok4 Er4
  have g4_2 : reg n4 sp = B + 0x21A0 := by rw [rk4 sp (by decide) (by decide), g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk4 (3 : Fin 32) (by decide) (by decide), g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk4 (4 : Fin 32) (by decide) (by decide), g3_4]
  have g4_8 : reg n4 (8 : Fin 32) = x8 := by rw [rk4 (8 : Fin 32) (by decide) (by decide), g3_8]
  have g4_18 : reg n4 (18 : Fin 32) = out := by rw [rk4 (18 : Fin 32) (by decide) (by decide), g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [rk4 (19 : Fin 32) (by decide) (by decide), g3_19]
  have g4_20 : reg n4 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rk4 (20 : Fin 32) (by decide) (by decide), g3_20]
  have g4_21 : reg n4 (21 : Fin 32) = x21 := by rw [rk4 (21 : Fin 32) (by decide) (by decide), g3_21]
  have g4_22 : reg n4 (22 : Fin 32) = dp := by rw [rk4 (22 : Fin 32) (by decide) (by decide), g3_22]
  have g4_24 : reg n4 (24 : Fin 32) = dg := by rw [rk4 (24 : Fin 32) (by decide) (by decide), g3_24]
  have g4_25 : reg n4 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [rk4 (25 : Fin 32) (by decide) (by decide), g3_25]
  have g4_26 : reg n4 (26 : Fin 32) = x26 := by rw [rk4 (26 : Fin 32) (by decide) (by decide), g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk4 (27 : Fin 32) (by decide) (by decide), g3_27]
  obtain ⟨r4, hr4⟩ : ∃ r, derIntOf (memBytes M0 (rp) (rl).toNat) (rp) (derElement 2 (memBytes M0 (rp) (rl).toNat)) = r := ⟨_, rfl⟩
  rcases r4 with ei4 | ⟨ip4, il4⟩
  · obtain ⟨z4, -⟩ := Er4 ei4 hr4
    have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x420, 0x8), (0x1328, 0x8)] := keep_kk3.trans K4
    clear keep_kk3
    have w4_24 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K4.w32 (by decide) (by decide)).trans w3_24
    have w4_28 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K4.w32 (by decide) (by decide)).trans w3_28
    have w4_2c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K4.w32 (by decide) (by decide)).trans w3_2c
    have w4_30 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K4.w32 (by decide) (by decide)).trans w3_30
    have w4_34 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K4.w32 (by decide) (by decide)).trans w3_34
    have w4_38 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K4.w32 (by decide) (by decide)).trans w3_38
    have w4_3c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K4.w32 (by decide) (by decide)).trans w3_3c
    have w4_40 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K4.w32 (by decide) (by decide)).trans w3_40
    have w4_44 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K4.w32 (by decide) (by decide)).trans w3_44
    have w4_48 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K4.w32 (by decide) (by decide)).trans w3_48
    have w4_4c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K4.w32 (by decide) (by decide)).trans w3_4c
    have w4_50 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K4.w32 (by decide) (by decide)).trans w3_50
    have w4_54 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K4.w32 (by decide) (by decide)).trans w3_54
    have w4_58 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K4.w32 (by decide) (by decide)).trans w3_58
    have w4_5c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K4.w32 (by decide) (by decide)).trans w3_5c
    have w4_60 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K4.w32 (by decide) (by decide)).trans w3_60
    have w4_64 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K4.w32 (by decide) (by decide)).trans w3_64
    have w4_68 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K4.w32 (by decide) (by decide)).trans w3_68
    have w4_6c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K4.w32 (by decide) (by decide)).trans w3_6c
    have w4_70 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K4.w32 (by decide) (by decide)).trans w3_70
    have w4_78 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K4.w32 (by decide) (by decide)).trans w3_78
    have w4_7c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K4.w32 (by decide) (by decide)).trans w3_7c
    have w4_80 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K4.w32 (by decide) (by decide)).trans w3_80
    have w4_84 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K4.w32 (by decide) (by decide)).trans w3_84
    have w4_88 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K4.w32 (by decide) (by decide)).trans w3_88
    have w4_8c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K4.w32 (by decide) (by decide)).trans w3_8c
    have w4_90 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K4.w32 (by decide) (by decide)).trans w3_90
    have w4_94 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K4.w32 (by decide) (by decide)).trans w3_94
    have w4_98 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K4.w32 (by decide) (by decide)).trans w3_98
    have w4_9c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K4.w32 (by decide) (by decide)).trans w3_9c
    have w4_a0 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K4.w32 (by decide) (by decide)).trans w3_a0
    have w4_a4 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K4.w32 (by decide) (by decide)).trans w3_a4
    have w4_a8 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K4.w32 (by decide) (by decide)).trans w3_a8
    have w4_ac : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K4.w32 (by decide) (by decide)).trans w3_ac
    have w4_b0 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K4.w32 (by decide) (by decide)).trans w3_b0
    have w4_b4 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K4.w32 (by decide) (by decide)).trans w3_b4
    have w4_b8 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K4.w32 (by decide) (by decide)).trans w3_b8
    have w4_bc : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K4.w32 (by decide) (by decide)).trans w3_bc
    have w4_c0 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K4.w32 (by decide) (by decide)).trans w3_c0
    have w4_c4 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K4.w32 (by decide) (by decide)).trans w3_c4
    have w4_c8 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K4.w32 (by decide) (by decide)).trans w3_c8
    have w4_cc : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K4.w32 (by decide) (by decide)).trans w3_cc
    have w4_d0 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K4.w32 (by decide) (by decide)).trans w3_d0
    have w4_d4 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K4.w32 (by decide) (by decide)).trans w3_d4
    have w4_d8 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K4.w32 (by decide) (by decide)).trans w3_d8
    have w4_dc : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K4.w32 (by decide) (by decide)).trans w3_dc
    have w4_e0 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K4.w32 (by decide) (by decide)).trans w3_e0
    have w4_e4 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K4.w32 (by decide) (by decide)).trans w3_e4
    have w4_e8 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K4.w32 (by decide) (by decide)).trans w3_e8
    have w4_ec : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K4.w32 (by decide) (by decide)).trans w3_ec
    have w4_f0 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K4.w32 (by decide) (by decide)).trans w3_f0
    have w4_f4 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K4.w32 (by decide) (by decide)).trans w3_f4
    have w4_f8 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K4.w32 (by decide) (by decide)).trans w3_f8
    have w4_fc : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K4.w32 (by decide) (by decide)).trans w3_fc
    have w4_100 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K4.w32 (by decide) (by decide)).trans w3_100
    have w4_104 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K4.w32 (by decide) (by decide)).trans w3_104
    have w4_108 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K4.w32 (by decide) (by decide)).trans w3_108
    have w4_10c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K4.w32 (by decide) (by decide)).trans w3_10c
    have w4_110 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K4.w32 (by decide) (by decide)).trans w3_110
    have w4_114 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K4.w32 (by decide) (by decide)).trans w3_114
    have w4_118 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K4.w32 (by decide) (by decide)).trans w3_118
    have w4_11c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K4.w32 (by decide) (by decide)).trans w3_11c
    have w4_120 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K4.w32 (by decide) (by decide)).trans w3_120
    have w4_124 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K4.w32 (by decide) (by decide)).trans w3_124
    have w4_128 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K4.w32 (by decide) (by decide)).trans w3_128
    have w4_12c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K4.w32 (by decide) (by decide)).trans w3_12c
    have w4_130 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K4.w32 (by decide) (by decide)).trans w3_130
    have q4_1020 : ∀ j, j < 47 → n4.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1020 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K4.range (by decide) (by decide) j hj).trans (q3_1020 j hj)
    have q4_104f : ∀ j, j < 48 → n4.mem (B + 0x21A0 + BitVec.ofNat 32 (0x104F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K4.range (by decide) (by decide) j hj).trans (q3_104f j hj)
    have w4_420 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := z4
    clear q3_104f q3_1020 w3_132c w3_1328 w3_130 w3_12c w3_128 w3_124 w3_120 w3_11c w3_118 w3_114 w3_110 w3_10c w3_108 w3_104 w3_100 w3_fc w3_f8 w3_f4 w3_f0 w3_ec w3_e8 w3_e4 w3_e0 w3_dc w3_d8 w3_d4 w3_d0 w3_cc w3_c8 w3_c4 w3_c0 w3_bc w3_b8 w3_b4 w3_b0 w3_ac w3_a8 w3_a4 w3_a0 w3_9c w3_98 w3_94 w3_90 w3_8c w3_88 w3_84 w3_80 w3_7c w3_78 w3_70 w3_6c w3_68 w3_64 w3_60 w3_5c w3_58 w3_54 w3_50 w3_4c w3_48 w3_44 w3_40 w3_3c w3_38 w3_34 w3_30 w3_2c w3_28 w3_24 g3_11 g3_10 g3_27 g3_26 g3_25 g3_24 g3_22 g3_21 g3_20 g3_19 g3_18 g3_8 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 rb3 s3 m3 u3 c3
    -- 0x294C: lw
    obtain ⟨n5, d5, u5⟩ := s4.lw E4.self sv_at_294c (off' := 0x2950) (by decide)
      (by rw [g4_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s5 : St n5.mem SV n5 0x2950 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
    have m5 : n5.mem = n4.mem := u5.mem
    have fr5 : ∀ x, SvR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
    have t5 : Steps n0 n5 := t4.trans (.single d5)
    have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
    have E5 : SvCode n5.mem := E4.fr F fr5
    have V5 : SvSaves B n5.mem v := V4.same m5
    have g5_2 : reg n5 sp = B + 0x21A0 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_2]
    have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u5.regs, upd_ne (by decide) (by decide), g4_3]
    have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u5.regs, upd_ne (by decide) (by decide), g4_4]
    have g5_8 : reg n5 (8 : Fin 32) = x8 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_8]
    have g5_18 : reg n5 (18 : Fin 32) = out := by rw [u5.regs, upd_ne (by decide) (by decide), g4_18]
    have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_19]
    have g5_20 : reg n5 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_20]
    have g5_21 : reg n5 (21 : Fin 32) = x21 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_21]
    have g5_22 : reg n5 (22 : Fin 32) = dp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_22]
    have g5_24 : reg n5 (24 : Fin 32) = dg := by rw [u5.regs, upd_ne (by decide) (by decide), g4_24]
    have g5_25 : reg n5 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_25]
    have g5_26 : reg n5 (26 : Fin 32) = x26 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_26]
    have g5_27 : reg n5 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_27]
    have g5_10 : reg n5 a0 = 0 := by
      rw [u5.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g4_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w4_420]
    have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x420, 0x8), (0x1328, 0x8)] := by rw [m5]; exact keep_kk4
    clear keep_kk4
    have w5_24 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m5]; exact w4_24
    have w5_28 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m5]; exact w4_28
    have w5_2c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m5]; exact w4_2c
    have w5_30 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m5]; exact w4_30
    have w5_34 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m5]; exact w4_34
    have w5_38 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m5]; exact w4_38
    have w5_3c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m5]; exact w4_3c
    have w5_40 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m5]; exact w4_40
    have w5_44 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m5]; exact w4_44
    have w5_48 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m5]; exact w4_48
    have w5_4c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m5]; exact w4_4c
    have w5_50 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m5]; exact w4_50
    have w5_54 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m5]; exact w4_54
    have w5_58 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m5]; exact w4_58
    have w5_5c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m5]; exact w4_5c
    have w5_60 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m5]; exact w4_60
    have w5_64 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m5]; exact w4_64
    have w5_68 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m5]; exact w4_68
    have w5_6c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m5]; exact w4_6c
    have w5_70 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m5]; exact w4_70
    have w5_78 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m5]; exact w4_78
    have w5_7c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m5]; exact w4_7c
    have w5_80 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m5]; exact w4_80
    have w5_84 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m5]; exact w4_84
    have w5_88 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m5]; exact w4_88
    have w5_8c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m5]; exact w4_8c
    have w5_90 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m5]; exact w4_90
    have w5_94 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m5]; exact w4_94
    have w5_98 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m5]; exact w4_98
    have w5_9c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m5]; exact w4_9c
    have w5_a0 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m5]; exact w4_a0
    have w5_a4 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m5]; exact w4_a4
    have w5_a8 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m5]; exact w4_a8
    have w5_ac : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m5]; exact w4_ac
    have w5_b0 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m5]; exact w4_b0
    have w5_b4 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m5]; exact w4_b4
    have w5_b8 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m5]; exact w4_b8
    have w5_bc : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m5]; exact w4_bc
    have w5_c0 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m5]; exact w4_c0
    have w5_c4 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m5]; exact w4_c4
    have w5_c8 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m5]; exact w4_c8
    have w5_cc : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m5]; exact w4_cc
    have w5_d0 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m5]; exact w4_d0
    have w5_d4 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m5]; exact w4_d4
    have w5_d8 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m5]; exact w4_d8
    have w5_dc : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m5]; exact w4_dc
    have w5_e0 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m5]; exact w4_e0
    have w5_e4 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m5]; exact w4_e4
    have w5_e8 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m5]; exact w4_e8
    have w5_ec : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m5]; exact w4_ec
    have w5_f0 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m5]; exact w4_f0
    have w5_f4 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m5]; exact w4_f4
    have w5_f8 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m5]; exact w4_f8
    have w5_fc : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m5]; exact w4_fc
    have w5_100 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m5]; exact w4_100
    have w5_104 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m5]; exact w4_104
    have w5_108 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m5]; exact w4_108
    have w5_10c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m5]; exact w4_10c
    have w5_110 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m5]; exact w4_110
    have w5_114 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m5]; exact w4_114
    have w5_118 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m5]; exact w4_118
    have w5_11c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m5]; exact w4_11c
    have w5_120 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m5]; exact w4_120
    have w5_124 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m5]; exact w4_124
    have w5_128 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m5]; exact w4_128
    have w5_12c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m5]; exact w4_12c
    have w5_130 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m5]; exact w4_130
    have w5_420 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m5]; exact w4_420
    have q5_1020 : ∀ j, j < 47 → n5.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1020 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m5]; exact q4_1020 j hj
    have q5_104f : ∀ j, j < 48 → n5.mem (B + 0x21A0 + BitVec.ofNat 32 (0x104F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m5]; exact q4_104f j hj
    clear w4_420 q4_104f q4_1020 w4_130 w4_12c w4_128 w4_124 w4_120 w4_11c w4_118 w4_114 w4_110 w4_10c w4_108 w4_104 w4_100 w4_fc w4_f8 w4_f4 w4_f0 w4_ec w4_e8 w4_e4 w4_e0 w4_dc w4_d8 w4_d4 w4_d0 w4_cc w4_c8 w4_c4 w4_c0 w4_bc w4_b8 w4_b4 w4_b0 w4_ac w4_a8 w4_a4 w4_a0 w4_9c w4_98 w4_94 w4_90 w4_8c w4_88 w4_84 w4_80 w4_7c w4_78 w4_70 w4_6c w4_68 w4_64 w4_60 w4_5c w4_58 w4_54 w4_50 w4_4c w4_48 w4_44 w4_40 w4_3c w4_38 w4_34 w4_30 w4_2c w4_28 w4_24 z4
    -- 0x2950: branch, taken
    obtain ⟨n6, d6, u6⟩ := s5.taken E5.self 0x2994 sv_at_2950
      (by decide) (by rw [g5_10, s5.zero]; rfl)
    have s6 : St n6.mem SV n6 0x2994 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
    have m6 : n6.mem = n5.mem := u6.mem
    have fr6 : ∀ x, SvR B x → n6.mem x = n5.mem x := fun x _ => by rw [m6]
    have t6 : Steps n0 n6 := t5.trans (.single d6)
    have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
    have E6 : SvCode n6.mem := E5.fr F fr6
    have V6 : SvSaves B n6.mem v := V5.same m6
    have g6_2 : reg n6 sp = B + 0x21A0 := by rw [u6.regs, g5_2]
    have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u6.regs, g5_3]
    have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u6.regs, g5_4]
    have g6_8 : reg n6 (8 : Fin 32) = x8 := by rw [u6.regs, g5_8]
    have g6_10 : reg n6 a0 = 0 := by rw [u6.regs, g5_10]
    have g6_18 : reg n6 (18 : Fin 32) = out := by rw [u6.regs, g5_18]
    have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [u6.regs, g5_19]
    have g6_20 : reg n6 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u6.regs, g5_20]
    have g6_21 : reg n6 (21 : Fin 32) = x21 := by rw [u6.regs, g5_21]
    have g6_22 : reg n6 (22 : Fin 32) = dp := by rw [u6.regs, g5_22]
    have g6_24 : reg n6 (24 : Fin 32) = dg := by rw [u6.regs, g5_24]
    have g6_25 : reg n6 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [u6.regs, g5_25]
    have g6_26 : reg n6 (26 : Fin 32) = x26 := by rw [u6.regs, g5_26]
    have g6_27 : reg n6 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u6.regs, g5_27]
    have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x420, 0x8), (0x1328, 0x8)] := by rw [m6]; exact keep_kk5
    clear keep_kk5
    have w6_24 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m6]; exact w5_24
    have w6_28 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m6]; exact w5_28
    have w6_2c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m6]; exact w5_2c
    have w6_30 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m6]; exact w5_30
    have w6_34 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m6]; exact w5_34
    have w6_38 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m6]; exact w5_38
    have w6_3c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m6]; exact w5_3c
    have w6_40 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m6]; exact w5_40
    have w6_44 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m6]; exact w5_44
    have w6_48 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m6]; exact w5_48
    have w6_4c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m6]; exact w5_4c
    have w6_50 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m6]; exact w5_50
    have w6_54 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m6]; exact w5_54
    have w6_58 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m6]; exact w5_58
    have w6_5c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m6]; exact w5_5c
    have w6_60 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m6]; exact w5_60
    have w6_64 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m6]; exact w5_64
    have w6_68 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m6]; exact w5_68
    have w6_6c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m6]; exact w5_6c
    have w6_70 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m6]; exact w5_70
    have w6_78 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m6]; exact w5_78
    have w6_7c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m6]; exact w5_7c
    have w6_80 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m6]; exact w5_80
    have w6_84 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m6]; exact w5_84
    have w6_88 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m6]; exact w5_88
    have w6_8c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m6]; exact w5_8c
    have w6_90 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m6]; exact w5_90
    have w6_94 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m6]; exact w5_94
    have w6_98 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m6]; exact w5_98
    have w6_9c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m6]; exact w5_9c
    have w6_a0 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m6]; exact w5_a0
    have w6_a4 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m6]; exact w5_a4
    have w6_a8 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m6]; exact w5_a8
    have w6_ac : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m6]; exact w5_ac
    have w6_b0 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m6]; exact w5_b0
    have w6_b4 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m6]; exact w5_b4
    have w6_b8 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m6]; exact w5_b8
    have w6_bc : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m6]; exact w5_bc
    have w6_c0 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m6]; exact w5_c0
    have w6_c4 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m6]; exact w5_c4
    have w6_c8 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m6]; exact w5_c8
    have w6_cc : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m6]; exact w5_cc
    have w6_d0 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m6]; exact w5_d0
    have w6_d4 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m6]; exact w5_d4
    have w6_d8 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m6]; exact w5_d8
    have w6_dc : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m6]; exact w5_dc
    have w6_e0 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m6]; exact w5_e0
    have w6_e4 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m6]; exact w5_e4
    have w6_e8 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m6]; exact w5_e8
    have w6_ec : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m6]; exact w5_ec
    have w6_f0 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m6]; exact w5_f0
    have w6_f4 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m6]; exact w5_f4
    have w6_f8 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m6]; exact w5_f8
    have w6_fc : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m6]; exact w5_fc
    have w6_100 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m6]; exact w5_100
    have w6_104 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m6]; exact w5_104
    have w6_108 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m6]; exact w5_108
    have w6_10c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m6]; exact w5_10c
    have w6_110 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m6]; exact w5_110
    have w6_114 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m6]; exact w5_114
    have w6_118 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m6]; exact w5_118
    have w6_11c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m6]; exact w5_11c
    have w6_120 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m6]; exact w5_120
    have w6_124 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m6]; exact w5_124
    have w6_128 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m6]; exact w5_128
    have w6_12c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m6]; exact w5_12c
    have w6_130 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m6]; exact w5_130
    have w6_420 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m6]; exact w5_420
    have q6_1020 : ∀ j, j < 47 → n6.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1020 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m6]; exact q5_1020 j hj
    have q6_104f : ∀ j, j < 48 → n6.mem (B + 0x21A0 + BitVec.ofNat 32 (0x104F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m6]; exact q5_104f j hj
    clear q5_104f q5_1020 w5_420 w5_130 w5_12c w5_128 w5_124 w5_120 w5_11c w5_118 w5_114 w5_110 w5_10c w5_108 w5_104 w5_100 w5_fc w5_f8 w5_f4 w5_f0 w5_ec w5_e8 w5_e4 w5_e0 w5_dc w5_d8 w5_d4 w5_d0 w5_cc w5_c8 w5_c4 w5_c0 w5_bc w5_b8 w5_b4 w5_b0 w5_ac w5_a8 w5_a4 w5_a0 w5_9c w5_98 w5_94 w5_90 w5_8c w5_88 w5_84 w5_80 w5_7c w5_78 w5_70 w5_6c w5_68 w5_64 w5_60 w5_5c w5_58 w5_54 w5_50 w5_4c w5_48 w5_44 w5_40 w5_3c w5_38 w5_34 w5_30 w5_2c w5_28 w5_24 g5_10 g5_27 g5_26 g5_25 g5_24 g5_22 g5_21 g5_20 g5_19 g5_18 g5_8 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5
    -- 0x2994: lbu
    obtain ⟨n7, d7, u7⟩ := s6.lbu E6.self sv_at_2994 (off' := 0x2998) (by decide)
    have s7 : St n7.mem SV n7 0x2998 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
    have m7 : n7.mem = n6.mem := u7.mem
    have fr7 : ∀ x, SvR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
    have t7 : Steps n0 n7 := t6.trans (.single d7)
    have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
    have E7 : SvCode n7.mem := E6.fr F fr7
    have V7 : SvSaves B n7.mem v := V6.same m7
    have g7_2 : reg n7 sp = B + 0x21A0 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_2]
    have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_3]
    have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_4]
    have g7_10 : reg n7 a0 = 0 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_10]
    have g7_18 : reg n7 (18 : Fin 32) = out := by rw [u7.regs, upd_ne (by decide) (by decide), g6_18]
    have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [u7.regs, upd_ne (by decide) (by decide), g6_19]
    have g7_20 : reg n7 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_20]
    have g7_21 : reg n7 (21 : Fin 32) = x21 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_21]
    have g7_22 : reg n7 (22 : Fin 32) = dp := by rw [u7.regs, upd_ne (by decide) (by decide), g6_22]
    have g7_24 : reg n7 (24 : Fin 32) = dg := by rw [u7.regs, upd_ne (by decide) (by decide), g6_24]
    have g7_25 : reg n7 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_25]
    have g7_26 : reg n7 (26 : Fin 32) = x26 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_26]
    have g7_27 : reg n7 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_27]
    have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x420, 0x8), (0x1328, 0x8)] := by rw [m7]; exact keep_kk6
    clear keep_kk6
    have w7_24 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m7]; exact w6_24
    have w7_28 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m7]; exact w6_28
    have w7_2c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m7]; exact w6_2c
    have w7_30 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m7]; exact w6_30
    have w7_34 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m7]; exact w6_34
    have w7_38 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m7]; exact w6_38
    have w7_3c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m7]; exact w6_3c
    have w7_40 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m7]; exact w6_40
    have w7_44 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m7]; exact w6_44
    have w7_48 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m7]; exact w6_48
    have w7_4c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m7]; exact w6_4c
    have w7_50 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m7]; exact w6_50
    have w7_54 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m7]; exact w6_54
    have w7_58 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m7]; exact w6_58
    have w7_5c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m7]; exact w6_5c
    have w7_60 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m7]; exact w6_60
    have w7_64 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m7]; exact w6_64
    have w7_68 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m7]; exact w6_68
    have w7_6c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m7]; exact w6_6c
    have w7_70 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m7]; exact w6_70
    have w7_78 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m7]; exact w6_78
    have w7_7c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m7]; exact w6_7c
    have w7_80 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m7]; exact w6_80
    have w7_84 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m7]; exact w6_84
    have w7_88 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m7]; exact w6_88
    have w7_8c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m7]; exact w6_8c
    have w7_90 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m7]; exact w6_90
    have w7_94 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m7]; exact w6_94
    have w7_98 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m7]; exact w6_98
    have w7_9c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m7]; exact w6_9c
    have w7_a0 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m7]; exact w6_a0
    have w7_a4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m7]; exact w6_a4
    have w7_a8 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m7]; exact w6_a8
    have w7_ac : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m7]; exact w6_ac
    have w7_b0 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m7]; exact w6_b0
    have w7_b4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m7]; exact w6_b4
    have w7_b8 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m7]; exact w6_b8
    have w7_bc : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m7]; exact w6_bc
    have w7_c0 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m7]; exact w6_c0
    have w7_c4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m7]; exact w6_c4
    have w7_c8 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m7]; exact w6_c8
    have w7_cc : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m7]; exact w6_cc
    have w7_d0 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m7]; exact w6_d0
    have w7_d4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m7]; exact w6_d4
    have w7_d8 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m7]; exact w6_d8
    have w7_dc : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m7]; exact w6_dc
    have w7_e0 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m7]; exact w6_e0
    have w7_e4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m7]; exact w6_e4
    have w7_e8 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m7]; exact w6_e8
    have w7_ec : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m7]; exact w6_ec
    have w7_f0 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m7]; exact w6_f0
    have w7_f4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m7]; exact w6_f4
    have w7_f8 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m7]; exact w6_f8
    have w7_fc : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m7]; exact w6_fc
    have w7_100 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m7]; exact w6_100
    have w7_104 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m7]; exact w6_104
    have w7_108 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m7]; exact w6_108
    have w7_10c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m7]; exact w6_10c
    have w7_110 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m7]; exact w6_110
    have w7_114 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m7]; exact w6_114
    have w7_118 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m7]; exact w6_118
    have w7_11c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m7]; exact w6_11c
    have w7_120 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m7]; exact w6_120
    have w7_124 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m7]; exact w6_124
    have w7_128 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m7]; exact w6_128
    have w7_12c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m7]; exact w6_12c
    have w7_130 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m7]; exact w6_130
    have w7_420 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m7]; exact w6_420
    have q7_1020 : ∀ j, j < 47 → n7.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1020 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m7]; exact q6_1020 j hj
    have q7_104f : ∀ j, j < 48 → n7.mem (B + 0x21A0 + BitVec.ofNat 32 (0x104F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m7]; exact q6_104f j hj
    clear q6_104f q6_1020 w6_420 w6_130 w6_12c w6_128 w6_124 w6_120 w6_11c w6_118 w6_114 w6_110 w6_10c w6_108 w6_104 w6_100 w6_fc w6_f8 w6_f4 w6_f0 w6_ec w6_e8 w6_e4 w6_e0 w6_dc w6_d8 w6_d4 w6_d0 w6_cc w6_c8 w6_c4 w6_c0 w6_bc w6_b8 w6_b4 w6_b0 w6_ac w6_a8 w6_a4 w6_a0 w6_9c w6_98 w6_94 w6_90 w6_8c w6_88 w6_84 w6_80 w6_7c w6_78 w6_70 w6_6c w6_68 w6_64 w6_60 w6_5c w6_58 w6_54 w6_50 w6_4c w6_48 w6_44 w6_40 w6_3c w6_38 w6_34 w6_30 w6_2c w6_28 w6_24 g6_27 g6_26 g6_25 g6_24 g6_22 g6_21 g6_20 g6_19 g6_18 g6_10 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 m6 s6 u6 d6
    -- 0x2998: j
    obtain ⟨n8, d8, u8⟩ := s7.jump E7.self sv_at_2998 (off' := 0x2C60) (by decide)
      (by rw [s7.pc]; decide)
    have s8 : St n8.mem SV n8 0x2C60 (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
    have m8 : n8.mem = n7.mem := u8.mem
    have fr8 : ∀ x, SvR B x → n8.mem x = n7.mem x := fun x _ => by rw [m8]
    have t8 : Steps n0 n8 := t7.trans (.single d8)
    have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
    have E8 : SvCode n8.mem := E7.fr F fr8
    have V8 : SvSaves B n8.mem v := V7.same m8
    have g8_2 : reg n8 sp = B + 0x21A0 := by rw [u8.regs, g7_2]
    have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u8.regs, g7_3]
    have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u8.regs, g7_4]
    have g8_10 : reg n8 a0 = 0 := by rw [u8.regs, g7_10]
    have g8_18 : reg n8 (18 : Fin 32) = out := by rw [u8.regs, g7_18]
    have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [u8.regs, g7_19]
    have g8_20 : reg n8 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u8.regs, g7_20]
    have g8_21 : reg n8 (21 : Fin 32) = x21 := by rw [u8.regs, g7_21]
    have g8_22 : reg n8 (22 : Fin 32) = dp := by rw [u8.regs, g7_22]
    have g8_24 : reg n8 (24 : Fin 32) = dg := by rw [u8.regs, g7_24]
    have g8_25 : reg n8 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [u8.regs, g7_25]
    have g8_26 : reg n8 (26 : Fin 32) = x26 := by rw [u8.regs, g7_26]
    have g8_27 : reg n8 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u8.regs, g7_27]
    have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x420, 0x8), (0x1328, 0x8)] := by rw [m8]; exact keep_kk7
    clear keep_kk7
    have w8_24 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m8]; exact w7_24
    have w8_28 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m8]; exact w7_28
    have w8_2c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m8]; exact w7_2c
    have w8_30 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m8]; exact w7_30
    have w8_34 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m8]; exact w7_34
    have w8_38 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m8]; exact w7_38
    have w8_3c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m8]; exact w7_3c
    have w8_40 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m8]; exact w7_40
    have w8_44 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m8]; exact w7_44
    have w8_48 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m8]; exact w7_48
    have w8_4c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m8]; exact w7_4c
    have w8_50 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m8]; exact w7_50
    have w8_54 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m8]; exact w7_54
    have w8_58 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m8]; exact w7_58
    have w8_5c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m8]; exact w7_5c
    have w8_60 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m8]; exact w7_60
    have w8_64 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m8]; exact w7_64
    have w8_68 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m8]; exact w7_68
    have w8_6c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m8]; exact w7_6c
    have w8_70 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m8]; exact w7_70
    have w8_78 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m8]; exact w7_78
    have w8_7c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m8]; exact w7_7c
    have w8_80 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m8]; exact w7_80
    have w8_84 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m8]; exact w7_84
    have w8_88 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m8]; exact w7_88
    have w8_8c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m8]; exact w7_8c
    have w8_90 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m8]; exact w7_90
    have w8_94 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m8]; exact w7_94
    have w8_98 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m8]; exact w7_98
    have w8_9c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m8]; exact w7_9c
    have w8_a0 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m8]; exact w7_a0
    have w8_a4 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m8]; exact w7_a4
    have w8_a8 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m8]; exact w7_a8
    have w8_ac : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m8]; exact w7_ac
    have w8_b0 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m8]; exact w7_b0
    have w8_b4 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m8]; exact w7_b4
    have w8_b8 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m8]; exact w7_b8
    have w8_bc : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m8]; exact w7_bc
    have w8_c0 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m8]; exact w7_c0
    have w8_c4 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m8]; exact w7_c4
    have w8_c8 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m8]; exact w7_c8
    have w8_cc : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m8]; exact w7_cc
    have w8_d0 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m8]; exact w7_d0
    have w8_d4 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m8]; exact w7_d4
    have w8_d8 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m8]; exact w7_d8
    have w8_dc : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m8]; exact w7_dc
    have w8_e0 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m8]; exact w7_e0
    have w8_e4 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m8]; exact w7_e4
    have w8_e8 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m8]; exact w7_e8
    have w8_ec : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m8]; exact w7_ec
    have w8_f0 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m8]; exact w7_f0
    have w8_f4 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m8]; exact w7_f4
    have w8_f8 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m8]; exact w7_f8
    have w8_fc : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m8]; exact w7_fc
    have w8_100 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m8]; exact w7_100
    have w8_104 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m8]; exact w7_104
    have w8_108 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m8]; exact w7_108
    have w8_10c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m8]; exact w7_10c
    have w8_110 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m8]; exact w7_110
    have w8_114 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m8]; exact w7_114
    have w8_118 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m8]; exact w7_118
    have w8_11c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m8]; exact w7_11c
    have w8_120 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m8]; exact w7_120
    have w8_124 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m8]; exact w7_124
    have w8_128 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m8]; exact w7_128
    have w8_12c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m8]; exact w7_12c
    have w8_130 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m8]; exact w7_130
    have w8_420 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m8]; exact w7_420
    have q8_1020 : ∀ j, j < 47 → n8.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1020 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m8]; exact q7_1020 j hj
    have q8_104f : ∀ j, j < 48 → n8.mem (B + 0x21A0 + BitVec.ofNat 32 (0x104F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m8]; exact q7_104f j hj
    clear q7_104f q7_1020 w7_420 w7_130 w7_12c w7_128 w7_124 w7_120 w7_11c w7_118 w7_114 w7_110 w7_10c w7_108 w7_104 w7_100 w7_fc w7_f8 w7_f4 w7_f0 w7_ec w7_e8 w7_e4 w7_e0 w7_dc w7_d8 w7_d4 w7_d0 w7_cc w7_c8 w7_c4 w7_c0 w7_bc w7_b8 w7_b4 w7_b0 w7_ac w7_a8 w7_a4 w7_a0 w7_9c w7_98 w7_94 w7_90 w7_8c w7_88 w7_84 w7_80 w7_7c w7_78 w7_70 w7_6c w7_68 w7_64 w7_60 w7_5c w7_58 w7_54 w7_50 w7_4c w7_48 w7_44 w7_40 w7_3c w7_38 w7_34 w7_30 w7_2c w7_28 w7_24 g7_27 g7_26 g7_25 g7_24 g7_22 g7_21 g7_20 g7_19 g7_18 g7_10 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 m7 s7 u7 d7
    exact .inl ⟨(fun ⟨ip4', il4', h0', _⟩ => by rw [hr4] at h0'; cases h0'), sv_fail_2c60 F E8 s8 t8 (fun x hx => (fR8 x hx).trans (fM x hx).symm) V8 hret g8_2 g8_18 hO g8_3 g8_4⟩
  obtain ⟨ti4, hti4⟩ := int_ok_elem hr4
  obtain ⟨p0_4, p4_4⟩ := Ok4 ip4 il4 hr4
  obtain ⟨d8_4, d12_4⟩ := A4 ti4 hti4
  have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x420, 0x8), (0x1328, 0x8)] := keep_kk3.trans K4
  clear keep_kk3
  have w4_24 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K4.w32 (by decide) (by decide)).trans w3_24
  have w4_28 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K4.w32 (by decide) (by decide)).trans w3_28
  have w4_2c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K4.w32 (by decide) (by decide)).trans w3_2c
  have w4_30 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K4.w32 (by decide) (by decide)).trans w3_30
  have w4_34 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K4.w32 (by decide) (by decide)).trans w3_34
  have w4_38 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K4.w32 (by decide) (by decide)).trans w3_38
  have w4_3c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K4.w32 (by decide) (by decide)).trans w3_3c
  have w4_40 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K4.w32 (by decide) (by decide)).trans w3_40
  have w4_44 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K4.w32 (by decide) (by decide)).trans w3_44
  have w4_48 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K4.w32 (by decide) (by decide)).trans w3_48
  have w4_4c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K4.w32 (by decide) (by decide)).trans w3_4c
  have w4_50 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K4.w32 (by decide) (by decide)).trans w3_50
  have w4_54 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K4.w32 (by decide) (by decide)).trans w3_54
  have w4_58 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K4.w32 (by decide) (by decide)).trans w3_58
  have w4_5c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K4.w32 (by decide) (by decide)).trans w3_5c
  have w4_60 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K4.w32 (by decide) (by decide)).trans w3_60
  have w4_64 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K4.w32 (by decide) (by decide)).trans w3_64
  have w4_68 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K4.w32 (by decide) (by decide)).trans w3_68
  have w4_6c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K4.w32 (by decide) (by decide)).trans w3_6c
  have w4_70 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K4.w32 (by decide) (by decide)).trans w3_70
  have w4_78 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K4.w32 (by decide) (by decide)).trans w3_78
  have w4_7c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K4.w32 (by decide) (by decide)).trans w3_7c
  have w4_80 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K4.w32 (by decide) (by decide)).trans w3_80
  have w4_84 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K4.w32 (by decide) (by decide)).trans w3_84
  have w4_88 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K4.w32 (by decide) (by decide)).trans w3_88
  have w4_8c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K4.w32 (by decide) (by decide)).trans w3_8c
  have w4_90 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K4.w32 (by decide) (by decide)).trans w3_90
  have w4_94 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K4.w32 (by decide) (by decide)).trans w3_94
  have w4_98 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K4.w32 (by decide) (by decide)).trans w3_98
  have w4_9c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K4.w32 (by decide) (by decide)).trans w3_9c
  have w4_a0 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K4.w32 (by decide) (by decide)).trans w3_a0
  have w4_a4 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K4.w32 (by decide) (by decide)).trans w3_a4
  have w4_a8 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K4.w32 (by decide) (by decide)).trans w3_a8
  have w4_ac : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K4.w32 (by decide) (by decide)).trans w3_ac
  have w4_b0 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K4.w32 (by decide) (by decide)).trans w3_b0
  have w4_b4 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K4.w32 (by decide) (by decide)).trans w3_b4
  have w4_b8 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K4.w32 (by decide) (by decide)).trans w3_b8
  have w4_bc : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K4.w32 (by decide) (by decide)).trans w3_bc
  have w4_c0 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K4.w32 (by decide) (by decide)).trans w3_c0
  have w4_c4 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K4.w32 (by decide) (by decide)).trans w3_c4
  have w4_c8 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K4.w32 (by decide) (by decide)).trans w3_c8
  have w4_cc : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K4.w32 (by decide) (by decide)).trans w3_cc
  have w4_d0 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K4.w32 (by decide) (by decide)).trans w3_d0
  have w4_d4 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K4.w32 (by decide) (by decide)).trans w3_d4
  have w4_d8 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K4.w32 (by decide) (by decide)).trans w3_d8
  have w4_dc : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K4.w32 (by decide) (by decide)).trans w3_dc
  have w4_e0 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K4.w32 (by decide) (by decide)).trans w3_e0
  have w4_e4 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K4.w32 (by decide) (by decide)).trans w3_e4
  have w4_e8 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K4.w32 (by decide) (by decide)).trans w3_e8
  have w4_ec : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K4.w32 (by decide) (by decide)).trans w3_ec
  have w4_f0 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K4.w32 (by decide) (by decide)).trans w3_f0
  have w4_f4 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K4.w32 (by decide) (by decide)).trans w3_f4
  have w4_f8 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K4.w32 (by decide) (by decide)).trans w3_f8
  have w4_fc : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K4.w32 (by decide) (by decide)).trans w3_fc
  have w4_100 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K4.w32 (by decide) (by decide)).trans w3_100
  have w4_104 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K4.w32 (by decide) (by decide)).trans w3_104
  have w4_108 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K4.w32 (by decide) (by decide)).trans w3_108
  have w4_10c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K4.w32 (by decide) (by decide)).trans w3_10c
  have w4_110 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K4.w32 (by decide) (by decide)).trans w3_110
  have w4_114 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K4.w32 (by decide) (by decide)).trans w3_114
  have w4_118 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K4.w32 (by decide) (by decide)).trans w3_118
  have w4_11c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K4.w32 (by decide) (by decide)).trans w3_11c
  have w4_120 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K4.w32 (by decide) (by decide)).trans w3_120
  have w4_124 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K4.w32 (by decide) (by decide)).trans w3_124
  have w4_128 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K4.w32 (by decide) (by decide)).trans w3_128
  have w4_12c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K4.w32 (by decide) (by decide)).trans w3_12c
  have w4_130 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K4.w32 (by decide) (by decide)).trans w3_130
  have q4_1020 : ∀ j, j < 47 → n4.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1020 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => (K4.range (by decide) (by decide) j hj).trans (q3_1020 j hj)
  have q4_104f : ∀ j, j < 48 → n4.mem (B + 0x21A0 + BitVec.ofNat 32 (0x104F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => (K4.range (by decide) (by decide) j hj).trans (q3_104f j hj)
  have w4_420 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ip4 := p0_4
  have w4_424 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = il4 := p4_4
  have w4_1328 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = (rp) + BitVec.ofNat 32 (ti4.header + ti4.len) := d8_4
  have w4_132c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = (rl) - BitVec.ofNat 32 (ti4.header + ti4.len) := d12_4
  clear q3_104f q3_1020 w3_132c w3_1328 w3_130 w3_12c w3_128 w3_124 w3_120 w3_11c w3_118 w3_114 w3_110 w3_10c w3_108 w3_104 w3_100 w3_fc w3_f8 w3_f4 w3_f0 w3_ec w3_e8 w3_e4 w3_e0 w3_dc w3_d8 w3_d4 w3_d0 w3_cc w3_c8 w3_c4 w3_c0 w3_bc w3_b8 w3_b4 w3_b0 w3_ac w3_a8 w3_a4 w3_a0 w3_9c w3_98 w3_94 w3_90 w3_8c w3_88 w3_84 w3_80 w3_7c w3_78 w3_70 w3_6c w3_68 w3_64 w3_60 w3_5c w3_58 w3_54 w3_50 w3_4c w3_48 w3_44 w3_40 w3_3c w3_38 w3_34 w3_30 w3_2c w3_28 w3_24 g3_11 g3_10 g3_27 g3_26 g3_25 g3_24 g3_22 g3_21 g3_20 g3_19 g3_18 g3_8 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 rb3 s3 m3 u3 c3
  -- 0x294C: lw
  obtain ⟨n5, d5, u5⟩ := s4.lw E4.self sv_at_294c (off' := 0x2950) (by decide)
    (by rw [g4_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s5 : St n5.mem SV n5 0x2950 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have fr5 : ∀ x, SvR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
  have t5 : Steps n0 n5 := t4.trans (.single d5)
  have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : SvCode n5.mem := E4.fr F fr5
  have V5 : SvSaves B n5.mem v := V4.same m5
  have g5_2 : reg n5 sp = B + 0x21A0 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u5.regs, upd_ne (by decide) (by decide), g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u5.regs, upd_ne (by decide) (by decide), g4_4]
  have g5_8 : reg n5 (8 : Fin 32) = x8 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_8]
  have g5_18 : reg n5 (18 : Fin 32) = out := by rw [u5.regs, upd_ne (by decide) (by decide), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_19]
  have g5_20 : reg n5 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_20]
  have g5_21 : reg n5 (21 : Fin 32) = x21 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = dp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_22]
  have g5_24 : reg n5 (24 : Fin 32) = dg := by rw [u5.regs, upd_ne (by decide) (by decide), g4_24]
  have g5_25 : reg n5 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = x26 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_27]
  have g5_10 : reg n5 a0 = ip4 := by
    rw [u5.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g4_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w4_420]
  have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x420, 0x8), (0x1328, 0x8)] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have w5_24 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m5]; exact w4_24
  have w5_28 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m5]; exact w4_28
  have w5_2c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m5]; exact w4_2c
  have w5_30 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m5]; exact w4_30
  have w5_34 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m5]; exact w4_34
  have w5_38 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m5]; exact w4_38
  have w5_3c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m5]; exact w4_3c
  have w5_40 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m5]; exact w4_40
  have w5_44 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m5]; exact w4_44
  have w5_48 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m5]; exact w4_48
  have w5_4c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m5]; exact w4_4c
  have w5_50 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m5]; exact w4_50
  have w5_54 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m5]; exact w4_54
  have w5_58 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m5]; exact w4_58
  have w5_5c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m5]; exact w4_5c
  have w5_60 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m5]; exact w4_60
  have w5_64 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m5]; exact w4_64
  have w5_68 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m5]; exact w4_68
  have w5_6c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m5]; exact w4_6c
  have w5_70 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m5]; exact w4_70
  have w5_78 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m5]; exact w4_78
  have w5_7c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m5]; exact w4_7c
  have w5_80 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m5]; exact w4_80
  have w5_84 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m5]; exact w4_84
  have w5_88 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m5]; exact w4_88
  have w5_8c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m5]; exact w4_8c
  have w5_90 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m5]; exact w4_90
  have w5_94 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m5]; exact w4_94
  have w5_98 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m5]; exact w4_98
  have w5_9c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m5]; exact w4_9c
  have w5_a0 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m5]; exact w4_a0
  have w5_a4 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m5]; exact w4_a4
  have w5_a8 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m5]; exact w4_a8
  have w5_ac : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m5]; exact w4_ac
  have w5_b0 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m5]; exact w4_b0
  have w5_b4 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m5]; exact w4_b4
  have w5_b8 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m5]; exact w4_b8
  have w5_bc : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m5]; exact w4_bc
  have w5_c0 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m5]; exact w4_c0
  have w5_c4 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m5]; exact w4_c4
  have w5_c8 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m5]; exact w4_c8
  have w5_cc : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m5]; exact w4_cc
  have w5_d0 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m5]; exact w4_d0
  have w5_d4 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m5]; exact w4_d4
  have w5_d8 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m5]; exact w4_d8
  have w5_dc : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m5]; exact w4_dc
  have w5_e0 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m5]; exact w4_e0
  have w5_e4 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m5]; exact w4_e4
  have w5_e8 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m5]; exact w4_e8
  have w5_ec : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m5]; exact w4_ec
  have w5_f0 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m5]; exact w4_f0
  have w5_f4 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m5]; exact w4_f4
  have w5_f8 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m5]; exact w4_f8
  have w5_fc : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m5]; exact w4_fc
  have w5_100 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m5]; exact w4_100
  have w5_104 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m5]; exact w4_104
  have w5_108 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m5]; exact w4_108
  have w5_10c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m5]; exact w4_10c
  have w5_110 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m5]; exact w4_110
  have w5_114 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m5]; exact w4_114
  have w5_118 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m5]; exact w4_118
  have w5_11c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m5]; exact w4_11c
  have w5_120 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m5]; exact w4_120
  have w5_124 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m5]; exact w4_124
  have w5_128 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m5]; exact w4_128
  have w5_12c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m5]; exact w4_12c
  have w5_130 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m5]; exact w4_130
  have w5_420 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ip4 := by rw [m5]; exact w4_420
  have w5_424 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = il4 := by rw [m5]; exact w4_424
  have w5_1328 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = (rp) + BitVec.ofNat 32 (ti4.header + ti4.len) := by rw [m5]; exact w4_1328
  have w5_132c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = (rl) - BitVec.ofNat 32 (ti4.header + ti4.len) := by rw [m5]; exact w4_132c
  have q5_1020 : ∀ j, j < 47 → n5.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1020 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m5]; exact q4_1020 j hj
  have q5_104f : ∀ j, j < 48 → n5.mem (B + 0x21A0 + BitVec.ofNat 32 (0x104F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m5]; exact q4_104f j hj
  clear w4_132c w4_1328 w4_424 w4_420 q4_104f q4_1020 w4_130 w4_12c w4_128 w4_124 w4_120 w4_11c w4_118 w4_114 w4_110 w4_10c w4_108 w4_104 w4_100 w4_fc w4_f8 w4_f4 w4_f0 w4_ec w4_e8 w4_e4 w4_e0 w4_dc w4_d8 w4_d4 w4_d0 w4_cc w4_c8 w4_c4 w4_c0 w4_bc w4_b8 w4_b4 w4_b0 w4_ac w4_a8 w4_a4 w4_a0 w4_9c w4_98 w4_94 w4_90 w4_8c w4_88 w4_84 w4_80 w4_7c w4_78 w4_70 w4_6c w4_68 w4_64 w4_60 w4_5c w4_58 w4_54 w4_50 w4_4c w4_48 w4_44 w4_40 w4_3c w4_38 w4_34 w4_30 w4_2c w4_28 w4_24 d12_4 d8_4 p4_4 p0_4 g4_27 g4_26 g4_25 g4_24 g4_22 g4_21 g4_20 g4_19 g4_18 g4_8 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 Er4 Ok4 A4 K4 rk4 sp4 s4 c4
  -- 0x2950: branch, not taken
  obtain ⟨n6, d6, u6⟩ := s5.notTaken E5.self 0x2952 sv_at_2950
    (by decide) (by rw [g5_10, s5.zero]; exact br_beq_f (rd_in.int_ne hr4))
  have s6 : St n6.mem SV n6 0x2952 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have fr6 : ∀ x, SvR B x → n6.mem x = n5.mem x := fun x _ => by rw [m6]
  have t6 : Steps n0 n6 := t5.trans (.single d6)
  have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : SvCode n6.mem := E5.fr F fr6
  have V6 : SvSaves B n6.mem v := V5.same m6
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [u6.regs, g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u6.regs, g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u6.regs, g5_4]
  have g6_8 : reg n6 (8 : Fin 32) = x8 := by rw [u6.regs, g5_8]
  have g6_10 : reg n6 a0 = ip4 := by rw [u6.regs, g5_10]
  have g6_18 : reg n6 (18 : Fin 32) = out := by rw [u6.regs, g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [u6.regs, g5_19]
  have g6_20 : reg n6 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u6.regs, g5_20]
  have g6_21 : reg n6 (21 : Fin 32) = x21 := by rw [u6.regs, g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = dp := by rw [u6.regs, g5_22]
  have g6_24 : reg n6 (24 : Fin 32) = dg := by rw [u6.regs, g5_24]
  have g6_25 : reg n6 (25 : Fin 32) = (BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32 := by rw [u6.regs, g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = x26 := by rw [u6.regs, g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u6.regs, g5_27]
  have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x420, 0x8), (0x1328, 0x8)] := by rw [m6]; exact keep_kk5
  clear keep_kk5
  have w6_24 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m6]; exact w5_24
  have w6_28 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m6]; exact w5_28
  have w6_2c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m6]; exact w5_2c
  have w6_30 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m6]; exact w5_30
  have w6_34 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m6]; exact w5_34
  have w6_38 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m6]; exact w5_38
  have w6_3c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m6]; exact w5_3c
  have w6_40 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m6]; exact w5_40
  have w6_44 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m6]; exact w5_44
  have w6_48 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m6]; exact w5_48
  have w6_4c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m6]; exact w5_4c
  have w6_50 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m6]; exact w5_50
  have w6_54 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m6]; exact w5_54
  have w6_58 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m6]; exact w5_58
  have w6_5c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m6]; exact w5_5c
  have w6_60 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m6]; exact w5_60
  have w6_64 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m6]; exact w5_64
  have w6_68 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m6]; exact w5_68
  have w6_6c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m6]; exact w5_6c
  have w6_70 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m6]; exact w5_70
  have w6_78 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m6]; exact w5_78
  have w6_7c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m6]; exact w5_7c
  have w6_80 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m6]; exact w5_80
  have w6_84 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m6]; exact w5_84
  have w6_88 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m6]; exact w5_88
  have w6_8c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m6]; exact w5_8c
  have w6_90 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m6]; exact w5_90
  have w6_94 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m6]; exact w5_94
  have w6_98 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m6]; exact w5_98
  have w6_9c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m6]; exact w5_9c
  have w6_a0 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m6]; exact w5_a0
  have w6_a4 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m6]; exact w5_a4
  have w6_a8 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m6]; exact w5_a8
  have w6_ac : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m6]; exact w5_ac
  have w6_b0 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m6]; exact w5_b0
  have w6_b4 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m6]; exact w5_b4
  have w6_b8 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m6]; exact w5_b8
  have w6_bc : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m6]; exact w5_bc
  have w6_c0 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m6]; exact w5_c0
  have w6_c4 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m6]; exact w5_c4
  have w6_c8 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m6]; exact w5_c8
  have w6_cc : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m6]; exact w5_cc
  have w6_d0 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m6]; exact w5_d0
  have w6_d4 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m6]; exact w5_d4
  have w6_d8 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m6]; exact w5_d8
  have w6_dc : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m6]; exact w5_dc
  have w6_e0 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m6]; exact w5_e0
  have w6_e4 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m6]; exact w5_e4
  have w6_e8 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m6]; exact w5_e8
  have w6_ec : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m6]; exact w5_ec
  have w6_f0 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m6]; exact w5_f0
  have w6_f4 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m6]; exact w5_f4
  have w6_f8 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m6]; exact w5_f8
  have w6_fc : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m6]; exact w5_fc
  have w6_100 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m6]; exact w5_100
  have w6_104 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m6]; exact w5_104
  have w6_108 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m6]; exact w5_108
  have w6_10c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m6]; exact w5_10c
  have w6_110 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m6]; exact w5_110
  have w6_114 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m6]; exact w5_114
  have w6_118 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m6]; exact w5_118
  have w6_11c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m6]; exact w5_11c
  have w6_120 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m6]; exact w5_120
  have w6_124 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m6]; exact w5_124
  have w6_128 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m6]; exact w5_128
  have w6_12c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m6]; exact w5_12c
  have w6_130 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m6]; exact w5_130
  have w6_420 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ip4 := by rw [m6]; exact w5_420
  have w6_424 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = il4 := by rw [m6]; exact w5_424
  have w6_1328 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = (rp) + BitVec.ofNat 32 (ti4.header + ti4.len) := by rw [m6]; exact w5_1328
  have w6_132c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = (rl) - BitVec.ofNat 32 (ti4.header + ti4.len) := by rw [m6]; exact w5_132c
  have q6_1020 : ∀ j, j < 47 → n6.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1020 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0) := fun j hj => by rw [m6]; exact q5_1020 j hj
  have q6_104f : ∀ j, j < 48 → n6.mem (B + 0x21A0 + BitVec.ofNat 32 (0x104F + j)) = BitVec.ofNat 8 (ss.getD j 0) := fun j hj => by rw [m6]; exact q5_104f j hj
  clear q5_104f q5_1020 w5_132c w5_1328 w5_424 w5_420 w5_130 w5_12c w5_128 w5_124 w5_120 w5_11c w5_118 w5_114 w5_110 w5_10c w5_108 w5_104 w5_100 w5_fc w5_f8 w5_f4 w5_f0 w5_ec w5_e8 w5_e4 w5_e0 w5_dc w5_d8 w5_d4 w5_d0 w5_cc w5_c8 w5_c4 w5_c0 w5_bc w5_b8 w5_b4 w5_b0 w5_ac w5_a8 w5_a4 w5_a0 w5_9c w5_98 w5_94 w5_90 w5_8c w5_88 w5_84 w5_80 w5_7c w5_78 w5_70 w5_6c w5_68 w5_64 w5_60 w5_5c w5_58 w5_54 w5_50 w5_4c w5_48 w5_44 w5_40 w5_3c w5_38 w5_34 w5_30 w5_2c w5_28 w5_24 g5_10 g5_27 g5_26 g5_25 g5_24 g5_22 g5_21 g5_20 g5_19 g5_18 g5_8 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5
  exact .inr ⟨ip4, il4, hr4, ti4, hti4, n6, t6, s6, E6, V6, fR6, g6_2, g6_3, g6_4, g6_8, g6_18, g6_19, g6_20, g6_21, g6_22, g6_24, g6_25, g6_26, g6_27, w6_24, w6_28, w6_2c, w6_30, w6_34, w6_38, w6_3c, w6_40, w6_44, w6_48, w6_4c, w6_50, w6_54, w6_58, w6_5c, w6_60, w6_64, w6_68, w6_6c, w6_70, w6_78, w6_7c, w6_80, w6_84, w6_88, w6_8c, w6_90, w6_94, w6_98, w6_9c, w6_a0, w6_a4, w6_a8, w6_ac, w6_b0, w6_b4, w6_b8, w6_bc, w6_c0, w6_c4, w6_c8, w6_cc, w6_d0, w6_d4, w6_d8, w6_dc, w6_e0, w6_e4, w6_e8, w6_ec, w6_f0, w6_f4, w6_f8, w6_fc, w6_100, w6_104, w6_108, w6_10c, w6_110, w6_114, w6_118, w6_11c, w6_120, w6_124, w6_128, w6_12c, w6_130, w6_1328, w6_132c, q6_1020, q6_104f, keep_kk6.mono (by decide)⟩

end C3.RV32.Sv
