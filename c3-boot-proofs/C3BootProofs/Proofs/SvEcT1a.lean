import C3BootProofs.Proofs.SvEcT0b

/-!
# `sigstore::verify`: the tables of the linear combination, part 1a

Part 1a of the table loop from 0x1690 to 0x178A: the odd multiples `P + j·2P` of `G` and of `Q`, stored at offsets 0xA20 and 0xD20.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svEcT1a1694 : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x380, .alu .add a0 a0 sp, .aluImm .add a2 x0 0x80, .alu .add a1 x0 (23 : Fin 32)]
theorem svEcT1a1694_end : blockEnd sigstoreVerifyCode 0x1694 svEcT1a1694 = some 0x16A2 := by
  simp only [svEcT1a1694]
  rw [blockEnd, sv_at_1694]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1696]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_169a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_169c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_16a0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svEcT1a16aa : List BInstr :=
  [.aluImm .add (8 : Fin 32) sp 0x420, .aluImm .add (9 : Fin 32) x0 0x8]
theorem svEcT1a16aa_end : blockEnd sigstoreVerifyCode 0x16AA svEcT1a16aa = some 0x16B0 := by
  simp only [svEcT1a16aa]
  rw [blockEnd, sv_at_16aa]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_16ae]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svEcT1a16b2 : List BInstr :=
  [.aluImm .add a2 x0 0x60, .alu .add a0 x0 (8 : Fin 32), .alu .add a1 x0 (22 : Fin 32)]
theorem svEcT1a16b2_end : blockEnd sigstoreVerifyCode 0x16B2 svEcT1a16b2 = some 0x16BA := by
  simp only [svEcT1a16b2]
  rw [blockEnd, sv_at_16b2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_16b6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_16b8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svEcT1a16c2 : List BInstr :=
  [.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x60, .aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFF]
theorem svEcT1a16c2_end : blockEnd sigstoreVerifyCode 0x16C2 svEcT1a16c2 = some 0x16C8 := by
  simp only [svEcT1a16c2]
  rw [blockEnd, sv_at_16c2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_16c6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svEcT1a16ca : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x20, .alu .add a0 a0 sp, .aluImm .add a1 sp 0x420, .aluImm .add a2 x0 0x300, .lui a3 0x1000, .aluImm .add a3 a3 0x20, .alu .add (8 : Fin 32) sp a3, .aluImm .add (9 : Fin 32) x0 0x300]
theorem svEcT1a16ca_end : blockEnd sigstoreVerifyCode 0x16CA svEcT1a16ca = some 0x16E8 := by
  simp only [svEcT1a16ca]
  rw [blockEnd, sv_at_16ca]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_16cc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_16d0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_16d2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_16d6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_16da]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_16dc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_16e0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_16e4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_ect1a {B out bp x21 x26 s5v s8v dlo dhi rem : Word} {er es : Bytes} {fs gs ds es : BitVec 8} {U1 U2 : Nat} {P0 P1 : Pt2} {qx qy qz rv sv zv fv gv dv ev : Nat} {w24 w28 w2c w30 w34 w38 w3c w40 w44 w48 w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w7c w80 w84 w88 w8c w90 w94 w98 w9c wa0 wa4 wa8 wac wb0 wb4 wb8 wbc wc0 wc4 wc8 wcc wd0 wd4 wd8 wdc we0 we4 we8 wec wf0 wf4 wf8 wfc w100 w104 w108 w10c w110 w114 w118 w11c w120 w124 w128 w12c w130 : Word} {v : Nat → Word} {n0 : Machine}
    (F : Fr B 0x3830) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x1694 (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_8 : reg n0 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320)
    (g0_9 : reg n0 (9 : Fin 32) = BitVec.ofNat 32 0x0)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20)
    (g0_21 : reg n0 (21 : Fin 32) = BitVec.ofNat 32 0x2)
    (g0_22 : reg n0 (22 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress))
    (g0_23 : reg n0 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1500)
    (g0_24 : reg n0 (24 : Fin 32) = BitVec.ofNat 32 0x1)
    (g0_25 : reg n0 (25 : Fin 32) = BitVec.ofNat 32 0x300)
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
    (w0_78 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem)
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
    (b0_440 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) = gs)
    (b0_a40 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = gs)
    (b0_1040 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = gs)
    (b0_13a0 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = gs)
    (b0_14a0 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs)
    (a0_240 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx)
    (a0_260 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy)
    (a0_280 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz)
    (a0_2a0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv)
    (a0_2c0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv)
    (a0_2e0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv)
    (a0_380 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1)
    (a0_400 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2)
    (a0_13e0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1)
    (a0_14e0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x14E0) 8 = U1)
    (a0_1560 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1560) 8 = U2)
    (p0_320 : ptF n0.mem B 0x320 = P0)
    (p0_3a0 : ptF n0.mem B 0x3A0 = P1)
    (p0_420 : ptF n0.mem B 0x420 = tbl2 P0 0)
    (p0_480 : ptF n0.mem B 0x480 = tbl2 P0 1)
    (p0_4e0 : ptF n0.mem B 0x4E0 = tbl2 P0 2)
    (p0_540 : ptF n0.mem B 0x540 = tbl2 P0 3)
    (p0_5a0 : ptF n0.mem B 0x5A0 = tbl2 P0 4)
    (p0_600 : ptF n0.mem B 0x600 = tbl2 P0 5)
    (p0_660 : ptF n0.mem B 0x660 = tbl2 P0 6)
    (p0_6c0 : ptF n0.mem B 0x6C0 = tbl2 P0 7)
    (p0_a20 : ptF n0.mem B 0xA20 = tbl2 P0 0)
    (p0_a80 : ptF n0.mem B 0xA80 = tbl2 P0 1)
    (p0_ae0 : ptF n0.mem B 0xAE0 = tbl2 P0 2)
    (p0_b40 : ptF n0.mem B 0xB40 = tbl2 P0 3)
    (p0_ba0 : ptF n0.mem B 0xBA0 = tbl2 P0 4)
    (p0_c00 : ptF n0.mem B 0xC00 = tbl2 P0 5)
    (p0_c60 : ptF n0.mem B 0xC60 = tbl2 P0 6)
    (p0_cc0 : ptF n0.mem B 0xCC0 = tbl2 P0 7)
    (p0_1020 : ptF n0.mem B 0x1020 = tbl2 P0 0)
    (p0_1080 : ptF n0.mem B 0x1080 = tbl2 P0 1)
    (p0_10e0 : ptF n0.mem B 0x10E0 = tbl2 P0 2)
    (p0_1140 : ptF n0.mem B 0x1140 = tbl2 P0 3)
    (p0_11a0 : ptF n0.mem B 0x11A0 = tbl2 P0 4)
    (p0_1200 : ptF n0.mem B 0x1200 = tbl2 P0 5)
    (p0_1260 : ptF n0.mem B 0x1260 = tbl2 P0 6)
    (p0_12c0 : ptF n0.mem B 0x12C0 = tbl2 P0 7)
    (p0_1320 : ptF n0.mem B 0x1320 = ptDbl2 P0)
    (p0_1380 : ptF n0.mem B 0x1380 = P0)
    (p0_1480 : ptF n0.mem B 0x1480 = P0)
    (p0_1500 : ptF n0.mem B 0x1500 = P1)
    (IC0 : SvIvCode M0)
    (EC0 : SvEcCode M0)
    (hP0 : Pt2Lt P0)
    (hP1 : Pt2Lt P1)
    (RS : SvRoSep B)
    (PT0 : SvPtCode M0) :
    (¬ (True) ∧ SvErrRet B out v n0) ∨
    (∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x16F0 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1020 ∧
        reg n' (9 : Fin 32) = BitVec.ofNat 32 0x300 ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
        reg n' (21 : Fin 32) = BitVec.ofNat 32 0x2 ∧
        reg n' (22 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) ∧
        reg n' (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1500 ∧
        reg n' (24 : Fin 32) = BitVec.ofNat 32 0x1 ∧
        reg n' (25 : Fin 32) = BitVec.ofNat 32 0x300 ∧
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
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem ∧
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
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = gs ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs ∧
        (∀ j, j < 96 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 96 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x480 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 96 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x4E0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 96 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x540 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 96 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x5A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 96 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x600 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 96 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x660 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 96 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x6C0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 96 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1020 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 96 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1080 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 96 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x10E0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 96 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1140 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 96 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x11A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 96 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1200 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 96 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1260 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 96 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x12C0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j)) ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U2 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x14E0) 8 = U1 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1560) 8 = U2 ∧
        ptF n'.mem B 0x320 = P0 ∧
        ptF n'.mem B 0x3A0 = P1 ∧
        ptF n'.mem B 0xA20 = tbl2 P0 0 ∧
        ptF n'.mem B 0xA80 = tbl2 P0 1 ∧
        ptF n'.mem B 0xAE0 = tbl2 P0 2 ∧
        ptF n'.mem B 0xB40 = tbl2 P0 3 ∧
        ptF n'.mem B 0xBA0 = tbl2 P0 4 ∧
        ptF n'.mem B 0xC00 = tbl2 P0 5 ∧
        ptF n'.mem B 0xC60 = tbl2 P0 6 ∧
        ptF n'.mem B 0xCC0 = tbl2 P0 7 ∧
        ptF n'.mem B 0x1320 = ptDbl2 P0 ∧
        ptF n'.mem B 0x1380 = P1 ∧
        ptF n'.mem B 0x1480 = P0 ∧
        ptF n'.mem B 0x1500 = P1 ∧
        SvKeepL B n0.mem n'.mem [(0x1380, 0x80), (0x420, 0x60), (0x480, 0x60), (0x4E0, 0x60), (0x540, 0x60), (0x5A0, 0x60), (0x600, 0x60), (0x660, 0x60), (0x6C0, 0x60), (0x1020, 0x300)]) := by
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x1694
  obtain ⟨n1, c1, u1⟩ := s0.block svEcT1a1694 E0.self svEcT1a1694_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have s1 : St n1.mem SV n1 0x16A2 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have rb1 : ∀ q, reg n1 q = (runBlock svEcT1a1694 (n0.mem, reg n0)).2 q := fun q => by rw [u1.regs]
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
  have g1_8 : reg n1 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
    rw [rb1, runBlock_reg _ _ _ (8 : Fin 32) s0.zero (by decide), g0_8]
  have g1_9 : reg n1 (9 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb1, runBlock_reg _ _ _ (9 : Fin 32) s0.zero (by decide), g0_9]
  have g1_18 : reg n1 (18 : Fin 32) = out := by
    rw [rb1, runBlock_reg _ _ _ (18 : Fin 32) s0.zero (by decide), g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = bp := by
    rw [rb1, runBlock_reg _ _ _ (19 : Fin 32) s0.zero (by decide), g0_19]
  have g1_20 : reg n1 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb1, runBlock_reg _ _ _ (20 : Fin 32) s0.zero (by decide), g0_20]
  have g1_21 : reg n1 (21 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb1, runBlock_reg _ _ _ (21 : Fin 32) s0.zero (by decide), g0_21]
  have g1_22 : reg n1 (22 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb1, runBlock_reg _ _ _ (22 : Fin 32) s0.zero (by decide), g0_22]
  have g1_23 : reg n1 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1500 := by
    rw [rb1, runBlock_reg _ _ _ (23 : Fin 32) s0.zero (by decide), g0_23]
  have g1_24 : reg n1 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb1, runBlock_reg _ _ _ (24 : Fin 32) s0.zero (by decide), g0_24]
  have g1_25 : reg n1 (25 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb1, runBlock_reg _ _ _ (25 : Fin 32) s0.zero (by decide), g0_25]
  have g1_26 : reg n1 (26 : Fin 32) = x26 := by
    rw [rb1, runBlock_reg _ _ _ (26 : Fin 32) s0.zero (by decide), g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb1, runBlock_reg _ _ _ (27 : Fin 32) s0.zero (by decide), g0_27]
  have g1_10 : reg n1 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1380 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svEcT1a1694, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_8, g0_9, g0_18, g0_19, g0_20, g0_21, g0_22, g0_23, g0_24, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g1_11 : reg n1 a1 = B + 0x21A0 + BitVec.ofNat 32 0x1500 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svEcT1a1694, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_8, g0_9, g0_18, g0_19, g0_20, g0_21, g0_22, g0_23, g0_24, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g1_12 : reg n1 a2 = BitVec.ofNat 32 0x80 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svEcT1a1694, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_8, g0_9, g0_18, g0_19, g0_20, g0_21, g0_22, g0_23, g0_24, g0_25, g0_26, g0_27, s0.zero])
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
  have w1_78 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m1]; exact w0_78
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
  have b1_440 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) = gs := by rw [m1]; exact b0_440
  have b1_a40 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = gs := by rw [m1]; exact b0_a40
  have b1_1040 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = gs := by rw [m1]; exact b0_1040
  have b1_13a0 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = gs := by rw [m1]; exact b0_13a0
  have b1_14a0 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := by rw [m1]; exact b0_14a0
  have a1_240 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m1]; exact a0_240
  have a1_260 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m1]; exact a0_260
  have a1_280 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m1]; exact a0_280
  have a1_2a0 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m1]; exact a0_2a0
  have a1_2c0 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m1]; exact a0_2c0
  have a1_2e0 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m1]; exact a0_2e0
  have a1_380 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m1]; exact a0_380
  have a1_400 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m1]; exact a0_400
  have a1_13e0 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := by rw [m1]; exact a0_13e0
  have a1_14e0 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x14E0) 8 = U1 := by rw [m1]; exact a0_14e0
  have a1_1560 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1560) 8 = U2 := by rw [m1]; exact a0_1560
  have p1_320 : ptF n1.mem B 0x320 = P0 := by rw [m1]; exact p0_320
  have p1_3a0 : ptF n1.mem B 0x3A0 = P1 := by rw [m1]; exact p0_3a0
  have p1_420 : ptF n1.mem B 0x420 = tbl2 P0 0 := by rw [m1]; exact p0_420
  have p1_480 : ptF n1.mem B 0x480 = tbl2 P0 1 := by rw [m1]; exact p0_480
  have p1_4e0 : ptF n1.mem B 0x4E0 = tbl2 P0 2 := by rw [m1]; exact p0_4e0
  have p1_540 : ptF n1.mem B 0x540 = tbl2 P0 3 := by rw [m1]; exact p0_540
  have p1_5a0 : ptF n1.mem B 0x5A0 = tbl2 P0 4 := by rw [m1]; exact p0_5a0
  have p1_600 : ptF n1.mem B 0x600 = tbl2 P0 5 := by rw [m1]; exact p0_600
  have p1_660 : ptF n1.mem B 0x660 = tbl2 P0 6 := by rw [m1]; exact p0_660
  have p1_6c0 : ptF n1.mem B 0x6C0 = tbl2 P0 7 := by rw [m1]; exact p0_6c0
  have p1_a20 : ptF n1.mem B 0xA20 = tbl2 P0 0 := by rw [m1]; exact p0_a20
  have p1_a80 : ptF n1.mem B 0xA80 = tbl2 P0 1 := by rw [m1]; exact p0_a80
  have p1_ae0 : ptF n1.mem B 0xAE0 = tbl2 P0 2 := by rw [m1]; exact p0_ae0
  have p1_b40 : ptF n1.mem B 0xB40 = tbl2 P0 3 := by rw [m1]; exact p0_b40
  have p1_ba0 : ptF n1.mem B 0xBA0 = tbl2 P0 4 := by rw [m1]; exact p0_ba0
  have p1_c00 : ptF n1.mem B 0xC00 = tbl2 P0 5 := by rw [m1]; exact p0_c00
  have p1_c60 : ptF n1.mem B 0xC60 = tbl2 P0 6 := by rw [m1]; exact p0_c60
  have p1_cc0 : ptF n1.mem B 0xCC0 = tbl2 P0 7 := by rw [m1]; exact p0_cc0
  have p1_1020 : ptF n1.mem B 0x1020 = tbl2 P0 0 := by rw [m1]; exact p0_1020
  have p1_1080 : ptF n1.mem B 0x1080 = tbl2 P0 1 := by rw [m1]; exact p0_1080
  have p1_10e0 : ptF n1.mem B 0x10E0 = tbl2 P0 2 := by rw [m1]; exact p0_10e0
  have p1_1140 : ptF n1.mem B 0x1140 = tbl2 P0 3 := by rw [m1]; exact p0_1140
  have p1_11a0 : ptF n1.mem B 0x11A0 = tbl2 P0 4 := by rw [m1]; exact p0_11a0
  have p1_1200 : ptF n1.mem B 0x1200 = tbl2 P0 5 := by rw [m1]; exact p0_1200
  have p1_1260 : ptF n1.mem B 0x1260 = tbl2 P0 6 := by rw [m1]; exact p0_1260
  have p1_12c0 : ptF n1.mem B 0x12C0 = tbl2 P0 7 := by rw [m1]; exact p0_12c0
  have p1_1320 : ptF n1.mem B 0x1320 = ptDbl2 P0 := by rw [m1]; exact p0_1320
  have p1_1380 : ptF n1.mem B 0x1380 = P0 := by rw [m1]; exact p0_1380
  have p1_1480 : ptF n1.mem B 0x1480 = P0 := by rw [m1]; exact p0_1480
  have p1_1500 : ptF n1.mem B 0x1500 = P1 := by rw [m1]; exact p0_1500
  -- 0x16A2: memcpy
  obtain ⟨n2, P2, K2, X2⟩ := sv_mc (c := 0x1380) (d := 0x1500) (N := 0x80) F E1 s1 sv_at_16a2 sv_at_16a6
    (by decide) (by decide) g1_2 g1_10 g1_11 g1_12
    (by decide) (by decide) (by decide)
  have s2 := P2.st
  have fr2 := P2.fr
  have t2 : Steps n0 n2 := t1.trans P2.steps
  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.keep K2 (by decide)
  have g2_2 : reg n2 sp = B + 0x21A0 := by rw [P2.regs sp (by decide), g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P2.regs (3 : Fin 32) (by decide), g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P2.regs (4 : Fin 32) (by decide), g1_4]
  have g2_8 : reg n2 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [P2.regs (8 : Fin 32) (by decide), g1_8]
  have g2_9 : reg n2 (9 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [P2.regs (9 : Fin 32) (by decide), g1_9]
  have g2_18 : reg n2 (18 : Fin 32) = out := by rw [P2.regs (18 : Fin 32) (by decide), g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [P2.regs (19 : Fin 32) (by decide), g1_19]
  have g2_20 : reg n2 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P2.regs (20 : Fin 32) (by decide), g1_20]
  have g2_21 : reg n2 (21 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P2.regs (21 : Fin 32) (by decide), g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [P2.regs (22 : Fin 32) (by decide), g1_22]
  have g2_23 : reg n2 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1500 := by rw [P2.regs (23 : Fin 32) (by decide), g1_23]
  have g2_24 : reg n2 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P2.regs (24 : Fin 32) (by decide), g1_24]
  have g2_25 : reg n2 (25 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [P2.regs (25 : Fin 32) (by decide), g1_25]
  have g2_26 : reg n2 (26 : Fin 32) = x26 := by rw [P2.regs (26 : Fin 32) (by decide), g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P2.regs (27 : Fin 32) (by decide), g1_27]
  have keep_kk2 : SvKeepL B n0.mem n2.mem [(0x1380, 0x80)] := keep_kk1.trans K2.toL
  clear keep_kk1
  have w2_24 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K2.w32 (by decide) (by decide)).trans w1_24
  have w2_28 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K2.w32 (by decide) (by decide)).trans w1_28
  have w2_2c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K2.w32 (by decide) (by decide)).trans w1_2c
  have w2_30 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K2.w32 (by decide) (by decide)).trans w1_30
  have w2_34 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K2.w32 (by decide) (by decide)).trans w1_34
  have w2_38 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K2.w32 (by decide) (by decide)).trans w1_38
  have w2_3c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K2.w32 (by decide) (by decide)).trans w1_3c
  have w2_40 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K2.w32 (by decide) (by decide)).trans w1_40
  have w2_44 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K2.w32 (by decide) (by decide)).trans w1_44
  have w2_48 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K2.w32 (by decide) (by decide)).trans w1_48
  have w2_4c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K2.w32 (by decide) (by decide)).trans w1_4c
  have w2_50 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K2.w32 (by decide) (by decide)).trans w1_50
  have w2_54 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K2.w32 (by decide) (by decide)).trans w1_54
  have w2_58 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K2.w32 (by decide) (by decide)).trans w1_58
  have w2_5c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K2.w32 (by decide) (by decide)).trans w1_5c
  have w2_60 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K2.w32 (by decide) (by decide)).trans w1_60
  have w2_64 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K2.w32 (by decide) (by decide)).trans w1_64
  have w2_68 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K2.w32 (by decide) (by decide)).trans w1_68
  have w2_6c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K2.w32 (by decide) (by decide)).trans w1_6c
  have w2_70 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K2.w32 (by decide) (by decide)).trans w1_70
  have w2_78 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := (K2.w32 (by decide) (by decide)).trans w1_78
  have w2_7c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K2.w32 (by decide) (by decide)).trans w1_7c
  have w2_80 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K2.w32 (by decide) (by decide)).trans w1_80
  have w2_84 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K2.w32 (by decide) (by decide)).trans w1_84
  have w2_88 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K2.w32 (by decide) (by decide)).trans w1_88
  have w2_8c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K2.w32 (by decide) (by decide)).trans w1_8c
  have w2_90 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K2.w32 (by decide) (by decide)).trans w1_90
  have w2_94 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K2.w32 (by decide) (by decide)).trans w1_94
  have w2_98 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K2.w32 (by decide) (by decide)).trans w1_98
  have w2_9c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K2.w32 (by decide) (by decide)).trans w1_9c
  have w2_a0 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K2.w32 (by decide) (by decide)).trans w1_a0
  have w2_a4 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K2.w32 (by decide) (by decide)).trans w1_a4
  have w2_a8 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K2.w32 (by decide) (by decide)).trans w1_a8
  have w2_ac : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K2.w32 (by decide) (by decide)).trans w1_ac
  have w2_b0 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K2.w32 (by decide) (by decide)).trans w1_b0
  have w2_b4 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K2.w32 (by decide) (by decide)).trans w1_b4
  have w2_b8 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K2.w32 (by decide) (by decide)).trans w1_b8
  have w2_bc : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K2.w32 (by decide) (by decide)).trans w1_bc
  have w2_c0 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K2.w32 (by decide) (by decide)).trans w1_c0
  have w2_c4 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K2.w32 (by decide) (by decide)).trans w1_c4
  have w2_c8 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K2.w32 (by decide) (by decide)).trans w1_c8
  have w2_cc : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K2.w32 (by decide) (by decide)).trans w1_cc
  have w2_d0 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K2.w32 (by decide) (by decide)).trans w1_d0
  have w2_d4 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K2.w32 (by decide) (by decide)).trans w1_d4
  have w2_d8 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K2.w32 (by decide) (by decide)).trans w1_d8
  have w2_dc : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K2.w32 (by decide) (by decide)).trans w1_dc
  have w2_e0 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K2.w32 (by decide) (by decide)).trans w1_e0
  have w2_e4 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K2.w32 (by decide) (by decide)).trans w1_e4
  have w2_e8 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K2.w32 (by decide) (by decide)).trans w1_e8
  have w2_ec : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K2.w32 (by decide) (by decide)).trans w1_ec
  have w2_f0 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K2.w32 (by decide) (by decide)).trans w1_f0
  have w2_f4 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K2.w32 (by decide) (by decide)).trans w1_f4
  have w2_f8 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K2.w32 (by decide) (by decide)).trans w1_f8
  have w2_fc : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K2.w32 (by decide) (by decide)).trans w1_fc
  have w2_100 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K2.w32 (by decide) (by decide)).trans w1_100
  have w2_104 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K2.w32 (by decide) (by decide)).trans w1_104
  have w2_108 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K2.w32 (by decide) (by decide)).trans w1_108
  have w2_10c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K2.w32 (by decide) (by decide)).trans w1_10c
  have w2_110 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K2.w32 (by decide) (by decide)).trans w1_110
  have w2_114 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K2.w32 (by decide) (by decide)).trans w1_114
  have w2_118 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K2.w32 (by decide) (by decide)).trans w1_118
  have w2_11c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K2.w32 (by decide) (by decide)).trans w1_11c
  have w2_120 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K2.w32 (by decide) (by decide)).trans w1_120
  have w2_124 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K2.w32 (by decide) (by decide)).trans w1_124
  have w2_128 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K2.w32 (by decide) (by decide)).trans w1_128
  have w2_12c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K2.w32 (by decide) (by decide)).trans w1_12c
  have w2_130 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K2.w32 (by decide) (by decide)).trans w1_130
  have b2_440 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) = gs := (K2.b8 (by decide) (by decide)).trans b1_440
  have b2_a40 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = gs := (K2.b8 (by decide) (by decide)).trans b1_a40
  have b2_1040 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = gs := (K2.b8 (by decide) (by decide)).trans b1_1040
  have b2_14a0 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := (K2.b8 (by decide) (by decide)).trans b1_14a0
  have a2_240 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := (K2.acc (by decide) (by decide)).trans a1_240
  have a2_260 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := (K2.acc (by decide) (by decide)).trans a1_260
  have a2_280 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := (K2.acc (by decide) (by decide)).trans a1_280
  have a2_2a0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K2.acc (by decide) (by decide)).trans a1_2a0
  have a2_2c0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K2.acc (by decide) (by decide)).trans a1_2c0
  have a2_2e0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K2.acc (by decide) (by decide)).trans a1_2e0
  have a2_380 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := (K2.acc (by decide) (by decide)).trans a1_380
  have a2_400 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := (K2.acc (by decide) (by decide)).trans a1_400
  have a2_14e0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x14E0) 8 = U1 := (K2.acc (by decide) (by decide)).trans a1_14e0
  have a2_1560 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1560) 8 = U2 := (K2.acc (by decide) (by decide)).trans a1_1560
  have p2_320 : ptF n2.mem B 0x320 = P0 := (K2.pt (by decide) (by decide)).trans p1_320
  have p2_3a0 : ptF n2.mem B 0x3A0 = P1 := (K2.pt (by decide) (by decide)).trans p1_3a0
  have p2_420 : ptF n2.mem B 0x420 = tbl2 P0 0 := (K2.pt (by decide) (by decide)).trans p1_420
  have p2_480 : ptF n2.mem B 0x480 = tbl2 P0 1 := (K2.pt (by decide) (by decide)).trans p1_480
  have p2_4e0 : ptF n2.mem B 0x4E0 = tbl2 P0 2 := (K2.pt (by decide) (by decide)).trans p1_4e0
  have p2_540 : ptF n2.mem B 0x540 = tbl2 P0 3 := (K2.pt (by decide) (by decide)).trans p1_540
  have p2_5a0 : ptF n2.mem B 0x5A0 = tbl2 P0 4 := (K2.pt (by decide) (by decide)).trans p1_5a0
  have p2_600 : ptF n2.mem B 0x600 = tbl2 P0 5 := (K2.pt (by decide) (by decide)).trans p1_600
  have p2_660 : ptF n2.mem B 0x660 = tbl2 P0 6 := (K2.pt (by decide) (by decide)).trans p1_660
  have p2_6c0 : ptF n2.mem B 0x6C0 = tbl2 P0 7 := (K2.pt (by decide) (by decide)).trans p1_6c0
  have p2_a20 : ptF n2.mem B 0xA20 = tbl2 P0 0 := (K2.pt (by decide) (by decide)).trans p1_a20
  have p2_a80 : ptF n2.mem B 0xA80 = tbl2 P0 1 := (K2.pt (by decide) (by decide)).trans p1_a80
  have p2_ae0 : ptF n2.mem B 0xAE0 = tbl2 P0 2 := (K2.pt (by decide) (by decide)).trans p1_ae0
  have p2_b40 : ptF n2.mem B 0xB40 = tbl2 P0 3 := (K2.pt (by decide) (by decide)).trans p1_b40
  have p2_ba0 : ptF n2.mem B 0xBA0 = tbl2 P0 4 := (K2.pt (by decide) (by decide)).trans p1_ba0
  have p2_c00 : ptF n2.mem B 0xC00 = tbl2 P0 5 := (K2.pt (by decide) (by decide)).trans p1_c00
  have p2_c60 : ptF n2.mem B 0xC60 = tbl2 P0 6 := (K2.pt (by decide) (by decide)).trans p1_c60
  have p2_cc0 : ptF n2.mem B 0xCC0 = tbl2 P0 7 := (K2.pt (by decide) (by decide)).trans p1_cc0
  have p2_1020 : ptF n2.mem B 0x1020 = tbl2 P0 0 := (K2.pt (by decide) (by decide)).trans p1_1020
  have p2_1080 : ptF n2.mem B 0x1080 = tbl2 P0 1 := (K2.pt (by decide) (by decide)).trans p1_1080
  have p2_10e0 : ptF n2.mem B 0x10E0 = tbl2 P0 2 := (K2.pt (by decide) (by decide)).trans p1_10e0
  have p2_1140 : ptF n2.mem B 0x1140 = tbl2 P0 3 := (K2.pt (by decide) (by decide)).trans p1_1140
  have p2_11a0 : ptF n2.mem B 0x11A0 = tbl2 P0 4 := (K2.pt (by decide) (by decide)).trans p1_11a0
  have p2_1200 : ptF n2.mem B 0x1200 = tbl2 P0 5 := (K2.pt (by decide) (by decide)).trans p1_1200
  have p2_1260 : ptF n2.mem B 0x1260 = tbl2 P0 6 := (K2.pt (by decide) (by decide)).trans p1_1260
  have p2_12c0 : ptF n2.mem B 0x12C0 = tbl2 P0 7 := (K2.pt (by decide) (by decide)).trans p1_12c0
  have p2_1320 : ptF n2.mem B 0x1320 = ptDbl2 P0 := (K2.pt (by decide) (by decide)).trans p1_1320
  have p2_1480 : ptF n2.mem B 0x1480 = P0 := (K2.pt (by decide) (by decide)).trans p1_1480
  have p2_1500 : ptF n2.mem B 0x1500 = P1 := (K2.pt (by decide) (by decide)).trans p1_1500
  have p2_1380 : ptF n2.mem B 0x1380 = P1 := (ptF_cp X2 (by decide) (by decide) (by decide)).trans p1_1500
  have a2_13e0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U2 := (accV_S 8 fun q hq => by
    rw [show 0x13E0 + q = 0x1380 + (0x60 + q) by omega, X2 (0x60 + q) (by omega),
      show 0x1500 + (0x60 + q) = 0x1560 + q by omega]).trans a1_1560
  clear p1_1500 p1_1480 p1_1380 p1_1320 p1_12c0 p1_1260 p1_1200 p1_11a0 p1_1140 p1_10e0 p1_1080 p1_1020 p1_cc0 p1_c60 p1_c00 p1_ba0 p1_b40 p1_ae0 p1_a80 p1_a20 p1_6c0 p1_660 p1_600 p1_5a0 p1_540 p1_4e0 p1_480 p1_420 p1_3a0 p1_320 a1_1560 a1_14e0 a1_13e0 a1_400 a1_380 a1_2e0 a1_2c0 a1_2a0 a1_280 a1_260 a1_240 b1_14a0 b1_13a0 b1_1040 b1_a40 b1_440 w1_130 w1_12c w1_128 w1_124 w1_120 w1_11c w1_118 w1_114 w1_110 w1_10c w1_108 w1_104 w1_100 w1_fc w1_f8 w1_f4 w1_f0 w1_ec w1_e8 w1_e4 w1_e0 w1_dc w1_d8 w1_d4 w1_d0 w1_cc w1_c8 w1_c4 w1_c0 w1_bc w1_b8 w1_b4 w1_b0 w1_ac w1_a8 w1_a4 w1_a0 w1_9c w1_98 w1_94 w1_90 w1_8c w1_88 w1_84 w1_80 w1_7c w1_78 w1_70 w1_6c w1_68 w1_64 w1_60 w1_5c w1_58 w1_54 w1_50 w1_4c w1_48 w1_44 w1_40 w1_3c w1_38 w1_34 w1_30 w1_2c w1_28 w1_24 g1_12 g1_11 g1_10 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_9 g1_8 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
  -- 0x16AA
  obtain ⟨n3, c3, u3⟩ := s2.block svEcT1a16aa E2.self svEcT1a16aa_end
    ⟨trivial, trivial, trivial⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have s3 : St n3.mem SV n3 0x16B0 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have rb3 : ∀ q, reg n3 q = (runBlock svEcT1a16aa (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
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
  have g3_18 : reg n3 (18 : Fin 32) = out := by
    rw [rb3, runBlock_reg _ _ _ (18 : Fin 32) s2.zero (by decide), g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = bp := by
    rw [rb3, runBlock_reg _ _ _ (19 : Fin 32) s2.zero (by decide), g2_19]
  have g3_20 : reg n3 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb3, runBlock_reg _ _ _ (20 : Fin 32) s2.zero (by decide), g2_20]
  have g3_21 : reg n3 (21 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb3, runBlock_reg _ _ _ (21 : Fin 32) s2.zero (by decide), g2_21]
  have g3_22 : reg n3 (22 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb3, runBlock_reg _ _ _ (22 : Fin 32) s2.zero (by decide), g2_22]
  have g3_23 : reg n3 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1500 := by
    rw [rb3, runBlock_reg _ _ _ (23 : Fin 32) s2.zero (by decide), g2_23]
  have g3_24 : reg n3 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb3, runBlock_reg _ _ _ (24 : Fin 32) s2.zero (by decide), g2_24]
  have g3_25 : reg n3 (25 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb3, runBlock_reg _ _ _ (25 : Fin 32) s2.zero (by decide), g2_25]
  have g3_26 : reg n3 (26 : Fin 32) = x26 := by
    rw [rb3, runBlock_reg _ _ _ (26 : Fin 32) s2.zero (by decide), g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb3, runBlock_reg _ _ _ (27 : Fin 32) s2.zero (by decide), g2_27]
  have g3_8 : reg n3 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb3]; simp +decide only [runBlock, BInstr.run, svEcT1a16aa, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g2_2, g2_3, g2_4, g2_8, g2_9, g2_18, g2_19, g2_20, g2_21, g2_22, g2_23, g2_24, g2_25, g2_26, g2_27, s2.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g3_9 : reg n3 (9 : Fin 32) = BitVec.ofNat 32 0x8 := by
    rw [rb3]; simp +decide only [runBlock, BInstr.run, svEcT1a16aa, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g2_2, g2_3, g2_4, g2_8, g2_9, g2_18, g2_19, g2_20, g2_21, g2_22, g2_23, g2_24, g2_25, g2_26, g2_27, s2.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk3 : SvKeepL B n0.mem n3.mem [(0x1380, 0x80)] := by rw [m3]; exact keep_kk2
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
  have w3_78 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m3]; exact w2_78
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
  have b3_440 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) = gs := by rw [m3]; exact b2_440
  have b3_a40 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = gs := by rw [m3]; exact b2_a40
  have b3_1040 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = gs := by rw [m3]; exact b2_1040
  have b3_14a0 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := by rw [m3]; exact b2_14a0
  have a3_240 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m3]; exact a2_240
  have a3_260 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m3]; exact a2_260
  have a3_280 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m3]; exact a2_280
  have a3_2a0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m3]; exact a2_2a0
  have a3_2c0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m3]; exact a2_2c0
  have a3_2e0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m3]; exact a2_2e0
  have a3_380 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m3]; exact a2_380
  have a3_400 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m3]; exact a2_400
  have a3_13e0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U2 := by rw [m3]; exact a2_13e0
  have a3_14e0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x14E0) 8 = U1 := by rw [m3]; exact a2_14e0
  have a3_1560 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1560) 8 = U2 := by rw [m3]; exact a2_1560
  have p3_320 : ptF n3.mem B 0x320 = P0 := by rw [m3]; exact p2_320
  have p3_3a0 : ptF n3.mem B 0x3A0 = P1 := by rw [m3]; exact p2_3a0
  have p3_420 : ptF n3.mem B 0x420 = tbl2 P0 0 := by rw [m3]; exact p2_420
  have p3_480 : ptF n3.mem B 0x480 = tbl2 P0 1 := by rw [m3]; exact p2_480
  have p3_4e0 : ptF n3.mem B 0x4E0 = tbl2 P0 2 := by rw [m3]; exact p2_4e0
  have p3_540 : ptF n3.mem B 0x540 = tbl2 P0 3 := by rw [m3]; exact p2_540
  have p3_5a0 : ptF n3.mem B 0x5A0 = tbl2 P0 4 := by rw [m3]; exact p2_5a0
  have p3_600 : ptF n3.mem B 0x600 = tbl2 P0 5 := by rw [m3]; exact p2_600
  have p3_660 : ptF n3.mem B 0x660 = tbl2 P0 6 := by rw [m3]; exact p2_660
  have p3_6c0 : ptF n3.mem B 0x6C0 = tbl2 P0 7 := by rw [m3]; exact p2_6c0
  have p3_a20 : ptF n3.mem B 0xA20 = tbl2 P0 0 := by rw [m3]; exact p2_a20
  have p3_a80 : ptF n3.mem B 0xA80 = tbl2 P0 1 := by rw [m3]; exact p2_a80
  have p3_ae0 : ptF n3.mem B 0xAE0 = tbl2 P0 2 := by rw [m3]; exact p2_ae0
  have p3_b40 : ptF n3.mem B 0xB40 = tbl2 P0 3 := by rw [m3]; exact p2_b40
  have p3_ba0 : ptF n3.mem B 0xBA0 = tbl2 P0 4 := by rw [m3]; exact p2_ba0
  have p3_c00 : ptF n3.mem B 0xC00 = tbl2 P0 5 := by rw [m3]; exact p2_c00
  have p3_c60 : ptF n3.mem B 0xC60 = tbl2 P0 6 := by rw [m3]; exact p2_c60
  have p3_cc0 : ptF n3.mem B 0xCC0 = tbl2 P0 7 := by rw [m3]; exact p2_cc0
  have p3_1020 : ptF n3.mem B 0x1020 = tbl2 P0 0 := by rw [m3]; exact p2_1020
  have p3_1080 : ptF n3.mem B 0x1080 = tbl2 P0 1 := by rw [m3]; exact p2_1080
  have p3_10e0 : ptF n3.mem B 0x10E0 = tbl2 P0 2 := by rw [m3]; exact p2_10e0
  have p3_1140 : ptF n3.mem B 0x1140 = tbl2 P0 3 := by rw [m3]; exact p2_1140
  have p3_11a0 : ptF n3.mem B 0x11A0 = tbl2 P0 4 := by rw [m3]; exact p2_11a0
  have p3_1200 : ptF n3.mem B 0x1200 = tbl2 P0 5 := by rw [m3]; exact p2_1200
  have p3_1260 : ptF n3.mem B 0x1260 = tbl2 P0 6 := by rw [m3]; exact p2_1260
  have p3_12c0 : ptF n3.mem B 0x12C0 = tbl2 P0 7 := by rw [m3]; exact p2_12c0
  have p3_1320 : ptF n3.mem B 0x1320 = ptDbl2 P0 := by rw [m3]; exact p2_1320
  have p3_1380 : ptF n3.mem B 0x1380 = P1 := by rw [m3]; exact p2_1380
  have p3_1480 : ptF n3.mem B 0x1480 = P0 := by rw [m3]; exact p2_1480
  have p3_1500 : ptF n3.mem B 0x1500 = P1 := by rw [m3]; exact p2_1500
  clear a2_13e0 p2_1380 p2_1500 p2_1480 p2_1320 p2_12c0 p2_1260 p2_1200 p2_11a0 p2_1140 p2_10e0 p2_1080 p2_1020 p2_cc0 p2_c60 p2_c00 p2_ba0 p2_b40 p2_ae0 p2_a80 p2_a20 p2_6c0 p2_660 p2_600 p2_5a0 p2_540 p2_4e0 p2_480 p2_420 p2_3a0 p2_320 a2_1560 a2_14e0 a2_400 a2_380 a2_2e0 a2_2c0 a2_2a0 a2_280 a2_260 a2_240 b2_14a0 b2_1040 b2_a40 b2_440 w2_130 w2_12c w2_128 w2_124 w2_120 w2_11c w2_118 w2_114 w2_110 w2_10c w2_108 w2_104 w2_100 w2_fc w2_f8 w2_f4 w2_f0 w2_ec w2_e8 w2_e4 w2_e0 w2_dc w2_d8 w2_d4 w2_d0 w2_cc w2_c8 w2_c4 w2_c0 w2_bc w2_b8 w2_b4 w2_b0 w2_ac w2_a8 w2_a4 w2_a0 w2_9c w2_98 w2_94 w2_90 w2_8c w2_88 w2_84 w2_80 w2_7c w2_78 w2_70 w2_6c w2_68 w2_64 w2_60 w2_5c w2_58 w2_54 w2_50 w2_4c w2_48 w2_44 w2_40 w2_3c w2_38 w2_34 w2_30 w2_2c w2_28 w2_24 g2_27 g2_26 g2_25 g2_24 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_9 g2_8 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 s2 X2 K2 P2
  -- 0x16B0: branch, not taken
  obtain ⟨n4, d4, u4⟩ := s3.notTaken E3.self 0x16B2 sv_at_16b0
    (by decide) (by rw [g3_9, s3.zero]; decide)
  have s4 : St n4.mem SV n4 0x16B2 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have fr4 : ∀ x, SvR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
  have t4 : Steps n0 n4 := t3.trans (.single d4)
  have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : SvCode n4.mem := E3.fr F fr4
  have V4 : SvSaves B n4.mem v := V3.same m4
  have g4_2 : reg n4 sp = B + 0x21A0 := by rw [u4.regs, g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u4.regs, g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u4.regs, g3_4]
  have g4_8 : reg n4 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x420 := by rw [u4.regs, g3_8]
  have g4_9 : reg n4 (9 : Fin 32) = BitVec.ofNat 32 0x8 := by rw [u4.regs, g3_9]
  have g4_18 : reg n4 (18 : Fin 32) = out := by rw [u4.regs, g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [u4.regs, g3_19]
  have g4_20 : reg n4 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u4.regs, g3_20]
  have g4_21 : reg n4 (21 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u4.regs, g3_21]
  have g4_22 : reg n4 (22 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [u4.regs, g3_22]
  have g4_23 : reg n4 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1500 := by rw [u4.regs, g3_23]
  have g4_24 : reg n4 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u4.regs, g3_24]
  have g4_25 : reg n4 (25 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [u4.regs, g3_25]
  have g4_26 : reg n4 (26 : Fin 32) = x26 := by rw [u4.regs, g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u4.regs, g3_27]
  have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x1380, 0x80)] := by rw [m4]; exact keep_kk3
  clear keep_kk3
  have w4_24 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m4]; exact w3_24
  have w4_28 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m4]; exact w3_28
  have w4_2c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m4]; exact w3_2c
  have w4_30 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m4]; exact w3_30
  have w4_34 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m4]; exact w3_34
  have w4_38 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m4]; exact w3_38
  have w4_3c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m4]; exact w3_3c
  have w4_40 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m4]; exact w3_40
  have w4_44 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m4]; exact w3_44
  have w4_48 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m4]; exact w3_48
  have w4_4c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m4]; exact w3_4c
  have w4_50 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m4]; exact w3_50
  have w4_54 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m4]; exact w3_54
  have w4_58 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m4]; exact w3_58
  have w4_5c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m4]; exact w3_5c
  have w4_60 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m4]; exact w3_60
  have w4_64 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m4]; exact w3_64
  have w4_68 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m4]; exact w3_68
  have w4_6c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m4]; exact w3_6c
  have w4_70 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m4]; exact w3_70
  have w4_78 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m4]; exact w3_78
  have w4_7c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m4]; exact w3_7c
  have w4_80 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m4]; exact w3_80
  have w4_84 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m4]; exact w3_84
  have w4_88 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m4]; exact w3_88
  have w4_8c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m4]; exact w3_8c
  have w4_90 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m4]; exact w3_90
  have w4_94 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m4]; exact w3_94
  have w4_98 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m4]; exact w3_98
  have w4_9c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m4]; exact w3_9c
  have w4_a0 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m4]; exact w3_a0
  have w4_a4 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m4]; exact w3_a4
  have w4_a8 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m4]; exact w3_a8
  have w4_ac : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m4]; exact w3_ac
  have w4_b0 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m4]; exact w3_b0
  have w4_b4 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m4]; exact w3_b4
  have w4_b8 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m4]; exact w3_b8
  have w4_bc : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m4]; exact w3_bc
  have w4_c0 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m4]; exact w3_c0
  have w4_c4 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m4]; exact w3_c4
  have w4_c8 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m4]; exact w3_c8
  have w4_cc : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m4]; exact w3_cc
  have w4_d0 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m4]; exact w3_d0
  have w4_d4 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m4]; exact w3_d4
  have w4_d8 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m4]; exact w3_d8
  have w4_dc : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m4]; exact w3_dc
  have w4_e0 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m4]; exact w3_e0
  have w4_e4 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m4]; exact w3_e4
  have w4_e8 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m4]; exact w3_e8
  have w4_ec : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m4]; exact w3_ec
  have w4_f0 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m4]; exact w3_f0
  have w4_f4 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m4]; exact w3_f4
  have w4_f8 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m4]; exact w3_f8
  have w4_fc : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m4]; exact w3_fc
  have w4_100 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m4]; exact w3_100
  have w4_104 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m4]; exact w3_104
  have w4_108 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m4]; exact w3_108
  have w4_10c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m4]; exact w3_10c
  have w4_110 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m4]; exact w3_110
  have w4_114 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m4]; exact w3_114
  have w4_118 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m4]; exact w3_118
  have w4_11c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m4]; exact w3_11c
  have w4_120 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m4]; exact w3_120
  have w4_124 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m4]; exact w3_124
  have w4_128 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m4]; exact w3_128
  have w4_12c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m4]; exact w3_12c
  have w4_130 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m4]; exact w3_130
  have b4_440 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) = gs := by rw [m4]; exact b3_440
  have b4_a40 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = gs := by rw [m4]; exact b3_a40
  have b4_1040 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = gs := by rw [m4]; exact b3_1040
  have b4_14a0 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := by rw [m4]; exact b3_14a0
  have a4_240 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m4]; exact a3_240
  have a4_260 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m4]; exact a3_260
  have a4_280 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m4]; exact a3_280
  have a4_2a0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m4]; exact a3_2a0
  have a4_2c0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m4]; exact a3_2c0
  have a4_2e0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m4]; exact a3_2e0
  have a4_380 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m4]; exact a3_380
  have a4_400 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m4]; exact a3_400
  have a4_13e0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U2 := by rw [m4]; exact a3_13e0
  have a4_14e0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x14E0) 8 = U1 := by rw [m4]; exact a3_14e0
  have a4_1560 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1560) 8 = U2 := by rw [m4]; exact a3_1560
  have p4_320 : ptF n4.mem B 0x320 = P0 := by rw [m4]; exact p3_320
  have p4_3a0 : ptF n4.mem B 0x3A0 = P1 := by rw [m4]; exact p3_3a0
  have p4_420 : ptF n4.mem B 0x420 = tbl2 P0 0 := by rw [m4]; exact p3_420
  have p4_480 : ptF n4.mem B 0x480 = tbl2 P0 1 := by rw [m4]; exact p3_480
  have p4_4e0 : ptF n4.mem B 0x4E0 = tbl2 P0 2 := by rw [m4]; exact p3_4e0
  have p4_540 : ptF n4.mem B 0x540 = tbl2 P0 3 := by rw [m4]; exact p3_540
  have p4_5a0 : ptF n4.mem B 0x5A0 = tbl2 P0 4 := by rw [m4]; exact p3_5a0
  have p4_600 : ptF n4.mem B 0x600 = tbl2 P0 5 := by rw [m4]; exact p3_600
  have p4_660 : ptF n4.mem B 0x660 = tbl2 P0 6 := by rw [m4]; exact p3_660
  have p4_6c0 : ptF n4.mem B 0x6C0 = tbl2 P0 7 := by rw [m4]; exact p3_6c0
  have p4_a20 : ptF n4.mem B 0xA20 = tbl2 P0 0 := by rw [m4]; exact p3_a20
  have p4_a80 : ptF n4.mem B 0xA80 = tbl2 P0 1 := by rw [m4]; exact p3_a80
  have p4_ae0 : ptF n4.mem B 0xAE0 = tbl2 P0 2 := by rw [m4]; exact p3_ae0
  have p4_b40 : ptF n4.mem B 0xB40 = tbl2 P0 3 := by rw [m4]; exact p3_b40
  have p4_ba0 : ptF n4.mem B 0xBA0 = tbl2 P0 4 := by rw [m4]; exact p3_ba0
  have p4_c00 : ptF n4.mem B 0xC00 = tbl2 P0 5 := by rw [m4]; exact p3_c00
  have p4_c60 : ptF n4.mem B 0xC60 = tbl2 P0 6 := by rw [m4]; exact p3_c60
  have p4_cc0 : ptF n4.mem B 0xCC0 = tbl2 P0 7 := by rw [m4]; exact p3_cc0
  have p4_1020 : ptF n4.mem B 0x1020 = tbl2 P0 0 := by rw [m4]; exact p3_1020
  have p4_1080 : ptF n4.mem B 0x1080 = tbl2 P0 1 := by rw [m4]; exact p3_1080
  have p4_10e0 : ptF n4.mem B 0x10E0 = tbl2 P0 2 := by rw [m4]; exact p3_10e0
  have p4_1140 : ptF n4.mem B 0x1140 = tbl2 P0 3 := by rw [m4]; exact p3_1140
  have p4_11a0 : ptF n4.mem B 0x11A0 = tbl2 P0 4 := by rw [m4]; exact p3_11a0
  have p4_1200 : ptF n4.mem B 0x1200 = tbl2 P0 5 := by rw [m4]; exact p3_1200
  have p4_1260 : ptF n4.mem B 0x1260 = tbl2 P0 6 := by rw [m4]; exact p3_1260
  have p4_12c0 : ptF n4.mem B 0x12C0 = tbl2 P0 7 := by rw [m4]; exact p3_12c0
  have p4_1320 : ptF n4.mem B 0x1320 = ptDbl2 P0 := by rw [m4]; exact p3_1320
  have p4_1380 : ptF n4.mem B 0x1380 = P1 := by rw [m4]; exact p3_1380
  have p4_1480 : ptF n4.mem B 0x1480 = P0 := by rw [m4]; exact p3_1480
  have p4_1500 : ptF n4.mem B 0x1500 = P1 := by rw [m4]; exact p3_1500
  clear p3_1500 p3_1480 p3_1380 p3_1320 p3_12c0 p3_1260 p3_1200 p3_11a0 p3_1140 p3_10e0 p3_1080 p3_1020 p3_cc0 p3_c60 p3_c00 p3_ba0 p3_b40 p3_ae0 p3_a80 p3_a20 p3_6c0 p3_660 p3_600 p3_5a0 p3_540 p3_4e0 p3_480 p3_420 p3_3a0 p3_320 a3_1560 a3_14e0 a3_13e0 a3_400 a3_380 a3_2e0 a3_2c0 a3_2a0 a3_280 a3_260 a3_240 b3_14a0 b3_1040 b3_a40 b3_440 w3_130 w3_12c w3_128 w3_124 w3_120 w3_11c w3_118 w3_114 w3_110 w3_10c w3_108 w3_104 w3_100 w3_fc w3_f8 w3_f4 w3_f0 w3_ec w3_e8 w3_e4 w3_e0 w3_dc w3_d8 w3_d4 w3_d0 w3_cc w3_c8 w3_c4 w3_c0 w3_bc w3_b8 w3_b4 w3_b0 w3_ac w3_a8 w3_a4 w3_a0 w3_9c w3_98 w3_94 w3_90 w3_8c w3_88 w3_84 w3_80 w3_7c w3_78 w3_70 w3_6c w3_68 w3_64 w3_60 w3_5c w3_58 w3_54 w3_50 w3_4c w3_48 w3_44 w3_40 w3_3c w3_38 w3_34 w3_30 w3_2c w3_28 w3_24 g3_9 g3_8 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 rb3 s3 m3 u3 c3
  -- 0x16B2
  obtain ⟨n5, c5, u5⟩ := s4.block svEcT1a16b2 E4.self svEcT1a16b2_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have s5 : St n5.mem SV n5 0x16BA (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have rb5 : ∀ q, reg n5 q = (runBlock svEcT1a16b2 (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
  have fr5 : ∀ x, SvR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
  have t5 : Steps n0 n5 := t4.trans c5
  have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : SvCode n5.mem := E4.fr F fr5
  have V5 : SvSaves B n5.mem v := V4.same m5
  have g5_2 : reg n5 sp = B + 0x21A0 := by
    rw [rb5, runBlock_reg _ _ _ sp s4.zero (by decide), g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb5, runBlock_reg _ _ _ (3 : Fin 32) s4.zero (by decide), g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb5, runBlock_reg _ _ _ (4 : Fin 32) s4.zero (by decide), g4_4]
  have g5_8 : reg n5 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb5, runBlock_reg _ _ _ (8 : Fin 32) s4.zero (by decide), g4_8]
  have g5_9 : reg n5 (9 : Fin 32) = BitVec.ofNat 32 0x8 := by
    rw [rb5, runBlock_reg _ _ _ (9 : Fin 32) s4.zero (by decide), g4_9]
  have g5_18 : reg n5 (18 : Fin 32) = out := by
    rw [rb5, runBlock_reg _ _ _ (18 : Fin 32) s4.zero (by decide), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by
    rw [rb5, runBlock_reg _ _ _ (19 : Fin 32) s4.zero (by decide), g4_19]
  have g5_20 : reg n5 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb5, runBlock_reg _ _ _ (20 : Fin 32) s4.zero (by decide), g4_20]
  have g5_21 : reg n5 (21 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb5, runBlock_reg _ _ _ (21 : Fin 32) s4.zero (by decide), g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb5, runBlock_reg _ _ _ (22 : Fin 32) s4.zero (by decide), g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1500 := by
    rw [rb5, runBlock_reg _ _ _ (23 : Fin 32) s4.zero (by decide), g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb5, runBlock_reg _ _ _ (24 : Fin 32) s4.zero (by decide), g4_24]
  have g5_25 : reg n5 (25 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb5, runBlock_reg _ _ _ (25 : Fin 32) s4.zero (by decide), g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = x26 := by
    rw [rb5, runBlock_reg _ _ _ (26 : Fin 32) s4.zero (by decide), g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb5, runBlock_reg _ _ _ (27 : Fin 32) s4.zero (by decide), g4_27]
  have g5_10 : reg n5 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, svEcT1a16b2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_8, g4_9, g4_18, g4_19, g4_20, g4_21, g4_22, g4_23, g4_24, g4_25, g4_26, g4_27, s4.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g5_11 : reg n5 a1 = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, svEcT1a16b2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_8, g4_9, g4_18, g4_19, g4_20, g4_21, g4_22, g4_23, g4_24, g4_25, g4_26, g4_27, s4.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g5_12 : reg n5 a2 = BitVec.ofNat 32 0x60 := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, svEcT1a16b2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_8, g4_9, g4_18, g4_19, g4_20, g4_21, g4_22, g4_23, g4_24, g4_25, g4_26, g4_27, s4.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x1380, 0x80)] := by rw [m5]; exact keep_kk4
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
  have w5_78 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m5]; exact w4_78
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
  have b5_440 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) = gs := by rw [m5]; exact b4_440
  have b5_a40 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = gs := by rw [m5]; exact b4_a40
  have b5_1040 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = gs := by rw [m5]; exact b4_1040
  have b5_14a0 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := by rw [m5]; exact b4_14a0
  have a5_240 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m5]; exact a4_240
  have a5_260 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m5]; exact a4_260
  have a5_280 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m5]; exact a4_280
  have a5_2a0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m5]; exact a4_2a0
  have a5_2c0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m5]; exact a4_2c0
  have a5_2e0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m5]; exact a4_2e0
  have a5_380 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m5]; exact a4_380
  have a5_400 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m5]; exact a4_400
  have a5_13e0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U2 := by rw [m5]; exact a4_13e0
  have a5_14e0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x14E0) 8 = U1 := by rw [m5]; exact a4_14e0
  have a5_1560 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1560) 8 = U2 := by rw [m5]; exact a4_1560
  have p5_320 : ptF n5.mem B 0x320 = P0 := by rw [m5]; exact p4_320
  have p5_3a0 : ptF n5.mem B 0x3A0 = P1 := by rw [m5]; exact p4_3a0
  have p5_420 : ptF n5.mem B 0x420 = tbl2 P0 0 := by rw [m5]; exact p4_420
  have p5_480 : ptF n5.mem B 0x480 = tbl2 P0 1 := by rw [m5]; exact p4_480
  have p5_4e0 : ptF n5.mem B 0x4E0 = tbl2 P0 2 := by rw [m5]; exact p4_4e0
  have p5_540 : ptF n5.mem B 0x540 = tbl2 P0 3 := by rw [m5]; exact p4_540
  have p5_5a0 : ptF n5.mem B 0x5A0 = tbl2 P0 4 := by rw [m5]; exact p4_5a0
  have p5_600 : ptF n5.mem B 0x600 = tbl2 P0 5 := by rw [m5]; exact p4_600
  have p5_660 : ptF n5.mem B 0x660 = tbl2 P0 6 := by rw [m5]; exact p4_660
  have p5_6c0 : ptF n5.mem B 0x6C0 = tbl2 P0 7 := by rw [m5]; exact p4_6c0
  have p5_a20 : ptF n5.mem B 0xA20 = tbl2 P0 0 := by rw [m5]; exact p4_a20
  have p5_a80 : ptF n5.mem B 0xA80 = tbl2 P0 1 := by rw [m5]; exact p4_a80
  have p5_ae0 : ptF n5.mem B 0xAE0 = tbl2 P0 2 := by rw [m5]; exact p4_ae0
  have p5_b40 : ptF n5.mem B 0xB40 = tbl2 P0 3 := by rw [m5]; exact p4_b40
  have p5_ba0 : ptF n5.mem B 0xBA0 = tbl2 P0 4 := by rw [m5]; exact p4_ba0
  have p5_c00 : ptF n5.mem B 0xC00 = tbl2 P0 5 := by rw [m5]; exact p4_c00
  have p5_c60 : ptF n5.mem B 0xC60 = tbl2 P0 6 := by rw [m5]; exact p4_c60
  have p5_cc0 : ptF n5.mem B 0xCC0 = tbl2 P0 7 := by rw [m5]; exact p4_cc0
  have p5_1020 : ptF n5.mem B 0x1020 = tbl2 P0 0 := by rw [m5]; exact p4_1020
  have p5_1080 : ptF n5.mem B 0x1080 = tbl2 P0 1 := by rw [m5]; exact p4_1080
  have p5_10e0 : ptF n5.mem B 0x10E0 = tbl2 P0 2 := by rw [m5]; exact p4_10e0
  have p5_1140 : ptF n5.mem B 0x1140 = tbl2 P0 3 := by rw [m5]; exact p4_1140
  have p5_11a0 : ptF n5.mem B 0x11A0 = tbl2 P0 4 := by rw [m5]; exact p4_11a0
  have p5_1200 : ptF n5.mem B 0x1200 = tbl2 P0 5 := by rw [m5]; exact p4_1200
  have p5_1260 : ptF n5.mem B 0x1260 = tbl2 P0 6 := by rw [m5]; exact p4_1260
  have p5_12c0 : ptF n5.mem B 0x12C0 = tbl2 P0 7 := by rw [m5]; exact p4_12c0
  have p5_1320 : ptF n5.mem B 0x1320 = ptDbl2 P0 := by rw [m5]; exact p4_1320
  have p5_1380 : ptF n5.mem B 0x1380 = P1 := by rw [m5]; exact p4_1380
  have p5_1480 : ptF n5.mem B 0x1480 = P0 := by rw [m5]; exact p4_1480
  have p5_1500 : ptF n5.mem B 0x1500 = P1 := by rw [m5]; exact p4_1500
  clear p4_1500 p4_1480 p4_1380 p4_1320 p4_12c0 p4_1260 p4_1200 p4_11a0 p4_1140 p4_10e0 p4_1080 p4_1020 p4_cc0 p4_c60 p4_c00 p4_ba0 p4_b40 p4_ae0 p4_a80 p4_a20 p4_6c0 p4_660 p4_600 p4_5a0 p4_540 p4_4e0 p4_480 p4_420 p4_3a0 p4_320 a4_1560 a4_14e0 a4_13e0 a4_400 a4_380 a4_2e0 a4_2c0 a4_2a0 a4_280 a4_260 a4_240 b4_14a0 b4_1040 b4_a40 b4_440 w4_130 w4_12c w4_128 w4_124 w4_120 w4_11c w4_118 w4_114 w4_110 w4_10c w4_108 w4_104 w4_100 w4_fc w4_f8 w4_f4 w4_f0 w4_ec w4_e8 w4_e4 w4_e0 w4_dc w4_d8 w4_d4 w4_d0 w4_cc w4_c8 w4_c4 w4_c0 w4_bc w4_b8 w4_b4 w4_b0 w4_ac w4_a8 w4_a4 w4_a0 w4_9c w4_98 w4_94 w4_90 w4_8c w4_88 w4_84 w4_80 w4_7c w4_78 w4_70 w4_6c w4_68 w4_64 w4_60 w4_5c w4_58 w4_54 w4_50 w4_4c w4_48 w4_44 w4_40 w4_3c w4_38 w4_34 w4_30 w4_2c w4_28 w4_24 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_9 g4_8 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 m4 s4 u4 d4
  -- 0x16BA: memcpy from outside the stack
  obtain ⟨n6, P6, K6, X6⟩ := sv_mcRo2 (c := 0x420) (N := 0x60) F RS E5 s5 sv_at_16ba sv_at_16be
    (by decide) (by decide) g5_2 g5_10 g5_11 g5_12 (by decide) (Or.inr ⟨by decide, by decide⟩)
  have s6 := P6.st
  have fr6 := P6.fr
  have t6 : Steps n0 n6 := t5.trans P6.steps
  have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : SvCode n6.mem := E5.fr F fr6
  have V6 : SvSaves B n6.mem v := V5.keep K6 (by decide)
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [P6.regs sp (by decide), g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P6.regs (3 : Fin 32) (by decide), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P6.regs (4 : Fin 32) (by decide), g5_4]
  have g6_8 : reg n6 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x420 := by rw [P6.regs (8 : Fin 32) (by decide), g5_8]
  have g6_9 : reg n6 (9 : Fin 32) = BitVec.ofNat 32 0x8 := by rw [P6.regs (9 : Fin 32) (by decide), g5_9]
  have g6_18 : reg n6 (18 : Fin 32) = out := by rw [P6.regs (18 : Fin 32) (by decide), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [P6.regs (19 : Fin 32) (by decide), g5_19]
  have g6_20 : reg n6 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P6.regs (20 : Fin 32) (by decide), g5_20]
  have g6_21 : reg n6 (21 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P6.regs (21 : Fin 32) (by decide), g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [P6.regs (22 : Fin 32) (by decide), g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1500 := by rw [P6.regs (23 : Fin 32) (by decide), g5_23]
  have g6_24 : reg n6 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P6.regs (24 : Fin 32) (by decide), g5_24]
  have g6_25 : reg n6 (25 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [P6.regs (25 : Fin 32) (by decide), g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = x26 := by rw [P6.regs (26 : Fin 32) (by decide), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P6.regs (27 : Fin 32) (by decide), g5_27]
  have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x1380, 0x80), (0x420, 0x60)] := keep_kk5.trans K6.toL
  clear keep_kk5
  have w6_24 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K6.w32 (by decide) (by decide)).trans w5_24
  have w6_28 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K6.w32 (by decide) (by decide)).trans w5_28
  have w6_2c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K6.w32 (by decide) (by decide)).trans w5_2c
  have w6_30 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K6.w32 (by decide) (by decide)).trans w5_30
  have w6_34 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K6.w32 (by decide) (by decide)).trans w5_34
  have w6_38 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K6.w32 (by decide) (by decide)).trans w5_38
  have w6_3c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K6.w32 (by decide) (by decide)).trans w5_3c
  have w6_40 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K6.w32 (by decide) (by decide)).trans w5_40
  have w6_44 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K6.w32 (by decide) (by decide)).trans w5_44
  have w6_48 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K6.w32 (by decide) (by decide)).trans w5_48
  have w6_4c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K6.w32 (by decide) (by decide)).trans w5_4c
  have w6_50 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K6.w32 (by decide) (by decide)).trans w5_50
  have w6_54 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K6.w32 (by decide) (by decide)).trans w5_54
  have w6_58 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K6.w32 (by decide) (by decide)).trans w5_58
  have w6_5c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K6.w32 (by decide) (by decide)).trans w5_5c
  have w6_60 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K6.w32 (by decide) (by decide)).trans w5_60
  have w6_64 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K6.w32 (by decide) (by decide)).trans w5_64
  have w6_68 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K6.w32 (by decide) (by decide)).trans w5_68
  have w6_6c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K6.w32 (by decide) (by decide)).trans w5_6c
  have w6_70 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K6.w32 (by decide) (by decide)).trans w5_70
  have w6_78 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := (K6.w32 (by decide) (by decide)).trans w5_78
  have w6_7c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K6.w32 (by decide) (by decide)).trans w5_7c
  have w6_80 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K6.w32 (by decide) (by decide)).trans w5_80
  have w6_84 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K6.w32 (by decide) (by decide)).trans w5_84
  have w6_88 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K6.w32 (by decide) (by decide)).trans w5_88
  have w6_8c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K6.w32 (by decide) (by decide)).trans w5_8c
  have w6_90 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K6.w32 (by decide) (by decide)).trans w5_90
  have w6_94 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K6.w32 (by decide) (by decide)).trans w5_94
  have w6_98 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K6.w32 (by decide) (by decide)).trans w5_98
  have w6_9c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K6.w32 (by decide) (by decide)).trans w5_9c
  have w6_a0 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K6.w32 (by decide) (by decide)).trans w5_a0
  have w6_a4 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K6.w32 (by decide) (by decide)).trans w5_a4
  have w6_a8 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K6.w32 (by decide) (by decide)).trans w5_a8
  have w6_ac : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K6.w32 (by decide) (by decide)).trans w5_ac
  have w6_b0 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K6.w32 (by decide) (by decide)).trans w5_b0
  have w6_b4 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K6.w32 (by decide) (by decide)).trans w5_b4
  have w6_b8 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K6.w32 (by decide) (by decide)).trans w5_b8
  have w6_bc : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K6.w32 (by decide) (by decide)).trans w5_bc
  have w6_c0 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K6.w32 (by decide) (by decide)).trans w5_c0
  have w6_c4 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K6.w32 (by decide) (by decide)).trans w5_c4
  have w6_c8 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K6.w32 (by decide) (by decide)).trans w5_c8
  have w6_cc : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K6.w32 (by decide) (by decide)).trans w5_cc
  have w6_d0 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K6.w32 (by decide) (by decide)).trans w5_d0
  have w6_d4 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K6.w32 (by decide) (by decide)).trans w5_d4
  have w6_d8 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K6.w32 (by decide) (by decide)).trans w5_d8
  have w6_dc : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K6.w32 (by decide) (by decide)).trans w5_dc
  have w6_e0 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K6.w32 (by decide) (by decide)).trans w5_e0
  have w6_e4 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K6.w32 (by decide) (by decide)).trans w5_e4
  have w6_e8 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K6.w32 (by decide) (by decide)).trans w5_e8
  have w6_ec : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K6.w32 (by decide) (by decide)).trans w5_ec
  have w6_f0 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K6.w32 (by decide) (by decide)).trans w5_f0
  have w6_f4 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K6.w32 (by decide) (by decide)).trans w5_f4
  have w6_f8 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K6.w32 (by decide) (by decide)).trans w5_f8
  have w6_fc : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K6.w32 (by decide) (by decide)).trans w5_fc
  have w6_100 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K6.w32 (by decide) (by decide)).trans w5_100
  have w6_104 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K6.w32 (by decide) (by decide)).trans w5_104
  have w6_108 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K6.w32 (by decide) (by decide)).trans w5_108
  have w6_10c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K6.w32 (by decide) (by decide)).trans w5_10c
  have w6_110 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K6.w32 (by decide) (by decide)).trans w5_110
  have w6_114 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K6.w32 (by decide) (by decide)).trans w5_114
  have w6_118 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K6.w32 (by decide) (by decide)).trans w5_118
  have w6_11c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K6.w32 (by decide) (by decide)).trans w5_11c
  have w6_120 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K6.w32 (by decide) (by decide)).trans w5_120
  have w6_124 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K6.w32 (by decide) (by decide)).trans w5_124
  have w6_128 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K6.w32 (by decide) (by decide)).trans w5_128
  have w6_12c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K6.w32 (by decide) (by decide)).trans w5_12c
  have w6_130 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K6.w32 (by decide) (by decide)).trans w5_130
  have b6_a40 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = gs := (K6.b8 (by decide) (by decide)).trans b5_a40
  have b6_1040 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = gs := (K6.b8 (by decide) (by decide)).trans b5_1040
  have b6_14a0 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := (K6.b8 (by decide) (by decide)).trans b5_14a0
  have a6_240 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := (K6.acc (by decide) (by decide)).trans a5_240
  have a6_260 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := (K6.acc (by decide) (by decide)).trans a5_260
  have a6_280 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := (K6.acc (by decide) (by decide)).trans a5_280
  have a6_2a0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K6.acc (by decide) (by decide)).trans a5_2a0
  have a6_2c0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K6.acc (by decide) (by decide)).trans a5_2c0
  have a6_2e0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K6.acc (by decide) (by decide)).trans a5_2e0
  have a6_380 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := (K6.acc (by decide) (by decide)).trans a5_380
  have a6_400 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := (K6.acc (by decide) (by decide)).trans a5_400
  have a6_13e0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U2 := (K6.acc (by decide) (by decide)).trans a5_13e0
  have a6_14e0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x14E0) 8 = U1 := (K6.acc (by decide) (by decide)).trans a5_14e0
  have a6_1560 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1560) 8 = U2 := (K6.acc (by decide) (by decide)).trans a5_1560
  have p6_320 : ptF n6.mem B 0x320 = P0 := (K6.pt (by decide) (by decide)).trans p5_320
  have p6_3a0 : ptF n6.mem B 0x3A0 = P1 := (K6.pt (by decide) (by decide)).trans p5_3a0
  have p6_480 : ptF n6.mem B 0x480 = tbl2 P0 1 := (K6.pt (by decide) (by decide)).trans p5_480
  have p6_4e0 : ptF n6.mem B 0x4E0 = tbl2 P0 2 := (K6.pt (by decide) (by decide)).trans p5_4e0
  have p6_540 : ptF n6.mem B 0x540 = tbl2 P0 3 := (K6.pt (by decide) (by decide)).trans p5_540
  have p6_5a0 : ptF n6.mem B 0x5A0 = tbl2 P0 4 := (K6.pt (by decide) (by decide)).trans p5_5a0
  have p6_600 : ptF n6.mem B 0x600 = tbl2 P0 5 := (K6.pt (by decide) (by decide)).trans p5_600
  have p6_660 : ptF n6.mem B 0x660 = tbl2 P0 6 := (K6.pt (by decide) (by decide)).trans p5_660
  have p6_6c0 : ptF n6.mem B 0x6C0 = tbl2 P0 7 := (K6.pt (by decide) (by decide)).trans p5_6c0
  have p6_a20 : ptF n6.mem B 0xA20 = tbl2 P0 0 := (K6.pt (by decide) (by decide)).trans p5_a20
  have p6_a80 : ptF n6.mem B 0xA80 = tbl2 P0 1 := (K6.pt (by decide) (by decide)).trans p5_a80
  have p6_ae0 : ptF n6.mem B 0xAE0 = tbl2 P0 2 := (K6.pt (by decide) (by decide)).trans p5_ae0
  have p6_b40 : ptF n6.mem B 0xB40 = tbl2 P0 3 := (K6.pt (by decide) (by decide)).trans p5_b40
  have p6_ba0 : ptF n6.mem B 0xBA0 = tbl2 P0 4 := (K6.pt (by decide) (by decide)).trans p5_ba0
  have p6_c00 : ptF n6.mem B 0xC00 = tbl2 P0 5 := (K6.pt (by decide) (by decide)).trans p5_c00
  have p6_c60 : ptF n6.mem B 0xC60 = tbl2 P0 6 := (K6.pt (by decide) (by decide)).trans p5_c60
  have p6_cc0 : ptF n6.mem B 0xCC0 = tbl2 P0 7 := (K6.pt (by decide) (by decide)).trans p5_cc0
  have p6_1020 : ptF n6.mem B 0x1020 = tbl2 P0 0 := (K6.pt (by decide) (by decide)).trans p5_1020
  have p6_1080 : ptF n6.mem B 0x1080 = tbl2 P0 1 := (K6.pt (by decide) (by decide)).trans p5_1080
  have p6_10e0 : ptF n6.mem B 0x10E0 = tbl2 P0 2 := (K6.pt (by decide) (by decide)).trans p5_10e0
  have p6_1140 : ptF n6.mem B 0x1140 = tbl2 P0 3 := (K6.pt (by decide) (by decide)).trans p5_1140
  have p6_11a0 : ptF n6.mem B 0x11A0 = tbl2 P0 4 := (K6.pt (by decide) (by decide)).trans p5_11a0
  have p6_1200 : ptF n6.mem B 0x1200 = tbl2 P0 5 := (K6.pt (by decide) (by decide)).trans p5_1200
  have p6_1260 : ptF n6.mem B 0x1260 = tbl2 P0 6 := (K6.pt (by decide) (by decide)).trans p5_1260
  have p6_12c0 : ptF n6.mem B 0x12C0 = tbl2 P0 7 := (K6.pt (by decide) (by decide)).trans p5_12c0
  have p6_1320 : ptF n6.mem B 0x1320 = ptDbl2 P0 := (K6.pt (by decide) (by decide)).trans p5_1320
  have p6_1380 : ptF n6.mem B 0x1380 = P1 := (K6.pt (by decide) (by decide)).trans p5_1380
  have p6_1480 : ptF n6.mem B 0x1480 = P0 := (K6.pt (by decide) (by decide)).trans p5_1480
  have p6_1500 : ptF n6.mem B 0x1500 = P1 := (K6.pt (by decide) (by decide)).trans p5_1500
  have q6_420 : ∀ j, j < 96 → n6.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) :=
    fun j hj => (X6 j hj).trans (fR5 _ (SvRo2.r RS (Or.inr ⟨by decide, by decide⟩) hj))
  clear p5_1500 p5_1480 p5_1380 p5_1320 p5_12c0 p5_1260 p5_1200 p5_11a0 p5_1140 p5_10e0 p5_1080 p5_1020 p5_cc0 p5_c60 p5_c00 p5_ba0 p5_b40 p5_ae0 p5_a80 p5_a20 p5_6c0 p5_660 p5_600 p5_5a0 p5_540 p5_4e0 p5_480 p5_420 p5_3a0 p5_320 a5_1560 a5_14e0 a5_13e0 a5_400 a5_380 a5_2e0 a5_2c0 a5_2a0 a5_280 a5_260 a5_240 b5_14a0 b5_1040 b5_a40 b5_440 w5_130 w5_12c w5_128 w5_124 w5_120 w5_11c w5_118 w5_114 w5_110 w5_10c w5_108 w5_104 w5_100 w5_fc w5_f8 w5_f4 w5_f0 w5_ec w5_e8 w5_e4 w5_e0 w5_dc w5_d8 w5_d4 w5_d0 w5_cc w5_c8 w5_c4 w5_c0 w5_bc w5_b8 w5_b4 w5_b0 w5_ac w5_a8 w5_a4 w5_a0 w5_9c w5_98 w5_94 w5_90 w5_8c w5_88 w5_84 w5_80 w5_7c w5_78 w5_70 w5_6c w5_68 w5_64 w5_60 w5_5c w5_58 w5_54 w5_50 w5_4c w5_48 w5_44 w5_40 w5_3c w5_38 w5_34 w5_30 w5_2c w5_28 w5_24 g5_12 g5_11 g5_10 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_9 g5_8 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 rb5 s5 m5 u5 c5
  -- 0x16C2
  obtain ⟨n7, c7, u7⟩ := s6.block svEcT1a16c2 E6.self svEcT1a16c2_end
    ⟨trivial, trivial, trivial⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have s7 : St n7.mem SV n7 0x16C8 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have rb7 : ∀ q, reg n7 q = (runBlock svEcT1a16c2 (n6.mem, reg n6)).2 q := fun q => by rw [u7.regs]
  have fr7 : ∀ x, SvR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
  have t7 : Steps n0 n7 := t6.trans c7
  have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : SvCode n7.mem := E6.fr F fr7
  have V7 : SvSaves B n7.mem v := V6.same m7
  have g7_2 : reg n7 sp = B + 0x21A0 := by
    rw [rb7, runBlock_reg _ _ _ sp s6.zero (by decide), g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb7, runBlock_reg _ _ _ (3 : Fin 32) s6.zero (by decide), g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb7, runBlock_reg _ _ _ (4 : Fin 32) s6.zero (by decide), g6_4]
  have g7_18 : reg n7 (18 : Fin 32) = out := by
    rw [rb7, runBlock_reg _ _ _ (18 : Fin 32) s6.zero (by decide), g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = bp := by
    rw [rb7, runBlock_reg _ _ _ (19 : Fin 32) s6.zero (by decide), g6_19]
  have g7_20 : reg n7 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb7, runBlock_reg _ _ _ (20 : Fin 32) s6.zero (by decide), g6_20]
  have g7_21 : reg n7 (21 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb7, runBlock_reg _ _ _ (21 : Fin 32) s6.zero (by decide), g6_21]
  have g7_22 : reg n7 (22 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb7, runBlock_reg _ _ _ (22 : Fin 32) s6.zero (by decide), g6_22]
  have g7_23 : reg n7 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1500 := by
    rw [rb7, runBlock_reg _ _ _ (23 : Fin 32) s6.zero (by decide), g6_23]
  have g7_24 : reg n7 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb7, runBlock_reg _ _ _ (24 : Fin 32) s6.zero (by decide), g6_24]
  have g7_25 : reg n7 (25 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb7, runBlock_reg _ _ _ (25 : Fin 32) s6.zero (by decide), g6_25]
  have g7_26 : reg n7 (26 : Fin 32) = x26 := by
    rw [rb7, runBlock_reg _ _ _ (26 : Fin 32) s6.zero (by decide), g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb7, runBlock_reg _ _ _ (27 : Fin 32) s6.zero (by decide), g6_27]
  have g7_8 : reg n7 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x480 := by
    rw [rb7]; simp +decide only [runBlock, BInstr.run, svEcT1a16c2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g6_2, g6_3, g6_4, g6_8, g6_9, g6_18, g6_19, g6_20, g6_21, g6_22, g6_23, g6_24, g6_25, g6_26, g6_27, s6.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g7_9 : reg n7 (9 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb7]; simp +decide only [runBlock, BInstr.run, svEcT1a16c2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g6_2, g6_3, g6_4, g6_8, g6_9, g6_18, g6_19, g6_20, g6_21, g6_22, g6_23, g6_24, g6_25, g6_26, g6_27, s6.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x1380, 0x80), (0x420, 0x60)] := by rw [m7]; exact keep_kk6
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
  have w7_78 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m7]; exact w6_78
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
  have b7_a40 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = gs := by rw [m7]; exact b6_a40
  have b7_1040 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = gs := by rw [m7]; exact b6_1040
  have b7_14a0 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := by rw [m7]; exact b6_14a0
  have q7_420 : ∀ j, j < 96 → n7.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m7]; exact q6_420 j hj
  have a7_240 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m7]; exact a6_240
  have a7_260 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m7]; exact a6_260
  have a7_280 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m7]; exact a6_280
  have a7_2a0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m7]; exact a6_2a0
  have a7_2c0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m7]; exact a6_2c0
  have a7_2e0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m7]; exact a6_2e0
  have a7_380 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m7]; exact a6_380
  have a7_400 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m7]; exact a6_400
  have a7_13e0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U2 := by rw [m7]; exact a6_13e0
  have a7_14e0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x14E0) 8 = U1 := by rw [m7]; exact a6_14e0
  have a7_1560 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1560) 8 = U2 := by rw [m7]; exact a6_1560
  have p7_320 : ptF n7.mem B 0x320 = P0 := by rw [m7]; exact p6_320
  have p7_3a0 : ptF n7.mem B 0x3A0 = P1 := by rw [m7]; exact p6_3a0
  have p7_480 : ptF n7.mem B 0x480 = tbl2 P0 1 := by rw [m7]; exact p6_480
  have p7_4e0 : ptF n7.mem B 0x4E0 = tbl2 P0 2 := by rw [m7]; exact p6_4e0
  have p7_540 : ptF n7.mem B 0x540 = tbl2 P0 3 := by rw [m7]; exact p6_540
  have p7_5a0 : ptF n7.mem B 0x5A0 = tbl2 P0 4 := by rw [m7]; exact p6_5a0
  have p7_600 : ptF n7.mem B 0x600 = tbl2 P0 5 := by rw [m7]; exact p6_600
  have p7_660 : ptF n7.mem B 0x660 = tbl2 P0 6 := by rw [m7]; exact p6_660
  have p7_6c0 : ptF n7.mem B 0x6C0 = tbl2 P0 7 := by rw [m7]; exact p6_6c0
  have p7_a20 : ptF n7.mem B 0xA20 = tbl2 P0 0 := by rw [m7]; exact p6_a20
  have p7_a80 : ptF n7.mem B 0xA80 = tbl2 P0 1 := by rw [m7]; exact p6_a80
  have p7_ae0 : ptF n7.mem B 0xAE0 = tbl2 P0 2 := by rw [m7]; exact p6_ae0
  have p7_b40 : ptF n7.mem B 0xB40 = tbl2 P0 3 := by rw [m7]; exact p6_b40
  have p7_ba0 : ptF n7.mem B 0xBA0 = tbl2 P0 4 := by rw [m7]; exact p6_ba0
  have p7_c00 : ptF n7.mem B 0xC00 = tbl2 P0 5 := by rw [m7]; exact p6_c00
  have p7_c60 : ptF n7.mem B 0xC60 = tbl2 P0 6 := by rw [m7]; exact p6_c60
  have p7_cc0 : ptF n7.mem B 0xCC0 = tbl2 P0 7 := by rw [m7]; exact p6_cc0
  have p7_1020 : ptF n7.mem B 0x1020 = tbl2 P0 0 := by rw [m7]; exact p6_1020
  have p7_1080 : ptF n7.mem B 0x1080 = tbl2 P0 1 := by rw [m7]; exact p6_1080
  have p7_10e0 : ptF n7.mem B 0x10E0 = tbl2 P0 2 := by rw [m7]; exact p6_10e0
  have p7_1140 : ptF n7.mem B 0x1140 = tbl2 P0 3 := by rw [m7]; exact p6_1140
  have p7_11a0 : ptF n7.mem B 0x11A0 = tbl2 P0 4 := by rw [m7]; exact p6_11a0
  have p7_1200 : ptF n7.mem B 0x1200 = tbl2 P0 5 := by rw [m7]; exact p6_1200
  have p7_1260 : ptF n7.mem B 0x1260 = tbl2 P0 6 := by rw [m7]; exact p6_1260
  have p7_12c0 : ptF n7.mem B 0x12C0 = tbl2 P0 7 := by rw [m7]; exact p6_12c0
  have p7_1320 : ptF n7.mem B 0x1320 = ptDbl2 P0 := by rw [m7]; exact p6_1320
  have p7_1380 : ptF n7.mem B 0x1380 = P1 := by rw [m7]; exact p6_1380
  have p7_1480 : ptF n7.mem B 0x1480 = P0 := by rw [m7]; exact p6_1480
  have p7_1500 : ptF n7.mem B 0x1500 = P1 := by rw [m7]; exact p6_1500
  clear q6_420 p6_1500 p6_1480 p6_1380 p6_1320 p6_12c0 p6_1260 p6_1200 p6_11a0 p6_1140 p6_10e0 p6_1080 p6_1020 p6_cc0 p6_c60 p6_c00 p6_ba0 p6_b40 p6_ae0 p6_a80 p6_a20 p6_6c0 p6_660 p6_600 p6_5a0 p6_540 p6_4e0 p6_480 p6_3a0 p6_320 a6_1560 a6_14e0 a6_13e0 a6_400 a6_380 a6_2e0 a6_2c0 a6_2a0 a6_280 a6_260 a6_240 b6_14a0 b6_1040 b6_a40 w6_130 w6_12c w6_128 w6_124 w6_120 w6_11c w6_118 w6_114 w6_110 w6_10c w6_108 w6_104 w6_100 w6_fc w6_f8 w6_f4 w6_f0 w6_ec w6_e8 w6_e4 w6_e0 w6_dc w6_d8 w6_d4 w6_d0 w6_cc w6_c8 w6_c4 w6_c0 w6_bc w6_b8 w6_b4 w6_b0 w6_ac w6_a8 w6_a4 w6_a0 w6_9c w6_98 w6_94 w6_90 w6_8c w6_88 w6_84 w6_80 w6_7c w6_78 w6_70 w6_6c w6_68 w6_64 w6_60 w6_5c w6_58 w6_54 w6_50 w6_4c w6_48 w6_44 w6_40 w6_3c w6_38 w6_34 w6_30 w6_2c w6_28 w6_24 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_9 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 s6 X6 K6 P6
  -- 0x16C8: branch, taken
  obtain ⟨n8, d8, u8⟩ := s7.taken E7.self 0x16B2 sv_at_16c8
    (by decide) (by rw [g7_9, s7.zero]; decide)
  have s8 : St n8.mem SV n8 0x16B2 (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
  have m8 : n8.mem = n7.mem := u8.mem
  have fr8 : ∀ x, SvR B x → n8.mem x = n7.mem x := fun x _ => by rw [m8]
  have t8 : Steps n0 n8 := t7.trans (.single d8)
  have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : SvCode n8.mem := E7.fr F fr8
  have V8 : SvSaves B n8.mem v := V7.same m8
  have g8_2 : reg n8 sp = B + 0x21A0 := by rw [u8.regs, g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u8.regs, g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u8.regs, g7_4]
  have g8_8 : reg n8 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x480 := by rw [u8.regs, g7_8]
  have g8_9 : reg n8 (9 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [u8.regs, g7_9]
  have g8_18 : reg n8 (18 : Fin 32) = out := by rw [u8.regs, g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [u8.regs, g7_19]
  have g8_20 : reg n8 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u8.regs, g7_20]
  have g8_21 : reg n8 (21 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u8.regs, g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [u8.regs, g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1500 := by rw [u8.regs, g7_23]
  have g8_24 : reg n8 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u8.regs, g7_24]
  have g8_25 : reg n8 (25 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [u8.regs, g7_25]
  have g8_26 : reg n8 (26 : Fin 32) = x26 := by rw [u8.regs, g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u8.regs, g7_27]
  have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x1380, 0x80), (0x420, 0x60)] := by rw [m8]; exact keep_kk7
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
  have w8_78 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m8]; exact w7_78
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
  have b8_a40 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = gs := by rw [m8]; exact b7_a40
  have b8_1040 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = gs := by rw [m8]; exact b7_1040
  have b8_14a0 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := by rw [m8]; exact b7_14a0
  have q8_420 : ∀ j, j < 96 → n8.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m8]; exact q7_420 j hj
  have a8_240 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m8]; exact a7_240
  have a8_260 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m8]; exact a7_260
  have a8_280 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m8]; exact a7_280
  have a8_2a0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m8]; exact a7_2a0
  have a8_2c0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m8]; exact a7_2c0
  have a8_2e0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m8]; exact a7_2e0
  have a8_380 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m8]; exact a7_380
  have a8_400 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m8]; exact a7_400
  have a8_13e0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U2 := by rw [m8]; exact a7_13e0
  have a8_14e0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x14E0) 8 = U1 := by rw [m8]; exact a7_14e0
  have a8_1560 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1560) 8 = U2 := by rw [m8]; exact a7_1560
  have p8_320 : ptF n8.mem B 0x320 = P0 := by rw [m8]; exact p7_320
  have p8_3a0 : ptF n8.mem B 0x3A0 = P1 := by rw [m8]; exact p7_3a0
  have p8_480 : ptF n8.mem B 0x480 = tbl2 P0 1 := by rw [m8]; exact p7_480
  have p8_4e0 : ptF n8.mem B 0x4E0 = tbl2 P0 2 := by rw [m8]; exact p7_4e0
  have p8_540 : ptF n8.mem B 0x540 = tbl2 P0 3 := by rw [m8]; exact p7_540
  have p8_5a0 : ptF n8.mem B 0x5A0 = tbl2 P0 4 := by rw [m8]; exact p7_5a0
  have p8_600 : ptF n8.mem B 0x600 = tbl2 P0 5 := by rw [m8]; exact p7_600
  have p8_660 : ptF n8.mem B 0x660 = tbl2 P0 6 := by rw [m8]; exact p7_660
  have p8_6c0 : ptF n8.mem B 0x6C0 = tbl2 P0 7 := by rw [m8]; exact p7_6c0
  have p8_a20 : ptF n8.mem B 0xA20 = tbl2 P0 0 := by rw [m8]; exact p7_a20
  have p8_a80 : ptF n8.mem B 0xA80 = tbl2 P0 1 := by rw [m8]; exact p7_a80
  have p8_ae0 : ptF n8.mem B 0xAE0 = tbl2 P0 2 := by rw [m8]; exact p7_ae0
  have p8_b40 : ptF n8.mem B 0xB40 = tbl2 P0 3 := by rw [m8]; exact p7_b40
  have p8_ba0 : ptF n8.mem B 0xBA0 = tbl2 P0 4 := by rw [m8]; exact p7_ba0
  have p8_c00 : ptF n8.mem B 0xC00 = tbl2 P0 5 := by rw [m8]; exact p7_c00
  have p8_c60 : ptF n8.mem B 0xC60 = tbl2 P0 6 := by rw [m8]; exact p7_c60
  have p8_cc0 : ptF n8.mem B 0xCC0 = tbl2 P0 7 := by rw [m8]; exact p7_cc0
  have p8_1020 : ptF n8.mem B 0x1020 = tbl2 P0 0 := by rw [m8]; exact p7_1020
  have p8_1080 : ptF n8.mem B 0x1080 = tbl2 P0 1 := by rw [m8]; exact p7_1080
  have p8_10e0 : ptF n8.mem B 0x10E0 = tbl2 P0 2 := by rw [m8]; exact p7_10e0
  have p8_1140 : ptF n8.mem B 0x1140 = tbl2 P0 3 := by rw [m8]; exact p7_1140
  have p8_11a0 : ptF n8.mem B 0x11A0 = tbl2 P0 4 := by rw [m8]; exact p7_11a0
  have p8_1200 : ptF n8.mem B 0x1200 = tbl2 P0 5 := by rw [m8]; exact p7_1200
  have p8_1260 : ptF n8.mem B 0x1260 = tbl2 P0 6 := by rw [m8]; exact p7_1260
  have p8_12c0 : ptF n8.mem B 0x12C0 = tbl2 P0 7 := by rw [m8]; exact p7_12c0
  have p8_1320 : ptF n8.mem B 0x1320 = ptDbl2 P0 := by rw [m8]; exact p7_1320
  have p8_1380 : ptF n8.mem B 0x1380 = P1 := by rw [m8]; exact p7_1380
  have p8_1480 : ptF n8.mem B 0x1480 = P0 := by rw [m8]; exact p7_1480
  have p8_1500 : ptF n8.mem B 0x1500 = P1 := by rw [m8]; exact p7_1500
  clear p7_1500 p7_1480 p7_1380 p7_1320 p7_12c0 p7_1260 p7_1200 p7_11a0 p7_1140 p7_10e0 p7_1080 p7_1020 p7_cc0 p7_c60 p7_c00 p7_ba0 p7_b40 p7_ae0 p7_a80 p7_a20 p7_6c0 p7_660 p7_600 p7_5a0 p7_540 p7_4e0 p7_480 p7_3a0 p7_320 a7_1560 a7_14e0 a7_13e0 a7_400 a7_380 a7_2e0 a7_2c0 a7_2a0 a7_280 a7_260 a7_240 q7_420 b7_14a0 b7_1040 b7_a40 w7_130 w7_12c w7_128 w7_124 w7_120 w7_11c w7_118 w7_114 w7_110 w7_10c w7_108 w7_104 w7_100 w7_fc w7_f8 w7_f4 w7_f0 w7_ec w7_e8 w7_e4 w7_e0 w7_dc w7_d8 w7_d4 w7_d0 w7_cc w7_c8 w7_c4 w7_c0 w7_bc w7_b8 w7_b4 w7_b0 w7_ac w7_a8 w7_a4 w7_a0 w7_9c w7_98 w7_94 w7_90 w7_8c w7_88 w7_84 w7_80 w7_7c w7_78 w7_70 w7_6c w7_68 w7_64 w7_60 w7_5c w7_58 w7_54 w7_50 w7_4c w7_48 w7_44 w7_40 w7_3c w7_38 w7_34 w7_30 w7_2c w7_28 w7_24 g7_9 g7_8 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 rb7 s7 m7 u7 c7
  -- 0x16B2
  obtain ⟨n9, c9, u9⟩ := s8.block svEcT1a16b2 E8.self svEcT1a16b2_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m9 : n9.mem = n8.mem := u9.mem
  have s9 : St n9.mem SV n9 0x16BA (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have rb9 : ∀ q, reg n9 q = (runBlock svEcT1a16b2 (n8.mem, reg n8)).2 q := fun q => by rw [u9.regs]
  have fr9 : ∀ x, SvR B x → n9.mem x = n8.mem x := fun x _ => by rw [m9]
  have t9 : Steps n0 n9 := t8.trans c9
  have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : SvCode n9.mem := E8.fr F fr9
  have V9 : SvSaves B n9.mem v := V8.same m9
  have g9_2 : reg n9 sp = B + 0x21A0 := by
    rw [rb9, runBlock_reg _ _ _ sp s8.zero (by decide), g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb9, runBlock_reg _ _ _ (3 : Fin 32) s8.zero (by decide), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb9, runBlock_reg _ _ _ (4 : Fin 32) s8.zero (by decide), g8_4]
  have g9_8 : reg n9 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x480 := by
    rw [rb9, runBlock_reg _ _ _ (8 : Fin 32) s8.zero (by decide), g8_8]
  have g9_9 : reg n9 (9 : Fin 32) = BitVec.ofNat 32 0x7 := by
    rw [rb9, runBlock_reg _ _ _ (9 : Fin 32) s8.zero (by decide), g8_9]
  have g9_18 : reg n9 (18 : Fin 32) = out := by
    rw [rb9, runBlock_reg _ _ _ (18 : Fin 32) s8.zero (by decide), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by
    rw [rb9, runBlock_reg _ _ _ (19 : Fin 32) s8.zero (by decide), g8_19]
  have g9_20 : reg n9 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb9, runBlock_reg _ _ _ (20 : Fin 32) s8.zero (by decide), g8_20]
  have g9_21 : reg n9 (21 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb9, runBlock_reg _ _ _ (21 : Fin 32) s8.zero (by decide), g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb9, runBlock_reg _ _ _ (22 : Fin 32) s8.zero (by decide), g8_22]
  have g9_23 : reg n9 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1500 := by
    rw [rb9, runBlock_reg _ _ _ (23 : Fin 32) s8.zero (by decide), g8_23]
  have g9_24 : reg n9 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb9, runBlock_reg _ _ _ (24 : Fin 32) s8.zero (by decide), g8_24]
  have g9_25 : reg n9 (25 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb9, runBlock_reg _ _ _ (25 : Fin 32) s8.zero (by decide), g8_25]
  have g9_26 : reg n9 (26 : Fin 32) = x26 := by
    rw [rb9, runBlock_reg _ _ _ (26 : Fin 32) s8.zero (by decide), g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb9, runBlock_reg _ _ _ (27 : Fin 32) s8.zero (by decide), g8_27]
  have g9_10 : reg n9 a0 = B + 0x21A0 + BitVec.ofNat 32 0x480 := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, svEcT1a16b2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g8_2, g8_3, g8_4, g8_8, g8_9, g8_18, g8_19, g8_20, g8_21, g8_22, g8_23, g8_24, g8_25, g8_26, g8_27, s8.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g9_11 : reg n9 a1 = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, svEcT1a16b2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g8_2, g8_3, g8_4, g8_8, g8_9, g8_18, g8_19, g8_20, g8_21, g8_22, g8_23, g8_24, g8_25, g8_26, g8_27, s8.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g9_12 : reg n9 a2 = BitVec.ofNat 32 0x60 := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, svEcT1a16b2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g8_2, g8_3, g8_4, g8_8, g8_9, g8_18, g8_19, g8_20, g8_21, g8_22, g8_23, g8_24, g8_25, g8_26, g8_27, s8.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x1380, 0x80), (0x420, 0x60)] := by rw [m9]; exact keep_kk8
  clear keep_kk8
  have w9_24 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m9]; exact w8_24
  have w9_28 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m9]; exact w8_28
  have w9_2c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m9]; exact w8_2c
  have w9_30 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m9]; exact w8_30
  have w9_34 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m9]; exact w8_34
  have w9_38 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m9]; exact w8_38
  have w9_3c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m9]; exact w8_3c
  have w9_40 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m9]; exact w8_40
  have w9_44 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m9]; exact w8_44
  have w9_48 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m9]; exact w8_48
  have w9_4c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m9]; exact w8_4c
  have w9_50 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m9]; exact w8_50
  have w9_54 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m9]; exact w8_54
  have w9_58 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m9]; exact w8_58
  have w9_5c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m9]; exact w8_5c
  have w9_60 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m9]; exact w8_60
  have w9_64 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m9]; exact w8_64
  have w9_68 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m9]; exact w8_68
  have w9_6c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m9]; exact w8_6c
  have w9_70 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m9]; exact w8_70
  have w9_78 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m9]; exact w8_78
  have w9_7c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m9]; exact w8_7c
  have w9_80 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m9]; exact w8_80
  have w9_84 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m9]; exact w8_84
  have w9_88 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m9]; exact w8_88
  have w9_8c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m9]; exact w8_8c
  have w9_90 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m9]; exact w8_90
  have w9_94 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m9]; exact w8_94
  have w9_98 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m9]; exact w8_98
  have w9_9c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m9]; exact w8_9c
  have w9_a0 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m9]; exact w8_a0
  have w9_a4 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m9]; exact w8_a4
  have w9_a8 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m9]; exact w8_a8
  have w9_ac : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m9]; exact w8_ac
  have w9_b0 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m9]; exact w8_b0
  have w9_b4 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m9]; exact w8_b4
  have w9_b8 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m9]; exact w8_b8
  have w9_bc : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m9]; exact w8_bc
  have w9_c0 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m9]; exact w8_c0
  have w9_c4 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m9]; exact w8_c4
  have w9_c8 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m9]; exact w8_c8
  have w9_cc : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m9]; exact w8_cc
  have w9_d0 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m9]; exact w8_d0
  have w9_d4 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m9]; exact w8_d4
  have w9_d8 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m9]; exact w8_d8
  have w9_dc : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m9]; exact w8_dc
  have w9_e0 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m9]; exact w8_e0
  have w9_e4 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m9]; exact w8_e4
  have w9_e8 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m9]; exact w8_e8
  have w9_ec : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m9]; exact w8_ec
  have w9_f0 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m9]; exact w8_f0
  have w9_f4 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m9]; exact w8_f4
  have w9_f8 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m9]; exact w8_f8
  have w9_fc : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m9]; exact w8_fc
  have w9_100 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m9]; exact w8_100
  have w9_104 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m9]; exact w8_104
  have w9_108 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m9]; exact w8_108
  have w9_10c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m9]; exact w8_10c
  have w9_110 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m9]; exact w8_110
  have w9_114 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m9]; exact w8_114
  have w9_118 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m9]; exact w8_118
  have w9_11c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m9]; exact w8_11c
  have w9_120 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m9]; exact w8_120
  have w9_124 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m9]; exact w8_124
  have w9_128 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m9]; exact w8_128
  have w9_12c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m9]; exact w8_12c
  have w9_130 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m9]; exact w8_130
  have b9_a40 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = gs := by rw [m9]; exact b8_a40
  have b9_1040 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = gs := by rw [m9]; exact b8_1040
  have b9_14a0 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := by rw [m9]; exact b8_14a0
  have q9_420 : ∀ j, j < 96 → n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m9]; exact q8_420 j hj
  have a9_240 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m9]; exact a8_240
  have a9_260 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m9]; exact a8_260
  have a9_280 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m9]; exact a8_280
  have a9_2a0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m9]; exact a8_2a0
  have a9_2c0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m9]; exact a8_2c0
  have a9_2e0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m9]; exact a8_2e0
  have a9_380 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m9]; exact a8_380
  have a9_400 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m9]; exact a8_400
  have a9_13e0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U2 := by rw [m9]; exact a8_13e0
  have a9_14e0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x14E0) 8 = U1 := by rw [m9]; exact a8_14e0
  have a9_1560 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1560) 8 = U2 := by rw [m9]; exact a8_1560
  have p9_320 : ptF n9.mem B 0x320 = P0 := by rw [m9]; exact p8_320
  have p9_3a0 : ptF n9.mem B 0x3A0 = P1 := by rw [m9]; exact p8_3a0
  have p9_480 : ptF n9.mem B 0x480 = tbl2 P0 1 := by rw [m9]; exact p8_480
  have p9_4e0 : ptF n9.mem B 0x4E0 = tbl2 P0 2 := by rw [m9]; exact p8_4e0
  have p9_540 : ptF n9.mem B 0x540 = tbl2 P0 3 := by rw [m9]; exact p8_540
  have p9_5a0 : ptF n9.mem B 0x5A0 = tbl2 P0 4 := by rw [m9]; exact p8_5a0
  have p9_600 : ptF n9.mem B 0x600 = tbl2 P0 5 := by rw [m9]; exact p8_600
  have p9_660 : ptF n9.mem B 0x660 = tbl2 P0 6 := by rw [m9]; exact p8_660
  have p9_6c0 : ptF n9.mem B 0x6C0 = tbl2 P0 7 := by rw [m9]; exact p8_6c0
  have p9_a20 : ptF n9.mem B 0xA20 = tbl2 P0 0 := by rw [m9]; exact p8_a20
  have p9_a80 : ptF n9.mem B 0xA80 = tbl2 P0 1 := by rw [m9]; exact p8_a80
  have p9_ae0 : ptF n9.mem B 0xAE0 = tbl2 P0 2 := by rw [m9]; exact p8_ae0
  have p9_b40 : ptF n9.mem B 0xB40 = tbl2 P0 3 := by rw [m9]; exact p8_b40
  have p9_ba0 : ptF n9.mem B 0xBA0 = tbl2 P0 4 := by rw [m9]; exact p8_ba0
  have p9_c00 : ptF n9.mem B 0xC00 = tbl2 P0 5 := by rw [m9]; exact p8_c00
  have p9_c60 : ptF n9.mem B 0xC60 = tbl2 P0 6 := by rw [m9]; exact p8_c60
  have p9_cc0 : ptF n9.mem B 0xCC0 = tbl2 P0 7 := by rw [m9]; exact p8_cc0
  have p9_1020 : ptF n9.mem B 0x1020 = tbl2 P0 0 := by rw [m9]; exact p8_1020
  have p9_1080 : ptF n9.mem B 0x1080 = tbl2 P0 1 := by rw [m9]; exact p8_1080
  have p9_10e0 : ptF n9.mem B 0x10E0 = tbl2 P0 2 := by rw [m9]; exact p8_10e0
  have p9_1140 : ptF n9.mem B 0x1140 = tbl2 P0 3 := by rw [m9]; exact p8_1140
  have p9_11a0 : ptF n9.mem B 0x11A0 = tbl2 P0 4 := by rw [m9]; exact p8_11a0
  have p9_1200 : ptF n9.mem B 0x1200 = tbl2 P0 5 := by rw [m9]; exact p8_1200
  have p9_1260 : ptF n9.mem B 0x1260 = tbl2 P0 6 := by rw [m9]; exact p8_1260
  have p9_12c0 : ptF n9.mem B 0x12C0 = tbl2 P0 7 := by rw [m9]; exact p8_12c0
  have p9_1320 : ptF n9.mem B 0x1320 = ptDbl2 P0 := by rw [m9]; exact p8_1320
  have p9_1380 : ptF n9.mem B 0x1380 = P1 := by rw [m9]; exact p8_1380
  have p9_1480 : ptF n9.mem B 0x1480 = P0 := by rw [m9]; exact p8_1480
  have p9_1500 : ptF n9.mem B 0x1500 = P1 := by rw [m9]; exact p8_1500
  clear p8_1500 p8_1480 p8_1380 p8_1320 p8_12c0 p8_1260 p8_1200 p8_11a0 p8_1140 p8_10e0 p8_1080 p8_1020 p8_cc0 p8_c60 p8_c00 p8_ba0 p8_b40 p8_ae0 p8_a80 p8_a20 p8_6c0 p8_660 p8_600 p8_5a0 p8_540 p8_4e0 p8_480 p8_3a0 p8_320 a8_1560 a8_14e0 a8_13e0 a8_400 a8_380 a8_2e0 a8_2c0 a8_2a0 a8_280 a8_260 a8_240 q8_420 b8_14a0 b8_1040 b8_a40 w8_130 w8_12c w8_128 w8_124 w8_120 w8_11c w8_118 w8_114 w8_110 w8_10c w8_108 w8_104 w8_100 w8_fc w8_f8 w8_f4 w8_f0 w8_ec w8_e8 w8_e4 w8_e0 w8_dc w8_d8 w8_d4 w8_d0 w8_cc w8_c8 w8_c4 w8_c0 w8_bc w8_b8 w8_b4 w8_b0 w8_ac w8_a8 w8_a4 w8_a0 w8_9c w8_98 w8_94 w8_90 w8_8c w8_88 w8_84 w8_80 w8_7c w8_78 w8_70 w8_6c w8_68 w8_64 w8_60 w8_5c w8_58 w8_54 w8_50 w8_4c w8_48 w8_44 w8_40 w8_3c w8_38 w8_34 w8_30 w8_2c w8_28 w8_24 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_9 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 m8 s8 u8 d8
  -- 0x16BA: memcpy from outside the stack
  obtain ⟨n10, P10, K10, X10⟩ := sv_mcRo2 (c := 0x480) (N := 0x60) F RS E9 s9 sv_at_16ba sv_at_16be
    (by decide) (by decide) g9_2 g9_10 g9_11 g9_12 (by decide) (Or.inr ⟨by decide, by decide⟩)
  have s10 := P10.st
  have fr10 := P10.fr
  have t10 : Steps n0 n10 := t9.trans P10.steps
  have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : SvCode n10.mem := E9.fr F fr10
  have V10 : SvSaves B n10.mem v := V9.keep K10 (by decide)
  have g10_2 : reg n10 sp = B + 0x21A0 := by rw [P10.regs sp (by decide), g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P10.regs (3 : Fin 32) (by decide), g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P10.regs (4 : Fin 32) (by decide), g9_4]
  have g10_8 : reg n10 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x480 := by rw [P10.regs (8 : Fin 32) (by decide), g9_8]
  have g10_9 : reg n10 (9 : Fin 32) = BitVec.ofNat 32 0x7 := by rw [P10.regs (9 : Fin 32) (by decide), g9_9]
  have g10_18 : reg n10 (18 : Fin 32) = out := by rw [P10.regs (18 : Fin 32) (by decide), g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [P10.regs (19 : Fin 32) (by decide), g9_19]
  have g10_20 : reg n10 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P10.regs (20 : Fin 32) (by decide), g9_20]
  have g10_21 : reg n10 (21 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P10.regs (21 : Fin 32) (by decide), g9_21]
  have g10_22 : reg n10 (22 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [P10.regs (22 : Fin 32) (by decide), g9_22]
  have g10_23 : reg n10 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1500 := by rw [P10.regs (23 : Fin 32) (by decide), g9_23]
  have g10_24 : reg n10 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P10.regs (24 : Fin 32) (by decide), g9_24]
  have g10_25 : reg n10 (25 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [P10.regs (25 : Fin 32) (by decide), g9_25]
  have g10_26 : reg n10 (26 : Fin 32) = x26 := by rw [P10.regs (26 : Fin 32) (by decide), g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P10.regs (27 : Fin 32) (by decide), g9_27]
  have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x1380, 0x80), (0x420, 0x60), (0x480, 0x60)] := keep_kk9.trans K10.toL
  clear keep_kk9
  have w10_24 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K10.w32 (by decide) (by decide)).trans w9_24
  have w10_28 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K10.w32 (by decide) (by decide)).trans w9_28
  have w10_2c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K10.w32 (by decide) (by decide)).trans w9_2c
  have w10_30 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K10.w32 (by decide) (by decide)).trans w9_30
  have w10_34 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K10.w32 (by decide) (by decide)).trans w9_34
  have w10_38 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K10.w32 (by decide) (by decide)).trans w9_38
  have w10_3c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K10.w32 (by decide) (by decide)).trans w9_3c
  have w10_40 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K10.w32 (by decide) (by decide)).trans w9_40
  have w10_44 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K10.w32 (by decide) (by decide)).trans w9_44
  have w10_48 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K10.w32 (by decide) (by decide)).trans w9_48
  have w10_4c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K10.w32 (by decide) (by decide)).trans w9_4c
  have w10_50 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K10.w32 (by decide) (by decide)).trans w9_50
  have w10_54 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K10.w32 (by decide) (by decide)).trans w9_54
  have w10_58 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K10.w32 (by decide) (by decide)).trans w9_58
  have w10_5c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K10.w32 (by decide) (by decide)).trans w9_5c
  have w10_60 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K10.w32 (by decide) (by decide)).trans w9_60
  have w10_64 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K10.w32 (by decide) (by decide)).trans w9_64
  have w10_68 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K10.w32 (by decide) (by decide)).trans w9_68
  have w10_6c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K10.w32 (by decide) (by decide)).trans w9_6c
  have w10_70 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K10.w32 (by decide) (by decide)).trans w9_70
  have w10_78 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := (K10.w32 (by decide) (by decide)).trans w9_78
  have w10_7c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K10.w32 (by decide) (by decide)).trans w9_7c
  have w10_80 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K10.w32 (by decide) (by decide)).trans w9_80
  have w10_84 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K10.w32 (by decide) (by decide)).trans w9_84
  have w10_88 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K10.w32 (by decide) (by decide)).trans w9_88
  have w10_8c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K10.w32 (by decide) (by decide)).trans w9_8c
  have w10_90 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K10.w32 (by decide) (by decide)).trans w9_90
  have w10_94 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K10.w32 (by decide) (by decide)).trans w9_94
  have w10_98 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K10.w32 (by decide) (by decide)).trans w9_98
  have w10_9c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K10.w32 (by decide) (by decide)).trans w9_9c
  have w10_a0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K10.w32 (by decide) (by decide)).trans w9_a0
  have w10_a4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K10.w32 (by decide) (by decide)).trans w9_a4
  have w10_a8 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K10.w32 (by decide) (by decide)).trans w9_a8
  have w10_ac : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K10.w32 (by decide) (by decide)).trans w9_ac
  have w10_b0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K10.w32 (by decide) (by decide)).trans w9_b0
  have w10_b4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K10.w32 (by decide) (by decide)).trans w9_b4
  have w10_b8 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K10.w32 (by decide) (by decide)).trans w9_b8
  have w10_bc : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K10.w32 (by decide) (by decide)).trans w9_bc
  have w10_c0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K10.w32 (by decide) (by decide)).trans w9_c0
  have w10_c4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K10.w32 (by decide) (by decide)).trans w9_c4
  have w10_c8 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K10.w32 (by decide) (by decide)).trans w9_c8
  have w10_cc : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K10.w32 (by decide) (by decide)).trans w9_cc
  have w10_d0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K10.w32 (by decide) (by decide)).trans w9_d0
  have w10_d4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K10.w32 (by decide) (by decide)).trans w9_d4
  have w10_d8 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K10.w32 (by decide) (by decide)).trans w9_d8
  have w10_dc : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K10.w32 (by decide) (by decide)).trans w9_dc
  have w10_e0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K10.w32 (by decide) (by decide)).trans w9_e0
  have w10_e4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K10.w32 (by decide) (by decide)).trans w9_e4
  have w10_e8 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K10.w32 (by decide) (by decide)).trans w9_e8
  have w10_ec : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K10.w32 (by decide) (by decide)).trans w9_ec
  have w10_f0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K10.w32 (by decide) (by decide)).trans w9_f0
  have w10_f4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K10.w32 (by decide) (by decide)).trans w9_f4
  have w10_f8 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K10.w32 (by decide) (by decide)).trans w9_f8
  have w10_fc : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K10.w32 (by decide) (by decide)).trans w9_fc
  have w10_100 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K10.w32 (by decide) (by decide)).trans w9_100
  have w10_104 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K10.w32 (by decide) (by decide)).trans w9_104
  have w10_108 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K10.w32 (by decide) (by decide)).trans w9_108
  have w10_10c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K10.w32 (by decide) (by decide)).trans w9_10c
  have w10_110 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K10.w32 (by decide) (by decide)).trans w9_110
  have w10_114 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K10.w32 (by decide) (by decide)).trans w9_114
  have w10_118 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K10.w32 (by decide) (by decide)).trans w9_118
  have w10_11c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K10.w32 (by decide) (by decide)).trans w9_11c
  have w10_120 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K10.w32 (by decide) (by decide)).trans w9_120
  have w10_124 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K10.w32 (by decide) (by decide)).trans w9_124
  have w10_128 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K10.w32 (by decide) (by decide)).trans w9_128
  have w10_12c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K10.w32 (by decide) (by decide)).trans w9_12c
  have w10_130 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K10.w32 (by decide) (by decide)).trans w9_130
  have b10_a40 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = gs := (K10.b8 (by decide) (by decide)).trans b9_a40
  have b10_1040 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = gs := (K10.b8 (by decide) (by decide)).trans b9_1040
  have b10_14a0 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := (K10.b8 (by decide) (by decide)).trans b9_14a0
  have q10_420 : ∀ j, j < 96 → n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K10.range (by decide) (by decide) j hj).trans (q9_420 j hj)
  have a10_240 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := (K10.acc (by decide) (by decide)).trans a9_240
  have a10_260 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := (K10.acc (by decide) (by decide)).trans a9_260
  have a10_280 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := (K10.acc (by decide) (by decide)).trans a9_280
  have a10_2a0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K10.acc (by decide) (by decide)).trans a9_2a0
  have a10_2c0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K10.acc (by decide) (by decide)).trans a9_2c0
  have a10_2e0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K10.acc (by decide) (by decide)).trans a9_2e0
  have a10_380 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := (K10.acc (by decide) (by decide)).trans a9_380
  have a10_400 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := (K10.acc (by decide) (by decide)).trans a9_400
  have a10_13e0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U2 := (K10.acc (by decide) (by decide)).trans a9_13e0
  have a10_14e0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x14E0) 8 = U1 := (K10.acc (by decide) (by decide)).trans a9_14e0
  have a10_1560 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1560) 8 = U2 := (K10.acc (by decide) (by decide)).trans a9_1560
  have p10_320 : ptF n10.mem B 0x320 = P0 := (K10.pt (by decide) (by decide)).trans p9_320
  have p10_3a0 : ptF n10.mem B 0x3A0 = P1 := (K10.pt (by decide) (by decide)).trans p9_3a0
  have p10_4e0 : ptF n10.mem B 0x4E0 = tbl2 P0 2 := (K10.pt (by decide) (by decide)).trans p9_4e0
  have p10_540 : ptF n10.mem B 0x540 = tbl2 P0 3 := (K10.pt (by decide) (by decide)).trans p9_540
  have p10_5a0 : ptF n10.mem B 0x5A0 = tbl2 P0 4 := (K10.pt (by decide) (by decide)).trans p9_5a0
  have p10_600 : ptF n10.mem B 0x600 = tbl2 P0 5 := (K10.pt (by decide) (by decide)).trans p9_600
  have p10_660 : ptF n10.mem B 0x660 = tbl2 P0 6 := (K10.pt (by decide) (by decide)).trans p9_660
  have p10_6c0 : ptF n10.mem B 0x6C0 = tbl2 P0 7 := (K10.pt (by decide) (by decide)).trans p9_6c0
  have p10_a20 : ptF n10.mem B 0xA20 = tbl2 P0 0 := (K10.pt (by decide) (by decide)).trans p9_a20
  have p10_a80 : ptF n10.mem B 0xA80 = tbl2 P0 1 := (K10.pt (by decide) (by decide)).trans p9_a80
  have p10_ae0 : ptF n10.mem B 0xAE0 = tbl2 P0 2 := (K10.pt (by decide) (by decide)).trans p9_ae0
  have p10_b40 : ptF n10.mem B 0xB40 = tbl2 P0 3 := (K10.pt (by decide) (by decide)).trans p9_b40
  have p10_ba0 : ptF n10.mem B 0xBA0 = tbl2 P0 4 := (K10.pt (by decide) (by decide)).trans p9_ba0
  have p10_c00 : ptF n10.mem B 0xC00 = tbl2 P0 5 := (K10.pt (by decide) (by decide)).trans p9_c00
  have p10_c60 : ptF n10.mem B 0xC60 = tbl2 P0 6 := (K10.pt (by decide) (by decide)).trans p9_c60
  have p10_cc0 : ptF n10.mem B 0xCC0 = tbl2 P0 7 := (K10.pt (by decide) (by decide)).trans p9_cc0
  have p10_1020 : ptF n10.mem B 0x1020 = tbl2 P0 0 := (K10.pt (by decide) (by decide)).trans p9_1020
  have p10_1080 : ptF n10.mem B 0x1080 = tbl2 P0 1 := (K10.pt (by decide) (by decide)).trans p9_1080
  have p10_10e0 : ptF n10.mem B 0x10E0 = tbl2 P0 2 := (K10.pt (by decide) (by decide)).trans p9_10e0
  have p10_1140 : ptF n10.mem B 0x1140 = tbl2 P0 3 := (K10.pt (by decide) (by decide)).trans p9_1140
  have p10_11a0 : ptF n10.mem B 0x11A0 = tbl2 P0 4 := (K10.pt (by decide) (by decide)).trans p9_11a0
  have p10_1200 : ptF n10.mem B 0x1200 = tbl2 P0 5 := (K10.pt (by decide) (by decide)).trans p9_1200
  have p10_1260 : ptF n10.mem B 0x1260 = tbl2 P0 6 := (K10.pt (by decide) (by decide)).trans p9_1260
  have p10_12c0 : ptF n10.mem B 0x12C0 = tbl2 P0 7 := (K10.pt (by decide) (by decide)).trans p9_12c0
  have p10_1320 : ptF n10.mem B 0x1320 = ptDbl2 P0 := (K10.pt (by decide) (by decide)).trans p9_1320
  have p10_1380 : ptF n10.mem B 0x1380 = P1 := (K10.pt (by decide) (by decide)).trans p9_1380
  have p10_1480 : ptF n10.mem B 0x1480 = P0 := (K10.pt (by decide) (by decide)).trans p9_1480
  have p10_1500 : ptF n10.mem B 0x1500 = P1 := (K10.pt (by decide) (by decide)).trans p9_1500
  have q10_480 : ∀ j, j < 96 → n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0x480 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) :=
    fun j hj => (X10 j hj).trans (fR9 _ (SvRo2.r RS (Or.inr ⟨by decide, by decide⟩) hj))
  clear p9_1500 p9_1480 p9_1380 p9_1320 p9_12c0 p9_1260 p9_1200 p9_11a0 p9_1140 p9_10e0 p9_1080 p9_1020 p9_cc0 p9_c60 p9_c00 p9_ba0 p9_b40 p9_ae0 p9_a80 p9_a20 p9_6c0 p9_660 p9_600 p9_5a0 p9_540 p9_4e0 p9_480 p9_3a0 p9_320 a9_1560 a9_14e0 a9_13e0 a9_400 a9_380 a9_2e0 a9_2c0 a9_2a0 a9_280 a9_260 a9_240 q9_420 b9_14a0 b9_1040 b9_a40 w9_130 w9_12c w9_128 w9_124 w9_120 w9_11c w9_118 w9_114 w9_110 w9_10c w9_108 w9_104 w9_100 w9_fc w9_f8 w9_f4 w9_f0 w9_ec w9_e8 w9_e4 w9_e0 w9_dc w9_d8 w9_d4 w9_d0 w9_cc w9_c8 w9_c4 w9_c0 w9_bc w9_b8 w9_b4 w9_b0 w9_ac w9_a8 w9_a4 w9_a0 w9_9c w9_98 w9_94 w9_90 w9_8c w9_88 w9_84 w9_80 w9_7c w9_78 w9_70 w9_6c w9_68 w9_64 w9_60 w9_5c w9_58 w9_54 w9_50 w9_4c w9_48 w9_44 w9_40 w9_3c w9_38 w9_34 w9_30 w9_2c w9_28 w9_24 g9_12 g9_11 g9_10 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 rb9 s9 m9 u9 c9
  -- 0x16C2
  obtain ⟨n11, c11, u11⟩ := s10.block svEcT1a16c2 E10.self svEcT1a16c2_end
    ⟨trivial, trivial, trivial⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have s11 : St n11.mem SV n11 0x16C8 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have rb11 : ∀ q, reg n11 q = (runBlock svEcT1a16c2 (n10.mem, reg n10)).2 q := fun q => by rw [u11.regs]
  have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
  have t11 : Steps n0 n11 := t10.trans c11
  have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : SvCode n11.mem := E10.fr F fr11
  have V11 : SvSaves B n11.mem v := V10.same m11
  have g11_2 : reg n11 sp = B + 0x21A0 := by
    rw [rb11, runBlock_reg _ _ _ sp s10.zero (by decide), g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb11, runBlock_reg _ _ _ (3 : Fin 32) s10.zero (by decide), g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb11, runBlock_reg _ _ _ (4 : Fin 32) s10.zero (by decide), g10_4]
  have g11_18 : reg n11 (18 : Fin 32) = out := by
    rw [rb11, runBlock_reg _ _ _ (18 : Fin 32) s10.zero (by decide), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by
    rw [rb11, runBlock_reg _ _ _ (19 : Fin 32) s10.zero (by decide), g10_19]
  have g11_20 : reg n11 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb11, runBlock_reg _ _ _ (20 : Fin 32) s10.zero (by decide), g10_20]
  have g11_21 : reg n11 (21 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb11, runBlock_reg _ _ _ (21 : Fin 32) s10.zero (by decide), g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb11, runBlock_reg _ _ _ (22 : Fin 32) s10.zero (by decide), g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1500 := by
    rw [rb11, runBlock_reg _ _ _ (23 : Fin 32) s10.zero (by decide), g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb11, runBlock_reg _ _ _ (24 : Fin 32) s10.zero (by decide), g10_24]
  have g11_25 : reg n11 (25 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb11, runBlock_reg _ _ _ (25 : Fin 32) s10.zero (by decide), g10_25]
  have g11_26 : reg n11 (26 : Fin 32) = x26 := by
    rw [rb11, runBlock_reg _ _ _ (26 : Fin 32) s10.zero (by decide), g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb11, runBlock_reg _ _ _ (27 : Fin 32) s10.zero (by decide), g10_27]
  have g11_8 : reg n11 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x4E0 := by
    rw [rb11]; simp +decide only [runBlock, BInstr.run, svEcT1a16c2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g10_2, g10_3, g10_4, g10_8, g10_9, g10_18, g10_19, g10_20, g10_21, g10_22, g10_23, g10_24, g10_25, g10_26, g10_27, s10.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g11_9 : reg n11 (9 : Fin 32) = BitVec.ofNat 32 0x6 := by
    rw [rb11]; simp +decide only [runBlock, BInstr.run, svEcT1a16c2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g10_2, g10_3, g10_4, g10_8, g10_9, g10_18, g10_19, g10_20, g10_21, g10_22, g10_23, g10_24, g10_25, g10_26, g10_27, s10.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x1380, 0x80), (0x420, 0x60), (0x480, 0x60)] := by rw [m11]; exact keep_kk10
  clear keep_kk10
  have w11_24 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m11]; exact w10_24
  have w11_28 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m11]; exact w10_28
  have w11_2c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m11]; exact w10_2c
  have w11_30 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m11]; exact w10_30
  have w11_34 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m11]; exact w10_34
  have w11_38 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m11]; exact w10_38
  have w11_3c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m11]; exact w10_3c
  have w11_40 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m11]; exact w10_40
  have w11_44 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m11]; exact w10_44
  have w11_48 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m11]; exact w10_48
  have w11_4c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m11]; exact w10_4c
  have w11_50 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m11]; exact w10_50
  have w11_54 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m11]; exact w10_54
  have w11_58 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m11]; exact w10_58
  have w11_5c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m11]; exact w10_5c
  have w11_60 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m11]; exact w10_60
  have w11_64 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m11]; exact w10_64
  have w11_68 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m11]; exact w10_68
  have w11_6c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m11]; exact w10_6c
  have w11_70 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m11]; exact w10_70
  have w11_78 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m11]; exact w10_78
  have w11_7c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m11]; exact w10_7c
  have w11_80 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m11]; exact w10_80
  have w11_84 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m11]; exact w10_84
  have w11_88 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m11]; exact w10_88
  have w11_8c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m11]; exact w10_8c
  have w11_90 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m11]; exact w10_90
  have w11_94 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m11]; exact w10_94
  have w11_98 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m11]; exact w10_98
  have w11_9c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m11]; exact w10_9c
  have w11_a0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m11]; exact w10_a0
  have w11_a4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m11]; exact w10_a4
  have w11_a8 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m11]; exact w10_a8
  have w11_ac : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m11]; exact w10_ac
  have w11_b0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m11]; exact w10_b0
  have w11_b4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m11]; exact w10_b4
  have w11_b8 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m11]; exact w10_b8
  have w11_bc : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m11]; exact w10_bc
  have w11_c0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m11]; exact w10_c0
  have w11_c4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m11]; exact w10_c4
  have w11_c8 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m11]; exact w10_c8
  have w11_cc : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m11]; exact w10_cc
  have w11_d0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m11]; exact w10_d0
  have w11_d4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m11]; exact w10_d4
  have w11_d8 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m11]; exact w10_d8
  have w11_dc : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m11]; exact w10_dc
  have w11_e0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m11]; exact w10_e0
  have w11_e4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m11]; exact w10_e4
  have w11_e8 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m11]; exact w10_e8
  have w11_ec : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m11]; exact w10_ec
  have w11_f0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m11]; exact w10_f0
  have w11_f4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m11]; exact w10_f4
  have w11_f8 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m11]; exact w10_f8
  have w11_fc : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m11]; exact w10_fc
  have w11_100 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m11]; exact w10_100
  have w11_104 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m11]; exact w10_104
  have w11_108 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m11]; exact w10_108
  have w11_10c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m11]; exact w10_10c
  have w11_110 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m11]; exact w10_110
  have w11_114 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m11]; exact w10_114
  have w11_118 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m11]; exact w10_118
  have w11_11c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m11]; exact w10_11c
  have w11_120 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m11]; exact w10_120
  have w11_124 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m11]; exact w10_124
  have w11_128 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m11]; exact w10_128
  have w11_12c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m11]; exact w10_12c
  have w11_130 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m11]; exact w10_130
  have b11_a40 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = gs := by rw [m11]; exact b10_a40
  have b11_1040 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = gs := by rw [m11]; exact b10_1040
  have b11_14a0 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := by rw [m11]; exact b10_14a0
  have q11_420 : ∀ j, j < 96 → n11.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m11]; exact q10_420 j hj
  have q11_480 : ∀ j, j < 96 → n11.mem (B + 0x21A0 + BitVec.ofNat 32 (0x480 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m11]; exact q10_480 j hj
  have a11_240 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m11]; exact a10_240
  have a11_260 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m11]; exact a10_260
  have a11_280 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m11]; exact a10_280
  have a11_2a0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m11]; exact a10_2a0
  have a11_2c0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m11]; exact a10_2c0
  have a11_2e0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m11]; exact a10_2e0
  have a11_380 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m11]; exact a10_380
  have a11_400 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m11]; exact a10_400
  have a11_13e0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U2 := by rw [m11]; exact a10_13e0
  have a11_14e0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x14E0) 8 = U1 := by rw [m11]; exact a10_14e0
  have a11_1560 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1560) 8 = U2 := by rw [m11]; exact a10_1560
  have p11_320 : ptF n11.mem B 0x320 = P0 := by rw [m11]; exact p10_320
  have p11_3a0 : ptF n11.mem B 0x3A0 = P1 := by rw [m11]; exact p10_3a0
  have p11_4e0 : ptF n11.mem B 0x4E0 = tbl2 P0 2 := by rw [m11]; exact p10_4e0
  have p11_540 : ptF n11.mem B 0x540 = tbl2 P0 3 := by rw [m11]; exact p10_540
  have p11_5a0 : ptF n11.mem B 0x5A0 = tbl2 P0 4 := by rw [m11]; exact p10_5a0
  have p11_600 : ptF n11.mem B 0x600 = tbl2 P0 5 := by rw [m11]; exact p10_600
  have p11_660 : ptF n11.mem B 0x660 = tbl2 P0 6 := by rw [m11]; exact p10_660
  have p11_6c0 : ptF n11.mem B 0x6C0 = tbl2 P0 7 := by rw [m11]; exact p10_6c0
  have p11_a20 : ptF n11.mem B 0xA20 = tbl2 P0 0 := by rw [m11]; exact p10_a20
  have p11_a80 : ptF n11.mem B 0xA80 = tbl2 P0 1 := by rw [m11]; exact p10_a80
  have p11_ae0 : ptF n11.mem B 0xAE0 = tbl2 P0 2 := by rw [m11]; exact p10_ae0
  have p11_b40 : ptF n11.mem B 0xB40 = tbl2 P0 3 := by rw [m11]; exact p10_b40
  have p11_ba0 : ptF n11.mem B 0xBA0 = tbl2 P0 4 := by rw [m11]; exact p10_ba0
  have p11_c00 : ptF n11.mem B 0xC00 = tbl2 P0 5 := by rw [m11]; exact p10_c00
  have p11_c60 : ptF n11.mem B 0xC60 = tbl2 P0 6 := by rw [m11]; exact p10_c60
  have p11_cc0 : ptF n11.mem B 0xCC0 = tbl2 P0 7 := by rw [m11]; exact p10_cc0
  have p11_1020 : ptF n11.mem B 0x1020 = tbl2 P0 0 := by rw [m11]; exact p10_1020
  have p11_1080 : ptF n11.mem B 0x1080 = tbl2 P0 1 := by rw [m11]; exact p10_1080
  have p11_10e0 : ptF n11.mem B 0x10E0 = tbl2 P0 2 := by rw [m11]; exact p10_10e0
  have p11_1140 : ptF n11.mem B 0x1140 = tbl2 P0 3 := by rw [m11]; exact p10_1140
  have p11_11a0 : ptF n11.mem B 0x11A0 = tbl2 P0 4 := by rw [m11]; exact p10_11a0
  have p11_1200 : ptF n11.mem B 0x1200 = tbl2 P0 5 := by rw [m11]; exact p10_1200
  have p11_1260 : ptF n11.mem B 0x1260 = tbl2 P0 6 := by rw [m11]; exact p10_1260
  have p11_12c0 : ptF n11.mem B 0x12C0 = tbl2 P0 7 := by rw [m11]; exact p10_12c0
  have p11_1320 : ptF n11.mem B 0x1320 = ptDbl2 P0 := by rw [m11]; exact p10_1320
  have p11_1380 : ptF n11.mem B 0x1380 = P1 := by rw [m11]; exact p10_1380
  have p11_1480 : ptF n11.mem B 0x1480 = P0 := by rw [m11]; exact p10_1480
  have p11_1500 : ptF n11.mem B 0x1500 = P1 := by rw [m11]; exact p10_1500
  clear q10_480 p10_1500 p10_1480 p10_1380 p10_1320 p10_12c0 p10_1260 p10_1200 p10_11a0 p10_1140 p10_10e0 p10_1080 p10_1020 p10_cc0 p10_c60 p10_c00 p10_ba0 p10_b40 p10_ae0 p10_a80 p10_a20 p10_6c0 p10_660 p10_600 p10_5a0 p10_540 p10_4e0 p10_3a0 p10_320 a10_1560 a10_14e0 a10_13e0 a10_400 a10_380 a10_2e0 a10_2c0 a10_2a0 a10_280 a10_260 a10_240 q10_420 b10_14a0 b10_1040 b10_a40 w10_130 w10_12c w10_128 w10_124 w10_120 w10_11c w10_118 w10_114 w10_110 w10_10c w10_108 w10_104 w10_100 w10_fc w10_f8 w10_f4 w10_f0 w10_ec w10_e8 w10_e4 w10_e0 w10_dc w10_d8 w10_d4 w10_d0 w10_cc w10_c8 w10_c4 w10_c0 w10_bc w10_b8 w10_b4 w10_b0 w10_ac w10_a8 w10_a4 w10_a0 w10_9c w10_98 w10_94 w10_90 w10_8c w10_88 w10_84 w10_80 w10_7c w10_78 w10_70 w10_6c w10_68 w10_64 w10_60 w10_5c w10_58 w10_54 w10_50 w10_4c w10_48 w10_44 w10_40 w10_3c w10_38 w10_34 w10_30 w10_2c w10_28 w10_24 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 s10 X10 K10 P10
  -- 0x16C8: branch, taken
  obtain ⟨n12, d12, u12⟩ := s11.taken E11.self 0x16B2 sv_at_16c8
    (by decide) (by rw [g11_9, s11.zero]; decide)
  have s12 : St n12.mem SV n12 0x16B2 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have fr12 : ∀ x, SvR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
  have t12 : Steps n0 n12 := t11.trans (.single d12)
  have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : SvCode n12.mem := E11.fr F fr12
  have V12 : SvSaves B n12.mem v := V11.same m12
  have g12_2 : reg n12 sp = B + 0x21A0 := by rw [u12.regs, g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u12.regs, g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u12.regs, g11_4]
  have g12_8 : reg n12 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x4E0 := by rw [u12.regs, g11_8]
  have g12_9 : reg n12 (9 : Fin 32) = BitVec.ofNat 32 0x6 := by rw [u12.regs, g11_9]
  have g12_18 : reg n12 (18 : Fin 32) = out := by rw [u12.regs, g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [u12.regs, g11_19]
  have g12_20 : reg n12 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u12.regs, g11_20]
  have g12_21 : reg n12 (21 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u12.regs, g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [u12.regs, g11_22]
  have g12_23 : reg n12 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1500 := by rw [u12.regs, g11_23]
  have g12_24 : reg n12 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u12.regs, g11_24]
  have g12_25 : reg n12 (25 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [u12.regs, g11_25]
  have g12_26 : reg n12 (26 : Fin 32) = x26 := by rw [u12.regs, g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u12.regs, g11_27]
  have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x1380, 0x80), (0x420, 0x60), (0x480, 0x60)] := by rw [m12]; exact keep_kk11
  clear keep_kk11
  have w12_24 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m12]; exact w11_24
  have w12_28 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m12]; exact w11_28
  have w12_2c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m12]; exact w11_2c
  have w12_30 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m12]; exact w11_30
  have w12_34 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m12]; exact w11_34
  have w12_38 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m12]; exact w11_38
  have w12_3c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m12]; exact w11_3c
  have w12_40 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m12]; exact w11_40
  have w12_44 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m12]; exact w11_44
  have w12_48 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m12]; exact w11_48
  have w12_4c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m12]; exact w11_4c
  have w12_50 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m12]; exact w11_50
  have w12_54 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m12]; exact w11_54
  have w12_58 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m12]; exact w11_58
  have w12_5c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m12]; exact w11_5c
  have w12_60 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m12]; exact w11_60
  have w12_64 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m12]; exact w11_64
  have w12_68 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m12]; exact w11_68
  have w12_6c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m12]; exact w11_6c
  have w12_70 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m12]; exact w11_70
  have w12_78 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m12]; exact w11_78
  have w12_7c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m12]; exact w11_7c
  have w12_80 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m12]; exact w11_80
  have w12_84 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m12]; exact w11_84
  have w12_88 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m12]; exact w11_88
  have w12_8c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m12]; exact w11_8c
  have w12_90 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m12]; exact w11_90
  have w12_94 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m12]; exact w11_94
  have w12_98 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m12]; exact w11_98
  have w12_9c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m12]; exact w11_9c
  have w12_a0 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m12]; exact w11_a0
  have w12_a4 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m12]; exact w11_a4
  have w12_a8 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m12]; exact w11_a8
  have w12_ac : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m12]; exact w11_ac
  have w12_b0 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m12]; exact w11_b0
  have w12_b4 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m12]; exact w11_b4
  have w12_b8 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m12]; exact w11_b8
  have w12_bc : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m12]; exact w11_bc
  have w12_c0 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m12]; exact w11_c0
  have w12_c4 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m12]; exact w11_c4
  have w12_c8 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m12]; exact w11_c8
  have w12_cc : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m12]; exact w11_cc
  have w12_d0 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m12]; exact w11_d0
  have w12_d4 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m12]; exact w11_d4
  have w12_d8 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m12]; exact w11_d8
  have w12_dc : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m12]; exact w11_dc
  have w12_e0 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m12]; exact w11_e0
  have w12_e4 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m12]; exact w11_e4
  have w12_e8 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m12]; exact w11_e8
  have w12_ec : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m12]; exact w11_ec
  have w12_f0 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m12]; exact w11_f0
  have w12_f4 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m12]; exact w11_f4
  have w12_f8 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m12]; exact w11_f8
  have w12_fc : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m12]; exact w11_fc
  have w12_100 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m12]; exact w11_100
  have w12_104 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m12]; exact w11_104
  have w12_108 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m12]; exact w11_108
  have w12_10c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m12]; exact w11_10c
  have w12_110 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m12]; exact w11_110
  have w12_114 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m12]; exact w11_114
  have w12_118 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m12]; exact w11_118
  have w12_11c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m12]; exact w11_11c
  have w12_120 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m12]; exact w11_120
  have w12_124 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m12]; exact w11_124
  have w12_128 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m12]; exact w11_128
  have w12_12c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m12]; exact w11_12c
  have w12_130 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m12]; exact w11_130
  have b12_a40 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = gs := by rw [m12]; exact b11_a40
  have b12_1040 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = gs := by rw [m12]; exact b11_1040
  have b12_14a0 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := by rw [m12]; exact b11_14a0
  have q12_420 : ∀ j, j < 96 → n12.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m12]; exact q11_420 j hj
  have q12_480 : ∀ j, j < 96 → n12.mem (B + 0x21A0 + BitVec.ofNat 32 (0x480 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m12]; exact q11_480 j hj
  have a12_240 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m12]; exact a11_240
  have a12_260 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m12]; exact a11_260
  have a12_280 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m12]; exact a11_280
  have a12_2a0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m12]; exact a11_2a0
  have a12_2c0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m12]; exact a11_2c0
  have a12_2e0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m12]; exact a11_2e0
  have a12_380 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m12]; exact a11_380
  have a12_400 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m12]; exact a11_400
  have a12_13e0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U2 := by rw [m12]; exact a11_13e0
  have a12_14e0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x14E0) 8 = U1 := by rw [m12]; exact a11_14e0
  have a12_1560 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1560) 8 = U2 := by rw [m12]; exact a11_1560
  have p12_320 : ptF n12.mem B 0x320 = P0 := by rw [m12]; exact p11_320
  have p12_3a0 : ptF n12.mem B 0x3A0 = P1 := by rw [m12]; exact p11_3a0
  have p12_4e0 : ptF n12.mem B 0x4E0 = tbl2 P0 2 := by rw [m12]; exact p11_4e0
  have p12_540 : ptF n12.mem B 0x540 = tbl2 P0 3 := by rw [m12]; exact p11_540
  have p12_5a0 : ptF n12.mem B 0x5A0 = tbl2 P0 4 := by rw [m12]; exact p11_5a0
  have p12_600 : ptF n12.mem B 0x600 = tbl2 P0 5 := by rw [m12]; exact p11_600
  have p12_660 : ptF n12.mem B 0x660 = tbl2 P0 6 := by rw [m12]; exact p11_660
  have p12_6c0 : ptF n12.mem B 0x6C0 = tbl2 P0 7 := by rw [m12]; exact p11_6c0
  have p12_a20 : ptF n12.mem B 0xA20 = tbl2 P0 0 := by rw [m12]; exact p11_a20
  have p12_a80 : ptF n12.mem B 0xA80 = tbl2 P0 1 := by rw [m12]; exact p11_a80
  have p12_ae0 : ptF n12.mem B 0xAE0 = tbl2 P0 2 := by rw [m12]; exact p11_ae0
  have p12_b40 : ptF n12.mem B 0xB40 = tbl2 P0 3 := by rw [m12]; exact p11_b40
  have p12_ba0 : ptF n12.mem B 0xBA0 = tbl2 P0 4 := by rw [m12]; exact p11_ba0
  have p12_c00 : ptF n12.mem B 0xC00 = tbl2 P0 5 := by rw [m12]; exact p11_c00
  have p12_c60 : ptF n12.mem B 0xC60 = tbl2 P0 6 := by rw [m12]; exact p11_c60
  have p12_cc0 : ptF n12.mem B 0xCC0 = tbl2 P0 7 := by rw [m12]; exact p11_cc0
  have p12_1020 : ptF n12.mem B 0x1020 = tbl2 P0 0 := by rw [m12]; exact p11_1020
  have p12_1080 : ptF n12.mem B 0x1080 = tbl2 P0 1 := by rw [m12]; exact p11_1080
  have p12_10e0 : ptF n12.mem B 0x10E0 = tbl2 P0 2 := by rw [m12]; exact p11_10e0
  have p12_1140 : ptF n12.mem B 0x1140 = tbl2 P0 3 := by rw [m12]; exact p11_1140
  have p12_11a0 : ptF n12.mem B 0x11A0 = tbl2 P0 4 := by rw [m12]; exact p11_11a0
  have p12_1200 : ptF n12.mem B 0x1200 = tbl2 P0 5 := by rw [m12]; exact p11_1200
  have p12_1260 : ptF n12.mem B 0x1260 = tbl2 P0 6 := by rw [m12]; exact p11_1260
  have p12_12c0 : ptF n12.mem B 0x12C0 = tbl2 P0 7 := by rw [m12]; exact p11_12c0
  have p12_1320 : ptF n12.mem B 0x1320 = ptDbl2 P0 := by rw [m12]; exact p11_1320
  have p12_1380 : ptF n12.mem B 0x1380 = P1 := by rw [m12]; exact p11_1380
  have p12_1480 : ptF n12.mem B 0x1480 = P0 := by rw [m12]; exact p11_1480
  have p12_1500 : ptF n12.mem B 0x1500 = P1 := by rw [m12]; exact p11_1500
  clear p11_1500 p11_1480 p11_1380 p11_1320 p11_12c0 p11_1260 p11_1200 p11_11a0 p11_1140 p11_10e0 p11_1080 p11_1020 p11_cc0 p11_c60 p11_c00 p11_ba0 p11_b40 p11_ae0 p11_a80 p11_a20 p11_6c0 p11_660 p11_600 p11_5a0 p11_540 p11_4e0 p11_3a0 p11_320 a11_1560 a11_14e0 a11_13e0 a11_400 a11_380 a11_2e0 a11_2c0 a11_2a0 a11_280 a11_260 a11_240 q11_480 q11_420 b11_14a0 b11_1040 b11_a40 w11_130 w11_12c w11_128 w11_124 w11_120 w11_11c w11_118 w11_114 w11_110 w11_10c w11_108 w11_104 w11_100 w11_fc w11_f8 w11_f4 w11_f0 w11_ec w11_e8 w11_e4 w11_e0 w11_dc w11_d8 w11_d4 w11_d0 w11_cc w11_c8 w11_c4 w11_c0 w11_bc w11_b8 w11_b4 w11_b0 w11_ac w11_a8 w11_a4 w11_a0 w11_9c w11_98 w11_94 w11_90 w11_8c w11_88 w11_84 w11_80 w11_7c w11_78 w11_70 w11_6c w11_68 w11_64 w11_60 w11_5c w11_58 w11_54 w11_50 w11_4c w11_48 w11_44 w11_40 w11_3c w11_38 w11_34 w11_30 w11_2c w11_28 w11_24 g11_9 g11_8 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 rb11 s11 m11 u11 c11
  -- 0x16B2
  obtain ⟨n13, c13, u13⟩ := s12.block svEcT1a16b2 E12.self svEcT1a16b2_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m13 : n13.mem = n12.mem := u13.mem
  have s13 : St n13.mem SV n13 0x16BA (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
  have rb13 : ∀ q, reg n13 q = (runBlock svEcT1a16b2 (n12.mem, reg n12)).2 q := fun q => by rw [u13.regs]
  have fr13 : ∀ x, SvR B x → n13.mem x = n12.mem x := fun x _ => by rw [m13]
  have t13 : Steps n0 n13 := t12.trans c13
  have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : SvCode n13.mem := E12.fr F fr13
  have V13 : SvSaves B n13.mem v := V12.same m13
  have g13_2 : reg n13 sp = B + 0x21A0 := by
    rw [rb13, runBlock_reg _ _ _ sp s12.zero (by decide), g12_2]
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb13, runBlock_reg _ _ _ (3 : Fin 32) s12.zero (by decide), g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb13, runBlock_reg _ _ _ (4 : Fin 32) s12.zero (by decide), g12_4]
  have g13_8 : reg n13 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x4E0 := by
    rw [rb13, runBlock_reg _ _ _ (8 : Fin 32) s12.zero (by decide), g12_8]
  have g13_9 : reg n13 (9 : Fin 32) = BitVec.ofNat 32 0x6 := by
    rw [rb13, runBlock_reg _ _ _ (9 : Fin 32) s12.zero (by decide), g12_9]
  have g13_18 : reg n13 (18 : Fin 32) = out := by
    rw [rb13, runBlock_reg _ _ _ (18 : Fin 32) s12.zero (by decide), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = bp := by
    rw [rb13, runBlock_reg _ _ _ (19 : Fin 32) s12.zero (by decide), g12_19]
  have g13_20 : reg n13 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb13, runBlock_reg _ _ _ (20 : Fin 32) s12.zero (by decide), g12_20]
  have g13_21 : reg n13 (21 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb13, runBlock_reg _ _ _ (21 : Fin 32) s12.zero (by decide), g12_21]
  have g13_22 : reg n13 (22 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb13, runBlock_reg _ _ _ (22 : Fin 32) s12.zero (by decide), g12_22]
  have g13_23 : reg n13 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1500 := by
    rw [rb13, runBlock_reg _ _ _ (23 : Fin 32) s12.zero (by decide), g12_23]
  have g13_24 : reg n13 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb13, runBlock_reg _ _ _ (24 : Fin 32) s12.zero (by decide), g12_24]
  have g13_25 : reg n13 (25 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb13, runBlock_reg _ _ _ (25 : Fin 32) s12.zero (by decide), g12_25]
  have g13_26 : reg n13 (26 : Fin 32) = x26 := by
    rw [rb13, runBlock_reg _ _ _ (26 : Fin 32) s12.zero (by decide), g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb13, runBlock_reg _ _ _ (27 : Fin 32) s12.zero (by decide), g12_27]
  have g13_10 : reg n13 a0 = B + 0x21A0 + BitVec.ofNat 32 0x4E0 := by
    rw [rb13]; simp +decide only [runBlock, BInstr.run, svEcT1a16b2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g12_2, g12_3, g12_4, g12_8, g12_9, g12_18, g12_19, g12_20, g12_21, g12_22, g12_23, g12_24, g12_25, g12_26, g12_27, s12.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g13_11 : reg n13 a1 = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb13]; simp +decide only [runBlock, BInstr.run, svEcT1a16b2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g12_2, g12_3, g12_4, g12_8, g12_9, g12_18, g12_19, g12_20, g12_21, g12_22, g12_23, g12_24, g12_25, g12_26, g12_27, s12.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g13_12 : reg n13 a2 = BitVec.ofNat 32 0x60 := by
    rw [rb13]; simp +decide only [runBlock, BInstr.run, svEcT1a16b2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g12_2, g12_3, g12_4, g12_8, g12_9, g12_18, g12_19, g12_20, g12_21, g12_22, g12_23, g12_24, g12_25, g12_26, g12_27, s12.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x1380, 0x80), (0x420, 0x60), (0x480, 0x60)] := by rw [m13]; exact keep_kk12
  clear keep_kk12
  have w13_24 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m13]; exact w12_24
  have w13_28 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m13]; exact w12_28
  have w13_2c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m13]; exact w12_2c
  have w13_30 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m13]; exact w12_30
  have w13_34 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m13]; exact w12_34
  have w13_38 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m13]; exact w12_38
  have w13_3c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m13]; exact w12_3c
  have w13_40 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m13]; exact w12_40
  have w13_44 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m13]; exact w12_44
  have w13_48 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m13]; exact w12_48
  have w13_4c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m13]; exact w12_4c
  have w13_50 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m13]; exact w12_50
  have w13_54 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m13]; exact w12_54
  have w13_58 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m13]; exact w12_58
  have w13_5c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m13]; exact w12_5c
  have w13_60 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m13]; exact w12_60
  have w13_64 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m13]; exact w12_64
  have w13_68 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m13]; exact w12_68
  have w13_6c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m13]; exact w12_6c
  have w13_70 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m13]; exact w12_70
  have w13_78 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m13]; exact w12_78
  have w13_7c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m13]; exact w12_7c
  have w13_80 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m13]; exact w12_80
  have w13_84 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m13]; exact w12_84
  have w13_88 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m13]; exact w12_88
  have w13_8c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m13]; exact w12_8c
  have w13_90 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m13]; exact w12_90
  have w13_94 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m13]; exact w12_94
  have w13_98 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m13]; exact w12_98
  have w13_9c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m13]; exact w12_9c
  have w13_a0 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m13]; exact w12_a0
  have w13_a4 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m13]; exact w12_a4
  have w13_a8 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m13]; exact w12_a8
  have w13_ac : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m13]; exact w12_ac
  have w13_b0 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m13]; exact w12_b0
  have w13_b4 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m13]; exact w12_b4
  have w13_b8 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m13]; exact w12_b8
  have w13_bc : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m13]; exact w12_bc
  have w13_c0 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m13]; exact w12_c0
  have w13_c4 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m13]; exact w12_c4
  have w13_c8 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m13]; exact w12_c8
  have w13_cc : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m13]; exact w12_cc
  have w13_d0 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m13]; exact w12_d0
  have w13_d4 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m13]; exact w12_d4
  have w13_d8 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m13]; exact w12_d8
  have w13_dc : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m13]; exact w12_dc
  have w13_e0 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m13]; exact w12_e0
  have w13_e4 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m13]; exact w12_e4
  have w13_e8 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m13]; exact w12_e8
  have w13_ec : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m13]; exact w12_ec
  have w13_f0 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m13]; exact w12_f0
  have w13_f4 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m13]; exact w12_f4
  have w13_f8 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m13]; exact w12_f8
  have w13_fc : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m13]; exact w12_fc
  have w13_100 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m13]; exact w12_100
  have w13_104 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m13]; exact w12_104
  have w13_108 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m13]; exact w12_108
  have w13_10c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m13]; exact w12_10c
  have w13_110 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m13]; exact w12_110
  have w13_114 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m13]; exact w12_114
  have w13_118 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m13]; exact w12_118
  have w13_11c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m13]; exact w12_11c
  have w13_120 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m13]; exact w12_120
  have w13_124 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m13]; exact w12_124
  have w13_128 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m13]; exact w12_128
  have w13_12c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m13]; exact w12_12c
  have w13_130 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m13]; exact w12_130
  have b13_a40 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = gs := by rw [m13]; exact b12_a40
  have b13_1040 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = gs := by rw [m13]; exact b12_1040
  have b13_14a0 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := by rw [m13]; exact b12_14a0
  have q13_420 : ∀ j, j < 96 → n13.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m13]; exact q12_420 j hj
  have q13_480 : ∀ j, j < 96 → n13.mem (B + 0x21A0 + BitVec.ofNat 32 (0x480 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m13]; exact q12_480 j hj
  have a13_240 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m13]; exact a12_240
  have a13_260 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m13]; exact a12_260
  have a13_280 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m13]; exact a12_280
  have a13_2a0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m13]; exact a12_2a0
  have a13_2c0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m13]; exact a12_2c0
  have a13_2e0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m13]; exact a12_2e0
  have a13_380 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m13]; exact a12_380
  have a13_400 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m13]; exact a12_400
  have a13_13e0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U2 := by rw [m13]; exact a12_13e0
  have a13_14e0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x14E0) 8 = U1 := by rw [m13]; exact a12_14e0
  have a13_1560 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1560) 8 = U2 := by rw [m13]; exact a12_1560
  have p13_320 : ptF n13.mem B 0x320 = P0 := by rw [m13]; exact p12_320
  have p13_3a0 : ptF n13.mem B 0x3A0 = P1 := by rw [m13]; exact p12_3a0
  have p13_4e0 : ptF n13.mem B 0x4E0 = tbl2 P0 2 := by rw [m13]; exact p12_4e0
  have p13_540 : ptF n13.mem B 0x540 = tbl2 P0 3 := by rw [m13]; exact p12_540
  have p13_5a0 : ptF n13.mem B 0x5A0 = tbl2 P0 4 := by rw [m13]; exact p12_5a0
  have p13_600 : ptF n13.mem B 0x600 = tbl2 P0 5 := by rw [m13]; exact p12_600
  have p13_660 : ptF n13.mem B 0x660 = tbl2 P0 6 := by rw [m13]; exact p12_660
  have p13_6c0 : ptF n13.mem B 0x6C0 = tbl2 P0 7 := by rw [m13]; exact p12_6c0
  have p13_a20 : ptF n13.mem B 0xA20 = tbl2 P0 0 := by rw [m13]; exact p12_a20
  have p13_a80 : ptF n13.mem B 0xA80 = tbl2 P0 1 := by rw [m13]; exact p12_a80
  have p13_ae0 : ptF n13.mem B 0xAE0 = tbl2 P0 2 := by rw [m13]; exact p12_ae0
  have p13_b40 : ptF n13.mem B 0xB40 = tbl2 P0 3 := by rw [m13]; exact p12_b40
  have p13_ba0 : ptF n13.mem B 0xBA0 = tbl2 P0 4 := by rw [m13]; exact p12_ba0
  have p13_c00 : ptF n13.mem B 0xC00 = tbl2 P0 5 := by rw [m13]; exact p12_c00
  have p13_c60 : ptF n13.mem B 0xC60 = tbl2 P0 6 := by rw [m13]; exact p12_c60
  have p13_cc0 : ptF n13.mem B 0xCC0 = tbl2 P0 7 := by rw [m13]; exact p12_cc0
  have p13_1020 : ptF n13.mem B 0x1020 = tbl2 P0 0 := by rw [m13]; exact p12_1020
  have p13_1080 : ptF n13.mem B 0x1080 = tbl2 P0 1 := by rw [m13]; exact p12_1080
  have p13_10e0 : ptF n13.mem B 0x10E0 = tbl2 P0 2 := by rw [m13]; exact p12_10e0
  have p13_1140 : ptF n13.mem B 0x1140 = tbl2 P0 3 := by rw [m13]; exact p12_1140
  have p13_11a0 : ptF n13.mem B 0x11A0 = tbl2 P0 4 := by rw [m13]; exact p12_11a0
  have p13_1200 : ptF n13.mem B 0x1200 = tbl2 P0 5 := by rw [m13]; exact p12_1200
  have p13_1260 : ptF n13.mem B 0x1260 = tbl2 P0 6 := by rw [m13]; exact p12_1260
  have p13_12c0 : ptF n13.mem B 0x12C0 = tbl2 P0 7 := by rw [m13]; exact p12_12c0
  have p13_1320 : ptF n13.mem B 0x1320 = ptDbl2 P0 := by rw [m13]; exact p12_1320
  have p13_1380 : ptF n13.mem B 0x1380 = P1 := by rw [m13]; exact p12_1380
  have p13_1480 : ptF n13.mem B 0x1480 = P0 := by rw [m13]; exact p12_1480
  have p13_1500 : ptF n13.mem B 0x1500 = P1 := by rw [m13]; exact p12_1500
  clear p12_1500 p12_1480 p12_1380 p12_1320 p12_12c0 p12_1260 p12_1200 p12_11a0 p12_1140 p12_10e0 p12_1080 p12_1020 p12_cc0 p12_c60 p12_c00 p12_ba0 p12_b40 p12_ae0 p12_a80 p12_a20 p12_6c0 p12_660 p12_600 p12_5a0 p12_540 p12_4e0 p12_3a0 p12_320 a12_1560 a12_14e0 a12_13e0 a12_400 a12_380 a12_2e0 a12_2c0 a12_2a0 a12_280 a12_260 a12_240 q12_480 q12_420 b12_14a0 b12_1040 b12_a40 w12_130 w12_12c w12_128 w12_124 w12_120 w12_11c w12_118 w12_114 w12_110 w12_10c w12_108 w12_104 w12_100 w12_fc w12_f8 w12_f4 w12_f0 w12_ec w12_e8 w12_e4 w12_e0 w12_dc w12_d8 w12_d4 w12_d0 w12_cc w12_c8 w12_c4 w12_c0 w12_bc w12_b8 w12_b4 w12_b0 w12_ac w12_a8 w12_a4 w12_a0 w12_9c w12_98 w12_94 w12_90 w12_8c w12_88 w12_84 w12_80 w12_7c w12_78 w12_70 w12_6c w12_68 w12_64 w12_60 w12_5c w12_58 w12_54 w12_50 w12_4c w12_48 w12_44 w12_40 w12_3c w12_38 w12_34 w12_30 w12_2c w12_28 w12_24 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_9 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 m12 s12 u12 d12
  -- 0x16BA: memcpy from outside the stack
  obtain ⟨n14, P14, K14, X14⟩ := sv_mcRo2 (c := 0x4E0) (N := 0x60) F RS E13 s13 sv_at_16ba sv_at_16be
    (by decide) (by decide) g13_2 g13_10 g13_11 g13_12 (by decide) (Or.inr ⟨by decide, by decide⟩)
  have s14 := P14.st
  have fr14 := P14.fr
  have t14 : Steps n0 n14 := t13.trans P14.steps
  have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : SvCode n14.mem := E13.fr F fr14
  have V14 : SvSaves B n14.mem v := V13.keep K14 (by decide)
  have g14_2 : reg n14 sp = B + 0x21A0 := by rw [P14.regs sp (by decide), g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P14.regs (3 : Fin 32) (by decide), g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P14.regs (4 : Fin 32) (by decide), g13_4]
  have g14_8 : reg n14 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x4E0 := by rw [P14.regs (8 : Fin 32) (by decide), g13_8]
  have g14_9 : reg n14 (9 : Fin 32) = BitVec.ofNat 32 0x6 := by rw [P14.regs (9 : Fin 32) (by decide), g13_9]
  have g14_18 : reg n14 (18 : Fin 32) = out := by rw [P14.regs (18 : Fin 32) (by decide), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [P14.regs (19 : Fin 32) (by decide), g13_19]
  have g14_20 : reg n14 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P14.regs (20 : Fin 32) (by decide), g13_20]
  have g14_21 : reg n14 (21 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P14.regs (21 : Fin 32) (by decide), g13_21]
  have g14_22 : reg n14 (22 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [P14.regs (22 : Fin 32) (by decide), g13_22]
  have g14_23 : reg n14 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1500 := by rw [P14.regs (23 : Fin 32) (by decide), g13_23]
  have g14_24 : reg n14 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P14.regs (24 : Fin 32) (by decide), g13_24]
  have g14_25 : reg n14 (25 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [P14.regs (25 : Fin 32) (by decide), g13_25]
  have g14_26 : reg n14 (26 : Fin 32) = x26 := by rw [P14.regs (26 : Fin 32) (by decide), g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P14.regs (27 : Fin 32) (by decide), g13_27]
  have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x1380, 0x80), (0x420, 0x60), (0x480, 0x60), (0x4E0, 0x60)] := keep_kk13.trans K14.toL
  clear keep_kk13
  have w14_24 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K14.w32 (by decide) (by decide)).trans w13_24
  have w14_28 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K14.w32 (by decide) (by decide)).trans w13_28
  have w14_2c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K14.w32 (by decide) (by decide)).trans w13_2c
  have w14_30 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K14.w32 (by decide) (by decide)).trans w13_30
  have w14_34 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K14.w32 (by decide) (by decide)).trans w13_34
  have w14_38 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K14.w32 (by decide) (by decide)).trans w13_38
  have w14_3c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K14.w32 (by decide) (by decide)).trans w13_3c
  have w14_40 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K14.w32 (by decide) (by decide)).trans w13_40
  have w14_44 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K14.w32 (by decide) (by decide)).trans w13_44
  have w14_48 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K14.w32 (by decide) (by decide)).trans w13_48
  have w14_4c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K14.w32 (by decide) (by decide)).trans w13_4c
  have w14_50 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K14.w32 (by decide) (by decide)).trans w13_50
  have w14_54 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K14.w32 (by decide) (by decide)).trans w13_54
  have w14_58 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K14.w32 (by decide) (by decide)).trans w13_58
  have w14_5c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K14.w32 (by decide) (by decide)).trans w13_5c
  have w14_60 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K14.w32 (by decide) (by decide)).trans w13_60
  have w14_64 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K14.w32 (by decide) (by decide)).trans w13_64
  have w14_68 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K14.w32 (by decide) (by decide)).trans w13_68
  have w14_6c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K14.w32 (by decide) (by decide)).trans w13_6c
  have w14_70 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K14.w32 (by decide) (by decide)).trans w13_70
  have w14_78 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := (K14.w32 (by decide) (by decide)).trans w13_78
  have w14_7c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K14.w32 (by decide) (by decide)).trans w13_7c
  have w14_80 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K14.w32 (by decide) (by decide)).trans w13_80
  have w14_84 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K14.w32 (by decide) (by decide)).trans w13_84
  have w14_88 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K14.w32 (by decide) (by decide)).trans w13_88
  have w14_8c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K14.w32 (by decide) (by decide)).trans w13_8c
  have w14_90 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K14.w32 (by decide) (by decide)).trans w13_90
  have w14_94 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K14.w32 (by decide) (by decide)).trans w13_94
  have w14_98 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K14.w32 (by decide) (by decide)).trans w13_98
  have w14_9c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K14.w32 (by decide) (by decide)).trans w13_9c
  have w14_a0 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K14.w32 (by decide) (by decide)).trans w13_a0
  have w14_a4 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K14.w32 (by decide) (by decide)).trans w13_a4
  have w14_a8 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K14.w32 (by decide) (by decide)).trans w13_a8
  have w14_ac : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K14.w32 (by decide) (by decide)).trans w13_ac
  have w14_b0 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K14.w32 (by decide) (by decide)).trans w13_b0
  have w14_b4 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K14.w32 (by decide) (by decide)).trans w13_b4
  have w14_b8 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K14.w32 (by decide) (by decide)).trans w13_b8
  have w14_bc : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K14.w32 (by decide) (by decide)).trans w13_bc
  have w14_c0 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K14.w32 (by decide) (by decide)).trans w13_c0
  have w14_c4 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K14.w32 (by decide) (by decide)).trans w13_c4
  have w14_c8 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K14.w32 (by decide) (by decide)).trans w13_c8
  have w14_cc : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K14.w32 (by decide) (by decide)).trans w13_cc
  have w14_d0 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K14.w32 (by decide) (by decide)).trans w13_d0
  have w14_d4 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K14.w32 (by decide) (by decide)).trans w13_d4
  have w14_d8 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K14.w32 (by decide) (by decide)).trans w13_d8
  have w14_dc : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K14.w32 (by decide) (by decide)).trans w13_dc
  have w14_e0 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K14.w32 (by decide) (by decide)).trans w13_e0
  have w14_e4 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K14.w32 (by decide) (by decide)).trans w13_e4
  have w14_e8 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K14.w32 (by decide) (by decide)).trans w13_e8
  have w14_ec : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K14.w32 (by decide) (by decide)).trans w13_ec
  have w14_f0 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K14.w32 (by decide) (by decide)).trans w13_f0
  have w14_f4 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K14.w32 (by decide) (by decide)).trans w13_f4
  have w14_f8 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K14.w32 (by decide) (by decide)).trans w13_f8
  have w14_fc : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K14.w32 (by decide) (by decide)).trans w13_fc
  have w14_100 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K14.w32 (by decide) (by decide)).trans w13_100
  have w14_104 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K14.w32 (by decide) (by decide)).trans w13_104
  have w14_108 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K14.w32 (by decide) (by decide)).trans w13_108
  have w14_10c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K14.w32 (by decide) (by decide)).trans w13_10c
  have w14_110 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K14.w32 (by decide) (by decide)).trans w13_110
  have w14_114 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K14.w32 (by decide) (by decide)).trans w13_114
  have w14_118 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K14.w32 (by decide) (by decide)).trans w13_118
  have w14_11c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K14.w32 (by decide) (by decide)).trans w13_11c
  have w14_120 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K14.w32 (by decide) (by decide)).trans w13_120
  have w14_124 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K14.w32 (by decide) (by decide)).trans w13_124
  have w14_128 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K14.w32 (by decide) (by decide)).trans w13_128
  have w14_12c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K14.w32 (by decide) (by decide)).trans w13_12c
  have w14_130 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K14.w32 (by decide) (by decide)).trans w13_130
  have b14_a40 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = gs := (K14.b8 (by decide) (by decide)).trans b13_a40
  have b14_1040 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = gs := (K14.b8 (by decide) (by decide)).trans b13_1040
  have b14_14a0 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := (K14.b8 (by decide) (by decide)).trans b13_14a0
  have q14_420 : ∀ j, j < 96 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K14.range (by decide) (by decide) j hj).trans (q13_420 j hj)
  have q14_480 : ∀ j, j < 96 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0x480 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K14.range (by decide) (by decide) j hj).trans (q13_480 j hj)
  have a14_240 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := (K14.acc (by decide) (by decide)).trans a13_240
  have a14_260 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := (K14.acc (by decide) (by decide)).trans a13_260
  have a14_280 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := (K14.acc (by decide) (by decide)).trans a13_280
  have a14_2a0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K14.acc (by decide) (by decide)).trans a13_2a0
  have a14_2c0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K14.acc (by decide) (by decide)).trans a13_2c0
  have a14_2e0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K14.acc (by decide) (by decide)).trans a13_2e0
  have a14_380 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := (K14.acc (by decide) (by decide)).trans a13_380
  have a14_400 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := (K14.acc (by decide) (by decide)).trans a13_400
  have a14_13e0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U2 := (K14.acc (by decide) (by decide)).trans a13_13e0
  have a14_14e0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x14E0) 8 = U1 := (K14.acc (by decide) (by decide)).trans a13_14e0
  have a14_1560 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1560) 8 = U2 := (K14.acc (by decide) (by decide)).trans a13_1560
  have p14_320 : ptF n14.mem B 0x320 = P0 := (K14.pt (by decide) (by decide)).trans p13_320
  have p14_3a0 : ptF n14.mem B 0x3A0 = P1 := (K14.pt (by decide) (by decide)).trans p13_3a0
  have p14_540 : ptF n14.mem B 0x540 = tbl2 P0 3 := (K14.pt (by decide) (by decide)).trans p13_540
  have p14_5a0 : ptF n14.mem B 0x5A0 = tbl2 P0 4 := (K14.pt (by decide) (by decide)).trans p13_5a0
  have p14_600 : ptF n14.mem B 0x600 = tbl2 P0 5 := (K14.pt (by decide) (by decide)).trans p13_600
  have p14_660 : ptF n14.mem B 0x660 = tbl2 P0 6 := (K14.pt (by decide) (by decide)).trans p13_660
  have p14_6c0 : ptF n14.mem B 0x6C0 = tbl2 P0 7 := (K14.pt (by decide) (by decide)).trans p13_6c0
  have p14_a20 : ptF n14.mem B 0xA20 = tbl2 P0 0 := (K14.pt (by decide) (by decide)).trans p13_a20
  have p14_a80 : ptF n14.mem B 0xA80 = tbl2 P0 1 := (K14.pt (by decide) (by decide)).trans p13_a80
  have p14_ae0 : ptF n14.mem B 0xAE0 = tbl2 P0 2 := (K14.pt (by decide) (by decide)).trans p13_ae0
  have p14_b40 : ptF n14.mem B 0xB40 = tbl2 P0 3 := (K14.pt (by decide) (by decide)).trans p13_b40
  have p14_ba0 : ptF n14.mem B 0xBA0 = tbl2 P0 4 := (K14.pt (by decide) (by decide)).trans p13_ba0
  have p14_c00 : ptF n14.mem B 0xC00 = tbl2 P0 5 := (K14.pt (by decide) (by decide)).trans p13_c00
  have p14_c60 : ptF n14.mem B 0xC60 = tbl2 P0 6 := (K14.pt (by decide) (by decide)).trans p13_c60
  have p14_cc0 : ptF n14.mem B 0xCC0 = tbl2 P0 7 := (K14.pt (by decide) (by decide)).trans p13_cc0
  have p14_1020 : ptF n14.mem B 0x1020 = tbl2 P0 0 := (K14.pt (by decide) (by decide)).trans p13_1020
  have p14_1080 : ptF n14.mem B 0x1080 = tbl2 P0 1 := (K14.pt (by decide) (by decide)).trans p13_1080
  have p14_10e0 : ptF n14.mem B 0x10E0 = tbl2 P0 2 := (K14.pt (by decide) (by decide)).trans p13_10e0
  have p14_1140 : ptF n14.mem B 0x1140 = tbl2 P0 3 := (K14.pt (by decide) (by decide)).trans p13_1140
  have p14_11a0 : ptF n14.mem B 0x11A0 = tbl2 P0 4 := (K14.pt (by decide) (by decide)).trans p13_11a0
  have p14_1200 : ptF n14.mem B 0x1200 = tbl2 P0 5 := (K14.pt (by decide) (by decide)).trans p13_1200
  have p14_1260 : ptF n14.mem B 0x1260 = tbl2 P0 6 := (K14.pt (by decide) (by decide)).trans p13_1260
  have p14_12c0 : ptF n14.mem B 0x12C0 = tbl2 P0 7 := (K14.pt (by decide) (by decide)).trans p13_12c0
  have p14_1320 : ptF n14.mem B 0x1320 = ptDbl2 P0 := (K14.pt (by decide) (by decide)).trans p13_1320
  have p14_1380 : ptF n14.mem B 0x1380 = P1 := (K14.pt (by decide) (by decide)).trans p13_1380
  have p14_1480 : ptF n14.mem B 0x1480 = P0 := (K14.pt (by decide) (by decide)).trans p13_1480
  have p14_1500 : ptF n14.mem B 0x1500 = P1 := (K14.pt (by decide) (by decide)).trans p13_1500
  have q14_4e0 : ∀ j, j < 96 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0x4E0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) :=
    fun j hj => (X14 j hj).trans (fR13 _ (SvRo2.r RS (Or.inr ⟨by decide, by decide⟩) hj))
  clear p13_1500 p13_1480 p13_1380 p13_1320 p13_12c0 p13_1260 p13_1200 p13_11a0 p13_1140 p13_10e0 p13_1080 p13_1020 p13_cc0 p13_c60 p13_c00 p13_ba0 p13_b40 p13_ae0 p13_a80 p13_a20 p13_6c0 p13_660 p13_600 p13_5a0 p13_540 p13_4e0 p13_3a0 p13_320 a13_1560 a13_14e0 a13_13e0 a13_400 a13_380 a13_2e0 a13_2c0 a13_2a0 a13_280 a13_260 a13_240 q13_480 q13_420 b13_14a0 b13_1040 b13_a40 w13_130 w13_12c w13_128 w13_124 w13_120 w13_11c w13_118 w13_114 w13_110 w13_10c w13_108 w13_104 w13_100 w13_fc w13_f8 w13_f4 w13_f0 w13_ec w13_e8 w13_e4 w13_e0 w13_dc w13_d8 w13_d4 w13_d0 w13_cc w13_c8 w13_c4 w13_c0 w13_bc w13_b8 w13_b4 w13_b0 w13_ac w13_a8 w13_a4 w13_a0 w13_9c w13_98 w13_94 w13_90 w13_8c w13_88 w13_84 w13_80 w13_7c w13_78 w13_70 w13_6c w13_68 w13_64 w13_60 w13_5c w13_58 w13_54 w13_50 w13_4c w13_48 w13_44 w13_40 w13_3c w13_38 w13_34 w13_30 w13_2c w13_28 w13_24 g13_12 g13_11 g13_10 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_9 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 rb13 s13 m13 u13 c13
  -- 0x16C2
  obtain ⟨n15, c15, u15⟩ := s14.block svEcT1a16c2 E14.self svEcT1a16c2_end
    ⟨trivial, trivial, trivial⟩
  have m15 : n15.mem = n14.mem := u15.mem
  have s15 : St n15.mem SV n15 0x16C8 (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
  have rb15 : ∀ q, reg n15 q = (runBlock svEcT1a16c2 (n14.mem, reg n14)).2 q := fun q => by rw [u15.regs]
  have fr15 : ∀ x, SvR B x → n15.mem x = n14.mem x := fun x _ => by rw [m15]
  have t15 : Steps n0 n15 := t14.trans c15
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.same m15
  have g15_2 : reg n15 sp = B + 0x21A0 := by
    rw [rb15, runBlock_reg _ _ _ sp s14.zero (by decide), g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb15, runBlock_reg _ _ _ (3 : Fin 32) s14.zero (by decide), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb15, runBlock_reg _ _ _ (4 : Fin 32) s14.zero (by decide), g14_4]
  have g15_18 : reg n15 (18 : Fin 32) = out := by
    rw [rb15, runBlock_reg _ _ _ (18 : Fin 32) s14.zero (by decide), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by
    rw [rb15, runBlock_reg _ _ _ (19 : Fin 32) s14.zero (by decide), g14_19]
  have g15_20 : reg n15 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb15, runBlock_reg _ _ _ (20 : Fin 32) s14.zero (by decide), g14_20]
  have g15_21 : reg n15 (21 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb15, runBlock_reg _ _ _ (21 : Fin 32) s14.zero (by decide), g14_21]
  have g15_22 : reg n15 (22 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb15, runBlock_reg _ _ _ (22 : Fin 32) s14.zero (by decide), g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1500 := by
    rw [rb15, runBlock_reg _ _ _ (23 : Fin 32) s14.zero (by decide), g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb15, runBlock_reg _ _ _ (24 : Fin 32) s14.zero (by decide), g14_24]
  have g15_25 : reg n15 (25 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb15, runBlock_reg _ _ _ (25 : Fin 32) s14.zero (by decide), g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = x26 := by
    rw [rb15, runBlock_reg _ _ _ (26 : Fin 32) s14.zero (by decide), g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb15, runBlock_reg _ _ _ (27 : Fin 32) s14.zero (by decide), g14_27]
  have g15_8 : reg n15 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x540 := by
    rw [rb15]; simp +decide only [runBlock, BInstr.run, svEcT1a16c2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g14_2, g14_3, g14_4, g14_8, g14_9, g14_18, g14_19, g14_20, g14_21, g14_22, g14_23, g14_24, g14_25, g14_26, g14_27, s14.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g15_9 : reg n15 (9 : Fin 32) = BitVec.ofNat 32 0x5 := by
    rw [rb15]; simp +decide only [runBlock, BInstr.run, svEcT1a16c2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g14_2, g14_3, g14_4, g14_8, g14_9, g14_18, g14_19, g14_20, g14_21, g14_22, g14_23, g14_24, g14_25, g14_26, g14_27, s14.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x1380, 0x80), (0x420, 0x60), (0x480, 0x60), (0x4E0, 0x60)] := by rw [m15]; exact keep_kk14
  clear keep_kk14
  have w15_24 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m15]; exact w14_24
  have w15_28 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m15]; exact w14_28
  have w15_2c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m15]; exact w14_2c
  have w15_30 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m15]; exact w14_30
  have w15_34 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m15]; exact w14_34
  have w15_38 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m15]; exact w14_38
  have w15_3c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m15]; exact w14_3c
  have w15_40 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m15]; exact w14_40
  have w15_44 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m15]; exact w14_44
  have w15_48 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m15]; exact w14_48
  have w15_4c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m15]; exact w14_4c
  have w15_50 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m15]; exact w14_50
  have w15_54 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m15]; exact w14_54
  have w15_58 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m15]; exact w14_58
  have w15_5c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m15]; exact w14_5c
  have w15_60 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m15]; exact w14_60
  have w15_64 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m15]; exact w14_64
  have w15_68 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m15]; exact w14_68
  have w15_6c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m15]; exact w14_6c
  have w15_70 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m15]; exact w14_70
  have w15_78 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m15]; exact w14_78
  have w15_7c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m15]; exact w14_7c
  have w15_80 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m15]; exact w14_80
  have w15_84 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m15]; exact w14_84
  have w15_88 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m15]; exact w14_88
  have w15_8c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m15]; exact w14_8c
  have w15_90 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m15]; exact w14_90
  have w15_94 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m15]; exact w14_94
  have w15_98 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m15]; exact w14_98
  have w15_9c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m15]; exact w14_9c
  have w15_a0 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m15]; exact w14_a0
  have w15_a4 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m15]; exact w14_a4
  have w15_a8 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m15]; exact w14_a8
  have w15_ac : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m15]; exact w14_ac
  have w15_b0 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m15]; exact w14_b0
  have w15_b4 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m15]; exact w14_b4
  have w15_b8 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m15]; exact w14_b8
  have w15_bc : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m15]; exact w14_bc
  have w15_c0 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m15]; exact w14_c0
  have w15_c4 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m15]; exact w14_c4
  have w15_c8 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m15]; exact w14_c8
  have w15_cc : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m15]; exact w14_cc
  have w15_d0 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m15]; exact w14_d0
  have w15_d4 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m15]; exact w14_d4
  have w15_d8 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m15]; exact w14_d8
  have w15_dc : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m15]; exact w14_dc
  have w15_e0 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m15]; exact w14_e0
  have w15_e4 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m15]; exact w14_e4
  have w15_e8 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m15]; exact w14_e8
  have w15_ec : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m15]; exact w14_ec
  have w15_f0 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m15]; exact w14_f0
  have w15_f4 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m15]; exact w14_f4
  have w15_f8 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m15]; exact w14_f8
  have w15_fc : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m15]; exact w14_fc
  have w15_100 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m15]; exact w14_100
  have w15_104 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m15]; exact w14_104
  have w15_108 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m15]; exact w14_108
  have w15_10c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m15]; exact w14_10c
  have w15_110 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m15]; exact w14_110
  have w15_114 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m15]; exact w14_114
  have w15_118 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m15]; exact w14_118
  have w15_11c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m15]; exact w14_11c
  have w15_120 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m15]; exact w14_120
  have w15_124 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m15]; exact w14_124
  have w15_128 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m15]; exact w14_128
  have w15_12c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m15]; exact w14_12c
  have w15_130 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m15]; exact w14_130
  have b15_a40 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = gs := by rw [m15]; exact b14_a40
  have b15_1040 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = gs := by rw [m15]; exact b14_1040
  have b15_14a0 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := by rw [m15]; exact b14_14a0
  have q15_420 : ∀ j, j < 96 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m15]; exact q14_420 j hj
  have q15_480 : ∀ j, j < 96 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0x480 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m15]; exact q14_480 j hj
  have q15_4e0 : ∀ j, j < 96 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0x4E0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m15]; exact q14_4e0 j hj
  have a15_240 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m15]; exact a14_240
  have a15_260 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m15]; exact a14_260
  have a15_280 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m15]; exact a14_280
  have a15_2a0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m15]; exact a14_2a0
  have a15_2c0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m15]; exact a14_2c0
  have a15_2e0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m15]; exact a14_2e0
  have a15_380 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m15]; exact a14_380
  have a15_400 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m15]; exact a14_400
  have a15_13e0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U2 := by rw [m15]; exact a14_13e0
  have a15_14e0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x14E0) 8 = U1 := by rw [m15]; exact a14_14e0
  have a15_1560 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1560) 8 = U2 := by rw [m15]; exact a14_1560
  have p15_320 : ptF n15.mem B 0x320 = P0 := by rw [m15]; exact p14_320
  have p15_3a0 : ptF n15.mem B 0x3A0 = P1 := by rw [m15]; exact p14_3a0
  have p15_540 : ptF n15.mem B 0x540 = tbl2 P0 3 := by rw [m15]; exact p14_540
  have p15_5a0 : ptF n15.mem B 0x5A0 = tbl2 P0 4 := by rw [m15]; exact p14_5a0
  have p15_600 : ptF n15.mem B 0x600 = tbl2 P0 5 := by rw [m15]; exact p14_600
  have p15_660 : ptF n15.mem B 0x660 = tbl2 P0 6 := by rw [m15]; exact p14_660
  have p15_6c0 : ptF n15.mem B 0x6C0 = tbl2 P0 7 := by rw [m15]; exact p14_6c0
  have p15_a20 : ptF n15.mem B 0xA20 = tbl2 P0 0 := by rw [m15]; exact p14_a20
  have p15_a80 : ptF n15.mem B 0xA80 = tbl2 P0 1 := by rw [m15]; exact p14_a80
  have p15_ae0 : ptF n15.mem B 0xAE0 = tbl2 P0 2 := by rw [m15]; exact p14_ae0
  have p15_b40 : ptF n15.mem B 0xB40 = tbl2 P0 3 := by rw [m15]; exact p14_b40
  have p15_ba0 : ptF n15.mem B 0xBA0 = tbl2 P0 4 := by rw [m15]; exact p14_ba0
  have p15_c00 : ptF n15.mem B 0xC00 = tbl2 P0 5 := by rw [m15]; exact p14_c00
  have p15_c60 : ptF n15.mem B 0xC60 = tbl2 P0 6 := by rw [m15]; exact p14_c60
  have p15_cc0 : ptF n15.mem B 0xCC0 = tbl2 P0 7 := by rw [m15]; exact p14_cc0
  have p15_1020 : ptF n15.mem B 0x1020 = tbl2 P0 0 := by rw [m15]; exact p14_1020
  have p15_1080 : ptF n15.mem B 0x1080 = tbl2 P0 1 := by rw [m15]; exact p14_1080
  have p15_10e0 : ptF n15.mem B 0x10E0 = tbl2 P0 2 := by rw [m15]; exact p14_10e0
  have p15_1140 : ptF n15.mem B 0x1140 = tbl2 P0 3 := by rw [m15]; exact p14_1140
  have p15_11a0 : ptF n15.mem B 0x11A0 = tbl2 P0 4 := by rw [m15]; exact p14_11a0
  have p15_1200 : ptF n15.mem B 0x1200 = tbl2 P0 5 := by rw [m15]; exact p14_1200
  have p15_1260 : ptF n15.mem B 0x1260 = tbl2 P0 6 := by rw [m15]; exact p14_1260
  have p15_12c0 : ptF n15.mem B 0x12C0 = tbl2 P0 7 := by rw [m15]; exact p14_12c0
  have p15_1320 : ptF n15.mem B 0x1320 = ptDbl2 P0 := by rw [m15]; exact p14_1320
  have p15_1380 : ptF n15.mem B 0x1380 = P1 := by rw [m15]; exact p14_1380
  have p15_1480 : ptF n15.mem B 0x1480 = P0 := by rw [m15]; exact p14_1480
  have p15_1500 : ptF n15.mem B 0x1500 = P1 := by rw [m15]; exact p14_1500
  clear q14_4e0 p14_1500 p14_1480 p14_1380 p14_1320 p14_12c0 p14_1260 p14_1200 p14_11a0 p14_1140 p14_10e0 p14_1080 p14_1020 p14_cc0 p14_c60 p14_c00 p14_ba0 p14_b40 p14_ae0 p14_a80 p14_a20 p14_6c0 p14_660 p14_600 p14_5a0 p14_540 p14_3a0 p14_320 a14_1560 a14_14e0 a14_13e0 a14_400 a14_380 a14_2e0 a14_2c0 a14_2a0 a14_280 a14_260 a14_240 q14_480 q14_420 b14_14a0 b14_1040 b14_a40 w14_130 w14_12c w14_128 w14_124 w14_120 w14_11c w14_118 w14_114 w14_110 w14_10c w14_108 w14_104 w14_100 w14_fc w14_f8 w14_f4 w14_f0 w14_ec w14_e8 w14_e4 w14_e0 w14_dc w14_d8 w14_d4 w14_d0 w14_cc w14_c8 w14_c4 w14_c0 w14_bc w14_b8 w14_b4 w14_b0 w14_ac w14_a8 w14_a4 w14_a0 w14_9c w14_98 w14_94 w14_90 w14_8c w14_88 w14_84 w14_80 w14_7c w14_78 w14_70 w14_6c w14_68 w14_64 w14_60 w14_5c w14_58 w14_54 w14_50 w14_4c w14_48 w14_44 w14_40 w14_3c w14_38 w14_34 w14_30 w14_2c w14_28 w14_24 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_9 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 s14 X14 K14 P14
  -- 0x16C8: branch, taken
  obtain ⟨n16, d16, u16⟩ := s15.taken E15.self 0x16B2 sv_at_16c8
    (by decide) (by rw [g15_9, s15.zero]; decide)
  have s16 : St n16.mem SV n16 0x16B2 (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
  have m16 : n16.mem = n15.mem := u16.mem
  have fr16 : ∀ x, SvR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
  have t16 : Steps n0 n16 := t15.trans (.single d16)
  have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : SvCode n16.mem := E15.fr F fr16
  have V16 : SvSaves B n16.mem v := V15.same m16
  have g16_2 : reg n16 sp = B + 0x21A0 := by rw [u16.regs, g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u16.regs, g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u16.regs, g15_4]
  have g16_8 : reg n16 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x540 := by rw [u16.regs, g15_8]
  have g16_9 : reg n16 (9 : Fin 32) = BitVec.ofNat 32 0x5 := by rw [u16.regs, g15_9]
  have g16_18 : reg n16 (18 : Fin 32) = out := by rw [u16.regs, g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [u16.regs, g15_19]
  have g16_20 : reg n16 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u16.regs, g15_20]
  have g16_21 : reg n16 (21 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u16.regs, g15_21]
  have g16_22 : reg n16 (22 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [u16.regs, g15_22]
  have g16_23 : reg n16 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1500 := by rw [u16.regs, g15_23]
  have g16_24 : reg n16 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u16.regs, g15_24]
  have g16_25 : reg n16 (25 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [u16.regs, g15_25]
  have g16_26 : reg n16 (26 : Fin 32) = x26 := by rw [u16.regs, g15_26]
  have g16_27 : reg n16 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u16.regs, g15_27]
  have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x1380, 0x80), (0x420, 0x60), (0x480, 0x60), (0x4E0, 0x60)] := by rw [m16]; exact keep_kk15
  clear keep_kk15
  have w16_24 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m16]; exact w15_24
  have w16_28 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m16]; exact w15_28
  have w16_2c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m16]; exact w15_2c
  have w16_30 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m16]; exact w15_30
  have w16_34 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m16]; exact w15_34
  have w16_38 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m16]; exact w15_38
  have w16_3c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m16]; exact w15_3c
  have w16_40 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m16]; exact w15_40
  have w16_44 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m16]; exact w15_44
  have w16_48 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m16]; exact w15_48
  have w16_4c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m16]; exact w15_4c
  have w16_50 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m16]; exact w15_50
  have w16_54 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m16]; exact w15_54
  have w16_58 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m16]; exact w15_58
  have w16_5c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m16]; exact w15_5c
  have w16_60 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m16]; exact w15_60
  have w16_64 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m16]; exact w15_64
  have w16_68 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m16]; exact w15_68
  have w16_6c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m16]; exact w15_6c
  have w16_70 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m16]; exact w15_70
  have w16_78 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m16]; exact w15_78
  have w16_7c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m16]; exact w15_7c
  have w16_80 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m16]; exact w15_80
  have w16_84 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m16]; exact w15_84
  have w16_88 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m16]; exact w15_88
  have w16_8c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m16]; exact w15_8c
  have w16_90 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m16]; exact w15_90
  have w16_94 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m16]; exact w15_94
  have w16_98 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m16]; exact w15_98
  have w16_9c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m16]; exact w15_9c
  have w16_a0 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m16]; exact w15_a0
  have w16_a4 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m16]; exact w15_a4
  have w16_a8 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m16]; exact w15_a8
  have w16_ac : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m16]; exact w15_ac
  have w16_b0 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m16]; exact w15_b0
  have w16_b4 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m16]; exact w15_b4
  have w16_b8 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m16]; exact w15_b8
  have w16_bc : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m16]; exact w15_bc
  have w16_c0 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m16]; exact w15_c0
  have w16_c4 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m16]; exact w15_c4
  have w16_c8 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m16]; exact w15_c8
  have w16_cc : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m16]; exact w15_cc
  have w16_d0 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m16]; exact w15_d0
  have w16_d4 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m16]; exact w15_d4
  have w16_d8 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m16]; exact w15_d8
  have w16_dc : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m16]; exact w15_dc
  have w16_e0 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m16]; exact w15_e0
  have w16_e4 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m16]; exact w15_e4
  have w16_e8 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m16]; exact w15_e8
  have w16_ec : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m16]; exact w15_ec
  have w16_f0 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m16]; exact w15_f0
  have w16_f4 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m16]; exact w15_f4
  have w16_f8 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m16]; exact w15_f8
  have w16_fc : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m16]; exact w15_fc
  have w16_100 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m16]; exact w15_100
  have w16_104 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m16]; exact w15_104
  have w16_108 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m16]; exact w15_108
  have w16_10c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m16]; exact w15_10c
  have w16_110 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m16]; exact w15_110
  have w16_114 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m16]; exact w15_114
  have w16_118 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m16]; exact w15_118
  have w16_11c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m16]; exact w15_11c
  have w16_120 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m16]; exact w15_120
  have w16_124 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m16]; exact w15_124
  have w16_128 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m16]; exact w15_128
  have w16_12c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m16]; exact w15_12c
  have w16_130 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m16]; exact w15_130
  have b16_a40 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = gs := by rw [m16]; exact b15_a40
  have b16_1040 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = gs := by rw [m16]; exact b15_1040
  have b16_14a0 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := by rw [m16]; exact b15_14a0
  have q16_420 : ∀ j, j < 96 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m16]; exact q15_420 j hj
  have q16_480 : ∀ j, j < 96 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0x480 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m16]; exact q15_480 j hj
  have q16_4e0 : ∀ j, j < 96 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0x4E0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m16]; exact q15_4e0 j hj
  have a16_240 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m16]; exact a15_240
  have a16_260 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m16]; exact a15_260
  have a16_280 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m16]; exact a15_280
  have a16_2a0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m16]; exact a15_2a0
  have a16_2c0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m16]; exact a15_2c0
  have a16_2e0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m16]; exact a15_2e0
  have a16_380 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m16]; exact a15_380
  have a16_400 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m16]; exact a15_400
  have a16_13e0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U2 := by rw [m16]; exact a15_13e0
  have a16_14e0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x14E0) 8 = U1 := by rw [m16]; exact a15_14e0
  have a16_1560 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1560) 8 = U2 := by rw [m16]; exact a15_1560
  have p16_320 : ptF n16.mem B 0x320 = P0 := by rw [m16]; exact p15_320
  have p16_3a0 : ptF n16.mem B 0x3A0 = P1 := by rw [m16]; exact p15_3a0
  have p16_540 : ptF n16.mem B 0x540 = tbl2 P0 3 := by rw [m16]; exact p15_540
  have p16_5a0 : ptF n16.mem B 0x5A0 = tbl2 P0 4 := by rw [m16]; exact p15_5a0
  have p16_600 : ptF n16.mem B 0x600 = tbl2 P0 5 := by rw [m16]; exact p15_600
  have p16_660 : ptF n16.mem B 0x660 = tbl2 P0 6 := by rw [m16]; exact p15_660
  have p16_6c0 : ptF n16.mem B 0x6C0 = tbl2 P0 7 := by rw [m16]; exact p15_6c0
  have p16_a20 : ptF n16.mem B 0xA20 = tbl2 P0 0 := by rw [m16]; exact p15_a20
  have p16_a80 : ptF n16.mem B 0xA80 = tbl2 P0 1 := by rw [m16]; exact p15_a80
  have p16_ae0 : ptF n16.mem B 0xAE0 = tbl2 P0 2 := by rw [m16]; exact p15_ae0
  have p16_b40 : ptF n16.mem B 0xB40 = tbl2 P0 3 := by rw [m16]; exact p15_b40
  have p16_ba0 : ptF n16.mem B 0xBA0 = tbl2 P0 4 := by rw [m16]; exact p15_ba0
  have p16_c00 : ptF n16.mem B 0xC00 = tbl2 P0 5 := by rw [m16]; exact p15_c00
  have p16_c60 : ptF n16.mem B 0xC60 = tbl2 P0 6 := by rw [m16]; exact p15_c60
  have p16_cc0 : ptF n16.mem B 0xCC0 = tbl2 P0 7 := by rw [m16]; exact p15_cc0
  have p16_1020 : ptF n16.mem B 0x1020 = tbl2 P0 0 := by rw [m16]; exact p15_1020
  have p16_1080 : ptF n16.mem B 0x1080 = tbl2 P0 1 := by rw [m16]; exact p15_1080
  have p16_10e0 : ptF n16.mem B 0x10E0 = tbl2 P0 2 := by rw [m16]; exact p15_10e0
  have p16_1140 : ptF n16.mem B 0x1140 = tbl2 P0 3 := by rw [m16]; exact p15_1140
  have p16_11a0 : ptF n16.mem B 0x11A0 = tbl2 P0 4 := by rw [m16]; exact p15_11a0
  have p16_1200 : ptF n16.mem B 0x1200 = tbl2 P0 5 := by rw [m16]; exact p15_1200
  have p16_1260 : ptF n16.mem B 0x1260 = tbl2 P0 6 := by rw [m16]; exact p15_1260
  have p16_12c0 : ptF n16.mem B 0x12C0 = tbl2 P0 7 := by rw [m16]; exact p15_12c0
  have p16_1320 : ptF n16.mem B 0x1320 = ptDbl2 P0 := by rw [m16]; exact p15_1320
  have p16_1380 : ptF n16.mem B 0x1380 = P1 := by rw [m16]; exact p15_1380
  have p16_1480 : ptF n16.mem B 0x1480 = P0 := by rw [m16]; exact p15_1480
  have p16_1500 : ptF n16.mem B 0x1500 = P1 := by rw [m16]; exact p15_1500
  clear p15_1500 p15_1480 p15_1380 p15_1320 p15_12c0 p15_1260 p15_1200 p15_11a0 p15_1140 p15_10e0 p15_1080 p15_1020 p15_cc0 p15_c60 p15_c00 p15_ba0 p15_b40 p15_ae0 p15_a80 p15_a20 p15_6c0 p15_660 p15_600 p15_5a0 p15_540 p15_3a0 p15_320 a15_1560 a15_14e0 a15_13e0 a15_400 a15_380 a15_2e0 a15_2c0 a15_2a0 a15_280 a15_260 a15_240 q15_4e0 q15_480 q15_420 b15_14a0 b15_1040 b15_a40 w15_130 w15_12c w15_128 w15_124 w15_120 w15_11c w15_118 w15_114 w15_110 w15_10c w15_108 w15_104 w15_100 w15_fc w15_f8 w15_f4 w15_f0 w15_ec w15_e8 w15_e4 w15_e0 w15_dc w15_d8 w15_d4 w15_d0 w15_cc w15_c8 w15_c4 w15_c0 w15_bc w15_b8 w15_b4 w15_b0 w15_ac w15_a8 w15_a4 w15_a0 w15_9c w15_98 w15_94 w15_90 w15_8c w15_88 w15_84 w15_80 w15_7c w15_78 w15_70 w15_6c w15_68 w15_64 w15_60 w15_5c w15_58 w15_54 w15_50 w15_4c w15_48 w15_44 w15_40 w15_3c w15_38 w15_34 w15_30 w15_2c w15_28 w15_24 g15_9 g15_8 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 rb15 s15 m15 u15 c15
  -- 0x16B2
  obtain ⟨n17, c17, u17⟩ := s16.block svEcT1a16b2 E16.self svEcT1a16b2_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m17 : n17.mem = n16.mem := u17.mem
  have s17 : St n17.mem SV n17 0x16BA (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
  have rb17 : ∀ q, reg n17 q = (runBlock svEcT1a16b2 (n16.mem, reg n16)).2 q := fun q => by rw [u17.regs]
  have fr17 : ∀ x, SvR B x → n17.mem x = n16.mem x := fun x _ => by rw [m17]
  have t17 : Steps n0 n17 := t16.trans c17
  have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
  have E17 : SvCode n17.mem := E16.fr F fr17
  have V17 : SvSaves B n17.mem v := V16.same m17
  have g17_2 : reg n17 sp = B + 0x21A0 := by
    rw [rb17, runBlock_reg _ _ _ sp s16.zero (by decide), g16_2]
  have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb17, runBlock_reg _ _ _ (3 : Fin 32) s16.zero (by decide), g16_3]
  have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb17, runBlock_reg _ _ _ (4 : Fin 32) s16.zero (by decide), g16_4]
  have g17_8 : reg n17 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x540 := by
    rw [rb17, runBlock_reg _ _ _ (8 : Fin 32) s16.zero (by decide), g16_8]
  have g17_9 : reg n17 (9 : Fin 32) = BitVec.ofNat 32 0x5 := by
    rw [rb17, runBlock_reg _ _ _ (9 : Fin 32) s16.zero (by decide), g16_9]
  have g17_18 : reg n17 (18 : Fin 32) = out := by
    rw [rb17, runBlock_reg _ _ _ (18 : Fin 32) s16.zero (by decide), g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = bp := by
    rw [rb17, runBlock_reg _ _ _ (19 : Fin 32) s16.zero (by decide), g16_19]
  have g17_20 : reg n17 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb17, runBlock_reg _ _ _ (20 : Fin 32) s16.zero (by decide), g16_20]
  have g17_21 : reg n17 (21 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb17, runBlock_reg _ _ _ (21 : Fin 32) s16.zero (by decide), g16_21]
  have g17_22 : reg n17 (22 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb17, runBlock_reg _ _ _ (22 : Fin 32) s16.zero (by decide), g16_22]
  have g17_23 : reg n17 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1500 := by
    rw [rb17, runBlock_reg _ _ _ (23 : Fin 32) s16.zero (by decide), g16_23]
  have g17_24 : reg n17 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb17, runBlock_reg _ _ _ (24 : Fin 32) s16.zero (by decide), g16_24]
  have g17_25 : reg n17 (25 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb17, runBlock_reg _ _ _ (25 : Fin 32) s16.zero (by decide), g16_25]
  have g17_26 : reg n17 (26 : Fin 32) = x26 := by
    rw [rb17, runBlock_reg _ _ _ (26 : Fin 32) s16.zero (by decide), g16_26]
  have g17_27 : reg n17 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb17, runBlock_reg _ _ _ (27 : Fin 32) s16.zero (by decide), g16_27]
  have g17_10 : reg n17 a0 = B + 0x21A0 + BitVec.ofNat 32 0x540 := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, svEcT1a16b2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_8, g16_9, g16_18, g16_19, g16_20, g16_21, g16_22, g16_23, g16_24, g16_25, g16_26, g16_27, s16.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g17_11 : reg n17 a1 = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, svEcT1a16b2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_8, g16_9, g16_18, g16_19, g16_20, g16_21, g16_22, g16_23, g16_24, g16_25, g16_26, g16_27, s16.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g17_12 : reg n17 a2 = BitVec.ofNat 32 0x60 := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, svEcT1a16b2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_8, g16_9, g16_18, g16_19, g16_20, g16_21, g16_22, g16_23, g16_24, g16_25, g16_26, g16_27, s16.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x1380, 0x80), (0x420, 0x60), (0x480, 0x60), (0x4E0, 0x60)] := by rw [m17]; exact keep_kk16
  clear keep_kk16
  have w17_24 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m17]; exact w16_24
  have w17_28 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m17]; exact w16_28
  have w17_2c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m17]; exact w16_2c
  have w17_30 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m17]; exact w16_30
  have w17_34 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m17]; exact w16_34
  have w17_38 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m17]; exact w16_38
  have w17_3c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m17]; exact w16_3c
  have w17_40 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m17]; exact w16_40
  have w17_44 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m17]; exact w16_44
  have w17_48 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m17]; exact w16_48
  have w17_4c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m17]; exact w16_4c
  have w17_50 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m17]; exact w16_50
  have w17_54 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m17]; exact w16_54
  have w17_58 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m17]; exact w16_58
  have w17_5c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m17]; exact w16_5c
  have w17_60 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m17]; exact w16_60
  have w17_64 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m17]; exact w16_64
  have w17_68 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m17]; exact w16_68
  have w17_6c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m17]; exact w16_6c
  have w17_70 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m17]; exact w16_70
  have w17_78 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m17]; exact w16_78
  have w17_7c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m17]; exact w16_7c
  have w17_80 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m17]; exact w16_80
  have w17_84 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m17]; exact w16_84
  have w17_88 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m17]; exact w16_88
  have w17_8c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m17]; exact w16_8c
  have w17_90 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m17]; exact w16_90
  have w17_94 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m17]; exact w16_94
  have w17_98 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m17]; exact w16_98
  have w17_9c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m17]; exact w16_9c
  have w17_a0 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m17]; exact w16_a0
  have w17_a4 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m17]; exact w16_a4
  have w17_a8 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m17]; exact w16_a8
  have w17_ac : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m17]; exact w16_ac
  have w17_b0 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m17]; exact w16_b0
  have w17_b4 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m17]; exact w16_b4
  have w17_b8 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m17]; exact w16_b8
  have w17_bc : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m17]; exact w16_bc
  have w17_c0 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m17]; exact w16_c0
  have w17_c4 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m17]; exact w16_c4
  have w17_c8 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m17]; exact w16_c8
  have w17_cc : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m17]; exact w16_cc
  have w17_d0 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m17]; exact w16_d0
  have w17_d4 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m17]; exact w16_d4
  have w17_d8 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m17]; exact w16_d8
  have w17_dc : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m17]; exact w16_dc
  have w17_e0 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m17]; exact w16_e0
  have w17_e4 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m17]; exact w16_e4
  have w17_e8 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m17]; exact w16_e8
  have w17_ec : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m17]; exact w16_ec
  have w17_f0 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m17]; exact w16_f0
  have w17_f4 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m17]; exact w16_f4
  have w17_f8 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m17]; exact w16_f8
  have w17_fc : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m17]; exact w16_fc
  have w17_100 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m17]; exact w16_100
  have w17_104 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m17]; exact w16_104
  have w17_108 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m17]; exact w16_108
  have w17_10c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m17]; exact w16_10c
  have w17_110 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m17]; exact w16_110
  have w17_114 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m17]; exact w16_114
  have w17_118 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m17]; exact w16_118
  have w17_11c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m17]; exact w16_11c
  have w17_120 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m17]; exact w16_120
  have w17_124 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m17]; exact w16_124
  have w17_128 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m17]; exact w16_128
  have w17_12c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m17]; exact w16_12c
  have w17_130 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m17]; exact w16_130
  have b17_a40 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = gs := by rw [m17]; exact b16_a40
  have b17_1040 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = gs := by rw [m17]; exact b16_1040
  have b17_14a0 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := by rw [m17]; exact b16_14a0
  have q17_420 : ∀ j, j < 96 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m17]; exact q16_420 j hj
  have q17_480 : ∀ j, j < 96 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0x480 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m17]; exact q16_480 j hj
  have q17_4e0 : ∀ j, j < 96 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0x4E0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m17]; exact q16_4e0 j hj
  have a17_240 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m17]; exact a16_240
  have a17_260 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m17]; exact a16_260
  have a17_280 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m17]; exact a16_280
  have a17_2a0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m17]; exact a16_2a0
  have a17_2c0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m17]; exact a16_2c0
  have a17_2e0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m17]; exact a16_2e0
  have a17_380 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m17]; exact a16_380
  have a17_400 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m17]; exact a16_400
  have a17_13e0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U2 := by rw [m17]; exact a16_13e0
  have a17_14e0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x14E0) 8 = U1 := by rw [m17]; exact a16_14e0
  have a17_1560 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1560) 8 = U2 := by rw [m17]; exact a16_1560
  have p17_320 : ptF n17.mem B 0x320 = P0 := by rw [m17]; exact p16_320
  have p17_3a0 : ptF n17.mem B 0x3A0 = P1 := by rw [m17]; exact p16_3a0
  have p17_540 : ptF n17.mem B 0x540 = tbl2 P0 3 := by rw [m17]; exact p16_540
  have p17_5a0 : ptF n17.mem B 0x5A0 = tbl2 P0 4 := by rw [m17]; exact p16_5a0
  have p17_600 : ptF n17.mem B 0x600 = tbl2 P0 5 := by rw [m17]; exact p16_600
  have p17_660 : ptF n17.mem B 0x660 = tbl2 P0 6 := by rw [m17]; exact p16_660
  have p17_6c0 : ptF n17.mem B 0x6C0 = tbl2 P0 7 := by rw [m17]; exact p16_6c0
  have p17_a20 : ptF n17.mem B 0xA20 = tbl2 P0 0 := by rw [m17]; exact p16_a20
  have p17_a80 : ptF n17.mem B 0xA80 = tbl2 P0 1 := by rw [m17]; exact p16_a80
  have p17_ae0 : ptF n17.mem B 0xAE0 = tbl2 P0 2 := by rw [m17]; exact p16_ae0
  have p17_b40 : ptF n17.mem B 0xB40 = tbl2 P0 3 := by rw [m17]; exact p16_b40
  have p17_ba0 : ptF n17.mem B 0xBA0 = tbl2 P0 4 := by rw [m17]; exact p16_ba0
  have p17_c00 : ptF n17.mem B 0xC00 = tbl2 P0 5 := by rw [m17]; exact p16_c00
  have p17_c60 : ptF n17.mem B 0xC60 = tbl2 P0 6 := by rw [m17]; exact p16_c60
  have p17_cc0 : ptF n17.mem B 0xCC0 = tbl2 P0 7 := by rw [m17]; exact p16_cc0
  have p17_1020 : ptF n17.mem B 0x1020 = tbl2 P0 0 := by rw [m17]; exact p16_1020
  have p17_1080 : ptF n17.mem B 0x1080 = tbl2 P0 1 := by rw [m17]; exact p16_1080
  have p17_10e0 : ptF n17.mem B 0x10E0 = tbl2 P0 2 := by rw [m17]; exact p16_10e0
  have p17_1140 : ptF n17.mem B 0x1140 = tbl2 P0 3 := by rw [m17]; exact p16_1140
  have p17_11a0 : ptF n17.mem B 0x11A0 = tbl2 P0 4 := by rw [m17]; exact p16_11a0
  have p17_1200 : ptF n17.mem B 0x1200 = tbl2 P0 5 := by rw [m17]; exact p16_1200
  have p17_1260 : ptF n17.mem B 0x1260 = tbl2 P0 6 := by rw [m17]; exact p16_1260
  have p17_12c0 : ptF n17.mem B 0x12C0 = tbl2 P0 7 := by rw [m17]; exact p16_12c0
  have p17_1320 : ptF n17.mem B 0x1320 = ptDbl2 P0 := by rw [m17]; exact p16_1320
  have p17_1380 : ptF n17.mem B 0x1380 = P1 := by rw [m17]; exact p16_1380
  have p17_1480 : ptF n17.mem B 0x1480 = P0 := by rw [m17]; exact p16_1480
  have p17_1500 : ptF n17.mem B 0x1500 = P1 := by rw [m17]; exact p16_1500
  clear p16_1500 p16_1480 p16_1380 p16_1320 p16_12c0 p16_1260 p16_1200 p16_11a0 p16_1140 p16_10e0 p16_1080 p16_1020 p16_cc0 p16_c60 p16_c00 p16_ba0 p16_b40 p16_ae0 p16_a80 p16_a20 p16_6c0 p16_660 p16_600 p16_5a0 p16_540 p16_3a0 p16_320 a16_1560 a16_14e0 a16_13e0 a16_400 a16_380 a16_2e0 a16_2c0 a16_2a0 a16_280 a16_260 a16_240 q16_4e0 q16_480 q16_420 b16_14a0 b16_1040 b16_a40 w16_130 w16_12c w16_128 w16_124 w16_120 w16_11c w16_118 w16_114 w16_110 w16_10c w16_108 w16_104 w16_100 w16_fc w16_f8 w16_f4 w16_f0 w16_ec w16_e8 w16_e4 w16_e0 w16_dc w16_d8 w16_d4 w16_d0 w16_cc w16_c8 w16_c4 w16_c0 w16_bc w16_b8 w16_b4 w16_b0 w16_ac w16_a8 w16_a4 w16_a0 w16_9c w16_98 w16_94 w16_90 w16_8c w16_88 w16_84 w16_80 w16_7c w16_78 w16_70 w16_6c w16_68 w16_64 w16_60 w16_5c w16_58 w16_54 w16_50 w16_4c w16_48 w16_44 w16_40 w16_3c w16_38 w16_34 w16_30 w16_2c w16_28 w16_24 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_9 g16_8 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 m16 s16 u16 d16
  -- 0x16BA: memcpy from outside the stack
  obtain ⟨n18, P18, K18, X18⟩ := sv_mcRo2 (c := 0x540) (N := 0x60) F RS E17 s17 sv_at_16ba sv_at_16be
    (by decide) (by decide) g17_2 g17_10 g17_11 g17_12 (by decide) (Or.inr ⟨by decide, by decide⟩)
  have s18 := P18.st
  have fr18 := P18.fr
  have t18 : Steps n0 n18 := t17.trans P18.steps
  have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : SvCode n18.mem := E17.fr F fr18
  have V18 : SvSaves B n18.mem v := V17.keep K18 (by decide)
  have g18_2 : reg n18 sp = B + 0x21A0 := by rw [P18.regs sp (by decide), g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P18.regs (3 : Fin 32) (by decide), g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P18.regs (4 : Fin 32) (by decide), g17_4]
  have g18_8 : reg n18 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x540 := by rw [P18.regs (8 : Fin 32) (by decide), g17_8]
  have g18_9 : reg n18 (9 : Fin 32) = BitVec.ofNat 32 0x5 := by rw [P18.regs (9 : Fin 32) (by decide), g17_9]
  have g18_18 : reg n18 (18 : Fin 32) = out := by rw [P18.regs (18 : Fin 32) (by decide), g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [P18.regs (19 : Fin 32) (by decide), g17_19]
  have g18_20 : reg n18 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P18.regs (20 : Fin 32) (by decide), g17_20]
  have g18_21 : reg n18 (21 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P18.regs (21 : Fin 32) (by decide), g17_21]
  have g18_22 : reg n18 (22 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [P18.regs (22 : Fin 32) (by decide), g17_22]
  have g18_23 : reg n18 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1500 := by rw [P18.regs (23 : Fin 32) (by decide), g17_23]
  have g18_24 : reg n18 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P18.regs (24 : Fin 32) (by decide), g17_24]
  have g18_25 : reg n18 (25 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [P18.regs (25 : Fin 32) (by decide), g17_25]
  have g18_26 : reg n18 (26 : Fin 32) = x26 := by rw [P18.regs (26 : Fin 32) (by decide), g17_26]
  have g18_27 : reg n18 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P18.regs (27 : Fin 32) (by decide), g17_27]
  have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x1380, 0x80), (0x420, 0x60), (0x480, 0x60), (0x4E0, 0x60), (0x540, 0x60)] := keep_kk17.trans K18.toL
  clear keep_kk17
  have w18_24 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K18.w32 (by decide) (by decide)).trans w17_24
  have w18_28 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K18.w32 (by decide) (by decide)).trans w17_28
  have w18_2c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K18.w32 (by decide) (by decide)).trans w17_2c
  have w18_30 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K18.w32 (by decide) (by decide)).trans w17_30
  have w18_34 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K18.w32 (by decide) (by decide)).trans w17_34
  have w18_38 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K18.w32 (by decide) (by decide)).trans w17_38
  have w18_3c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K18.w32 (by decide) (by decide)).trans w17_3c
  have w18_40 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K18.w32 (by decide) (by decide)).trans w17_40
  have w18_44 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K18.w32 (by decide) (by decide)).trans w17_44
  have w18_48 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K18.w32 (by decide) (by decide)).trans w17_48
  have w18_4c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K18.w32 (by decide) (by decide)).trans w17_4c
  have w18_50 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K18.w32 (by decide) (by decide)).trans w17_50
  have w18_54 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K18.w32 (by decide) (by decide)).trans w17_54
  have w18_58 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K18.w32 (by decide) (by decide)).trans w17_58
  have w18_5c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K18.w32 (by decide) (by decide)).trans w17_5c
  have w18_60 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K18.w32 (by decide) (by decide)).trans w17_60
  have w18_64 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K18.w32 (by decide) (by decide)).trans w17_64
  have w18_68 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K18.w32 (by decide) (by decide)).trans w17_68
  have w18_6c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K18.w32 (by decide) (by decide)).trans w17_6c
  have w18_70 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K18.w32 (by decide) (by decide)).trans w17_70
  have w18_78 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := (K18.w32 (by decide) (by decide)).trans w17_78
  have w18_7c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K18.w32 (by decide) (by decide)).trans w17_7c
  have w18_80 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K18.w32 (by decide) (by decide)).trans w17_80
  have w18_84 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K18.w32 (by decide) (by decide)).trans w17_84
  have w18_88 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K18.w32 (by decide) (by decide)).trans w17_88
  have w18_8c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K18.w32 (by decide) (by decide)).trans w17_8c
  have w18_90 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K18.w32 (by decide) (by decide)).trans w17_90
  have w18_94 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K18.w32 (by decide) (by decide)).trans w17_94
  have w18_98 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K18.w32 (by decide) (by decide)).trans w17_98
  have w18_9c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K18.w32 (by decide) (by decide)).trans w17_9c
  have w18_a0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K18.w32 (by decide) (by decide)).trans w17_a0
  have w18_a4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K18.w32 (by decide) (by decide)).trans w17_a4
  have w18_a8 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K18.w32 (by decide) (by decide)).trans w17_a8
  have w18_ac : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K18.w32 (by decide) (by decide)).trans w17_ac
  have w18_b0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K18.w32 (by decide) (by decide)).trans w17_b0
  have w18_b4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K18.w32 (by decide) (by decide)).trans w17_b4
  have w18_b8 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K18.w32 (by decide) (by decide)).trans w17_b8
  have w18_bc : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K18.w32 (by decide) (by decide)).trans w17_bc
  have w18_c0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K18.w32 (by decide) (by decide)).trans w17_c0
  have w18_c4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K18.w32 (by decide) (by decide)).trans w17_c4
  have w18_c8 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K18.w32 (by decide) (by decide)).trans w17_c8
  have w18_cc : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K18.w32 (by decide) (by decide)).trans w17_cc
  have w18_d0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K18.w32 (by decide) (by decide)).trans w17_d0
  have w18_d4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K18.w32 (by decide) (by decide)).trans w17_d4
  have w18_d8 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K18.w32 (by decide) (by decide)).trans w17_d8
  have w18_dc : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K18.w32 (by decide) (by decide)).trans w17_dc
  have w18_e0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K18.w32 (by decide) (by decide)).trans w17_e0
  have w18_e4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K18.w32 (by decide) (by decide)).trans w17_e4
  have w18_e8 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K18.w32 (by decide) (by decide)).trans w17_e8
  have w18_ec : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K18.w32 (by decide) (by decide)).trans w17_ec
  have w18_f0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K18.w32 (by decide) (by decide)).trans w17_f0
  have w18_f4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K18.w32 (by decide) (by decide)).trans w17_f4
  have w18_f8 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K18.w32 (by decide) (by decide)).trans w17_f8
  have w18_fc : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K18.w32 (by decide) (by decide)).trans w17_fc
  have w18_100 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K18.w32 (by decide) (by decide)).trans w17_100
  have w18_104 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K18.w32 (by decide) (by decide)).trans w17_104
  have w18_108 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K18.w32 (by decide) (by decide)).trans w17_108
  have w18_10c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K18.w32 (by decide) (by decide)).trans w17_10c
  have w18_110 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K18.w32 (by decide) (by decide)).trans w17_110
  have w18_114 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K18.w32 (by decide) (by decide)).trans w17_114
  have w18_118 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K18.w32 (by decide) (by decide)).trans w17_118
  have w18_11c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K18.w32 (by decide) (by decide)).trans w17_11c
  have w18_120 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K18.w32 (by decide) (by decide)).trans w17_120
  have w18_124 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K18.w32 (by decide) (by decide)).trans w17_124
  have w18_128 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K18.w32 (by decide) (by decide)).trans w17_128
  have w18_12c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K18.w32 (by decide) (by decide)).trans w17_12c
  have w18_130 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K18.w32 (by decide) (by decide)).trans w17_130
  have b18_a40 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = gs := (K18.b8 (by decide) (by decide)).trans b17_a40
  have b18_1040 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = gs := (K18.b8 (by decide) (by decide)).trans b17_1040
  have b18_14a0 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := (K18.b8 (by decide) (by decide)).trans b17_14a0
  have q18_420 : ∀ j, j < 96 → n18.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K18.range (by decide) (by decide) j hj).trans (q17_420 j hj)
  have q18_480 : ∀ j, j < 96 → n18.mem (B + 0x21A0 + BitVec.ofNat 32 (0x480 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K18.range (by decide) (by decide) j hj).trans (q17_480 j hj)
  have q18_4e0 : ∀ j, j < 96 → n18.mem (B + 0x21A0 + BitVec.ofNat 32 (0x4E0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K18.range (by decide) (by decide) j hj).trans (q17_4e0 j hj)
  have a18_240 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := (K18.acc (by decide) (by decide)).trans a17_240
  have a18_260 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := (K18.acc (by decide) (by decide)).trans a17_260
  have a18_280 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := (K18.acc (by decide) (by decide)).trans a17_280
  have a18_2a0 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K18.acc (by decide) (by decide)).trans a17_2a0
  have a18_2c0 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K18.acc (by decide) (by decide)).trans a17_2c0
  have a18_2e0 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K18.acc (by decide) (by decide)).trans a17_2e0
  have a18_380 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := (K18.acc (by decide) (by decide)).trans a17_380
  have a18_400 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := (K18.acc (by decide) (by decide)).trans a17_400
  have a18_13e0 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U2 := (K18.acc (by decide) (by decide)).trans a17_13e0
  have a18_14e0 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x14E0) 8 = U1 := (K18.acc (by decide) (by decide)).trans a17_14e0
  have a18_1560 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1560) 8 = U2 := (K18.acc (by decide) (by decide)).trans a17_1560
  have p18_320 : ptF n18.mem B 0x320 = P0 := (K18.pt (by decide) (by decide)).trans p17_320
  have p18_3a0 : ptF n18.mem B 0x3A0 = P1 := (K18.pt (by decide) (by decide)).trans p17_3a0
  have p18_5a0 : ptF n18.mem B 0x5A0 = tbl2 P0 4 := (K18.pt (by decide) (by decide)).trans p17_5a0
  have p18_600 : ptF n18.mem B 0x600 = tbl2 P0 5 := (K18.pt (by decide) (by decide)).trans p17_600
  have p18_660 : ptF n18.mem B 0x660 = tbl2 P0 6 := (K18.pt (by decide) (by decide)).trans p17_660
  have p18_6c0 : ptF n18.mem B 0x6C0 = tbl2 P0 7 := (K18.pt (by decide) (by decide)).trans p17_6c0
  have p18_a20 : ptF n18.mem B 0xA20 = tbl2 P0 0 := (K18.pt (by decide) (by decide)).trans p17_a20
  have p18_a80 : ptF n18.mem B 0xA80 = tbl2 P0 1 := (K18.pt (by decide) (by decide)).trans p17_a80
  have p18_ae0 : ptF n18.mem B 0xAE0 = tbl2 P0 2 := (K18.pt (by decide) (by decide)).trans p17_ae0
  have p18_b40 : ptF n18.mem B 0xB40 = tbl2 P0 3 := (K18.pt (by decide) (by decide)).trans p17_b40
  have p18_ba0 : ptF n18.mem B 0xBA0 = tbl2 P0 4 := (K18.pt (by decide) (by decide)).trans p17_ba0
  have p18_c00 : ptF n18.mem B 0xC00 = tbl2 P0 5 := (K18.pt (by decide) (by decide)).trans p17_c00
  have p18_c60 : ptF n18.mem B 0xC60 = tbl2 P0 6 := (K18.pt (by decide) (by decide)).trans p17_c60
  have p18_cc0 : ptF n18.mem B 0xCC0 = tbl2 P0 7 := (K18.pt (by decide) (by decide)).trans p17_cc0
  have p18_1020 : ptF n18.mem B 0x1020 = tbl2 P0 0 := (K18.pt (by decide) (by decide)).trans p17_1020
  have p18_1080 : ptF n18.mem B 0x1080 = tbl2 P0 1 := (K18.pt (by decide) (by decide)).trans p17_1080
  have p18_10e0 : ptF n18.mem B 0x10E0 = tbl2 P0 2 := (K18.pt (by decide) (by decide)).trans p17_10e0
  have p18_1140 : ptF n18.mem B 0x1140 = tbl2 P0 3 := (K18.pt (by decide) (by decide)).trans p17_1140
  have p18_11a0 : ptF n18.mem B 0x11A0 = tbl2 P0 4 := (K18.pt (by decide) (by decide)).trans p17_11a0
  have p18_1200 : ptF n18.mem B 0x1200 = tbl2 P0 5 := (K18.pt (by decide) (by decide)).trans p17_1200
  have p18_1260 : ptF n18.mem B 0x1260 = tbl2 P0 6 := (K18.pt (by decide) (by decide)).trans p17_1260
  have p18_12c0 : ptF n18.mem B 0x12C0 = tbl2 P0 7 := (K18.pt (by decide) (by decide)).trans p17_12c0
  have p18_1320 : ptF n18.mem B 0x1320 = ptDbl2 P0 := (K18.pt (by decide) (by decide)).trans p17_1320
  have p18_1380 : ptF n18.mem B 0x1380 = P1 := (K18.pt (by decide) (by decide)).trans p17_1380
  have p18_1480 : ptF n18.mem B 0x1480 = P0 := (K18.pt (by decide) (by decide)).trans p17_1480
  have p18_1500 : ptF n18.mem B 0x1500 = P1 := (K18.pt (by decide) (by decide)).trans p17_1500
  have q18_540 : ∀ j, j < 96 → n18.mem (B + 0x21A0 + BitVec.ofNat 32 (0x540 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) :=
    fun j hj => (X18 j hj).trans (fR17 _ (SvRo2.r RS (Or.inr ⟨by decide, by decide⟩) hj))
  clear p17_1500 p17_1480 p17_1380 p17_1320 p17_12c0 p17_1260 p17_1200 p17_11a0 p17_1140 p17_10e0 p17_1080 p17_1020 p17_cc0 p17_c60 p17_c00 p17_ba0 p17_b40 p17_ae0 p17_a80 p17_a20 p17_6c0 p17_660 p17_600 p17_5a0 p17_540 p17_3a0 p17_320 a17_1560 a17_14e0 a17_13e0 a17_400 a17_380 a17_2e0 a17_2c0 a17_2a0 a17_280 a17_260 a17_240 q17_4e0 q17_480 q17_420 b17_14a0 b17_1040 b17_a40 w17_130 w17_12c w17_128 w17_124 w17_120 w17_11c w17_118 w17_114 w17_110 w17_10c w17_108 w17_104 w17_100 w17_fc w17_f8 w17_f4 w17_f0 w17_ec w17_e8 w17_e4 w17_e0 w17_dc w17_d8 w17_d4 w17_d0 w17_cc w17_c8 w17_c4 w17_c0 w17_bc w17_b8 w17_b4 w17_b0 w17_ac w17_a8 w17_a4 w17_a0 w17_9c w17_98 w17_94 w17_90 w17_8c w17_88 w17_84 w17_80 w17_7c w17_78 w17_70 w17_6c w17_68 w17_64 w17_60 w17_5c w17_58 w17_54 w17_50 w17_4c w17_48 w17_44 w17_40 w17_3c w17_38 w17_34 w17_30 w17_2c w17_28 w17_24 g17_12 g17_11 g17_10 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_9 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 rb17 s17 m17 u17 c17
  -- 0x16C2
  obtain ⟨n19, c19, u19⟩ := s18.block svEcT1a16c2 E18.self svEcT1a16c2_end
    ⟨trivial, trivial, trivial⟩
  have m19 : n19.mem = n18.mem := u19.mem
  have s19 : St n19.mem SV n19 0x16C8 (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
  have rb19 : ∀ q, reg n19 q = (runBlock svEcT1a16c2 (n18.mem, reg n18)).2 q := fun q => by rw [u19.regs]
  have fr19 : ∀ x, SvR B x → n19.mem x = n18.mem x := fun x _ => by rw [m19]
  have t19 : Steps n0 n19 := t18.trans c19
  have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
  have E19 : SvCode n19.mem := E18.fr F fr19
  have V19 : SvSaves B n19.mem v := V18.same m19
  have g19_2 : reg n19 sp = B + 0x21A0 := by
    rw [rb19, runBlock_reg _ _ _ sp s18.zero (by decide), g18_2]
  have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb19, runBlock_reg _ _ _ (3 : Fin 32) s18.zero (by decide), g18_3]
  have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb19, runBlock_reg _ _ _ (4 : Fin 32) s18.zero (by decide), g18_4]
  have g19_18 : reg n19 (18 : Fin 32) = out := by
    rw [rb19, runBlock_reg _ _ _ (18 : Fin 32) s18.zero (by decide), g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = bp := by
    rw [rb19, runBlock_reg _ _ _ (19 : Fin 32) s18.zero (by decide), g18_19]
  have g19_20 : reg n19 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb19, runBlock_reg _ _ _ (20 : Fin 32) s18.zero (by decide), g18_20]
  have g19_21 : reg n19 (21 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb19, runBlock_reg _ _ _ (21 : Fin 32) s18.zero (by decide), g18_21]
  have g19_22 : reg n19 (22 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb19, runBlock_reg _ _ _ (22 : Fin 32) s18.zero (by decide), g18_22]
  have g19_23 : reg n19 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1500 := by
    rw [rb19, runBlock_reg _ _ _ (23 : Fin 32) s18.zero (by decide), g18_23]
  have g19_24 : reg n19 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb19, runBlock_reg _ _ _ (24 : Fin 32) s18.zero (by decide), g18_24]
  have g19_25 : reg n19 (25 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb19, runBlock_reg _ _ _ (25 : Fin 32) s18.zero (by decide), g18_25]
  have g19_26 : reg n19 (26 : Fin 32) = x26 := by
    rw [rb19, runBlock_reg _ _ _ (26 : Fin 32) s18.zero (by decide), g18_26]
  have g19_27 : reg n19 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb19, runBlock_reg _ _ _ (27 : Fin 32) s18.zero (by decide), g18_27]
  have g19_8 : reg n19 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x5A0 := by
    rw [rb19]; simp +decide only [runBlock, BInstr.run, svEcT1a16c2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g18_2, g18_3, g18_4, g18_8, g18_9, g18_18, g18_19, g18_20, g18_21, g18_22, g18_23, g18_24, g18_25, g18_26, g18_27, s18.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g19_9 : reg n19 (9 : Fin 32) = BitVec.ofNat 32 0x4 := by
    rw [rb19]; simp +decide only [runBlock, BInstr.run, svEcT1a16c2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g18_2, g18_3, g18_4, g18_8, g18_9, g18_18, g18_19, g18_20, g18_21, g18_22, g18_23, g18_24, g18_25, g18_26, g18_27, s18.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x1380, 0x80), (0x420, 0x60), (0x480, 0x60), (0x4E0, 0x60), (0x540, 0x60)] := by rw [m19]; exact keep_kk18
  clear keep_kk18
  have w19_24 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m19]; exact w18_24
  have w19_28 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m19]; exact w18_28
  have w19_2c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m19]; exact w18_2c
  have w19_30 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m19]; exact w18_30
  have w19_34 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m19]; exact w18_34
  have w19_38 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m19]; exact w18_38
  have w19_3c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m19]; exact w18_3c
  have w19_40 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m19]; exact w18_40
  have w19_44 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m19]; exact w18_44
  have w19_48 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m19]; exact w18_48
  have w19_4c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m19]; exact w18_4c
  have w19_50 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m19]; exact w18_50
  have w19_54 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m19]; exact w18_54
  have w19_58 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m19]; exact w18_58
  have w19_5c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m19]; exact w18_5c
  have w19_60 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m19]; exact w18_60
  have w19_64 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m19]; exact w18_64
  have w19_68 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m19]; exact w18_68
  have w19_6c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m19]; exact w18_6c
  have w19_70 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m19]; exact w18_70
  have w19_78 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m19]; exact w18_78
  have w19_7c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m19]; exact w18_7c
  have w19_80 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m19]; exact w18_80
  have w19_84 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m19]; exact w18_84
  have w19_88 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m19]; exact w18_88
  have w19_8c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m19]; exact w18_8c
  have w19_90 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m19]; exact w18_90
  have w19_94 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m19]; exact w18_94
  have w19_98 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m19]; exact w18_98
  have w19_9c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m19]; exact w18_9c
  have w19_a0 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m19]; exact w18_a0
  have w19_a4 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m19]; exact w18_a4
  have w19_a8 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m19]; exact w18_a8
  have w19_ac : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m19]; exact w18_ac
  have w19_b0 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m19]; exact w18_b0
  have w19_b4 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m19]; exact w18_b4
  have w19_b8 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m19]; exact w18_b8
  have w19_bc : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m19]; exact w18_bc
  have w19_c0 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m19]; exact w18_c0
  have w19_c4 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m19]; exact w18_c4
  have w19_c8 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m19]; exact w18_c8
  have w19_cc : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m19]; exact w18_cc
  have w19_d0 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m19]; exact w18_d0
  have w19_d4 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m19]; exact w18_d4
  have w19_d8 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m19]; exact w18_d8
  have w19_dc : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m19]; exact w18_dc
  have w19_e0 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m19]; exact w18_e0
  have w19_e4 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m19]; exact w18_e4
  have w19_e8 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m19]; exact w18_e8
  have w19_ec : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m19]; exact w18_ec
  have w19_f0 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m19]; exact w18_f0
  have w19_f4 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m19]; exact w18_f4
  have w19_f8 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m19]; exact w18_f8
  have w19_fc : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m19]; exact w18_fc
  have w19_100 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m19]; exact w18_100
  have w19_104 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m19]; exact w18_104
  have w19_108 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m19]; exact w18_108
  have w19_10c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m19]; exact w18_10c
  have w19_110 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m19]; exact w18_110
  have w19_114 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m19]; exact w18_114
  have w19_118 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m19]; exact w18_118
  have w19_11c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m19]; exact w18_11c
  have w19_120 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m19]; exact w18_120
  have w19_124 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m19]; exact w18_124
  have w19_128 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m19]; exact w18_128
  have w19_12c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m19]; exact w18_12c
  have w19_130 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m19]; exact w18_130
  have b19_a40 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = gs := by rw [m19]; exact b18_a40
  have b19_1040 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = gs := by rw [m19]; exact b18_1040
  have b19_14a0 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := by rw [m19]; exact b18_14a0
  have q19_420 : ∀ j, j < 96 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m19]; exact q18_420 j hj
  have q19_480 : ∀ j, j < 96 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0x480 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m19]; exact q18_480 j hj
  have q19_4e0 : ∀ j, j < 96 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0x4E0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m19]; exact q18_4e0 j hj
  have q19_540 : ∀ j, j < 96 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0x540 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m19]; exact q18_540 j hj
  have a19_240 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m19]; exact a18_240
  have a19_260 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m19]; exact a18_260
  have a19_280 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m19]; exact a18_280
  have a19_2a0 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m19]; exact a18_2a0
  have a19_2c0 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m19]; exact a18_2c0
  have a19_2e0 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m19]; exact a18_2e0
  have a19_380 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m19]; exact a18_380
  have a19_400 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m19]; exact a18_400
  have a19_13e0 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U2 := by rw [m19]; exact a18_13e0
  have a19_14e0 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x14E0) 8 = U1 := by rw [m19]; exact a18_14e0
  have a19_1560 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1560) 8 = U2 := by rw [m19]; exact a18_1560
  have p19_320 : ptF n19.mem B 0x320 = P0 := by rw [m19]; exact p18_320
  have p19_3a0 : ptF n19.mem B 0x3A0 = P1 := by rw [m19]; exact p18_3a0
  have p19_5a0 : ptF n19.mem B 0x5A0 = tbl2 P0 4 := by rw [m19]; exact p18_5a0
  have p19_600 : ptF n19.mem B 0x600 = tbl2 P0 5 := by rw [m19]; exact p18_600
  have p19_660 : ptF n19.mem B 0x660 = tbl2 P0 6 := by rw [m19]; exact p18_660
  have p19_6c0 : ptF n19.mem B 0x6C0 = tbl2 P0 7 := by rw [m19]; exact p18_6c0
  have p19_a20 : ptF n19.mem B 0xA20 = tbl2 P0 0 := by rw [m19]; exact p18_a20
  have p19_a80 : ptF n19.mem B 0xA80 = tbl2 P0 1 := by rw [m19]; exact p18_a80
  have p19_ae0 : ptF n19.mem B 0xAE0 = tbl2 P0 2 := by rw [m19]; exact p18_ae0
  have p19_b40 : ptF n19.mem B 0xB40 = tbl2 P0 3 := by rw [m19]; exact p18_b40
  have p19_ba0 : ptF n19.mem B 0xBA0 = tbl2 P0 4 := by rw [m19]; exact p18_ba0
  have p19_c00 : ptF n19.mem B 0xC00 = tbl2 P0 5 := by rw [m19]; exact p18_c00
  have p19_c60 : ptF n19.mem B 0xC60 = tbl2 P0 6 := by rw [m19]; exact p18_c60
  have p19_cc0 : ptF n19.mem B 0xCC0 = tbl2 P0 7 := by rw [m19]; exact p18_cc0
  have p19_1020 : ptF n19.mem B 0x1020 = tbl2 P0 0 := by rw [m19]; exact p18_1020
  have p19_1080 : ptF n19.mem B 0x1080 = tbl2 P0 1 := by rw [m19]; exact p18_1080
  have p19_10e0 : ptF n19.mem B 0x10E0 = tbl2 P0 2 := by rw [m19]; exact p18_10e0
  have p19_1140 : ptF n19.mem B 0x1140 = tbl2 P0 3 := by rw [m19]; exact p18_1140
  have p19_11a0 : ptF n19.mem B 0x11A0 = tbl2 P0 4 := by rw [m19]; exact p18_11a0
  have p19_1200 : ptF n19.mem B 0x1200 = tbl2 P0 5 := by rw [m19]; exact p18_1200
  have p19_1260 : ptF n19.mem B 0x1260 = tbl2 P0 6 := by rw [m19]; exact p18_1260
  have p19_12c0 : ptF n19.mem B 0x12C0 = tbl2 P0 7 := by rw [m19]; exact p18_12c0
  have p19_1320 : ptF n19.mem B 0x1320 = ptDbl2 P0 := by rw [m19]; exact p18_1320
  have p19_1380 : ptF n19.mem B 0x1380 = P1 := by rw [m19]; exact p18_1380
  have p19_1480 : ptF n19.mem B 0x1480 = P0 := by rw [m19]; exact p18_1480
  have p19_1500 : ptF n19.mem B 0x1500 = P1 := by rw [m19]; exact p18_1500
  clear q18_540 p18_1500 p18_1480 p18_1380 p18_1320 p18_12c0 p18_1260 p18_1200 p18_11a0 p18_1140 p18_10e0 p18_1080 p18_1020 p18_cc0 p18_c60 p18_c00 p18_ba0 p18_b40 p18_ae0 p18_a80 p18_a20 p18_6c0 p18_660 p18_600 p18_5a0 p18_3a0 p18_320 a18_1560 a18_14e0 a18_13e0 a18_400 a18_380 a18_2e0 a18_2c0 a18_2a0 a18_280 a18_260 a18_240 q18_4e0 q18_480 q18_420 b18_14a0 b18_1040 b18_a40 w18_130 w18_12c w18_128 w18_124 w18_120 w18_11c w18_118 w18_114 w18_110 w18_10c w18_108 w18_104 w18_100 w18_fc w18_f8 w18_f4 w18_f0 w18_ec w18_e8 w18_e4 w18_e0 w18_dc w18_d8 w18_d4 w18_d0 w18_cc w18_c8 w18_c4 w18_c0 w18_bc w18_b8 w18_b4 w18_b0 w18_ac w18_a8 w18_a4 w18_a0 w18_9c w18_98 w18_94 w18_90 w18_8c w18_88 w18_84 w18_80 w18_7c w18_78 w18_70 w18_6c w18_68 w18_64 w18_60 w18_5c w18_58 w18_54 w18_50 w18_4c w18_48 w18_44 w18_40 w18_3c w18_38 w18_34 w18_30 w18_2c w18_28 w18_24 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_9 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 s18 X18 K18 P18
  -- 0x16C8: branch, taken
  obtain ⟨n20, d20, u20⟩ := s19.taken E19.self 0x16B2 sv_at_16c8
    (by decide) (by rw [g19_9, s19.zero]; decide)
  have s20 : St n20.mem SV n20 0x16B2 (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
  have m20 : n20.mem = n19.mem := u20.mem
  have fr20 : ∀ x, SvR B x → n20.mem x = n19.mem x := fun x _ => by rw [m20]
  have t20 : Steps n0 n20 := t19.trans (.single d20)
  have fR20 : ∀ x, SvR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
  have E20 : SvCode n20.mem := E19.fr F fr20
  have V20 : SvSaves B n20.mem v := V19.same m20
  have g20_2 : reg n20 sp = B + 0x21A0 := by rw [u20.regs, g19_2]
  have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u20.regs, g19_3]
  have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u20.regs, g19_4]
  have g20_8 : reg n20 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x5A0 := by rw [u20.regs, g19_8]
  have g20_9 : reg n20 (9 : Fin 32) = BitVec.ofNat 32 0x4 := by rw [u20.regs, g19_9]
  have g20_18 : reg n20 (18 : Fin 32) = out := by rw [u20.regs, g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = bp := by rw [u20.regs, g19_19]
  have g20_20 : reg n20 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u20.regs, g19_20]
  have g20_21 : reg n20 (21 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u20.regs, g19_21]
  have g20_22 : reg n20 (22 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [u20.regs, g19_22]
  have g20_23 : reg n20 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1500 := by rw [u20.regs, g19_23]
  have g20_24 : reg n20 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u20.regs, g19_24]
  have g20_25 : reg n20 (25 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [u20.regs, g19_25]
  have g20_26 : reg n20 (26 : Fin 32) = x26 := by rw [u20.regs, g19_26]
  have g20_27 : reg n20 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u20.regs, g19_27]
  have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x1380, 0x80), (0x420, 0x60), (0x480, 0x60), (0x4E0, 0x60), (0x540, 0x60)] := by rw [m20]; exact keep_kk19
  clear keep_kk19
  have w20_24 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m20]; exact w19_24
  have w20_28 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m20]; exact w19_28
  have w20_2c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m20]; exact w19_2c
  have w20_30 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m20]; exact w19_30
  have w20_34 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m20]; exact w19_34
  have w20_38 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m20]; exact w19_38
  have w20_3c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m20]; exact w19_3c
  have w20_40 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m20]; exact w19_40
  have w20_44 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m20]; exact w19_44
  have w20_48 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m20]; exact w19_48
  have w20_4c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m20]; exact w19_4c
  have w20_50 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m20]; exact w19_50
  have w20_54 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m20]; exact w19_54
  have w20_58 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m20]; exact w19_58
  have w20_5c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m20]; exact w19_5c
  have w20_60 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m20]; exact w19_60
  have w20_64 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m20]; exact w19_64
  have w20_68 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m20]; exact w19_68
  have w20_6c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m20]; exact w19_6c
  have w20_70 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m20]; exact w19_70
  have w20_78 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m20]; exact w19_78
  have w20_7c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m20]; exact w19_7c
  have w20_80 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m20]; exact w19_80
  have w20_84 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m20]; exact w19_84
  have w20_88 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m20]; exact w19_88
  have w20_8c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m20]; exact w19_8c
  have w20_90 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m20]; exact w19_90
  have w20_94 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m20]; exact w19_94
  have w20_98 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m20]; exact w19_98
  have w20_9c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m20]; exact w19_9c
  have w20_a0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m20]; exact w19_a0
  have w20_a4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m20]; exact w19_a4
  have w20_a8 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m20]; exact w19_a8
  have w20_ac : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m20]; exact w19_ac
  have w20_b0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m20]; exact w19_b0
  have w20_b4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m20]; exact w19_b4
  have w20_b8 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m20]; exact w19_b8
  have w20_bc : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m20]; exact w19_bc
  have w20_c0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m20]; exact w19_c0
  have w20_c4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m20]; exact w19_c4
  have w20_c8 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m20]; exact w19_c8
  have w20_cc : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m20]; exact w19_cc
  have w20_d0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m20]; exact w19_d0
  have w20_d4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m20]; exact w19_d4
  have w20_d8 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m20]; exact w19_d8
  have w20_dc : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m20]; exact w19_dc
  have w20_e0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m20]; exact w19_e0
  have w20_e4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m20]; exact w19_e4
  have w20_e8 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m20]; exact w19_e8
  have w20_ec : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m20]; exact w19_ec
  have w20_f0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m20]; exact w19_f0
  have w20_f4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m20]; exact w19_f4
  have w20_f8 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m20]; exact w19_f8
  have w20_fc : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m20]; exact w19_fc
  have w20_100 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m20]; exact w19_100
  have w20_104 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m20]; exact w19_104
  have w20_108 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m20]; exact w19_108
  have w20_10c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m20]; exact w19_10c
  have w20_110 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m20]; exact w19_110
  have w20_114 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m20]; exact w19_114
  have w20_118 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m20]; exact w19_118
  have w20_11c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m20]; exact w19_11c
  have w20_120 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m20]; exact w19_120
  have w20_124 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m20]; exact w19_124
  have w20_128 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m20]; exact w19_128
  have w20_12c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m20]; exact w19_12c
  have w20_130 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m20]; exact w19_130
  have b20_a40 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = gs := by rw [m20]; exact b19_a40
  have b20_1040 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = gs := by rw [m20]; exact b19_1040
  have b20_14a0 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := by rw [m20]; exact b19_14a0
  have q20_420 : ∀ j, j < 96 → n20.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m20]; exact q19_420 j hj
  have q20_480 : ∀ j, j < 96 → n20.mem (B + 0x21A0 + BitVec.ofNat 32 (0x480 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m20]; exact q19_480 j hj
  have q20_4e0 : ∀ j, j < 96 → n20.mem (B + 0x21A0 + BitVec.ofNat 32 (0x4E0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m20]; exact q19_4e0 j hj
  have q20_540 : ∀ j, j < 96 → n20.mem (B + 0x21A0 + BitVec.ofNat 32 (0x540 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m20]; exact q19_540 j hj
  have a20_240 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m20]; exact a19_240
  have a20_260 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m20]; exact a19_260
  have a20_280 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m20]; exact a19_280
  have a20_2a0 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m20]; exact a19_2a0
  have a20_2c0 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m20]; exact a19_2c0
  have a20_2e0 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m20]; exact a19_2e0
  have a20_380 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m20]; exact a19_380
  have a20_400 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m20]; exact a19_400
  have a20_13e0 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U2 := by rw [m20]; exact a19_13e0
  have a20_14e0 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x14E0) 8 = U1 := by rw [m20]; exact a19_14e0
  have a20_1560 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1560) 8 = U2 := by rw [m20]; exact a19_1560
  have p20_320 : ptF n20.mem B 0x320 = P0 := by rw [m20]; exact p19_320
  have p20_3a0 : ptF n20.mem B 0x3A0 = P1 := by rw [m20]; exact p19_3a0
  have p20_5a0 : ptF n20.mem B 0x5A0 = tbl2 P0 4 := by rw [m20]; exact p19_5a0
  have p20_600 : ptF n20.mem B 0x600 = tbl2 P0 5 := by rw [m20]; exact p19_600
  have p20_660 : ptF n20.mem B 0x660 = tbl2 P0 6 := by rw [m20]; exact p19_660
  have p20_6c0 : ptF n20.mem B 0x6C0 = tbl2 P0 7 := by rw [m20]; exact p19_6c0
  have p20_a20 : ptF n20.mem B 0xA20 = tbl2 P0 0 := by rw [m20]; exact p19_a20
  have p20_a80 : ptF n20.mem B 0xA80 = tbl2 P0 1 := by rw [m20]; exact p19_a80
  have p20_ae0 : ptF n20.mem B 0xAE0 = tbl2 P0 2 := by rw [m20]; exact p19_ae0
  have p20_b40 : ptF n20.mem B 0xB40 = tbl2 P0 3 := by rw [m20]; exact p19_b40
  have p20_ba0 : ptF n20.mem B 0xBA0 = tbl2 P0 4 := by rw [m20]; exact p19_ba0
  have p20_c00 : ptF n20.mem B 0xC00 = tbl2 P0 5 := by rw [m20]; exact p19_c00
  have p20_c60 : ptF n20.mem B 0xC60 = tbl2 P0 6 := by rw [m20]; exact p19_c60
  have p20_cc0 : ptF n20.mem B 0xCC0 = tbl2 P0 7 := by rw [m20]; exact p19_cc0
  have p20_1020 : ptF n20.mem B 0x1020 = tbl2 P0 0 := by rw [m20]; exact p19_1020
  have p20_1080 : ptF n20.mem B 0x1080 = tbl2 P0 1 := by rw [m20]; exact p19_1080
  have p20_10e0 : ptF n20.mem B 0x10E0 = tbl2 P0 2 := by rw [m20]; exact p19_10e0
  have p20_1140 : ptF n20.mem B 0x1140 = tbl2 P0 3 := by rw [m20]; exact p19_1140
  have p20_11a0 : ptF n20.mem B 0x11A0 = tbl2 P0 4 := by rw [m20]; exact p19_11a0
  have p20_1200 : ptF n20.mem B 0x1200 = tbl2 P0 5 := by rw [m20]; exact p19_1200
  have p20_1260 : ptF n20.mem B 0x1260 = tbl2 P0 6 := by rw [m20]; exact p19_1260
  have p20_12c0 : ptF n20.mem B 0x12C0 = tbl2 P0 7 := by rw [m20]; exact p19_12c0
  have p20_1320 : ptF n20.mem B 0x1320 = ptDbl2 P0 := by rw [m20]; exact p19_1320
  have p20_1380 : ptF n20.mem B 0x1380 = P1 := by rw [m20]; exact p19_1380
  have p20_1480 : ptF n20.mem B 0x1480 = P0 := by rw [m20]; exact p19_1480
  have p20_1500 : ptF n20.mem B 0x1500 = P1 := by rw [m20]; exact p19_1500
  clear p19_1500 p19_1480 p19_1380 p19_1320 p19_12c0 p19_1260 p19_1200 p19_11a0 p19_1140 p19_10e0 p19_1080 p19_1020 p19_cc0 p19_c60 p19_c00 p19_ba0 p19_b40 p19_ae0 p19_a80 p19_a20 p19_6c0 p19_660 p19_600 p19_5a0 p19_3a0 p19_320 a19_1560 a19_14e0 a19_13e0 a19_400 a19_380 a19_2e0 a19_2c0 a19_2a0 a19_280 a19_260 a19_240 q19_540 q19_4e0 q19_480 q19_420 b19_14a0 b19_1040 b19_a40 w19_130 w19_12c w19_128 w19_124 w19_120 w19_11c w19_118 w19_114 w19_110 w19_10c w19_108 w19_104 w19_100 w19_fc w19_f8 w19_f4 w19_f0 w19_ec w19_e8 w19_e4 w19_e0 w19_dc w19_d8 w19_d4 w19_d0 w19_cc w19_c8 w19_c4 w19_c0 w19_bc w19_b8 w19_b4 w19_b0 w19_ac w19_a8 w19_a4 w19_a0 w19_9c w19_98 w19_94 w19_90 w19_8c w19_88 w19_84 w19_80 w19_7c w19_78 w19_70 w19_6c w19_68 w19_64 w19_60 w19_5c w19_58 w19_54 w19_50 w19_4c w19_48 w19_44 w19_40 w19_3c w19_38 w19_34 w19_30 w19_2c w19_28 w19_24 g19_9 g19_8 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 rb19 s19 m19 u19 c19
  -- 0x16B2
  obtain ⟨n21, c21, u21⟩ := s20.block svEcT1a16b2 E20.self svEcT1a16b2_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m21 : n21.mem = n20.mem := u21.mem
  have s21 : St n21.mem SV n21 0x16BA (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
  have rb21 : ∀ q, reg n21 q = (runBlock svEcT1a16b2 (n20.mem, reg n20)).2 q := fun q => by rw [u21.regs]
  have fr21 : ∀ x, SvR B x → n21.mem x = n20.mem x := fun x _ => by rw [m21]
  have t21 : Steps n0 n21 := t20.trans c21
  have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
  have E21 : SvCode n21.mem := E20.fr F fr21
  have V21 : SvSaves B n21.mem v := V20.same m21
  have g21_2 : reg n21 sp = B + 0x21A0 := by
    rw [rb21, runBlock_reg _ _ _ sp s20.zero (by decide), g20_2]
  have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb21, runBlock_reg _ _ _ (3 : Fin 32) s20.zero (by decide), g20_3]
  have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb21, runBlock_reg _ _ _ (4 : Fin 32) s20.zero (by decide), g20_4]
  have g21_8 : reg n21 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x5A0 := by
    rw [rb21, runBlock_reg _ _ _ (8 : Fin 32) s20.zero (by decide), g20_8]
  have g21_9 : reg n21 (9 : Fin 32) = BitVec.ofNat 32 0x4 := by
    rw [rb21, runBlock_reg _ _ _ (9 : Fin 32) s20.zero (by decide), g20_9]
  have g21_18 : reg n21 (18 : Fin 32) = out := by
    rw [rb21, runBlock_reg _ _ _ (18 : Fin 32) s20.zero (by decide), g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = bp := by
    rw [rb21, runBlock_reg _ _ _ (19 : Fin 32) s20.zero (by decide), g20_19]
  have g21_20 : reg n21 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb21, runBlock_reg _ _ _ (20 : Fin 32) s20.zero (by decide), g20_20]
  have g21_21 : reg n21 (21 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb21, runBlock_reg _ _ _ (21 : Fin 32) s20.zero (by decide), g20_21]
  have g21_22 : reg n21 (22 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb21, runBlock_reg _ _ _ (22 : Fin 32) s20.zero (by decide), g20_22]
  have g21_23 : reg n21 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1500 := by
    rw [rb21, runBlock_reg _ _ _ (23 : Fin 32) s20.zero (by decide), g20_23]
  have g21_24 : reg n21 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb21, runBlock_reg _ _ _ (24 : Fin 32) s20.zero (by decide), g20_24]
  have g21_25 : reg n21 (25 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb21, runBlock_reg _ _ _ (25 : Fin 32) s20.zero (by decide), g20_25]
  have g21_26 : reg n21 (26 : Fin 32) = x26 := by
    rw [rb21, runBlock_reg _ _ _ (26 : Fin 32) s20.zero (by decide), g20_26]
  have g21_27 : reg n21 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb21, runBlock_reg _ _ _ (27 : Fin 32) s20.zero (by decide), g20_27]
  have g21_10 : reg n21 a0 = B + 0x21A0 + BitVec.ofNat 32 0x5A0 := by
    rw [rb21]; simp +decide only [runBlock, BInstr.run, svEcT1a16b2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g20_2, g20_3, g20_4, g20_8, g20_9, g20_18, g20_19, g20_20, g20_21, g20_22, g20_23, g20_24, g20_25, g20_26, g20_27, s20.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g21_11 : reg n21 a1 = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb21]; simp +decide only [runBlock, BInstr.run, svEcT1a16b2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g20_2, g20_3, g20_4, g20_8, g20_9, g20_18, g20_19, g20_20, g20_21, g20_22, g20_23, g20_24, g20_25, g20_26, g20_27, s20.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g21_12 : reg n21 a2 = BitVec.ofNat 32 0x60 := by
    rw [rb21]; simp +decide only [runBlock, BInstr.run, svEcT1a16b2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g20_2, g20_3, g20_4, g20_8, g20_9, g20_18, g20_19, g20_20, g20_21, g20_22, g20_23, g20_24, g20_25, g20_26, g20_27, s20.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x1380, 0x80), (0x420, 0x60), (0x480, 0x60), (0x4E0, 0x60), (0x540, 0x60)] := by rw [m21]; exact keep_kk20
  clear keep_kk20
  have w21_24 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m21]; exact w20_24
  have w21_28 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m21]; exact w20_28
  have w21_2c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m21]; exact w20_2c
  have w21_30 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m21]; exact w20_30
  have w21_34 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m21]; exact w20_34
  have w21_38 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m21]; exact w20_38
  have w21_3c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m21]; exact w20_3c
  have w21_40 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m21]; exact w20_40
  have w21_44 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m21]; exact w20_44
  have w21_48 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m21]; exact w20_48
  have w21_4c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m21]; exact w20_4c
  have w21_50 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m21]; exact w20_50
  have w21_54 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m21]; exact w20_54
  have w21_58 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m21]; exact w20_58
  have w21_5c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m21]; exact w20_5c
  have w21_60 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m21]; exact w20_60
  have w21_64 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m21]; exact w20_64
  have w21_68 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m21]; exact w20_68
  have w21_6c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m21]; exact w20_6c
  have w21_70 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m21]; exact w20_70
  have w21_78 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m21]; exact w20_78
  have w21_7c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m21]; exact w20_7c
  have w21_80 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m21]; exact w20_80
  have w21_84 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m21]; exact w20_84
  have w21_88 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m21]; exact w20_88
  have w21_8c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m21]; exact w20_8c
  have w21_90 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m21]; exact w20_90
  have w21_94 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m21]; exact w20_94
  have w21_98 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m21]; exact w20_98
  have w21_9c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m21]; exact w20_9c
  have w21_a0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m21]; exact w20_a0
  have w21_a4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m21]; exact w20_a4
  have w21_a8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m21]; exact w20_a8
  have w21_ac : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m21]; exact w20_ac
  have w21_b0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m21]; exact w20_b0
  have w21_b4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m21]; exact w20_b4
  have w21_b8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m21]; exact w20_b8
  have w21_bc : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m21]; exact w20_bc
  have w21_c0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m21]; exact w20_c0
  have w21_c4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m21]; exact w20_c4
  have w21_c8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m21]; exact w20_c8
  have w21_cc : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m21]; exact w20_cc
  have w21_d0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m21]; exact w20_d0
  have w21_d4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m21]; exact w20_d4
  have w21_d8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m21]; exact w20_d8
  have w21_dc : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m21]; exact w20_dc
  have w21_e0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m21]; exact w20_e0
  have w21_e4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m21]; exact w20_e4
  have w21_e8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m21]; exact w20_e8
  have w21_ec : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m21]; exact w20_ec
  have w21_f0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m21]; exact w20_f0
  have w21_f4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m21]; exact w20_f4
  have w21_f8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m21]; exact w20_f8
  have w21_fc : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m21]; exact w20_fc
  have w21_100 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m21]; exact w20_100
  have w21_104 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m21]; exact w20_104
  have w21_108 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m21]; exact w20_108
  have w21_10c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m21]; exact w20_10c
  have w21_110 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m21]; exact w20_110
  have w21_114 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m21]; exact w20_114
  have w21_118 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m21]; exact w20_118
  have w21_11c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m21]; exact w20_11c
  have w21_120 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m21]; exact w20_120
  have w21_124 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m21]; exact w20_124
  have w21_128 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m21]; exact w20_128
  have w21_12c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m21]; exact w20_12c
  have w21_130 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m21]; exact w20_130
  have b21_a40 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = gs := by rw [m21]; exact b20_a40
  have b21_1040 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = gs := by rw [m21]; exact b20_1040
  have b21_14a0 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := by rw [m21]; exact b20_14a0
  have q21_420 : ∀ j, j < 96 → n21.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m21]; exact q20_420 j hj
  have q21_480 : ∀ j, j < 96 → n21.mem (B + 0x21A0 + BitVec.ofNat 32 (0x480 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m21]; exact q20_480 j hj
  have q21_4e0 : ∀ j, j < 96 → n21.mem (B + 0x21A0 + BitVec.ofNat 32 (0x4E0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m21]; exact q20_4e0 j hj
  have q21_540 : ∀ j, j < 96 → n21.mem (B + 0x21A0 + BitVec.ofNat 32 (0x540 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m21]; exact q20_540 j hj
  have a21_240 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m21]; exact a20_240
  have a21_260 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m21]; exact a20_260
  have a21_280 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m21]; exact a20_280
  have a21_2a0 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m21]; exact a20_2a0
  have a21_2c0 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m21]; exact a20_2c0
  have a21_2e0 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m21]; exact a20_2e0
  have a21_380 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m21]; exact a20_380
  have a21_400 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m21]; exact a20_400
  have a21_13e0 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U2 := by rw [m21]; exact a20_13e0
  have a21_14e0 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x14E0) 8 = U1 := by rw [m21]; exact a20_14e0
  have a21_1560 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1560) 8 = U2 := by rw [m21]; exact a20_1560
  have p21_320 : ptF n21.mem B 0x320 = P0 := by rw [m21]; exact p20_320
  have p21_3a0 : ptF n21.mem B 0x3A0 = P1 := by rw [m21]; exact p20_3a0
  have p21_5a0 : ptF n21.mem B 0x5A0 = tbl2 P0 4 := by rw [m21]; exact p20_5a0
  have p21_600 : ptF n21.mem B 0x600 = tbl2 P0 5 := by rw [m21]; exact p20_600
  have p21_660 : ptF n21.mem B 0x660 = tbl2 P0 6 := by rw [m21]; exact p20_660
  have p21_6c0 : ptF n21.mem B 0x6C0 = tbl2 P0 7 := by rw [m21]; exact p20_6c0
  have p21_a20 : ptF n21.mem B 0xA20 = tbl2 P0 0 := by rw [m21]; exact p20_a20
  have p21_a80 : ptF n21.mem B 0xA80 = tbl2 P0 1 := by rw [m21]; exact p20_a80
  have p21_ae0 : ptF n21.mem B 0xAE0 = tbl2 P0 2 := by rw [m21]; exact p20_ae0
  have p21_b40 : ptF n21.mem B 0xB40 = tbl2 P0 3 := by rw [m21]; exact p20_b40
  have p21_ba0 : ptF n21.mem B 0xBA0 = tbl2 P0 4 := by rw [m21]; exact p20_ba0
  have p21_c00 : ptF n21.mem B 0xC00 = tbl2 P0 5 := by rw [m21]; exact p20_c00
  have p21_c60 : ptF n21.mem B 0xC60 = tbl2 P0 6 := by rw [m21]; exact p20_c60
  have p21_cc0 : ptF n21.mem B 0xCC0 = tbl2 P0 7 := by rw [m21]; exact p20_cc0
  have p21_1020 : ptF n21.mem B 0x1020 = tbl2 P0 0 := by rw [m21]; exact p20_1020
  have p21_1080 : ptF n21.mem B 0x1080 = tbl2 P0 1 := by rw [m21]; exact p20_1080
  have p21_10e0 : ptF n21.mem B 0x10E0 = tbl2 P0 2 := by rw [m21]; exact p20_10e0
  have p21_1140 : ptF n21.mem B 0x1140 = tbl2 P0 3 := by rw [m21]; exact p20_1140
  have p21_11a0 : ptF n21.mem B 0x11A0 = tbl2 P0 4 := by rw [m21]; exact p20_11a0
  have p21_1200 : ptF n21.mem B 0x1200 = tbl2 P0 5 := by rw [m21]; exact p20_1200
  have p21_1260 : ptF n21.mem B 0x1260 = tbl2 P0 6 := by rw [m21]; exact p20_1260
  have p21_12c0 : ptF n21.mem B 0x12C0 = tbl2 P0 7 := by rw [m21]; exact p20_12c0
  have p21_1320 : ptF n21.mem B 0x1320 = ptDbl2 P0 := by rw [m21]; exact p20_1320
  have p21_1380 : ptF n21.mem B 0x1380 = P1 := by rw [m21]; exact p20_1380
  have p21_1480 : ptF n21.mem B 0x1480 = P0 := by rw [m21]; exact p20_1480
  have p21_1500 : ptF n21.mem B 0x1500 = P1 := by rw [m21]; exact p20_1500
  clear p20_1500 p20_1480 p20_1380 p20_1320 p20_12c0 p20_1260 p20_1200 p20_11a0 p20_1140 p20_10e0 p20_1080 p20_1020 p20_cc0 p20_c60 p20_c00 p20_ba0 p20_b40 p20_ae0 p20_a80 p20_a20 p20_6c0 p20_660 p20_600 p20_5a0 p20_3a0 p20_320 a20_1560 a20_14e0 a20_13e0 a20_400 a20_380 a20_2e0 a20_2c0 a20_2a0 a20_280 a20_260 a20_240 q20_540 q20_4e0 q20_480 q20_420 b20_14a0 b20_1040 b20_a40 w20_130 w20_12c w20_128 w20_124 w20_120 w20_11c w20_118 w20_114 w20_110 w20_10c w20_108 w20_104 w20_100 w20_fc w20_f8 w20_f4 w20_f0 w20_ec w20_e8 w20_e4 w20_e0 w20_dc w20_d8 w20_d4 w20_d0 w20_cc w20_c8 w20_c4 w20_c0 w20_bc w20_b8 w20_b4 w20_b0 w20_ac w20_a8 w20_a4 w20_a0 w20_9c w20_98 w20_94 w20_90 w20_8c w20_88 w20_84 w20_80 w20_7c w20_78 w20_70 w20_6c w20_68 w20_64 w20_60 w20_5c w20_58 w20_54 w20_50 w20_4c w20_48 w20_44 w20_40 w20_3c w20_38 w20_34 w20_30 w20_2c w20_28 w20_24 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_9 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 m20 s20 u20 d20
  -- 0x16BA: memcpy from outside the stack
  obtain ⟨n22, P22, K22, X22⟩ := sv_mcRo2 (c := 0x5A0) (N := 0x60) F RS E21 s21 sv_at_16ba sv_at_16be
    (by decide) (by decide) g21_2 g21_10 g21_11 g21_12 (by decide) (Or.inr ⟨by decide, by decide⟩)
  have s22 := P22.st
  have fr22 := P22.fr
  have t22 : Steps n0 n22 := t21.trans P22.steps
  have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
  have E22 : SvCode n22.mem := E21.fr F fr22
  have V22 : SvSaves B n22.mem v := V21.keep K22 (by decide)
  have g22_2 : reg n22 sp = B + 0x21A0 := by rw [P22.regs sp (by decide), g21_2]
  have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P22.regs (3 : Fin 32) (by decide), g21_3]
  have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P22.regs (4 : Fin 32) (by decide), g21_4]
  have g22_8 : reg n22 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x5A0 := by rw [P22.regs (8 : Fin 32) (by decide), g21_8]
  have g22_9 : reg n22 (9 : Fin 32) = BitVec.ofNat 32 0x4 := by rw [P22.regs (9 : Fin 32) (by decide), g21_9]
  have g22_18 : reg n22 (18 : Fin 32) = out := by rw [P22.regs (18 : Fin 32) (by decide), g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [P22.regs (19 : Fin 32) (by decide), g21_19]
  have g22_20 : reg n22 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P22.regs (20 : Fin 32) (by decide), g21_20]
  have g22_21 : reg n22 (21 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P22.regs (21 : Fin 32) (by decide), g21_21]
  have g22_22 : reg n22 (22 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [P22.regs (22 : Fin 32) (by decide), g21_22]
  have g22_23 : reg n22 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1500 := by rw [P22.regs (23 : Fin 32) (by decide), g21_23]
  have g22_24 : reg n22 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P22.regs (24 : Fin 32) (by decide), g21_24]
  have g22_25 : reg n22 (25 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [P22.regs (25 : Fin 32) (by decide), g21_25]
  have g22_26 : reg n22 (26 : Fin 32) = x26 := by rw [P22.regs (26 : Fin 32) (by decide), g21_26]
  have g22_27 : reg n22 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P22.regs (27 : Fin 32) (by decide), g21_27]
  have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x1380, 0x80), (0x420, 0x60), (0x480, 0x60), (0x4E0, 0x60), (0x540, 0x60), (0x5A0, 0x60)] := keep_kk21.trans K22.toL
  clear keep_kk21
  have w22_24 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K22.w32 (by decide) (by decide)).trans w21_24
  have w22_28 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K22.w32 (by decide) (by decide)).trans w21_28
  have w22_2c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K22.w32 (by decide) (by decide)).trans w21_2c
  have w22_30 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K22.w32 (by decide) (by decide)).trans w21_30
  have w22_34 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K22.w32 (by decide) (by decide)).trans w21_34
  have w22_38 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K22.w32 (by decide) (by decide)).trans w21_38
  have w22_3c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K22.w32 (by decide) (by decide)).trans w21_3c
  have w22_40 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K22.w32 (by decide) (by decide)).trans w21_40
  have w22_44 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K22.w32 (by decide) (by decide)).trans w21_44
  have w22_48 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K22.w32 (by decide) (by decide)).trans w21_48
  have w22_4c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K22.w32 (by decide) (by decide)).trans w21_4c
  have w22_50 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K22.w32 (by decide) (by decide)).trans w21_50
  have w22_54 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K22.w32 (by decide) (by decide)).trans w21_54
  have w22_58 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K22.w32 (by decide) (by decide)).trans w21_58
  have w22_5c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K22.w32 (by decide) (by decide)).trans w21_5c
  have w22_60 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K22.w32 (by decide) (by decide)).trans w21_60
  have w22_64 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K22.w32 (by decide) (by decide)).trans w21_64
  have w22_68 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K22.w32 (by decide) (by decide)).trans w21_68
  have w22_6c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K22.w32 (by decide) (by decide)).trans w21_6c
  have w22_70 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K22.w32 (by decide) (by decide)).trans w21_70
  have w22_78 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := (K22.w32 (by decide) (by decide)).trans w21_78
  have w22_7c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K22.w32 (by decide) (by decide)).trans w21_7c
  have w22_80 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K22.w32 (by decide) (by decide)).trans w21_80
  have w22_84 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K22.w32 (by decide) (by decide)).trans w21_84
  have w22_88 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K22.w32 (by decide) (by decide)).trans w21_88
  have w22_8c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K22.w32 (by decide) (by decide)).trans w21_8c
  have w22_90 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K22.w32 (by decide) (by decide)).trans w21_90
  have w22_94 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K22.w32 (by decide) (by decide)).trans w21_94
  have w22_98 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K22.w32 (by decide) (by decide)).trans w21_98
  have w22_9c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K22.w32 (by decide) (by decide)).trans w21_9c
  have w22_a0 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K22.w32 (by decide) (by decide)).trans w21_a0
  have w22_a4 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K22.w32 (by decide) (by decide)).trans w21_a4
  have w22_a8 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K22.w32 (by decide) (by decide)).trans w21_a8
  have w22_ac : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K22.w32 (by decide) (by decide)).trans w21_ac
  have w22_b0 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K22.w32 (by decide) (by decide)).trans w21_b0
  have w22_b4 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K22.w32 (by decide) (by decide)).trans w21_b4
  have w22_b8 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K22.w32 (by decide) (by decide)).trans w21_b8
  have w22_bc : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K22.w32 (by decide) (by decide)).trans w21_bc
  have w22_c0 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K22.w32 (by decide) (by decide)).trans w21_c0
  have w22_c4 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K22.w32 (by decide) (by decide)).trans w21_c4
  have w22_c8 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K22.w32 (by decide) (by decide)).trans w21_c8
  have w22_cc : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K22.w32 (by decide) (by decide)).trans w21_cc
  have w22_d0 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K22.w32 (by decide) (by decide)).trans w21_d0
  have w22_d4 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K22.w32 (by decide) (by decide)).trans w21_d4
  have w22_d8 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K22.w32 (by decide) (by decide)).trans w21_d8
  have w22_dc : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K22.w32 (by decide) (by decide)).trans w21_dc
  have w22_e0 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K22.w32 (by decide) (by decide)).trans w21_e0
  have w22_e4 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K22.w32 (by decide) (by decide)).trans w21_e4
  have w22_e8 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K22.w32 (by decide) (by decide)).trans w21_e8
  have w22_ec : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K22.w32 (by decide) (by decide)).trans w21_ec
  have w22_f0 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K22.w32 (by decide) (by decide)).trans w21_f0
  have w22_f4 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K22.w32 (by decide) (by decide)).trans w21_f4
  have w22_f8 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K22.w32 (by decide) (by decide)).trans w21_f8
  have w22_fc : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K22.w32 (by decide) (by decide)).trans w21_fc
  have w22_100 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K22.w32 (by decide) (by decide)).trans w21_100
  have w22_104 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K22.w32 (by decide) (by decide)).trans w21_104
  have w22_108 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K22.w32 (by decide) (by decide)).trans w21_108
  have w22_10c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K22.w32 (by decide) (by decide)).trans w21_10c
  have w22_110 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K22.w32 (by decide) (by decide)).trans w21_110
  have w22_114 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K22.w32 (by decide) (by decide)).trans w21_114
  have w22_118 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K22.w32 (by decide) (by decide)).trans w21_118
  have w22_11c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K22.w32 (by decide) (by decide)).trans w21_11c
  have w22_120 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K22.w32 (by decide) (by decide)).trans w21_120
  have w22_124 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K22.w32 (by decide) (by decide)).trans w21_124
  have w22_128 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K22.w32 (by decide) (by decide)).trans w21_128
  have w22_12c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K22.w32 (by decide) (by decide)).trans w21_12c
  have w22_130 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K22.w32 (by decide) (by decide)).trans w21_130
  have b22_a40 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = gs := (K22.b8 (by decide) (by decide)).trans b21_a40
  have b22_1040 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = gs := (K22.b8 (by decide) (by decide)).trans b21_1040
  have b22_14a0 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := (K22.b8 (by decide) (by decide)).trans b21_14a0
  have q22_420 : ∀ j, j < 96 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K22.range (by decide) (by decide) j hj).trans (q21_420 j hj)
  have q22_480 : ∀ j, j < 96 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0x480 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K22.range (by decide) (by decide) j hj).trans (q21_480 j hj)
  have q22_4e0 : ∀ j, j < 96 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0x4E0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K22.range (by decide) (by decide) j hj).trans (q21_4e0 j hj)
  have q22_540 : ∀ j, j < 96 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0x540 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K22.range (by decide) (by decide) j hj).trans (q21_540 j hj)
  have a22_240 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := (K22.acc (by decide) (by decide)).trans a21_240
  have a22_260 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := (K22.acc (by decide) (by decide)).trans a21_260
  have a22_280 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := (K22.acc (by decide) (by decide)).trans a21_280
  have a22_2a0 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K22.acc (by decide) (by decide)).trans a21_2a0
  have a22_2c0 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K22.acc (by decide) (by decide)).trans a21_2c0
  have a22_2e0 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K22.acc (by decide) (by decide)).trans a21_2e0
  have a22_380 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := (K22.acc (by decide) (by decide)).trans a21_380
  have a22_400 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := (K22.acc (by decide) (by decide)).trans a21_400
  have a22_13e0 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U2 := (K22.acc (by decide) (by decide)).trans a21_13e0
  have a22_14e0 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x14E0) 8 = U1 := (K22.acc (by decide) (by decide)).trans a21_14e0
  have a22_1560 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1560) 8 = U2 := (K22.acc (by decide) (by decide)).trans a21_1560
  have p22_320 : ptF n22.mem B 0x320 = P0 := (K22.pt (by decide) (by decide)).trans p21_320
  have p22_3a0 : ptF n22.mem B 0x3A0 = P1 := (K22.pt (by decide) (by decide)).trans p21_3a0
  have p22_600 : ptF n22.mem B 0x600 = tbl2 P0 5 := (K22.pt (by decide) (by decide)).trans p21_600
  have p22_660 : ptF n22.mem B 0x660 = tbl2 P0 6 := (K22.pt (by decide) (by decide)).trans p21_660
  have p22_6c0 : ptF n22.mem B 0x6C0 = tbl2 P0 7 := (K22.pt (by decide) (by decide)).trans p21_6c0
  have p22_a20 : ptF n22.mem B 0xA20 = tbl2 P0 0 := (K22.pt (by decide) (by decide)).trans p21_a20
  have p22_a80 : ptF n22.mem B 0xA80 = tbl2 P0 1 := (K22.pt (by decide) (by decide)).trans p21_a80
  have p22_ae0 : ptF n22.mem B 0xAE0 = tbl2 P0 2 := (K22.pt (by decide) (by decide)).trans p21_ae0
  have p22_b40 : ptF n22.mem B 0xB40 = tbl2 P0 3 := (K22.pt (by decide) (by decide)).trans p21_b40
  have p22_ba0 : ptF n22.mem B 0xBA0 = tbl2 P0 4 := (K22.pt (by decide) (by decide)).trans p21_ba0
  have p22_c00 : ptF n22.mem B 0xC00 = tbl2 P0 5 := (K22.pt (by decide) (by decide)).trans p21_c00
  have p22_c60 : ptF n22.mem B 0xC60 = tbl2 P0 6 := (K22.pt (by decide) (by decide)).trans p21_c60
  have p22_cc0 : ptF n22.mem B 0xCC0 = tbl2 P0 7 := (K22.pt (by decide) (by decide)).trans p21_cc0
  have p22_1020 : ptF n22.mem B 0x1020 = tbl2 P0 0 := (K22.pt (by decide) (by decide)).trans p21_1020
  have p22_1080 : ptF n22.mem B 0x1080 = tbl2 P0 1 := (K22.pt (by decide) (by decide)).trans p21_1080
  have p22_10e0 : ptF n22.mem B 0x10E0 = tbl2 P0 2 := (K22.pt (by decide) (by decide)).trans p21_10e0
  have p22_1140 : ptF n22.mem B 0x1140 = tbl2 P0 3 := (K22.pt (by decide) (by decide)).trans p21_1140
  have p22_11a0 : ptF n22.mem B 0x11A0 = tbl2 P0 4 := (K22.pt (by decide) (by decide)).trans p21_11a0
  have p22_1200 : ptF n22.mem B 0x1200 = tbl2 P0 5 := (K22.pt (by decide) (by decide)).trans p21_1200
  have p22_1260 : ptF n22.mem B 0x1260 = tbl2 P0 6 := (K22.pt (by decide) (by decide)).trans p21_1260
  have p22_12c0 : ptF n22.mem B 0x12C0 = tbl2 P0 7 := (K22.pt (by decide) (by decide)).trans p21_12c0
  have p22_1320 : ptF n22.mem B 0x1320 = ptDbl2 P0 := (K22.pt (by decide) (by decide)).trans p21_1320
  have p22_1380 : ptF n22.mem B 0x1380 = P1 := (K22.pt (by decide) (by decide)).trans p21_1380
  have p22_1480 : ptF n22.mem B 0x1480 = P0 := (K22.pt (by decide) (by decide)).trans p21_1480
  have p22_1500 : ptF n22.mem B 0x1500 = P1 := (K22.pt (by decide) (by decide)).trans p21_1500
  have q22_5a0 : ∀ j, j < 96 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0x5A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) :=
    fun j hj => (X22 j hj).trans (fR21 _ (SvRo2.r RS (Or.inr ⟨by decide, by decide⟩) hj))
  clear p21_1500 p21_1480 p21_1380 p21_1320 p21_12c0 p21_1260 p21_1200 p21_11a0 p21_1140 p21_10e0 p21_1080 p21_1020 p21_cc0 p21_c60 p21_c00 p21_ba0 p21_b40 p21_ae0 p21_a80 p21_a20 p21_6c0 p21_660 p21_600 p21_5a0 p21_3a0 p21_320 a21_1560 a21_14e0 a21_13e0 a21_400 a21_380 a21_2e0 a21_2c0 a21_2a0 a21_280 a21_260 a21_240 q21_540 q21_4e0 q21_480 q21_420 b21_14a0 b21_1040 b21_a40 w21_130 w21_12c w21_128 w21_124 w21_120 w21_11c w21_118 w21_114 w21_110 w21_10c w21_108 w21_104 w21_100 w21_fc w21_f8 w21_f4 w21_f0 w21_ec w21_e8 w21_e4 w21_e0 w21_dc w21_d8 w21_d4 w21_d0 w21_cc w21_c8 w21_c4 w21_c0 w21_bc w21_b8 w21_b4 w21_b0 w21_ac w21_a8 w21_a4 w21_a0 w21_9c w21_98 w21_94 w21_90 w21_8c w21_88 w21_84 w21_80 w21_7c w21_78 w21_70 w21_6c w21_68 w21_64 w21_60 w21_5c w21_58 w21_54 w21_50 w21_4c w21_48 w21_44 w21_40 w21_3c w21_38 w21_34 w21_30 w21_2c w21_28 w21_24 g21_12 g21_11 g21_10 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_9 g21_8 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 rb21 s21 m21 u21 c21
  -- 0x16C2
  obtain ⟨n23, c23, u23⟩ := s22.block svEcT1a16c2 E22.self svEcT1a16c2_end
    ⟨trivial, trivial, trivial⟩
  have m23 : n23.mem = n22.mem := u23.mem
  have s23 : St n23.mem SV n23 0x16C8 (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
  have rb23 : ∀ q, reg n23 q = (runBlock svEcT1a16c2 (n22.mem, reg n22)).2 q := fun q => by rw [u23.regs]
  have fr23 : ∀ x, SvR B x → n23.mem x = n22.mem x := fun x _ => by rw [m23]
  have t23 : Steps n0 n23 := t22.trans c23
  have fR23 : ∀ x, SvR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
  have E23 : SvCode n23.mem := E22.fr F fr23
  have V23 : SvSaves B n23.mem v := V22.same m23
  have g23_2 : reg n23 sp = B + 0x21A0 := by
    rw [rb23, runBlock_reg _ _ _ sp s22.zero (by decide), g22_2]
  have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb23, runBlock_reg _ _ _ (3 : Fin 32) s22.zero (by decide), g22_3]
  have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb23, runBlock_reg _ _ _ (4 : Fin 32) s22.zero (by decide), g22_4]
  have g23_18 : reg n23 (18 : Fin 32) = out := by
    rw [rb23, runBlock_reg _ _ _ (18 : Fin 32) s22.zero (by decide), g22_18]
  have g23_19 : reg n23 (19 : Fin 32) = bp := by
    rw [rb23, runBlock_reg _ _ _ (19 : Fin 32) s22.zero (by decide), g22_19]
  have g23_20 : reg n23 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb23, runBlock_reg _ _ _ (20 : Fin 32) s22.zero (by decide), g22_20]
  have g23_21 : reg n23 (21 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb23, runBlock_reg _ _ _ (21 : Fin 32) s22.zero (by decide), g22_21]
  have g23_22 : reg n23 (22 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb23, runBlock_reg _ _ _ (22 : Fin 32) s22.zero (by decide), g22_22]
  have g23_23 : reg n23 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1500 := by
    rw [rb23, runBlock_reg _ _ _ (23 : Fin 32) s22.zero (by decide), g22_23]
  have g23_24 : reg n23 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb23, runBlock_reg _ _ _ (24 : Fin 32) s22.zero (by decide), g22_24]
  have g23_25 : reg n23 (25 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb23, runBlock_reg _ _ _ (25 : Fin 32) s22.zero (by decide), g22_25]
  have g23_26 : reg n23 (26 : Fin 32) = x26 := by
    rw [rb23, runBlock_reg _ _ _ (26 : Fin 32) s22.zero (by decide), g22_26]
  have g23_27 : reg n23 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb23, runBlock_reg _ _ _ (27 : Fin 32) s22.zero (by decide), g22_27]
  have g23_8 : reg n23 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x600 := by
    rw [rb23]; simp +decide only [runBlock, BInstr.run, svEcT1a16c2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g22_2, g22_3, g22_4, g22_8, g22_9, g22_18, g22_19, g22_20, g22_21, g22_22, g22_23, g22_24, g22_25, g22_26, g22_27, s22.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g23_9 : reg n23 (9 : Fin 32) = BitVec.ofNat 32 0x3 := by
    rw [rb23]; simp +decide only [runBlock, BInstr.run, svEcT1a16c2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g22_2, g22_3, g22_4, g22_8, g22_9, g22_18, g22_19, g22_20, g22_21, g22_22, g22_23, g22_24, g22_25, g22_26, g22_27, s22.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x1380, 0x80), (0x420, 0x60), (0x480, 0x60), (0x4E0, 0x60), (0x540, 0x60), (0x5A0, 0x60)] := by rw [m23]; exact keep_kk22
  clear keep_kk22
  have w23_24 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m23]; exact w22_24
  have w23_28 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m23]; exact w22_28
  have w23_2c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m23]; exact w22_2c
  have w23_30 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m23]; exact w22_30
  have w23_34 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m23]; exact w22_34
  have w23_38 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m23]; exact w22_38
  have w23_3c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m23]; exact w22_3c
  have w23_40 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m23]; exact w22_40
  have w23_44 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m23]; exact w22_44
  have w23_48 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m23]; exact w22_48
  have w23_4c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m23]; exact w22_4c
  have w23_50 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m23]; exact w22_50
  have w23_54 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m23]; exact w22_54
  have w23_58 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m23]; exact w22_58
  have w23_5c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m23]; exact w22_5c
  have w23_60 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m23]; exact w22_60
  have w23_64 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m23]; exact w22_64
  have w23_68 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m23]; exact w22_68
  have w23_6c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m23]; exact w22_6c
  have w23_70 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m23]; exact w22_70
  have w23_78 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m23]; exact w22_78
  have w23_7c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m23]; exact w22_7c
  have w23_80 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m23]; exact w22_80
  have w23_84 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m23]; exact w22_84
  have w23_88 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m23]; exact w22_88
  have w23_8c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m23]; exact w22_8c
  have w23_90 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m23]; exact w22_90
  have w23_94 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m23]; exact w22_94
  have w23_98 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m23]; exact w22_98
  have w23_9c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m23]; exact w22_9c
  have w23_a0 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m23]; exact w22_a0
  have w23_a4 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m23]; exact w22_a4
  have w23_a8 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m23]; exact w22_a8
  have w23_ac : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m23]; exact w22_ac
  have w23_b0 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m23]; exact w22_b0
  have w23_b4 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m23]; exact w22_b4
  have w23_b8 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m23]; exact w22_b8
  have w23_bc : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m23]; exact w22_bc
  have w23_c0 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m23]; exact w22_c0
  have w23_c4 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m23]; exact w22_c4
  have w23_c8 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m23]; exact w22_c8
  have w23_cc : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m23]; exact w22_cc
  have w23_d0 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m23]; exact w22_d0
  have w23_d4 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m23]; exact w22_d4
  have w23_d8 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m23]; exact w22_d8
  have w23_dc : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m23]; exact w22_dc
  have w23_e0 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m23]; exact w22_e0
  have w23_e4 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m23]; exact w22_e4
  have w23_e8 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m23]; exact w22_e8
  have w23_ec : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m23]; exact w22_ec
  have w23_f0 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m23]; exact w22_f0
  have w23_f4 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m23]; exact w22_f4
  have w23_f8 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m23]; exact w22_f8
  have w23_fc : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m23]; exact w22_fc
  have w23_100 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m23]; exact w22_100
  have w23_104 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m23]; exact w22_104
  have w23_108 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m23]; exact w22_108
  have w23_10c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m23]; exact w22_10c
  have w23_110 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m23]; exact w22_110
  have w23_114 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m23]; exact w22_114
  have w23_118 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m23]; exact w22_118
  have w23_11c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m23]; exact w22_11c
  have w23_120 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m23]; exact w22_120
  have w23_124 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m23]; exact w22_124
  have w23_128 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m23]; exact w22_128
  have w23_12c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m23]; exact w22_12c
  have w23_130 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m23]; exact w22_130
  have b23_a40 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = gs := by rw [m23]; exact b22_a40
  have b23_1040 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = gs := by rw [m23]; exact b22_1040
  have b23_14a0 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := by rw [m23]; exact b22_14a0
  have q23_420 : ∀ j, j < 96 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m23]; exact q22_420 j hj
  have q23_480 : ∀ j, j < 96 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0x480 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m23]; exact q22_480 j hj
  have q23_4e0 : ∀ j, j < 96 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0x4E0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m23]; exact q22_4e0 j hj
  have q23_540 : ∀ j, j < 96 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0x540 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m23]; exact q22_540 j hj
  have q23_5a0 : ∀ j, j < 96 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0x5A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m23]; exact q22_5a0 j hj
  have a23_240 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m23]; exact a22_240
  have a23_260 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m23]; exact a22_260
  have a23_280 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m23]; exact a22_280
  have a23_2a0 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m23]; exact a22_2a0
  have a23_2c0 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m23]; exact a22_2c0
  have a23_2e0 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m23]; exact a22_2e0
  have a23_380 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m23]; exact a22_380
  have a23_400 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m23]; exact a22_400
  have a23_13e0 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U2 := by rw [m23]; exact a22_13e0
  have a23_14e0 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x14E0) 8 = U1 := by rw [m23]; exact a22_14e0
  have a23_1560 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1560) 8 = U2 := by rw [m23]; exact a22_1560
  have p23_320 : ptF n23.mem B 0x320 = P0 := by rw [m23]; exact p22_320
  have p23_3a0 : ptF n23.mem B 0x3A0 = P1 := by rw [m23]; exact p22_3a0
  have p23_600 : ptF n23.mem B 0x600 = tbl2 P0 5 := by rw [m23]; exact p22_600
  have p23_660 : ptF n23.mem B 0x660 = tbl2 P0 6 := by rw [m23]; exact p22_660
  have p23_6c0 : ptF n23.mem B 0x6C0 = tbl2 P0 7 := by rw [m23]; exact p22_6c0
  have p23_a20 : ptF n23.mem B 0xA20 = tbl2 P0 0 := by rw [m23]; exact p22_a20
  have p23_a80 : ptF n23.mem B 0xA80 = tbl2 P0 1 := by rw [m23]; exact p22_a80
  have p23_ae0 : ptF n23.mem B 0xAE0 = tbl2 P0 2 := by rw [m23]; exact p22_ae0
  have p23_b40 : ptF n23.mem B 0xB40 = tbl2 P0 3 := by rw [m23]; exact p22_b40
  have p23_ba0 : ptF n23.mem B 0xBA0 = tbl2 P0 4 := by rw [m23]; exact p22_ba0
  have p23_c00 : ptF n23.mem B 0xC00 = tbl2 P0 5 := by rw [m23]; exact p22_c00
  have p23_c60 : ptF n23.mem B 0xC60 = tbl2 P0 6 := by rw [m23]; exact p22_c60
  have p23_cc0 : ptF n23.mem B 0xCC0 = tbl2 P0 7 := by rw [m23]; exact p22_cc0
  have p23_1020 : ptF n23.mem B 0x1020 = tbl2 P0 0 := by rw [m23]; exact p22_1020
  have p23_1080 : ptF n23.mem B 0x1080 = tbl2 P0 1 := by rw [m23]; exact p22_1080
  have p23_10e0 : ptF n23.mem B 0x10E0 = tbl2 P0 2 := by rw [m23]; exact p22_10e0
  have p23_1140 : ptF n23.mem B 0x1140 = tbl2 P0 3 := by rw [m23]; exact p22_1140
  have p23_11a0 : ptF n23.mem B 0x11A0 = tbl2 P0 4 := by rw [m23]; exact p22_11a0
  have p23_1200 : ptF n23.mem B 0x1200 = tbl2 P0 5 := by rw [m23]; exact p22_1200
  have p23_1260 : ptF n23.mem B 0x1260 = tbl2 P0 6 := by rw [m23]; exact p22_1260
  have p23_12c0 : ptF n23.mem B 0x12C0 = tbl2 P0 7 := by rw [m23]; exact p22_12c0
  have p23_1320 : ptF n23.mem B 0x1320 = ptDbl2 P0 := by rw [m23]; exact p22_1320
  have p23_1380 : ptF n23.mem B 0x1380 = P1 := by rw [m23]; exact p22_1380
  have p23_1480 : ptF n23.mem B 0x1480 = P0 := by rw [m23]; exact p22_1480
  have p23_1500 : ptF n23.mem B 0x1500 = P1 := by rw [m23]; exact p22_1500
  clear q22_5a0 p22_1500 p22_1480 p22_1380 p22_1320 p22_12c0 p22_1260 p22_1200 p22_11a0 p22_1140 p22_10e0 p22_1080 p22_1020 p22_cc0 p22_c60 p22_c00 p22_ba0 p22_b40 p22_ae0 p22_a80 p22_a20 p22_6c0 p22_660 p22_600 p22_3a0 p22_320 a22_1560 a22_14e0 a22_13e0 a22_400 a22_380 a22_2e0 a22_2c0 a22_2a0 a22_280 a22_260 a22_240 q22_540 q22_4e0 q22_480 q22_420 b22_14a0 b22_1040 b22_a40 w22_130 w22_12c w22_128 w22_124 w22_120 w22_11c w22_118 w22_114 w22_110 w22_10c w22_108 w22_104 w22_100 w22_fc w22_f8 w22_f4 w22_f0 w22_ec w22_e8 w22_e4 w22_e0 w22_dc w22_d8 w22_d4 w22_d0 w22_cc w22_c8 w22_c4 w22_c0 w22_bc w22_b8 w22_b4 w22_b0 w22_ac w22_a8 w22_a4 w22_a0 w22_9c w22_98 w22_94 w22_90 w22_8c w22_88 w22_84 w22_80 w22_7c w22_78 w22_70 w22_6c w22_68 w22_64 w22_60 w22_5c w22_58 w22_54 w22_50 w22_4c w22_48 w22_44 w22_40 w22_3c w22_38 w22_34 w22_30 w22_2c w22_28 w22_24 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_9 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 s22 X22 K22 P22
  -- 0x16C8: branch, taken
  obtain ⟨n24, d24, u24⟩ := s23.taken E23.self 0x16B2 sv_at_16c8
    (by decide) (by rw [g23_9, s23.zero]; decide)
  have s24 : St n24.mem SV n24 0x16B2 (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
  have m24 : n24.mem = n23.mem := u24.mem
  have fr24 : ∀ x, SvR B x → n24.mem x = n23.mem x := fun x _ => by rw [m24]
  have t24 : Steps n0 n24 := t23.trans (.single d24)
  have fR24 : ∀ x, SvR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
  have E24 : SvCode n24.mem := E23.fr F fr24
  have V24 : SvSaves B n24.mem v := V23.same m24
  have g24_2 : reg n24 sp = B + 0x21A0 := by rw [u24.regs, g23_2]
  have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u24.regs, g23_3]
  have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u24.regs, g23_4]
  have g24_8 : reg n24 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x600 := by rw [u24.regs, g23_8]
  have g24_9 : reg n24 (9 : Fin 32) = BitVec.ofNat 32 0x3 := by rw [u24.regs, g23_9]
  have g24_18 : reg n24 (18 : Fin 32) = out := by rw [u24.regs, g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = bp := by rw [u24.regs, g23_19]
  have g24_20 : reg n24 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u24.regs, g23_20]
  have g24_21 : reg n24 (21 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u24.regs, g23_21]
  have g24_22 : reg n24 (22 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [u24.regs, g23_22]
  have g24_23 : reg n24 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1500 := by rw [u24.regs, g23_23]
  have g24_24 : reg n24 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u24.regs, g23_24]
  have g24_25 : reg n24 (25 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [u24.regs, g23_25]
  have g24_26 : reg n24 (26 : Fin 32) = x26 := by rw [u24.regs, g23_26]
  have g24_27 : reg n24 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u24.regs, g23_27]
  have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x1380, 0x80), (0x420, 0x60), (0x480, 0x60), (0x4E0, 0x60), (0x540, 0x60), (0x5A0, 0x60)] := by rw [m24]; exact keep_kk23
  clear keep_kk23
  have w24_24 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m24]; exact w23_24
  have w24_28 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m24]; exact w23_28
  have w24_2c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m24]; exact w23_2c
  have w24_30 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m24]; exact w23_30
  have w24_34 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m24]; exact w23_34
  have w24_38 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m24]; exact w23_38
  have w24_3c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m24]; exact w23_3c
  have w24_40 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m24]; exact w23_40
  have w24_44 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m24]; exact w23_44
  have w24_48 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m24]; exact w23_48
  have w24_4c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m24]; exact w23_4c
  have w24_50 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m24]; exact w23_50
  have w24_54 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m24]; exact w23_54
  have w24_58 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m24]; exact w23_58
  have w24_5c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m24]; exact w23_5c
  have w24_60 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m24]; exact w23_60
  have w24_64 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m24]; exact w23_64
  have w24_68 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m24]; exact w23_68
  have w24_6c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m24]; exact w23_6c
  have w24_70 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m24]; exact w23_70
  have w24_78 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m24]; exact w23_78
  have w24_7c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m24]; exact w23_7c
  have w24_80 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m24]; exact w23_80
  have w24_84 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m24]; exact w23_84
  have w24_88 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m24]; exact w23_88
  have w24_8c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m24]; exact w23_8c
  have w24_90 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m24]; exact w23_90
  have w24_94 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m24]; exact w23_94
  have w24_98 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m24]; exact w23_98
  have w24_9c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m24]; exact w23_9c
  have w24_a0 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m24]; exact w23_a0
  have w24_a4 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m24]; exact w23_a4
  have w24_a8 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m24]; exact w23_a8
  have w24_ac : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m24]; exact w23_ac
  have w24_b0 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m24]; exact w23_b0
  have w24_b4 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m24]; exact w23_b4
  have w24_b8 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m24]; exact w23_b8
  have w24_bc : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m24]; exact w23_bc
  have w24_c0 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m24]; exact w23_c0
  have w24_c4 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m24]; exact w23_c4
  have w24_c8 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m24]; exact w23_c8
  have w24_cc : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m24]; exact w23_cc
  have w24_d0 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m24]; exact w23_d0
  have w24_d4 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m24]; exact w23_d4
  have w24_d8 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m24]; exact w23_d8
  have w24_dc : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m24]; exact w23_dc
  have w24_e0 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m24]; exact w23_e0
  have w24_e4 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m24]; exact w23_e4
  have w24_e8 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m24]; exact w23_e8
  have w24_ec : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m24]; exact w23_ec
  have w24_f0 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m24]; exact w23_f0
  have w24_f4 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m24]; exact w23_f4
  have w24_f8 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m24]; exact w23_f8
  have w24_fc : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m24]; exact w23_fc
  have w24_100 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m24]; exact w23_100
  have w24_104 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m24]; exact w23_104
  have w24_108 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m24]; exact w23_108
  have w24_10c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m24]; exact w23_10c
  have w24_110 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m24]; exact w23_110
  have w24_114 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m24]; exact w23_114
  have w24_118 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m24]; exact w23_118
  have w24_11c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m24]; exact w23_11c
  have w24_120 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m24]; exact w23_120
  have w24_124 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m24]; exact w23_124
  have w24_128 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m24]; exact w23_128
  have w24_12c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m24]; exact w23_12c
  have w24_130 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m24]; exact w23_130
  have b24_a40 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = gs := by rw [m24]; exact b23_a40
  have b24_1040 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = gs := by rw [m24]; exact b23_1040
  have b24_14a0 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := by rw [m24]; exact b23_14a0
  have q24_420 : ∀ j, j < 96 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m24]; exact q23_420 j hj
  have q24_480 : ∀ j, j < 96 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0x480 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m24]; exact q23_480 j hj
  have q24_4e0 : ∀ j, j < 96 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0x4E0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m24]; exact q23_4e0 j hj
  have q24_540 : ∀ j, j < 96 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0x540 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m24]; exact q23_540 j hj
  have q24_5a0 : ∀ j, j < 96 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0x5A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m24]; exact q23_5a0 j hj
  have a24_240 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m24]; exact a23_240
  have a24_260 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m24]; exact a23_260
  have a24_280 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m24]; exact a23_280
  have a24_2a0 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m24]; exact a23_2a0
  have a24_2c0 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m24]; exact a23_2c0
  have a24_2e0 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m24]; exact a23_2e0
  have a24_380 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m24]; exact a23_380
  have a24_400 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m24]; exact a23_400
  have a24_13e0 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U2 := by rw [m24]; exact a23_13e0
  have a24_14e0 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x14E0) 8 = U1 := by rw [m24]; exact a23_14e0
  have a24_1560 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1560) 8 = U2 := by rw [m24]; exact a23_1560
  have p24_320 : ptF n24.mem B 0x320 = P0 := by rw [m24]; exact p23_320
  have p24_3a0 : ptF n24.mem B 0x3A0 = P1 := by rw [m24]; exact p23_3a0
  have p24_600 : ptF n24.mem B 0x600 = tbl2 P0 5 := by rw [m24]; exact p23_600
  have p24_660 : ptF n24.mem B 0x660 = tbl2 P0 6 := by rw [m24]; exact p23_660
  have p24_6c0 : ptF n24.mem B 0x6C0 = tbl2 P0 7 := by rw [m24]; exact p23_6c0
  have p24_a20 : ptF n24.mem B 0xA20 = tbl2 P0 0 := by rw [m24]; exact p23_a20
  have p24_a80 : ptF n24.mem B 0xA80 = tbl2 P0 1 := by rw [m24]; exact p23_a80
  have p24_ae0 : ptF n24.mem B 0xAE0 = tbl2 P0 2 := by rw [m24]; exact p23_ae0
  have p24_b40 : ptF n24.mem B 0xB40 = tbl2 P0 3 := by rw [m24]; exact p23_b40
  have p24_ba0 : ptF n24.mem B 0xBA0 = tbl2 P0 4 := by rw [m24]; exact p23_ba0
  have p24_c00 : ptF n24.mem B 0xC00 = tbl2 P0 5 := by rw [m24]; exact p23_c00
  have p24_c60 : ptF n24.mem B 0xC60 = tbl2 P0 6 := by rw [m24]; exact p23_c60
  have p24_cc0 : ptF n24.mem B 0xCC0 = tbl2 P0 7 := by rw [m24]; exact p23_cc0
  have p24_1020 : ptF n24.mem B 0x1020 = tbl2 P0 0 := by rw [m24]; exact p23_1020
  have p24_1080 : ptF n24.mem B 0x1080 = tbl2 P0 1 := by rw [m24]; exact p23_1080
  have p24_10e0 : ptF n24.mem B 0x10E0 = tbl2 P0 2 := by rw [m24]; exact p23_10e0
  have p24_1140 : ptF n24.mem B 0x1140 = tbl2 P0 3 := by rw [m24]; exact p23_1140
  have p24_11a0 : ptF n24.mem B 0x11A0 = tbl2 P0 4 := by rw [m24]; exact p23_11a0
  have p24_1200 : ptF n24.mem B 0x1200 = tbl2 P0 5 := by rw [m24]; exact p23_1200
  have p24_1260 : ptF n24.mem B 0x1260 = tbl2 P0 6 := by rw [m24]; exact p23_1260
  have p24_12c0 : ptF n24.mem B 0x12C0 = tbl2 P0 7 := by rw [m24]; exact p23_12c0
  have p24_1320 : ptF n24.mem B 0x1320 = ptDbl2 P0 := by rw [m24]; exact p23_1320
  have p24_1380 : ptF n24.mem B 0x1380 = P1 := by rw [m24]; exact p23_1380
  have p24_1480 : ptF n24.mem B 0x1480 = P0 := by rw [m24]; exact p23_1480
  have p24_1500 : ptF n24.mem B 0x1500 = P1 := by rw [m24]; exact p23_1500
  clear p23_1500 p23_1480 p23_1380 p23_1320 p23_12c0 p23_1260 p23_1200 p23_11a0 p23_1140 p23_10e0 p23_1080 p23_1020 p23_cc0 p23_c60 p23_c00 p23_ba0 p23_b40 p23_ae0 p23_a80 p23_a20 p23_6c0 p23_660 p23_600 p23_3a0 p23_320 a23_1560 a23_14e0 a23_13e0 a23_400 a23_380 a23_2e0 a23_2c0 a23_2a0 a23_280 a23_260 a23_240 q23_5a0 q23_540 q23_4e0 q23_480 q23_420 b23_14a0 b23_1040 b23_a40 w23_130 w23_12c w23_128 w23_124 w23_120 w23_11c w23_118 w23_114 w23_110 w23_10c w23_108 w23_104 w23_100 w23_fc w23_f8 w23_f4 w23_f0 w23_ec w23_e8 w23_e4 w23_e0 w23_dc w23_d8 w23_d4 w23_d0 w23_cc w23_c8 w23_c4 w23_c0 w23_bc w23_b8 w23_b4 w23_b0 w23_ac w23_a8 w23_a4 w23_a0 w23_9c w23_98 w23_94 w23_90 w23_8c w23_88 w23_84 w23_80 w23_7c w23_78 w23_70 w23_6c w23_68 w23_64 w23_60 w23_5c w23_58 w23_54 w23_50 w23_4c w23_48 w23_44 w23_40 w23_3c w23_38 w23_34 w23_30 w23_2c w23_28 w23_24 g23_9 g23_8 g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 rb23 s23 m23 u23 c23
  -- 0x16B2
  obtain ⟨n25, c25, u25⟩ := s24.block svEcT1a16b2 E24.self svEcT1a16b2_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m25 : n25.mem = n24.mem := u25.mem
  have s25 : St n25.mem SV n25 0x16BA (reg n25) := ⟨u25.pc, rfl, fun _ => rfl⟩
  have rb25 : ∀ q, reg n25 q = (runBlock svEcT1a16b2 (n24.mem, reg n24)).2 q := fun q => by rw [u25.regs]
  have fr25 : ∀ x, SvR B x → n25.mem x = n24.mem x := fun x _ => by rw [m25]
  have t25 : Steps n0 n25 := t24.trans c25
  have fR25 : ∀ x, SvR B x → n25.mem x = M0 x := fun x hx => (fr25 x hx).trans (fR24 x hx)
  have E25 : SvCode n25.mem := E24.fr F fr25
  have V25 : SvSaves B n25.mem v := V24.same m25
  have g25_2 : reg n25 sp = B + 0x21A0 := by
    rw [rb25, runBlock_reg _ _ _ sp s24.zero (by decide), g24_2]
  have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb25, runBlock_reg _ _ _ (3 : Fin 32) s24.zero (by decide), g24_3]
  have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb25, runBlock_reg _ _ _ (4 : Fin 32) s24.zero (by decide), g24_4]
  have g25_8 : reg n25 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x600 := by
    rw [rb25, runBlock_reg _ _ _ (8 : Fin 32) s24.zero (by decide), g24_8]
  have g25_9 : reg n25 (9 : Fin 32) = BitVec.ofNat 32 0x3 := by
    rw [rb25, runBlock_reg _ _ _ (9 : Fin 32) s24.zero (by decide), g24_9]
  have g25_18 : reg n25 (18 : Fin 32) = out := by
    rw [rb25, runBlock_reg _ _ _ (18 : Fin 32) s24.zero (by decide), g24_18]
  have g25_19 : reg n25 (19 : Fin 32) = bp := by
    rw [rb25, runBlock_reg _ _ _ (19 : Fin 32) s24.zero (by decide), g24_19]
  have g25_20 : reg n25 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb25, runBlock_reg _ _ _ (20 : Fin 32) s24.zero (by decide), g24_20]
  have g25_21 : reg n25 (21 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb25, runBlock_reg _ _ _ (21 : Fin 32) s24.zero (by decide), g24_21]
  have g25_22 : reg n25 (22 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb25, runBlock_reg _ _ _ (22 : Fin 32) s24.zero (by decide), g24_22]
  have g25_23 : reg n25 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1500 := by
    rw [rb25, runBlock_reg _ _ _ (23 : Fin 32) s24.zero (by decide), g24_23]
  have g25_24 : reg n25 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb25, runBlock_reg _ _ _ (24 : Fin 32) s24.zero (by decide), g24_24]
  have g25_25 : reg n25 (25 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb25, runBlock_reg _ _ _ (25 : Fin 32) s24.zero (by decide), g24_25]
  have g25_26 : reg n25 (26 : Fin 32) = x26 := by
    rw [rb25, runBlock_reg _ _ _ (26 : Fin 32) s24.zero (by decide), g24_26]
  have g25_27 : reg n25 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb25, runBlock_reg _ _ _ (27 : Fin 32) s24.zero (by decide), g24_27]
  have g25_10 : reg n25 a0 = B + 0x21A0 + BitVec.ofNat 32 0x600 := by
    rw [rb25]; simp +decide only [runBlock, BInstr.run, svEcT1a16b2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_9, g24_18, g24_19, g24_20, g24_21, g24_22, g24_23, g24_24, g24_25, g24_26, g24_27, s24.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g25_11 : reg n25 a1 = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb25]; simp +decide only [runBlock, BInstr.run, svEcT1a16b2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_9, g24_18, g24_19, g24_20, g24_21, g24_22, g24_23, g24_24, g24_25, g24_26, g24_27, s24.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g25_12 : reg n25 a2 = BitVec.ofNat 32 0x60 := by
    rw [rb25]; simp +decide only [runBlock, BInstr.run, svEcT1a16b2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_9, g24_18, g24_19, g24_20, g24_21, g24_22, g24_23, g24_24, g24_25, g24_26, g24_27, s24.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk25 : SvKeepL B n0.mem n25.mem [(0x1380, 0x80), (0x420, 0x60), (0x480, 0x60), (0x4E0, 0x60), (0x540, 0x60), (0x5A0, 0x60)] := by rw [m25]; exact keep_kk24
  clear keep_kk24
  have w25_24 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m25]; exact w24_24
  have w25_28 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m25]; exact w24_28
  have w25_2c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m25]; exact w24_2c
  have w25_30 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m25]; exact w24_30
  have w25_34 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m25]; exact w24_34
  have w25_38 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m25]; exact w24_38
  have w25_3c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m25]; exact w24_3c
  have w25_40 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m25]; exact w24_40
  have w25_44 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m25]; exact w24_44
  have w25_48 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m25]; exact w24_48
  have w25_4c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m25]; exact w24_4c
  have w25_50 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m25]; exact w24_50
  have w25_54 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m25]; exact w24_54
  have w25_58 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m25]; exact w24_58
  have w25_5c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m25]; exact w24_5c
  have w25_60 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m25]; exact w24_60
  have w25_64 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m25]; exact w24_64
  have w25_68 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m25]; exact w24_68
  have w25_6c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m25]; exact w24_6c
  have w25_70 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m25]; exact w24_70
  have w25_78 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m25]; exact w24_78
  have w25_7c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m25]; exact w24_7c
  have w25_80 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m25]; exact w24_80
  have w25_84 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m25]; exact w24_84
  have w25_88 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m25]; exact w24_88
  have w25_8c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m25]; exact w24_8c
  have w25_90 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m25]; exact w24_90
  have w25_94 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m25]; exact w24_94
  have w25_98 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m25]; exact w24_98
  have w25_9c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m25]; exact w24_9c
  have w25_a0 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m25]; exact w24_a0
  have w25_a4 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m25]; exact w24_a4
  have w25_a8 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m25]; exact w24_a8
  have w25_ac : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m25]; exact w24_ac
  have w25_b0 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m25]; exact w24_b0
  have w25_b4 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m25]; exact w24_b4
  have w25_b8 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m25]; exact w24_b8
  have w25_bc : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m25]; exact w24_bc
  have w25_c0 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m25]; exact w24_c0
  have w25_c4 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m25]; exact w24_c4
  have w25_c8 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m25]; exact w24_c8
  have w25_cc : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m25]; exact w24_cc
  have w25_d0 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m25]; exact w24_d0
  have w25_d4 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m25]; exact w24_d4
  have w25_d8 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m25]; exact w24_d8
  have w25_dc : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m25]; exact w24_dc
  have w25_e0 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m25]; exact w24_e0
  have w25_e4 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m25]; exact w24_e4
  have w25_e8 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m25]; exact w24_e8
  have w25_ec : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m25]; exact w24_ec
  have w25_f0 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m25]; exact w24_f0
  have w25_f4 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m25]; exact w24_f4
  have w25_f8 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m25]; exact w24_f8
  have w25_fc : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m25]; exact w24_fc
  have w25_100 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m25]; exact w24_100
  have w25_104 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m25]; exact w24_104
  have w25_108 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m25]; exact w24_108
  have w25_10c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m25]; exact w24_10c
  have w25_110 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m25]; exact w24_110
  have w25_114 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m25]; exact w24_114
  have w25_118 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m25]; exact w24_118
  have w25_11c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m25]; exact w24_11c
  have w25_120 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m25]; exact w24_120
  have w25_124 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m25]; exact w24_124
  have w25_128 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m25]; exact w24_128
  have w25_12c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m25]; exact w24_12c
  have w25_130 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m25]; exact w24_130
  have b25_a40 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = gs := by rw [m25]; exact b24_a40
  have b25_1040 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = gs := by rw [m25]; exact b24_1040
  have b25_14a0 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := by rw [m25]; exact b24_14a0
  have q25_420 : ∀ j, j < 96 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m25]; exact q24_420 j hj
  have q25_480 : ∀ j, j < 96 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0x480 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m25]; exact q24_480 j hj
  have q25_4e0 : ∀ j, j < 96 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0x4E0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m25]; exact q24_4e0 j hj
  have q25_540 : ∀ j, j < 96 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0x540 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m25]; exact q24_540 j hj
  have q25_5a0 : ∀ j, j < 96 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0x5A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m25]; exact q24_5a0 j hj
  have a25_240 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m25]; exact a24_240
  have a25_260 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m25]; exact a24_260
  have a25_280 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m25]; exact a24_280
  have a25_2a0 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m25]; exact a24_2a0
  have a25_2c0 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m25]; exact a24_2c0
  have a25_2e0 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m25]; exact a24_2e0
  have a25_380 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m25]; exact a24_380
  have a25_400 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m25]; exact a24_400
  have a25_13e0 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U2 := by rw [m25]; exact a24_13e0
  have a25_14e0 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x14E0) 8 = U1 := by rw [m25]; exact a24_14e0
  have a25_1560 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1560) 8 = U2 := by rw [m25]; exact a24_1560
  have p25_320 : ptF n25.mem B 0x320 = P0 := by rw [m25]; exact p24_320
  have p25_3a0 : ptF n25.mem B 0x3A0 = P1 := by rw [m25]; exact p24_3a0
  have p25_600 : ptF n25.mem B 0x600 = tbl2 P0 5 := by rw [m25]; exact p24_600
  have p25_660 : ptF n25.mem B 0x660 = tbl2 P0 6 := by rw [m25]; exact p24_660
  have p25_6c0 : ptF n25.mem B 0x6C0 = tbl2 P0 7 := by rw [m25]; exact p24_6c0
  have p25_a20 : ptF n25.mem B 0xA20 = tbl2 P0 0 := by rw [m25]; exact p24_a20
  have p25_a80 : ptF n25.mem B 0xA80 = tbl2 P0 1 := by rw [m25]; exact p24_a80
  have p25_ae0 : ptF n25.mem B 0xAE0 = tbl2 P0 2 := by rw [m25]; exact p24_ae0
  have p25_b40 : ptF n25.mem B 0xB40 = tbl2 P0 3 := by rw [m25]; exact p24_b40
  have p25_ba0 : ptF n25.mem B 0xBA0 = tbl2 P0 4 := by rw [m25]; exact p24_ba0
  have p25_c00 : ptF n25.mem B 0xC00 = tbl2 P0 5 := by rw [m25]; exact p24_c00
  have p25_c60 : ptF n25.mem B 0xC60 = tbl2 P0 6 := by rw [m25]; exact p24_c60
  have p25_cc0 : ptF n25.mem B 0xCC0 = tbl2 P0 7 := by rw [m25]; exact p24_cc0
  have p25_1020 : ptF n25.mem B 0x1020 = tbl2 P0 0 := by rw [m25]; exact p24_1020
  have p25_1080 : ptF n25.mem B 0x1080 = tbl2 P0 1 := by rw [m25]; exact p24_1080
  have p25_10e0 : ptF n25.mem B 0x10E0 = tbl2 P0 2 := by rw [m25]; exact p24_10e0
  have p25_1140 : ptF n25.mem B 0x1140 = tbl2 P0 3 := by rw [m25]; exact p24_1140
  have p25_11a0 : ptF n25.mem B 0x11A0 = tbl2 P0 4 := by rw [m25]; exact p24_11a0
  have p25_1200 : ptF n25.mem B 0x1200 = tbl2 P0 5 := by rw [m25]; exact p24_1200
  have p25_1260 : ptF n25.mem B 0x1260 = tbl2 P0 6 := by rw [m25]; exact p24_1260
  have p25_12c0 : ptF n25.mem B 0x12C0 = tbl2 P0 7 := by rw [m25]; exact p24_12c0
  have p25_1320 : ptF n25.mem B 0x1320 = ptDbl2 P0 := by rw [m25]; exact p24_1320
  have p25_1380 : ptF n25.mem B 0x1380 = P1 := by rw [m25]; exact p24_1380
  have p25_1480 : ptF n25.mem B 0x1480 = P0 := by rw [m25]; exact p24_1480
  have p25_1500 : ptF n25.mem B 0x1500 = P1 := by rw [m25]; exact p24_1500
  clear p24_1500 p24_1480 p24_1380 p24_1320 p24_12c0 p24_1260 p24_1200 p24_11a0 p24_1140 p24_10e0 p24_1080 p24_1020 p24_cc0 p24_c60 p24_c00 p24_ba0 p24_b40 p24_ae0 p24_a80 p24_a20 p24_6c0 p24_660 p24_600 p24_3a0 p24_320 a24_1560 a24_14e0 a24_13e0 a24_400 a24_380 a24_2e0 a24_2c0 a24_2a0 a24_280 a24_260 a24_240 q24_5a0 q24_540 q24_4e0 q24_480 q24_420 b24_14a0 b24_1040 b24_a40 w24_130 w24_12c w24_128 w24_124 w24_120 w24_11c w24_118 w24_114 w24_110 w24_10c w24_108 w24_104 w24_100 w24_fc w24_f8 w24_f4 w24_f0 w24_ec w24_e8 w24_e4 w24_e0 w24_dc w24_d8 w24_d4 w24_d0 w24_cc w24_c8 w24_c4 w24_c0 w24_bc w24_b8 w24_b4 w24_b0 w24_ac w24_a8 w24_a4 w24_a0 w24_9c w24_98 w24_94 w24_90 w24_8c w24_88 w24_84 w24_80 w24_7c w24_78 w24_70 w24_6c w24_68 w24_64 w24_60 w24_5c w24_58 w24_54 w24_50 w24_4c w24_48 w24_44 w24_40 w24_3c w24_38 w24_34 w24_30 w24_2c w24_28 w24_24 g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 m24 s24 u24 d24
  -- 0x16BA: memcpy from outside the stack
  obtain ⟨n26, P26, K26, X26⟩ := sv_mcRo2 (c := 0x600) (N := 0x60) F RS E25 s25 sv_at_16ba sv_at_16be
    (by decide) (by decide) g25_2 g25_10 g25_11 g25_12 (by decide) (Or.inr ⟨by decide, by decide⟩)
  have s26 := P26.st
  have fr26 := P26.fr
  have t26 : Steps n0 n26 := t25.trans P26.steps
  have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
  have E26 : SvCode n26.mem := E25.fr F fr26
  have V26 : SvSaves B n26.mem v := V25.keep K26 (by decide)
  have g26_2 : reg n26 sp = B + 0x21A0 := by rw [P26.regs sp (by decide), g25_2]
  have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P26.regs (3 : Fin 32) (by decide), g25_3]
  have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P26.regs (4 : Fin 32) (by decide), g25_4]
  have g26_8 : reg n26 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x600 := by rw [P26.regs (8 : Fin 32) (by decide), g25_8]
  have g26_9 : reg n26 (9 : Fin 32) = BitVec.ofNat 32 0x3 := by rw [P26.regs (9 : Fin 32) (by decide), g25_9]
  have g26_18 : reg n26 (18 : Fin 32) = out := by rw [P26.regs (18 : Fin 32) (by decide), g25_18]
  have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [P26.regs (19 : Fin 32) (by decide), g25_19]
  have g26_20 : reg n26 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P26.regs (20 : Fin 32) (by decide), g25_20]
  have g26_21 : reg n26 (21 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P26.regs (21 : Fin 32) (by decide), g25_21]
  have g26_22 : reg n26 (22 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [P26.regs (22 : Fin 32) (by decide), g25_22]
  have g26_23 : reg n26 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1500 := by rw [P26.regs (23 : Fin 32) (by decide), g25_23]
  have g26_24 : reg n26 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P26.regs (24 : Fin 32) (by decide), g25_24]
  have g26_25 : reg n26 (25 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [P26.regs (25 : Fin 32) (by decide), g25_25]
  have g26_26 : reg n26 (26 : Fin 32) = x26 := by rw [P26.regs (26 : Fin 32) (by decide), g25_26]
  have g26_27 : reg n26 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P26.regs (27 : Fin 32) (by decide), g25_27]
  have keep_kk26 : SvKeepL B n0.mem n26.mem [(0x1380, 0x80), (0x420, 0x60), (0x480, 0x60), (0x4E0, 0x60), (0x540, 0x60), (0x5A0, 0x60), (0x600, 0x60)] := keep_kk25.trans K26.toL
  clear keep_kk25
  have w26_24 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K26.w32 (by decide) (by decide)).trans w25_24
  have w26_28 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K26.w32 (by decide) (by decide)).trans w25_28
  have w26_2c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K26.w32 (by decide) (by decide)).trans w25_2c
  have w26_30 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K26.w32 (by decide) (by decide)).trans w25_30
  have w26_34 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K26.w32 (by decide) (by decide)).trans w25_34
  have w26_38 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K26.w32 (by decide) (by decide)).trans w25_38
  have w26_3c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K26.w32 (by decide) (by decide)).trans w25_3c
  have w26_40 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K26.w32 (by decide) (by decide)).trans w25_40
  have w26_44 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K26.w32 (by decide) (by decide)).trans w25_44
  have w26_48 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K26.w32 (by decide) (by decide)).trans w25_48
  have w26_4c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K26.w32 (by decide) (by decide)).trans w25_4c
  have w26_50 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K26.w32 (by decide) (by decide)).trans w25_50
  have w26_54 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K26.w32 (by decide) (by decide)).trans w25_54
  have w26_58 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K26.w32 (by decide) (by decide)).trans w25_58
  have w26_5c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K26.w32 (by decide) (by decide)).trans w25_5c
  have w26_60 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K26.w32 (by decide) (by decide)).trans w25_60
  have w26_64 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K26.w32 (by decide) (by decide)).trans w25_64
  have w26_68 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K26.w32 (by decide) (by decide)).trans w25_68
  have w26_6c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K26.w32 (by decide) (by decide)).trans w25_6c
  have w26_70 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K26.w32 (by decide) (by decide)).trans w25_70
  have w26_78 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := (K26.w32 (by decide) (by decide)).trans w25_78
  have w26_7c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K26.w32 (by decide) (by decide)).trans w25_7c
  have w26_80 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K26.w32 (by decide) (by decide)).trans w25_80
  have w26_84 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K26.w32 (by decide) (by decide)).trans w25_84
  have w26_88 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K26.w32 (by decide) (by decide)).trans w25_88
  have w26_8c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K26.w32 (by decide) (by decide)).trans w25_8c
  have w26_90 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K26.w32 (by decide) (by decide)).trans w25_90
  have w26_94 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K26.w32 (by decide) (by decide)).trans w25_94
  have w26_98 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K26.w32 (by decide) (by decide)).trans w25_98
  have w26_9c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K26.w32 (by decide) (by decide)).trans w25_9c
  have w26_a0 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K26.w32 (by decide) (by decide)).trans w25_a0
  have w26_a4 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K26.w32 (by decide) (by decide)).trans w25_a4
  have w26_a8 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K26.w32 (by decide) (by decide)).trans w25_a8
  have w26_ac : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K26.w32 (by decide) (by decide)).trans w25_ac
  have w26_b0 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K26.w32 (by decide) (by decide)).trans w25_b0
  have w26_b4 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K26.w32 (by decide) (by decide)).trans w25_b4
  have w26_b8 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K26.w32 (by decide) (by decide)).trans w25_b8
  have w26_bc : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K26.w32 (by decide) (by decide)).trans w25_bc
  have w26_c0 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K26.w32 (by decide) (by decide)).trans w25_c0
  have w26_c4 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K26.w32 (by decide) (by decide)).trans w25_c4
  have w26_c8 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K26.w32 (by decide) (by decide)).trans w25_c8
  have w26_cc : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K26.w32 (by decide) (by decide)).trans w25_cc
  have w26_d0 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K26.w32 (by decide) (by decide)).trans w25_d0
  have w26_d4 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K26.w32 (by decide) (by decide)).trans w25_d4
  have w26_d8 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K26.w32 (by decide) (by decide)).trans w25_d8
  have w26_dc : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K26.w32 (by decide) (by decide)).trans w25_dc
  have w26_e0 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K26.w32 (by decide) (by decide)).trans w25_e0
  have w26_e4 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K26.w32 (by decide) (by decide)).trans w25_e4
  have w26_e8 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K26.w32 (by decide) (by decide)).trans w25_e8
  have w26_ec : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K26.w32 (by decide) (by decide)).trans w25_ec
  have w26_f0 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K26.w32 (by decide) (by decide)).trans w25_f0
  have w26_f4 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K26.w32 (by decide) (by decide)).trans w25_f4
  have w26_f8 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K26.w32 (by decide) (by decide)).trans w25_f8
  have w26_fc : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K26.w32 (by decide) (by decide)).trans w25_fc
  have w26_100 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K26.w32 (by decide) (by decide)).trans w25_100
  have w26_104 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K26.w32 (by decide) (by decide)).trans w25_104
  have w26_108 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K26.w32 (by decide) (by decide)).trans w25_108
  have w26_10c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K26.w32 (by decide) (by decide)).trans w25_10c
  have w26_110 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K26.w32 (by decide) (by decide)).trans w25_110
  have w26_114 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K26.w32 (by decide) (by decide)).trans w25_114
  have w26_118 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K26.w32 (by decide) (by decide)).trans w25_118
  have w26_11c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K26.w32 (by decide) (by decide)).trans w25_11c
  have w26_120 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K26.w32 (by decide) (by decide)).trans w25_120
  have w26_124 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K26.w32 (by decide) (by decide)).trans w25_124
  have w26_128 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K26.w32 (by decide) (by decide)).trans w25_128
  have w26_12c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K26.w32 (by decide) (by decide)).trans w25_12c
  have w26_130 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K26.w32 (by decide) (by decide)).trans w25_130
  have b26_a40 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = gs := (K26.b8 (by decide) (by decide)).trans b25_a40
  have b26_1040 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = gs := (K26.b8 (by decide) (by decide)).trans b25_1040
  have b26_14a0 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := (K26.b8 (by decide) (by decide)).trans b25_14a0
  have q26_420 : ∀ j, j < 96 → n26.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K26.range (by decide) (by decide) j hj).trans (q25_420 j hj)
  have q26_480 : ∀ j, j < 96 → n26.mem (B + 0x21A0 + BitVec.ofNat 32 (0x480 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K26.range (by decide) (by decide) j hj).trans (q25_480 j hj)
  have q26_4e0 : ∀ j, j < 96 → n26.mem (B + 0x21A0 + BitVec.ofNat 32 (0x4E0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K26.range (by decide) (by decide) j hj).trans (q25_4e0 j hj)
  have q26_540 : ∀ j, j < 96 → n26.mem (B + 0x21A0 + BitVec.ofNat 32 (0x540 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K26.range (by decide) (by decide) j hj).trans (q25_540 j hj)
  have q26_5a0 : ∀ j, j < 96 → n26.mem (B + 0x21A0 + BitVec.ofNat 32 (0x5A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K26.range (by decide) (by decide) j hj).trans (q25_5a0 j hj)
  have a26_240 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := (K26.acc (by decide) (by decide)).trans a25_240
  have a26_260 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := (K26.acc (by decide) (by decide)).trans a25_260
  have a26_280 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := (K26.acc (by decide) (by decide)).trans a25_280
  have a26_2a0 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K26.acc (by decide) (by decide)).trans a25_2a0
  have a26_2c0 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K26.acc (by decide) (by decide)).trans a25_2c0
  have a26_2e0 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K26.acc (by decide) (by decide)).trans a25_2e0
  have a26_380 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := (K26.acc (by decide) (by decide)).trans a25_380
  have a26_400 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := (K26.acc (by decide) (by decide)).trans a25_400
  have a26_13e0 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U2 := (K26.acc (by decide) (by decide)).trans a25_13e0
  have a26_14e0 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x14E0) 8 = U1 := (K26.acc (by decide) (by decide)).trans a25_14e0
  have a26_1560 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1560) 8 = U2 := (K26.acc (by decide) (by decide)).trans a25_1560
  have p26_320 : ptF n26.mem B 0x320 = P0 := (K26.pt (by decide) (by decide)).trans p25_320
  have p26_3a0 : ptF n26.mem B 0x3A0 = P1 := (K26.pt (by decide) (by decide)).trans p25_3a0
  have p26_660 : ptF n26.mem B 0x660 = tbl2 P0 6 := (K26.pt (by decide) (by decide)).trans p25_660
  have p26_6c0 : ptF n26.mem B 0x6C0 = tbl2 P0 7 := (K26.pt (by decide) (by decide)).trans p25_6c0
  have p26_a20 : ptF n26.mem B 0xA20 = tbl2 P0 0 := (K26.pt (by decide) (by decide)).trans p25_a20
  have p26_a80 : ptF n26.mem B 0xA80 = tbl2 P0 1 := (K26.pt (by decide) (by decide)).trans p25_a80
  have p26_ae0 : ptF n26.mem B 0xAE0 = tbl2 P0 2 := (K26.pt (by decide) (by decide)).trans p25_ae0
  have p26_b40 : ptF n26.mem B 0xB40 = tbl2 P0 3 := (K26.pt (by decide) (by decide)).trans p25_b40
  have p26_ba0 : ptF n26.mem B 0xBA0 = tbl2 P0 4 := (K26.pt (by decide) (by decide)).trans p25_ba0
  have p26_c00 : ptF n26.mem B 0xC00 = tbl2 P0 5 := (K26.pt (by decide) (by decide)).trans p25_c00
  have p26_c60 : ptF n26.mem B 0xC60 = tbl2 P0 6 := (K26.pt (by decide) (by decide)).trans p25_c60
  have p26_cc0 : ptF n26.mem B 0xCC0 = tbl2 P0 7 := (K26.pt (by decide) (by decide)).trans p25_cc0
  have p26_1020 : ptF n26.mem B 0x1020 = tbl2 P0 0 := (K26.pt (by decide) (by decide)).trans p25_1020
  have p26_1080 : ptF n26.mem B 0x1080 = tbl2 P0 1 := (K26.pt (by decide) (by decide)).trans p25_1080
  have p26_10e0 : ptF n26.mem B 0x10E0 = tbl2 P0 2 := (K26.pt (by decide) (by decide)).trans p25_10e0
  have p26_1140 : ptF n26.mem B 0x1140 = tbl2 P0 3 := (K26.pt (by decide) (by decide)).trans p25_1140
  have p26_11a0 : ptF n26.mem B 0x11A0 = tbl2 P0 4 := (K26.pt (by decide) (by decide)).trans p25_11a0
  have p26_1200 : ptF n26.mem B 0x1200 = tbl2 P0 5 := (K26.pt (by decide) (by decide)).trans p25_1200
  have p26_1260 : ptF n26.mem B 0x1260 = tbl2 P0 6 := (K26.pt (by decide) (by decide)).trans p25_1260
  have p26_12c0 : ptF n26.mem B 0x12C0 = tbl2 P0 7 := (K26.pt (by decide) (by decide)).trans p25_12c0
  have p26_1320 : ptF n26.mem B 0x1320 = ptDbl2 P0 := (K26.pt (by decide) (by decide)).trans p25_1320
  have p26_1380 : ptF n26.mem B 0x1380 = P1 := (K26.pt (by decide) (by decide)).trans p25_1380
  have p26_1480 : ptF n26.mem B 0x1480 = P0 := (K26.pt (by decide) (by decide)).trans p25_1480
  have p26_1500 : ptF n26.mem B 0x1500 = P1 := (K26.pt (by decide) (by decide)).trans p25_1500
  have q26_600 : ∀ j, j < 96 → n26.mem (B + 0x21A0 + BitVec.ofNat 32 (0x600 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) :=
    fun j hj => (X26 j hj).trans (fR25 _ (SvRo2.r RS (Or.inr ⟨by decide, by decide⟩) hj))
  clear p25_1500 p25_1480 p25_1380 p25_1320 p25_12c0 p25_1260 p25_1200 p25_11a0 p25_1140 p25_10e0 p25_1080 p25_1020 p25_cc0 p25_c60 p25_c00 p25_ba0 p25_b40 p25_ae0 p25_a80 p25_a20 p25_6c0 p25_660 p25_600 p25_3a0 p25_320 a25_1560 a25_14e0 a25_13e0 a25_400 a25_380 a25_2e0 a25_2c0 a25_2a0 a25_280 a25_260 a25_240 q25_5a0 q25_540 q25_4e0 q25_480 q25_420 b25_14a0 b25_1040 b25_a40 w25_130 w25_12c w25_128 w25_124 w25_120 w25_11c w25_118 w25_114 w25_110 w25_10c w25_108 w25_104 w25_100 w25_fc w25_f8 w25_f4 w25_f0 w25_ec w25_e8 w25_e4 w25_e0 w25_dc w25_d8 w25_d4 w25_d0 w25_cc w25_c8 w25_c4 w25_c0 w25_bc w25_b8 w25_b4 w25_b0 w25_ac w25_a8 w25_a4 w25_a0 w25_9c w25_98 w25_94 w25_90 w25_8c w25_88 w25_84 w25_80 w25_7c w25_78 w25_70 w25_6c w25_68 w25_64 w25_60 w25_5c w25_58 w25_54 w25_50 w25_4c w25_48 w25_44 w25_40 w25_3c w25_38 w25_34 w25_30 w25_2c w25_28 w25_24 g25_12 g25_11 g25_10 g25_27 g25_26 g25_25 g25_24 g25_23 g25_22 g25_21 g25_20 g25_19 g25_18 g25_9 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 fr25 rb25 s25 m25 u25 c25
  -- 0x16C2
  obtain ⟨n27, c27, u27⟩ := s26.block svEcT1a16c2 E26.self svEcT1a16c2_end
    ⟨trivial, trivial, trivial⟩
  have m27 : n27.mem = n26.mem := u27.mem
  have s27 : St n27.mem SV n27 0x16C8 (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
  have rb27 : ∀ q, reg n27 q = (runBlock svEcT1a16c2 (n26.mem, reg n26)).2 q := fun q => by rw [u27.regs]
  have fr27 : ∀ x, SvR B x → n27.mem x = n26.mem x := fun x _ => by rw [m27]
  have t27 : Steps n0 n27 := t26.trans c27
  have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
  have E27 : SvCode n27.mem := E26.fr F fr27
  have V27 : SvSaves B n27.mem v := V26.same m27
  have g27_2 : reg n27 sp = B + 0x21A0 := by
    rw [rb27, runBlock_reg _ _ _ sp s26.zero (by decide), g26_2]
  have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb27, runBlock_reg _ _ _ (3 : Fin 32) s26.zero (by decide), g26_3]
  have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb27, runBlock_reg _ _ _ (4 : Fin 32) s26.zero (by decide), g26_4]
  have g27_18 : reg n27 (18 : Fin 32) = out := by
    rw [rb27, runBlock_reg _ _ _ (18 : Fin 32) s26.zero (by decide), g26_18]
  have g27_19 : reg n27 (19 : Fin 32) = bp := by
    rw [rb27, runBlock_reg _ _ _ (19 : Fin 32) s26.zero (by decide), g26_19]
  have g27_20 : reg n27 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb27, runBlock_reg _ _ _ (20 : Fin 32) s26.zero (by decide), g26_20]
  have g27_21 : reg n27 (21 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb27, runBlock_reg _ _ _ (21 : Fin 32) s26.zero (by decide), g26_21]
  have g27_22 : reg n27 (22 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb27, runBlock_reg _ _ _ (22 : Fin 32) s26.zero (by decide), g26_22]
  have g27_23 : reg n27 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1500 := by
    rw [rb27, runBlock_reg _ _ _ (23 : Fin 32) s26.zero (by decide), g26_23]
  have g27_24 : reg n27 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb27, runBlock_reg _ _ _ (24 : Fin 32) s26.zero (by decide), g26_24]
  have g27_25 : reg n27 (25 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb27, runBlock_reg _ _ _ (25 : Fin 32) s26.zero (by decide), g26_25]
  have g27_26 : reg n27 (26 : Fin 32) = x26 := by
    rw [rb27, runBlock_reg _ _ _ (26 : Fin 32) s26.zero (by decide), g26_26]
  have g27_27 : reg n27 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb27, runBlock_reg _ _ _ (27 : Fin 32) s26.zero (by decide), g26_27]
  have g27_8 : reg n27 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x660 := by
    rw [rb27]; simp +decide only [runBlock, BInstr.run, svEcT1a16c2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g26_2, g26_3, g26_4, g26_8, g26_9, g26_18, g26_19, g26_20, g26_21, g26_22, g26_23, g26_24, g26_25, g26_26, g26_27, s26.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g27_9 : reg n27 (9 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb27]; simp +decide only [runBlock, BInstr.run, svEcT1a16c2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g26_2, g26_3, g26_4, g26_8, g26_9, g26_18, g26_19, g26_20, g26_21, g26_22, g26_23, g26_24, g26_25, g26_26, g26_27, s26.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk27 : SvKeepL B n0.mem n27.mem [(0x1380, 0x80), (0x420, 0x60), (0x480, 0x60), (0x4E0, 0x60), (0x540, 0x60), (0x5A0, 0x60), (0x600, 0x60)] := by rw [m27]; exact keep_kk26
  clear keep_kk26
  have w27_24 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m27]; exact w26_24
  have w27_28 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m27]; exact w26_28
  have w27_2c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m27]; exact w26_2c
  have w27_30 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m27]; exact w26_30
  have w27_34 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m27]; exact w26_34
  have w27_38 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m27]; exact w26_38
  have w27_3c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m27]; exact w26_3c
  have w27_40 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m27]; exact w26_40
  have w27_44 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m27]; exact w26_44
  have w27_48 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m27]; exact w26_48
  have w27_4c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m27]; exact w26_4c
  have w27_50 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m27]; exact w26_50
  have w27_54 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m27]; exact w26_54
  have w27_58 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m27]; exact w26_58
  have w27_5c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m27]; exact w26_5c
  have w27_60 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m27]; exact w26_60
  have w27_64 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m27]; exact w26_64
  have w27_68 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m27]; exact w26_68
  have w27_6c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m27]; exact w26_6c
  have w27_70 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m27]; exact w26_70
  have w27_78 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m27]; exact w26_78
  have w27_7c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m27]; exact w26_7c
  have w27_80 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m27]; exact w26_80
  have w27_84 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m27]; exact w26_84
  have w27_88 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m27]; exact w26_88
  have w27_8c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m27]; exact w26_8c
  have w27_90 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m27]; exact w26_90
  have w27_94 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m27]; exact w26_94
  have w27_98 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m27]; exact w26_98
  have w27_9c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m27]; exact w26_9c
  have w27_a0 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m27]; exact w26_a0
  have w27_a4 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m27]; exact w26_a4
  have w27_a8 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m27]; exact w26_a8
  have w27_ac : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m27]; exact w26_ac
  have w27_b0 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m27]; exact w26_b0
  have w27_b4 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m27]; exact w26_b4
  have w27_b8 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m27]; exact w26_b8
  have w27_bc : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m27]; exact w26_bc
  have w27_c0 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m27]; exact w26_c0
  have w27_c4 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m27]; exact w26_c4
  have w27_c8 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m27]; exact w26_c8
  have w27_cc : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m27]; exact w26_cc
  have w27_d0 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m27]; exact w26_d0
  have w27_d4 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m27]; exact w26_d4
  have w27_d8 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m27]; exact w26_d8
  have w27_dc : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m27]; exact w26_dc
  have w27_e0 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m27]; exact w26_e0
  have w27_e4 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m27]; exact w26_e4
  have w27_e8 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m27]; exact w26_e8
  have w27_ec : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m27]; exact w26_ec
  have w27_f0 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m27]; exact w26_f0
  have w27_f4 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m27]; exact w26_f4
  have w27_f8 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m27]; exact w26_f8
  have w27_fc : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m27]; exact w26_fc
  have w27_100 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m27]; exact w26_100
  have w27_104 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m27]; exact w26_104
  have w27_108 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m27]; exact w26_108
  have w27_10c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m27]; exact w26_10c
  have w27_110 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m27]; exact w26_110
  have w27_114 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m27]; exact w26_114
  have w27_118 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m27]; exact w26_118
  have w27_11c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m27]; exact w26_11c
  have w27_120 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m27]; exact w26_120
  have w27_124 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m27]; exact w26_124
  have w27_128 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m27]; exact w26_128
  have w27_12c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m27]; exact w26_12c
  have w27_130 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m27]; exact w26_130
  have b27_a40 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = gs := by rw [m27]; exact b26_a40
  have b27_1040 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = gs := by rw [m27]; exact b26_1040
  have b27_14a0 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := by rw [m27]; exact b26_14a0
  have q27_420 : ∀ j, j < 96 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m27]; exact q26_420 j hj
  have q27_480 : ∀ j, j < 96 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0x480 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m27]; exact q26_480 j hj
  have q27_4e0 : ∀ j, j < 96 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0x4E0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m27]; exact q26_4e0 j hj
  have q27_540 : ∀ j, j < 96 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0x540 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m27]; exact q26_540 j hj
  have q27_5a0 : ∀ j, j < 96 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0x5A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m27]; exact q26_5a0 j hj
  have q27_600 : ∀ j, j < 96 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0x600 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m27]; exact q26_600 j hj
  have a27_240 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m27]; exact a26_240
  have a27_260 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m27]; exact a26_260
  have a27_280 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m27]; exact a26_280
  have a27_2a0 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m27]; exact a26_2a0
  have a27_2c0 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m27]; exact a26_2c0
  have a27_2e0 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m27]; exact a26_2e0
  have a27_380 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m27]; exact a26_380
  have a27_400 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m27]; exact a26_400
  have a27_13e0 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U2 := by rw [m27]; exact a26_13e0
  have a27_14e0 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x14E0) 8 = U1 := by rw [m27]; exact a26_14e0
  have a27_1560 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1560) 8 = U2 := by rw [m27]; exact a26_1560
  have p27_320 : ptF n27.mem B 0x320 = P0 := by rw [m27]; exact p26_320
  have p27_3a0 : ptF n27.mem B 0x3A0 = P1 := by rw [m27]; exact p26_3a0
  have p27_660 : ptF n27.mem B 0x660 = tbl2 P0 6 := by rw [m27]; exact p26_660
  have p27_6c0 : ptF n27.mem B 0x6C0 = tbl2 P0 7 := by rw [m27]; exact p26_6c0
  have p27_a20 : ptF n27.mem B 0xA20 = tbl2 P0 0 := by rw [m27]; exact p26_a20
  have p27_a80 : ptF n27.mem B 0xA80 = tbl2 P0 1 := by rw [m27]; exact p26_a80
  have p27_ae0 : ptF n27.mem B 0xAE0 = tbl2 P0 2 := by rw [m27]; exact p26_ae0
  have p27_b40 : ptF n27.mem B 0xB40 = tbl2 P0 3 := by rw [m27]; exact p26_b40
  have p27_ba0 : ptF n27.mem B 0xBA0 = tbl2 P0 4 := by rw [m27]; exact p26_ba0
  have p27_c00 : ptF n27.mem B 0xC00 = tbl2 P0 5 := by rw [m27]; exact p26_c00
  have p27_c60 : ptF n27.mem B 0xC60 = tbl2 P0 6 := by rw [m27]; exact p26_c60
  have p27_cc0 : ptF n27.mem B 0xCC0 = tbl2 P0 7 := by rw [m27]; exact p26_cc0
  have p27_1020 : ptF n27.mem B 0x1020 = tbl2 P0 0 := by rw [m27]; exact p26_1020
  have p27_1080 : ptF n27.mem B 0x1080 = tbl2 P0 1 := by rw [m27]; exact p26_1080
  have p27_10e0 : ptF n27.mem B 0x10E0 = tbl2 P0 2 := by rw [m27]; exact p26_10e0
  have p27_1140 : ptF n27.mem B 0x1140 = tbl2 P0 3 := by rw [m27]; exact p26_1140
  have p27_11a0 : ptF n27.mem B 0x11A0 = tbl2 P0 4 := by rw [m27]; exact p26_11a0
  have p27_1200 : ptF n27.mem B 0x1200 = tbl2 P0 5 := by rw [m27]; exact p26_1200
  have p27_1260 : ptF n27.mem B 0x1260 = tbl2 P0 6 := by rw [m27]; exact p26_1260
  have p27_12c0 : ptF n27.mem B 0x12C0 = tbl2 P0 7 := by rw [m27]; exact p26_12c0
  have p27_1320 : ptF n27.mem B 0x1320 = ptDbl2 P0 := by rw [m27]; exact p26_1320
  have p27_1380 : ptF n27.mem B 0x1380 = P1 := by rw [m27]; exact p26_1380
  have p27_1480 : ptF n27.mem B 0x1480 = P0 := by rw [m27]; exact p26_1480
  have p27_1500 : ptF n27.mem B 0x1500 = P1 := by rw [m27]; exact p26_1500
  clear q26_600 p26_1500 p26_1480 p26_1380 p26_1320 p26_12c0 p26_1260 p26_1200 p26_11a0 p26_1140 p26_10e0 p26_1080 p26_1020 p26_cc0 p26_c60 p26_c00 p26_ba0 p26_b40 p26_ae0 p26_a80 p26_a20 p26_6c0 p26_660 p26_3a0 p26_320 a26_1560 a26_14e0 a26_13e0 a26_400 a26_380 a26_2e0 a26_2c0 a26_2a0 a26_280 a26_260 a26_240 q26_5a0 q26_540 q26_4e0 q26_480 q26_420 b26_14a0 b26_1040 b26_a40 w26_130 w26_12c w26_128 w26_124 w26_120 w26_11c w26_118 w26_114 w26_110 w26_10c w26_108 w26_104 w26_100 w26_fc w26_f8 w26_f4 w26_f0 w26_ec w26_e8 w26_e4 w26_e0 w26_dc w26_d8 w26_d4 w26_d0 w26_cc w26_c8 w26_c4 w26_c0 w26_bc w26_b8 w26_b4 w26_b0 w26_ac w26_a8 w26_a4 w26_a0 w26_9c w26_98 w26_94 w26_90 w26_8c w26_88 w26_84 w26_80 w26_7c w26_78 w26_70 w26_6c w26_68 w26_64 w26_60 w26_5c w26_58 w26_54 w26_50 w26_4c w26_48 w26_44 w26_40 w26_3c w26_38 w26_34 w26_30 w26_2c w26_28 w26_24 g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 s26 X26 K26 P26
  -- 0x16C8: branch, taken
  obtain ⟨n28, d28, u28⟩ := s27.taken E27.self 0x16B2 sv_at_16c8
    (by decide) (by rw [g27_9, s27.zero]; decide)
  have s28 : St n28.mem SV n28 0x16B2 (reg n28) := ⟨u28.pc, rfl, fun _ => rfl⟩
  have m28 : n28.mem = n27.mem := u28.mem
  have fr28 : ∀ x, SvR B x → n28.mem x = n27.mem x := fun x _ => by rw [m28]
  have t28 : Steps n0 n28 := t27.trans (.single d28)
  have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
  have E28 : SvCode n28.mem := E27.fr F fr28
  have V28 : SvSaves B n28.mem v := V27.same m28
  have g28_2 : reg n28 sp = B + 0x21A0 := by rw [u28.regs, g27_2]
  have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u28.regs, g27_3]
  have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u28.regs, g27_4]
  have g28_8 : reg n28 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x660 := by rw [u28.regs, g27_8]
  have g28_9 : reg n28 (9 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u28.regs, g27_9]
  have g28_18 : reg n28 (18 : Fin 32) = out := by rw [u28.regs, g27_18]
  have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [u28.regs, g27_19]
  have g28_20 : reg n28 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u28.regs, g27_20]
  have g28_21 : reg n28 (21 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u28.regs, g27_21]
  have g28_22 : reg n28 (22 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [u28.regs, g27_22]
  have g28_23 : reg n28 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1500 := by rw [u28.regs, g27_23]
  have g28_24 : reg n28 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u28.regs, g27_24]
  have g28_25 : reg n28 (25 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [u28.regs, g27_25]
  have g28_26 : reg n28 (26 : Fin 32) = x26 := by rw [u28.regs, g27_26]
  have g28_27 : reg n28 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u28.regs, g27_27]
  have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x1380, 0x80), (0x420, 0x60), (0x480, 0x60), (0x4E0, 0x60), (0x540, 0x60), (0x5A0, 0x60), (0x600, 0x60)] := by rw [m28]; exact keep_kk27
  clear keep_kk27
  have w28_24 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m28]; exact w27_24
  have w28_28 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m28]; exact w27_28
  have w28_2c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m28]; exact w27_2c
  have w28_30 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m28]; exact w27_30
  have w28_34 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m28]; exact w27_34
  have w28_38 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m28]; exact w27_38
  have w28_3c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m28]; exact w27_3c
  have w28_40 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m28]; exact w27_40
  have w28_44 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m28]; exact w27_44
  have w28_48 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m28]; exact w27_48
  have w28_4c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m28]; exact w27_4c
  have w28_50 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m28]; exact w27_50
  have w28_54 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m28]; exact w27_54
  have w28_58 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m28]; exact w27_58
  have w28_5c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m28]; exact w27_5c
  have w28_60 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m28]; exact w27_60
  have w28_64 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m28]; exact w27_64
  have w28_68 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m28]; exact w27_68
  have w28_6c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m28]; exact w27_6c
  have w28_70 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m28]; exact w27_70
  have w28_78 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m28]; exact w27_78
  have w28_7c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m28]; exact w27_7c
  have w28_80 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m28]; exact w27_80
  have w28_84 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m28]; exact w27_84
  have w28_88 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m28]; exact w27_88
  have w28_8c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m28]; exact w27_8c
  have w28_90 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m28]; exact w27_90
  have w28_94 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m28]; exact w27_94
  have w28_98 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m28]; exact w27_98
  have w28_9c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m28]; exact w27_9c
  have w28_a0 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m28]; exact w27_a0
  have w28_a4 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m28]; exact w27_a4
  have w28_a8 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m28]; exact w27_a8
  have w28_ac : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m28]; exact w27_ac
  have w28_b0 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m28]; exact w27_b0
  have w28_b4 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m28]; exact w27_b4
  have w28_b8 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m28]; exact w27_b8
  have w28_bc : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m28]; exact w27_bc
  have w28_c0 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m28]; exact w27_c0
  have w28_c4 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m28]; exact w27_c4
  have w28_c8 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m28]; exact w27_c8
  have w28_cc : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m28]; exact w27_cc
  have w28_d0 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m28]; exact w27_d0
  have w28_d4 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m28]; exact w27_d4
  have w28_d8 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m28]; exact w27_d8
  have w28_dc : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m28]; exact w27_dc
  have w28_e0 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m28]; exact w27_e0
  have w28_e4 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m28]; exact w27_e4
  have w28_e8 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m28]; exact w27_e8
  have w28_ec : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m28]; exact w27_ec
  have w28_f0 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m28]; exact w27_f0
  have w28_f4 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m28]; exact w27_f4
  have w28_f8 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m28]; exact w27_f8
  have w28_fc : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m28]; exact w27_fc
  have w28_100 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m28]; exact w27_100
  have w28_104 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m28]; exact w27_104
  have w28_108 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m28]; exact w27_108
  have w28_10c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m28]; exact w27_10c
  have w28_110 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m28]; exact w27_110
  have w28_114 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m28]; exact w27_114
  have w28_118 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m28]; exact w27_118
  have w28_11c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m28]; exact w27_11c
  have w28_120 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m28]; exact w27_120
  have w28_124 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m28]; exact w27_124
  have w28_128 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m28]; exact w27_128
  have w28_12c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m28]; exact w27_12c
  have w28_130 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m28]; exact w27_130
  have b28_a40 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = gs := by rw [m28]; exact b27_a40
  have b28_1040 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = gs := by rw [m28]; exact b27_1040
  have b28_14a0 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := by rw [m28]; exact b27_14a0
  have q28_420 : ∀ j, j < 96 → n28.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m28]; exact q27_420 j hj
  have q28_480 : ∀ j, j < 96 → n28.mem (B + 0x21A0 + BitVec.ofNat 32 (0x480 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m28]; exact q27_480 j hj
  have q28_4e0 : ∀ j, j < 96 → n28.mem (B + 0x21A0 + BitVec.ofNat 32 (0x4E0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m28]; exact q27_4e0 j hj
  have q28_540 : ∀ j, j < 96 → n28.mem (B + 0x21A0 + BitVec.ofNat 32 (0x540 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m28]; exact q27_540 j hj
  have q28_5a0 : ∀ j, j < 96 → n28.mem (B + 0x21A0 + BitVec.ofNat 32 (0x5A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m28]; exact q27_5a0 j hj
  have q28_600 : ∀ j, j < 96 → n28.mem (B + 0x21A0 + BitVec.ofNat 32 (0x600 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m28]; exact q27_600 j hj
  have a28_240 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m28]; exact a27_240
  have a28_260 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m28]; exact a27_260
  have a28_280 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m28]; exact a27_280
  have a28_2a0 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m28]; exact a27_2a0
  have a28_2c0 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m28]; exact a27_2c0
  have a28_2e0 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m28]; exact a27_2e0
  have a28_380 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m28]; exact a27_380
  have a28_400 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m28]; exact a27_400
  have a28_13e0 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U2 := by rw [m28]; exact a27_13e0
  have a28_14e0 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x14E0) 8 = U1 := by rw [m28]; exact a27_14e0
  have a28_1560 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1560) 8 = U2 := by rw [m28]; exact a27_1560
  have p28_320 : ptF n28.mem B 0x320 = P0 := by rw [m28]; exact p27_320
  have p28_3a0 : ptF n28.mem B 0x3A0 = P1 := by rw [m28]; exact p27_3a0
  have p28_660 : ptF n28.mem B 0x660 = tbl2 P0 6 := by rw [m28]; exact p27_660
  have p28_6c0 : ptF n28.mem B 0x6C0 = tbl2 P0 7 := by rw [m28]; exact p27_6c0
  have p28_a20 : ptF n28.mem B 0xA20 = tbl2 P0 0 := by rw [m28]; exact p27_a20
  have p28_a80 : ptF n28.mem B 0xA80 = tbl2 P0 1 := by rw [m28]; exact p27_a80
  have p28_ae0 : ptF n28.mem B 0xAE0 = tbl2 P0 2 := by rw [m28]; exact p27_ae0
  have p28_b40 : ptF n28.mem B 0xB40 = tbl2 P0 3 := by rw [m28]; exact p27_b40
  have p28_ba0 : ptF n28.mem B 0xBA0 = tbl2 P0 4 := by rw [m28]; exact p27_ba0
  have p28_c00 : ptF n28.mem B 0xC00 = tbl2 P0 5 := by rw [m28]; exact p27_c00
  have p28_c60 : ptF n28.mem B 0xC60 = tbl2 P0 6 := by rw [m28]; exact p27_c60
  have p28_cc0 : ptF n28.mem B 0xCC0 = tbl2 P0 7 := by rw [m28]; exact p27_cc0
  have p28_1020 : ptF n28.mem B 0x1020 = tbl2 P0 0 := by rw [m28]; exact p27_1020
  have p28_1080 : ptF n28.mem B 0x1080 = tbl2 P0 1 := by rw [m28]; exact p27_1080
  have p28_10e0 : ptF n28.mem B 0x10E0 = tbl2 P0 2 := by rw [m28]; exact p27_10e0
  have p28_1140 : ptF n28.mem B 0x1140 = tbl2 P0 3 := by rw [m28]; exact p27_1140
  have p28_11a0 : ptF n28.mem B 0x11A0 = tbl2 P0 4 := by rw [m28]; exact p27_11a0
  have p28_1200 : ptF n28.mem B 0x1200 = tbl2 P0 5 := by rw [m28]; exact p27_1200
  have p28_1260 : ptF n28.mem B 0x1260 = tbl2 P0 6 := by rw [m28]; exact p27_1260
  have p28_12c0 : ptF n28.mem B 0x12C0 = tbl2 P0 7 := by rw [m28]; exact p27_12c0
  have p28_1320 : ptF n28.mem B 0x1320 = ptDbl2 P0 := by rw [m28]; exact p27_1320
  have p28_1380 : ptF n28.mem B 0x1380 = P1 := by rw [m28]; exact p27_1380
  have p28_1480 : ptF n28.mem B 0x1480 = P0 := by rw [m28]; exact p27_1480
  have p28_1500 : ptF n28.mem B 0x1500 = P1 := by rw [m28]; exact p27_1500
  clear p27_1500 p27_1480 p27_1380 p27_1320 p27_12c0 p27_1260 p27_1200 p27_11a0 p27_1140 p27_10e0 p27_1080 p27_1020 p27_cc0 p27_c60 p27_c00 p27_ba0 p27_b40 p27_ae0 p27_a80 p27_a20 p27_6c0 p27_660 p27_3a0 p27_320 a27_1560 a27_14e0 a27_13e0 a27_400 a27_380 a27_2e0 a27_2c0 a27_2a0 a27_280 a27_260 a27_240 q27_600 q27_5a0 q27_540 q27_4e0 q27_480 q27_420 b27_14a0 b27_1040 b27_a40 w27_130 w27_12c w27_128 w27_124 w27_120 w27_11c w27_118 w27_114 w27_110 w27_10c w27_108 w27_104 w27_100 w27_fc w27_f8 w27_f4 w27_f0 w27_ec w27_e8 w27_e4 w27_e0 w27_dc w27_d8 w27_d4 w27_d0 w27_cc w27_c8 w27_c4 w27_c0 w27_bc w27_b8 w27_b4 w27_b0 w27_ac w27_a8 w27_a4 w27_a0 w27_9c w27_98 w27_94 w27_90 w27_8c w27_88 w27_84 w27_80 w27_7c w27_78 w27_70 w27_6c w27_68 w27_64 w27_60 w27_5c w27_58 w27_54 w27_50 w27_4c w27_48 w27_44 w27_40 w27_3c w27_38 w27_34 w27_30 w27_2c w27_28 w27_24 g27_9 g27_8 g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 rb27 s27 m27 u27 c27
  -- 0x16B2
  obtain ⟨n29, c29, u29⟩ := s28.block svEcT1a16b2 E28.self svEcT1a16b2_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m29 : n29.mem = n28.mem := u29.mem
  have s29 : St n29.mem SV n29 0x16BA (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
  have rb29 : ∀ q, reg n29 q = (runBlock svEcT1a16b2 (n28.mem, reg n28)).2 q := fun q => by rw [u29.regs]
  have fr29 : ∀ x, SvR B x → n29.mem x = n28.mem x := fun x _ => by rw [m29]
  have t29 : Steps n0 n29 := t28.trans c29
  have fR29 : ∀ x, SvR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
  have E29 : SvCode n29.mem := E28.fr F fr29
  have V29 : SvSaves B n29.mem v := V28.same m29
  have g29_2 : reg n29 sp = B + 0x21A0 := by
    rw [rb29, runBlock_reg _ _ _ sp s28.zero (by decide), g28_2]
  have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb29, runBlock_reg _ _ _ (3 : Fin 32) s28.zero (by decide), g28_3]
  have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb29, runBlock_reg _ _ _ (4 : Fin 32) s28.zero (by decide), g28_4]
  have g29_8 : reg n29 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x660 := by
    rw [rb29, runBlock_reg _ _ _ (8 : Fin 32) s28.zero (by decide), g28_8]
  have g29_9 : reg n29 (9 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb29, runBlock_reg _ _ _ (9 : Fin 32) s28.zero (by decide), g28_9]
  have g29_18 : reg n29 (18 : Fin 32) = out := by
    rw [rb29, runBlock_reg _ _ _ (18 : Fin 32) s28.zero (by decide), g28_18]
  have g29_19 : reg n29 (19 : Fin 32) = bp := by
    rw [rb29, runBlock_reg _ _ _ (19 : Fin 32) s28.zero (by decide), g28_19]
  have g29_20 : reg n29 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb29, runBlock_reg _ _ _ (20 : Fin 32) s28.zero (by decide), g28_20]
  have g29_21 : reg n29 (21 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb29, runBlock_reg _ _ _ (21 : Fin 32) s28.zero (by decide), g28_21]
  have g29_22 : reg n29 (22 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb29, runBlock_reg _ _ _ (22 : Fin 32) s28.zero (by decide), g28_22]
  have g29_23 : reg n29 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1500 := by
    rw [rb29, runBlock_reg _ _ _ (23 : Fin 32) s28.zero (by decide), g28_23]
  have g29_24 : reg n29 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb29, runBlock_reg _ _ _ (24 : Fin 32) s28.zero (by decide), g28_24]
  have g29_25 : reg n29 (25 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb29, runBlock_reg _ _ _ (25 : Fin 32) s28.zero (by decide), g28_25]
  have g29_26 : reg n29 (26 : Fin 32) = x26 := by
    rw [rb29, runBlock_reg _ _ _ (26 : Fin 32) s28.zero (by decide), g28_26]
  have g29_27 : reg n29 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb29, runBlock_reg _ _ _ (27 : Fin 32) s28.zero (by decide), g28_27]
  have g29_10 : reg n29 a0 = B + 0x21A0 + BitVec.ofNat 32 0x660 := by
    rw [rb29]; simp +decide only [runBlock, BInstr.run, svEcT1a16b2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g28_2, g28_3, g28_4, g28_8, g28_9, g28_18, g28_19, g28_20, g28_21, g28_22, g28_23, g28_24, g28_25, g28_26, g28_27, s28.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g29_11 : reg n29 a1 = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb29]; simp +decide only [runBlock, BInstr.run, svEcT1a16b2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g28_2, g28_3, g28_4, g28_8, g28_9, g28_18, g28_19, g28_20, g28_21, g28_22, g28_23, g28_24, g28_25, g28_26, g28_27, s28.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g29_12 : reg n29 a2 = BitVec.ofNat 32 0x60 := by
    rw [rb29]; simp +decide only [runBlock, BInstr.run, svEcT1a16b2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g28_2, g28_3, g28_4, g28_8, g28_9, g28_18, g28_19, g28_20, g28_21, g28_22, g28_23, g28_24, g28_25, g28_26, g28_27, s28.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x1380, 0x80), (0x420, 0x60), (0x480, 0x60), (0x4E0, 0x60), (0x540, 0x60), (0x5A0, 0x60), (0x600, 0x60)] := by rw [m29]; exact keep_kk28
  clear keep_kk28
  have w29_24 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m29]; exact w28_24
  have w29_28 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m29]; exact w28_28
  have w29_2c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m29]; exact w28_2c
  have w29_30 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m29]; exact w28_30
  have w29_34 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m29]; exact w28_34
  have w29_38 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m29]; exact w28_38
  have w29_3c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m29]; exact w28_3c
  have w29_40 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m29]; exact w28_40
  have w29_44 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m29]; exact w28_44
  have w29_48 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m29]; exact w28_48
  have w29_4c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m29]; exact w28_4c
  have w29_50 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m29]; exact w28_50
  have w29_54 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m29]; exact w28_54
  have w29_58 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m29]; exact w28_58
  have w29_5c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m29]; exact w28_5c
  have w29_60 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m29]; exact w28_60
  have w29_64 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m29]; exact w28_64
  have w29_68 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m29]; exact w28_68
  have w29_6c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m29]; exact w28_6c
  have w29_70 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m29]; exact w28_70
  have w29_78 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m29]; exact w28_78
  have w29_7c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m29]; exact w28_7c
  have w29_80 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m29]; exact w28_80
  have w29_84 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m29]; exact w28_84
  have w29_88 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m29]; exact w28_88
  have w29_8c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m29]; exact w28_8c
  have w29_90 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m29]; exact w28_90
  have w29_94 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m29]; exact w28_94
  have w29_98 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m29]; exact w28_98
  have w29_9c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m29]; exact w28_9c
  have w29_a0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m29]; exact w28_a0
  have w29_a4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m29]; exact w28_a4
  have w29_a8 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m29]; exact w28_a8
  have w29_ac : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m29]; exact w28_ac
  have w29_b0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m29]; exact w28_b0
  have w29_b4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m29]; exact w28_b4
  have w29_b8 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m29]; exact w28_b8
  have w29_bc : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m29]; exact w28_bc
  have w29_c0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m29]; exact w28_c0
  have w29_c4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m29]; exact w28_c4
  have w29_c8 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m29]; exact w28_c8
  have w29_cc : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m29]; exact w28_cc
  have w29_d0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m29]; exact w28_d0
  have w29_d4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m29]; exact w28_d4
  have w29_d8 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m29]; exact w28_d8
  have w29_dc : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m29]; exact w28_dc
  have w29_e0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m29]; exact w28_e0
  have w29_e4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m29]; exact w28_e4
  have w29_e8 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m29]; exact w28_e8
  have w29_ec : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m29]; exact w28_ec
  have w29_f0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m29]; exact w28_f0
  have w29_f4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m29]; exact w28_f4
  have w29_f8 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m29]; exact w28_f8
  have w29_fc : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m29]; exact w28_fc
  have w29_100 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m29]; exact w28_100
  have w29_104 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m29]; exact w28_104
  have w29_108 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m29]; exact w28_108
  have w29_10c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m29]; exact w28_10c
  have w29_110 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m29]; exact w28_110
  have w29_114 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m29]; exact w28_114
  have w29_118 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m29]; exact w28_118
  have w29_11c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m29]; exact w28_11c
  have w29_120 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m29]; exact w28_120
  have w29_124 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m29]; exact w28_124
  have w29_128 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m29]; exact w28_128
  have w29_12c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m29]; exact w28_12c
  have w29_130 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m29]; exact w28_130
  have b29_a40 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = gs := by rw [m29]; exact b28_a40
  have b29_1040 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = gs := by rw [m29]; exact b28_1040
  have b29_14a0 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := by rw [m29]; exact b28_14a0
  have q29_420 : ∀ j, j < 96 → n29.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m29]; exact q28_420 j hj
  have q29_480 : ∀ j, j < 96 → n29.mem (B + 0x21A0 + BitVec.ofNat 32 (0x480 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m29]; exact q28_480 j hj
  have q29_4e0 : ∀ j, j < 96 → n29.mem (B + 0x21A0 + BitVec.ofNat 32 (0x4E0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m29]; exact q28_4e0 j hj
  have q29_540 : ∀ j, j < 96 → n29.mem (B + 0x21A0 + BitVec.ofNat 32 (0x540 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m29]; exact q28_540 j hj
  have q29_5a0 : ∀ j, j < 96 → n29.mem (B + 0x21A0 + BitVec.ofNat 32 (0x5A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m29]; exact q28_5a0 j hj
  have q29_600 : ∀ j, j < 96 → n29.mem (B + 0x21A0 + BitVec.ofNat 32 (0x600 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m29]; exact q28_600 j hj
  have a29_240 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m29]; exact a28_240
  have a29_260 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m29]; exact a28_260
  have a29_280 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m29]; exact a28_280
  have a29_2a0 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m29]; exact a28_2a0
  have a29_2c0 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m29]; exact a28_2c0
  have a29_2e0 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m29]; exact a28_2e0
  have a29_380 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m29]; exact a28_380
  have a29_400 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m29]; exact a28_400
  have a29_13e0 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U2 := by rw [m29]; exact a28_13e0
  have a29_14e0 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x14E0) 8 = U1 := by rw [m29]; exact a28_14e0
  have a29_1560 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1560) 8 = U2 := by rw [m29]; exact a28_1560
  have p29_320 : ptF n29.mem B 0x320 = P0 := by rw [m29]; exact p28_320
  have p29_3a0 : ptF n29.mem B 0x3A0 = P1 := by rw [m29]; exact p28_3a0
  have p29_660 : ptF n29.mem B 0x660 = tbl2 P0 6 := by rw [m29]; exact p28_660
  have p29_6c0 : ptF n29.mem B 0x6C0 = tbl2 P0 7 := by rw [m29]; exact p28_6c0
  have p29_a20 : ptF n29.mem B 0xA20 = tbl2 P0 0 := by rw [m29]; exact p28_a20
  have p29_a80 : ptF n29.mem B 0xA80 = tbl2 P0 1 := by rw [m29]; exact p28_a80
  have p29_ae0 : ptF n29.mem B 0xAE0 = tbl2 P0 2 := by rw [m29]; exact p28_ae0
  have p29_b40 : ptF n29.mem B 0xB40 = tbl2 P0 3 := by rw [m29]; exact p28_b40
  have p29_ba0 : ptF n29.mem B 0xBA0 = tbl2 P0 4 := by rw [m29]; exact p28_ba0
  have p29_c00 : ptF n29.mem B 0xC00 = tbl2 P0 5 := by rw [m29]; exact p28_c00
  have p29_c60 : ptF n29.mem B 0xC60 = tbl2 P0 6 := by rw [m29]; exact p28_c60
  have p29_cc0 : ptF n29.mem B 0xCC0 = tbl2 P0 7 := by rw [m29]; exact p28_cc0
  have p29_1020 : ptF n29.mem B 0x1020 = tbl2 P0 0 := by rw [m29]; exact p28_1020
  have p29_1080 : ptF n29.mem B 0x1080 = tbl2 P0 1 := by rw [m29]; exact p28_1080
  have p29_10e0 : ptF n29.mem B 0x10E0 = tbl2 P0 2 := by rw [m29]; exact p28_10e0
  have p29_1140 : ptF n29.mem B 0x1140 = tbl2 P0 3 := by rw [m29]; exact p28_1140
  have p29_11a0 : ptF n29.mem B 0x11A0 = tbl2 P0 4 := by rw [m29]; exact p28_11a0
  have p29_1200 : ptF n29.mem B 0x1200 = tbl2 P0 5 := by rw [m29]; exact p28_1200
  have p29_1260 : ptF n29.mem B 0x1260 = tbl2 P0 6 := by rw [m29]; exact p28_1260
  have p29_12c0 : ptF n29.mem B 0x12C0 = tbl2 P0 7 := by rw [m29]; exact p28_12c0
  have p29_1320 : ptF n29.mem B 0x1320 = ptDbl2 P0 := by rw [m29]; exact p28_1320
  have p29_1380 : ptF n29.mem B 0x1380 = P1 := by rw [m29]; exact p28_1380
  have p29_1480 : ptF n29.mem B 0x1480 = P0 := by rw [m29]; exact p28_1480
  have p29_1500 : ptF n29.mem B 0x1500 = P1 := by rw [m29]; exact p28_1500
  clear p28_1500 p28_1480 p28_1380 p28_1320 p28_12c0 p28_1260 p28_1200 p28_11a0 p28_1140 p28_10e0 p28_1080 p28_1020 p28_cc0 p28_c60 p28_c00 p28_ba0 p28_b40 p28_ae0 p28_a80 p28_a20 p28_6c0 p28_660 p28_3a0 p28_320 a28_1560 a28_14e0 a28_13e0 a28_400 a28_380 a28_2e0 a28_2c0 a28_2a0 a28_280 a28_260 a28_240 q28_600 q28_5a0 q28_540 q28_4e0 q28_480 q28_420 b28_14a0 b28_1040 b28_a40 w28_130 w28_12c w28_128 w28_124 w28_120 w28_11c w28_118 w28_114 w28_110 w28_10c w28_108 w28_104 w28_100 w28_fc w28_f8 w28_f4 w28_f0 w28_ec w28_e8 w28_e4 w28_e0 w28_dc w28_d8 w28_d4 w28_d0 w28_cc w28_c8 w28_c4 w28_c0 w28_bc w28_b8 w28_b4 w28_b0 w28_ac w28_a8 w28_a4 w28_a0 w28_9c w28_98 w28_94 w28_90 w28_8c w28_88 w28_84 w28_80 w28_7c w28_78 w28_70 w28_6c w28_68 w28_64 w28_60 w28_5c w28_58 w28_54 w28_50 w28_4c w28_48 w28_44 w28_40 w28_3c w28_38 w28_34 w28_30 w28_2c w28_28 w28_24 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 m28 s28 u28 d28
  -- 0x16BA: memcpy from outside the stack
  obtain ⟨n30, P30, K30, X30⟩ := sv_mcRo2 (c := 0x660) (N := 0x60) F RS E29 s29 sv_at_16ba sv_at_16be
    (by decide) (by decide) g29_2 g29_10 g29_11 g29_12 (by decide) (Or.inr ⟨by decide, by decide⟩)
  have s30 := P30.st
  have fr30 := P30.fr
  have t30 : Steps n0 n30 := t29.trans P30.steps
  have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
  have E30 : SvCode n30.mem := E29.fr F fr30
  have V30 : SvSaves B n30.mem v := V29.keep K30 (by decide)
  have g30_2 : reg n30 sp = B + 0x21A0 := by rw [P30.regs sp (by decide), g29_2]
  have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P30.regs (3 : Fin 32) (by decide), g29_3]
  have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P30.regs (4 : Fin 32) (by decide), g29_4]
  have g30_8 : reg n30 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x660 := by rw [P30.regs (8 : Fin 32) (by decide), g29_8]
  have g30_9 : reg n30 (9 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P30.regs (9 : Fin 32) (by decide), g29_9]
  have g30_18 : reg n30 (18 : Fin 32) = out := by rw [P30.regs (18 : Fin 32) (by decide), g29_18]
  have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [P30.regs (19 : Fin 32) (by decide), g29_19]
  have g30_20 : reg n30 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P30.regs (20 : Fin 32) (by decide), g29_20]
  have g30_21 : reg n30 (21 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P30.regs (21 : Fin 32) (by decide), g29_21]
  have g30_22 : reg n30 (22 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [P30.regs (22 : Fin 32) (by decide), g29_22]
  have g30_23 : reg n30 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1500 := by rw [P30.regs (23 : Fin 32) (by decide), g29_23]
  have g30_24 : reg n30 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P30.regs (24 : Fin 32) (by decide), g29_24]
  have g30_25 : reg n30 (25 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [P30.regs (25 : Fin 32) (by decide), g29_25]
  have g30_26 : reg n30 (26 : Fin 32) = x26 := by rw [P30.regs (26 : Fin 32) (by decide), g29_26]
  have g30_27 : reg n30 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P30.regs (27 : Fin 32) (by decide), g29_27]
  have keep_kk30 : SvKeepL B n0.mem n30.mem [(0x1380, 0x80), (0x420, 0x60), (0x480, 0x60), (0x4E0, 0x60), (0x540, 0x60), (0x5A0, 0x60), (0x600, 0x60), (0x660, 0x60)] := keep_kk29.trans K30.toL
  clear keep_kk29
  have w30_24 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K30.w32 (by decide) (by decide)).trans w29_24
  have w30_28 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K30.w32 (by decide) (by decide)).trans w29_28
  have w30_2c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K30.w32 (by decide) (by decide)).trans w29_2c
  have w30_30 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K30.w32 (by decide) (by decide)).trans w29_30
  have w30_34 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K30.w32 (by decide) (by decide)).trans w29_34
  have w30_38 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K30.w32 (by decide) (by decide)).trans w29_38
  have w30_3c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K30.w32 (by decide) (by decide)).trans w29_3c
  have w30_40 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K30.w32 (by decide) (by decide)).trans w29_40
  have w30_44 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K30.w32 (by decide) (by decide)).trans w29_44
  have w30_48 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K30.w32 (by decide) (by decide)).trans w29_48
  have w30_4c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K30.w32 (by decide) (by decide)).trans w29_4c
  have w30_50 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K30.w32 (by decide) (by decide)).trans w29_50
  have w30_54 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K30.w32 (by decide) (by decide)).trans w29_54
  have w30_58 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K30.w32 (by decide) (by decide)).trans w29_58
  have w30_5c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K30.w32 (by decide) (by decide)).trans w29_5c
  have w30_60 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K30.w32 (by decide) (by decide)).trans w29_60
  have w30_64 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K30.w32 (by decide) (by decide)).trans w29_64
  have w30_68 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K30.w32 (by decide) (by decide)).trans w29_68
  have w30_6c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K30.w32 (by decide) (by decide)).trans w29_6c
  have w30_70 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K30.w32 (by decide) (by decide)).trans w29_70
  have w30_78 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := (K30.w32 (by decide) (by decide)).trans w29_78
  have w30_7c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K30.w32 (by decide) (by decide)).trans w29_7c
  have w30_80 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K30.w32 (by decide) (by decide)).trans w29_80
  have w30_84 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K30.w32 (by decide) (by decide)).trans w29_84
  have w30_88 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K30.w32 (by decide) (by decide)).trans w29_88
  have w30_8c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K30.w32 (by decide) (by decide)).trans w29_8c
  have w30_90 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K30.w32 (by decide) (by decide)).trans w29_90
  have w30_94 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K30.w32 (by decide) (by decide)).trans w29_94
  have w30_98 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K30.w32 (by decide) (by decide)).trans w29_98
  have w30_9c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K30.w32 (by decide) (by decide)).trans w29_9c
  have w30_a0 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K30.w32 (by decide) (by decide)).trans w29_a0
  have w30_a4 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K30.w32 (by decide) (by decide)).trans w29_a4
  have w30_a8 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K30.w32 (by decide) (by decide)).trans w29_a8
  have w30_ac : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K30.w32 (by decide) (by decide)).trans w29_ac
  have w30_b0 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K30.w32 (by decide) (by decide)).trans w29_b0
  have w30_b4 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K30.w32 (by decide) (by decide)).trans w29_b4
  have w30_b8 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K30.w32 (by decide) (by decide)).trans w29_b8
  have w30_bc : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K30.w32 (by decide) (by decide)).trans w29_bc
  have w30_c0 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K30.w32 (by decide) (by decide)).trans w29_c0
  have w30_c4 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K30.w32 (by decide) (by decide)).trans w29_c4
  have w30_c8 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K30.w32 (by decide) (by decide)).trans w29_c8
  have w30_cc : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K30.w32 (by decide) (by decide)).trans w29_cc
  have w30_d0 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K30.w32 (by decide) (by decide)).trans w29_d0
  have w30_d4 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K30.w32 (by decide) (by decide)).trans w29_d4
  have w30_d8 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K30.w32 (by decide) (by decide)).trans w29_d8
  have w30_dc : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K30.w32 (by decide) (by decide)).trans w29_dc
  have w30_e0 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K30.w32 (by decide) (by decide)).trans w29_e0
  have w30_e4 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K30.w32 (by decide) (by decide)).trans w29_e4
  have w30_e8 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K30.w32 (by decide) (by decide)).trans w29_e8
  have w30_ec : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K30.w32 (by decide) (by decide)).trans w29_ec
  have w30_f0 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K30.w32 (by decide) (by decide)).trans w29_f0
  have w30_f4 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K30.w32 (by decide) (by decide)).trans w29_f4
  have w30_f8 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K30.w32 (by decide) (by decide)).trans w29_f8
  have w30_fc : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K30.w32 (by decide) (by decide)).trans w29_fc
  have w30_100 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K30.w32 (by decide) (by decide)).trans w29_100
  have w30_104 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K30.w32 (by decide) (by decide)).trans w29_104
  have w30_108 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K30.w32 (by decide) (by decide)).trans w29_108
  have w30_10c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K30.w32 (by decide) (by decide)).trans w29_10c
  have w30_110 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K30.w32 (by decide) (by decide)).trans w29_110
  have w30_114 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K30.w32 (by decide) (by decide)).trans w29_114
  have w30_118 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K30.w32 (by decide) (by decide)).trans w29_118
  have w30_11c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K30.w32 (by decide) (by decide)).trans w29_11c
  have w30_120 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K30.w32 (by decide) (by decide)).trans w29_120
  have w30_124 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K30.w32 (by decide) (by decide)).trans w29_124
  have w30_128 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K30.w32 (by decide) (by decide)).trans w29_128
  have w30_12c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K30.w32 (by decide) (by decide)).trans w29_12c
  have w30_130 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K30.w32 (by decide) (by decide)).trans w29_130
  have b30_a40 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = gs := (K30.b8 (by decide) (by decide)).trans b29_a40
  have b30_1040 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = gs := (K30.b8 (by decide) (by decide)).trans b29_1040
  have b30_14a0 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := (K30.b8 (by decide) (by decide)).trans b29_14a0
  have q30_420 : ∀ j, j < 96 → n30.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K30.range (by decide) (by decide) j hj).trans (q29_420 j hj)
  have q30_480 : ∀ j, j < 96 → n30.mem (B + 0x21A0 + BitVec.ofNat 32 (0x480 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K30.range (by decide) (by decide) j hj).trans (q29_480 j hj)
  have q30_4e0 : ∀ j, j < 96 → n30.mem (B + 0x21A0 + BitVec.ofNat 32 (0x4E0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K30.range (by decide) (by decide) j hj).trans (q29_4e0 j hj)
  have q30_540 : ∀ j, j < 96 → n30.mem (B + 0x21A0 + BitVec.ofNat 32 (0x540 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K30.range (by decide) (by decide) j hj).trans (q29_540 j hj)
  have q30_5a0 : ∀ j, j < 96 → n30.mem (B + 0x21A0 + BitVec.ofNat 32 (0x5A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K30.range (by decide) (by decide) j hj).trans (q29_5a0 j hj)
  have q30_600 : ∀ j, j < 96 → n30.mem (B + 0x21A0 + BitVec.ofNat 32 (0x600 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K30.range (by decide) (by decide) j hj).trans (q29_600 j hj)
  have a30_240 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := (K30.acc (by decide) (by decide)).trans a29_240
  have a30_260 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := (K30.acc (by decide) (by decide)).trans a29_260
  have a30_280 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := (K30.acc (by decide) (by decide)).trans a29_280
  have a30_2a0 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K30.acc (by decide) (by decide)).trans a29_2a0
  have a30_2c0 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K30.acc (by decide) (by decide)).trans a29_2c0
  have a30_2e0 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K30.acc (by decide) (by decide)).trans a29_2e0
  have a30_380 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := (K30.acc (by decide) (by decide)).trans a29_380
  have a30_400 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := (K30.acc (by decide) (by decide)).trans a29_400
  have a30_13e0 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U2 := (K30.acc (by decide) (by decide)).trans a29_13e0
  have a30_14e0 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x14E0) 8 = U1 := (K30.acc (by decide) (by decide)).trans a29_14e0
  have a30_1560 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1560) 8 = U2 := (K30.acc (by decide) (by decide)).trans a29_1560
  have p30_320 : ptF n30.mem B 0x320 = P0 := (K30.pt (by decide) (by decide)).trans p29_320
  have p30_3a0 : ptF n30.mem B 0x3A0 = P1 := (K30.pt (by decide) (by decide)).trans p29_3a0
  have p30_6c0 : ptF n30.mem B 0x6C0 = tbl2 P0 7 := (K30.pt (by decide) (by decide)).trans p29_6c0
  have p30_a20 : ptF n30.mem B 0xA20 = tbl2 P0 0 := (K30.pt (by decide) (by decide)).trans p29_a20
  have p30_a80 : ptF n30.mem B 0xA80 = tbl2 P0 1 := (K30.pt (by decide) (by decide)).trans p29_a80
  have p30_ae0 : ptF n30.mem B 0xAE0 = tbl2 P0 2 := (K30.pt (by decide) (by decide)).trans p29_ae0
  have p30_b40 : ptF n30.mem B 0xB40 = tbl2 P0 3 := (K30.pt (by decide) (by decide)).trans p29_b40
  have p30_ba0 : ptF n30.mem B 0xBA0 = tbl2 P0 4 := (K30.pt (by decide) (by decide)).trans p29_ba0
  have p30_c00 : ptF n30.mem B 0xC00 = tbl2 P0 5 := (K30.pt (by decide) (by decide)).trans p29_c00
  have p30_c60 : ptF n30.mem B 0xC60 = tbl2 P0 6 := (K30.pt (by decide) (by decide)).trans p29_c60
  have p30_cc0 : ptF n30.mem B 0xCC0 = tbl2 P0 7 := (K30.pt (by decide) (by decide)).trans p29_cc0
  have p30_1020 : ptF n30.mem B 0x1020 = tbl2 P0 0 := (K30.pt (by decide) (by decide)).trans p29_1020
  have p30_1080 : ptF n30.mem B 0x1080 = tbl2 P0 1 := (K30.pt (by decide) (by decide)).trans p29_1080
  have p30_10e0 : ptF n30.mem B 0x10E0 = tbl2 P0 2 := (K30.pt (by decide) (by decide)).trans p29_10e0
  have p30_1140 : ptF n30.mem B 0x1140 = tbl2 P0 3 := (K30.pt (by decide) (by decide)).trans p29_1140
  have p30_11a0 : ptF n30.mem B 0x11A0 = tbl2 P0 4 := (K30.pt (by decide) (by decide)).trans p29_11a0
  have p30_1200 : ptF n30.mem B 0x1200 = tbl2 P0 5 := (K30.pt (by decide) (by decide)).trans p29_1200
  have p30_1260 : ptF n30.mem B 0x1260 = tbl2 P0 6 := (K30.pt (by decide) (by decide)).trans p29_1260
  have p30_12c0 : ptF n30.mem B 0x12C0 = tbl2 P0 7 := (K30.pt (by decide) (by decide)).trans p29_12c0
  have p30_1320 : ptF n30.mem B 0x1320 = ptDbl2 P0 := (K30.pt (by decide) (by decide)).trans p29_1320
  have p30_1380 : ptF n30.mem B 0x1380 = P1 := (K30.pt (by decide) (by decide)).trans p29_1380
  have p30_1480 : ptF n30.mem B 0x1480 = P0 := (K30.pt (by decide) (by decide)).trans p29_1480
  have p30_1500 : ptF n30.mem B 0x1500 = P1 := (K30.pt (by decide) (by decide)).trans p29_1500
  have q30_660 : ∀ j, j < 96 → n30.mem (B + 0x21A0 + BitVec.ofNat 32 (0x660 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) :=
    fun j hj => (X30 j hj).trans (fR29 _ (SvRo2.r RS (Or.inr ⟨by decide, by decide⟩) hj))
  clear p29_1500 p29_1480 p29_1380 p29_1320 p29_12c0 p29_1260 p29_1200 p29_11a0 p29_1140 p29_10e0 p29_1080 p29_1020 p29_cc0 p29_c60 p29_c00 p29_ba0 p29_b40 p29_ae0 p29_a80 p29_a20 p29_6c0 p29_660 p29_3a0 p29_320 a29_1560 a29_14e0 a29_13e0 a29_400 a29_380 a29_2e0 a29_2c0 a29_2a0 a29_280 a29_260 a29_240 q29_600 q29_5a0 q29_540 q29_4e0 q29_480 q29_420 b29_14a0 b29_1040 b29_a40 w29_130 w29_12c w29_128 w29_124 w29_120 w29_11c w29_118 w29_114 w29_110 w29_10c w29_108 w29_104 w29_100 w29_fc w29_f8 w29_f4 w29_f0 w29_ec w29_e8 w29_e4 w29_e0 w29_dc w29_d8 w29_d4 w29_d0 w29_cc w29_c8 w29_c4 w29_c0 w29_bc w29_b8 w29_b4 w29_b0 w29_ac w29_a8 w29_a4 w29_a0 w29_9c w29_98 w29_94 w29_90 w29_8c w29_88 w29_84 w29_80 w29_7c w29_78 w29_70 w29_6c w29_68 w29_64 w29_60 w29_5c w29_58 w29_54 w29_50 w29_4c w29_48 w29_44 w29_40 w29_3c w29_38 w29_34 w29_30 w29_2c w29_28 w29_24 g29_12 g29_11 g29_10 g29_27 g29_26 g29_25 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_9 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 rb29 s29 m29 u29 c29
  -- 0x16C2
  obtain ⟨n31, c31, u31⟩ := s30.block svEcT1a16c2 E30.self svEcT1a16c2_end
    ⟨trivial, trivial, trivial⟩
  have m31 : n31.mem = n30.mem := u31.mem
  have s31 : St n31.mem SV n31 0x16C8 (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
  have rb31 : ∀ q, reg n31 q = (runBlock svEcT1a16c2 (n30.mem, reg n30)).2 q := fun q => by rw [u31.regs]
  have fr31 : ∀ x, SvR B x → n31.mem x = n30.mem x := fun x _ => by rw [m31]
  have t31 : Steps n0 n31 := t30.trans c31
  have fR31 : ∀ x, SvR B x → n31.mem x = M0 x := fun x hx => (fr31 x hx).trans (fR30 x hx)
  have E31 : SvCode n31.mem := E30.fr F fr31
  have V31 : SvSaves B n31.mem v := V30.same m31
  have g31_2 : reg n31 sp = B + 0x21A0 := by
    rw [rb31, runBlock_reg _ _ _ sp s30.zero (by decide), g30_2]
  have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb31, runBlock_reg _ _ _ (3 : Fin 32) s30.zero (by decide), g30_3]
  have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb31, runBlock_reg _ _ _ (4 : Fin 32) s30.zero (by decide), g30_4]
  have g31_18 : reg n31 (18 : Fin 32) = out := by
    rw [rb31, runBlock_reg _ _ _ (18 : Fin 32) s30.zero (by decide), g30_18]
  have g31_19 : reg n31 (19 : Fin 32) = bp := by
    rw [rb31, runBlock_reg _ _ _ (19 : Fin 32) s30.zero (by decide), g30_19]
  have g31_20 : reg n31 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb31, runBlock_reg _ _ _ (20 : Fin 32) s30.zero (by decide), g30_20]
  have g31_21 : reg n31 (21 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb31, runBlock_reg _ _ _ (21 : Fin 32) s30.zero (by decide), g30_21]
  have g31_22 : reg n31 (22 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb31, runBlock_reg _ _ _ (22 : Fin 32) s30.zero (by decide), g30_22]
  have g31_23 : reg n31 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1500 := by
    rw [rb31, runBlock_reg _ _ _ (23 : Fin 32) s30.zero (by decide), g30_23]
  have g31_24 : reg n31 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb31, runBlock_reg _ _ _ (24 : Fin 32) s30.zero (by decide), g30_24]
  have g31_25 : reg n31 (25 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb31, runBlock_reg _ _ _ (25 : Fin 32) s30.zero (by decide), g30_25]
  have g31_26 : reg n31 (26 : Fin 32) = x26 := by
    rw [rb31, runBlock_reg _ _ _ (26 : Fin 32) s30.zero (by decide), g30_26]
  have g31_27 : reg n31 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb31, runBlock_reg _ _ _ (27 : Fin 32) s30.zero (by decide), g30_27]
  have g31_8 : reg n31 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x6C0 := by
    rw [rb31]; simp +decide only [runBlock, BInstr.run, svEcT1a16c2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g30_2, g30_3, g30_4, g30_8, g30_9, g30_18, g30_19, g30_20, g30_21, g30_22, g30_23, g30_24, g30_25, g30_26, g30_27, s30.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g31_9 : reg n31 (9 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb31]; simp +decide only [runBlock, BInstr.run, svEcT1a16c2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g30_2, g30_3, g30_4, g30_8, g30_9, g30_18, g30_19, g30_20, g30_21, g30_22, g30_23, g30_24, g30_25, g30_26, g30_27, s30.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk31 : SvKeepL B n0.mem n31.mem [(0x1380, 0x80), (0x420, 0x60), (0x480, 0x60), (0x4E0, 0x60), (0x540, 0x60), (0x5A0, 0x60), (0x600, 0x60), (0x660, 0x60)] := by rw [m31]; exact keep_kk30
  clear keep_kk30
  have w31_24 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m31]; exact w30_24
  have w31_28 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m31]; exact w30_28
  have w31_2c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m31]; exact w30_2c
  have w31_30 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m31]; exact w30_30
  have w31_34 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m31]; exact w30_34
  have w31_38 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m31]; exact w30_38
  have w31_3c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m31]; exact w30_3c
  have w31_40 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m31]; exact w30_40
  have w31_44 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m31]; exact w30_44
  have w31_48 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m31]; exact w30_48
  have w31_4c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m31]; exact w30_4c
  have w31_50 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m31]; exact w30_50
  have w31_54 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m31]; exact w30_54
  have w31_58 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m31]; exact w30_58
  have w31_5c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m31]; exact w30_5c
  have w31_60 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m31]; exact w30_60
  have w31_64 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m31]; exact w30_64
  have w31_68 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m31]; exact w30_68
  have w31_6c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m31]; exact w30_6c
  have w31_70 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m31]; exact w30_70
  have w31_78 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m31]; exact w30_78
  have w31_7c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m31]; exact w30_7c
  have w31_80 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m31]; exact w30_80
  have w31_84 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m31]; exact w30_84
  have w31_88 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m31]; exact w30_88
  have w31_8c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m31]; exact w30_8c
  have w31_90 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m31]; exact w30_90
  have w31_94 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m31]; exact w30_94
  have w31_98 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m31]; exact w30_98
  have w31_9c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m31]; exact w30_9c
  have w31_a0 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m31]; exact w30_a0
  have w31_a4 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m31]; exact w30_a4
  have w31_a8 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m31]; exact w30_a8
  have w31_ac : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m31]; exact w30_ac
  have w31_b0 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m31]; exact w30_b0
  have w31_b4 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m31]; exact w30_b4
  have w31_b8 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m31]; exact w30_b8
  have w31_bc : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m31]; exact w30_bc
  have w31_c0 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m31]; exact w30_c0
  have w31_c4 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m31]; exact w30_c4
  have w31_c8 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m31]; exact w30_c8
  have w31_cc : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m31]; exact w30_cc
  have w31_d0 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m31]; exact w30_d0
  have w31_d4 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m31]; exact w30_d4
  have w31_d8 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m31]; exact w30_d8
  have w31_dc : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m31]; exact w30_dc
  have w31_e0 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m31]; exact w30_e0
  have w31_e4 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m31]; exact w30_e4
  have w31_e8 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m31]; exact w30_e8
  have w31_ec : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m31]; exact w30_ec
  have w31_f0 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m31]; exact w30_f0
  have w31_f4 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m31]; exact w30_f4
  have w31_f8 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m31]; exact w30_f8
  have w31_fc : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m31]; exact w30_fc
  have w31_100 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m31]; exact w30_100
  have w31_104 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m31]; exact w30_104
  have w31_108 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m31]; exact w30_108
  have w31_10c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m31]; exact w30_10c
  have w31_110 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m31]; exact w30_110
  have w31_114 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m31]; exact w30_114
  have w31_118 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m31]; exact w30_118
  have w31_11c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m31]; exact w30_11c
  have w31_120 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m31]; exact w30_120
  have w31_124 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m31]; exact w30_124
  have w31_128 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m31]; exact w30_128
  have w31_12c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m31]; exact w30_12c
  have w31_130 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m31]; exact w30_130
  have b31_a40 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = gs := by rw [m31]; exact b30_a40
  have b31_1040 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = gs := by rw [m31]; exact b30_1040
  have b31_14a0 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := by rw [m31]; exact b30_14a0
  have q31_420 : ∀ j, j < 96 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m31]; exact q30_420 j hj
  have q31_480 : ∀ j, j < 96 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0x480 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m31]; exact q30_480 j hj
  have q31_4e0 : ∀ j, j < 96 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0x4E0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m31]; exact q30_4e0 j hj
  have q31_540 : ∀ j, j < 96 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0x540 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m31]; exact q30_540 j hj
  have q31_5a0 : ∀ j, j < 96 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0x5A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m31]; exact q30_5a0 j hj
  have q31_600 : ∀ j, j < 96 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0x600 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m31]; exact q30_600 j hj
  have q31_660 : ∀ j, j < 96 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0x660 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m31]; exact q30_660 j hj
  have a31_240 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m31]; exact a30_240
  have a31_260 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m31]; exact a30_260
  have a31_280 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m31]; exact a30_280
  have a31_2a0 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m31]; exact a30_2a0
  have a31_2c0 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m31]; exact a30_2c0
  have a31_2e0 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m31]; exact a30_2e0
  have a31_380 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m31]; exact a30_380
  have a31_400 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m31]; exact a30_400
  have a31_13e0 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U2 := by rw [m31]; exact a30_13e0
  have a31_14e0 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x14E0) 8 = U1 := by rw [m31]; exact a30_14e0
  have a31_1560 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1560) 8 = U2 := by rw [m31]; exact a30_1560
  have p31_320 : ptF n31.mem B 0x320 = P0 := by rw [m31]; exact p30_320
  have p31_3a0 : ptF n31.mem B 0x3A0 = P1 := by rw [m31]; exact p30_3a0
  have p31_6c0 : ptF n31.mem B 0x6C0 = tbl2 P0 7 := by rw [m31]; exact p30_6c0
  have p31_a20 : ptF n31.mem B 0xA20 = tbl2 P0 0 := by rw [m31]; exact p30_a20
  have p31_a80 : ptF n31.mem B 0xA80 = tbl2 P0 1 := by rw [m31]; exact p30_a80
  have p31_ae0 : ptF n31.mem B 0xAE0 = tbl2 P0 2 := by rw [m31]; exact p30_ae0
  have p31_b40 : ptF n31.mem B 0xB40 = tbl2 P0 3 := by rw [m31]; exact p30_b40
  have p31_ba0 : ptF n31.mem B 0xBA0 = tbl2 P0 4 := by rw [m31]; exact p30_ba0
  have p31_c00 : ptF n31.mem B 0xC00 = tbl2 P0 5 := by rw [m31]; exact p30_c00
  have p31_c60 : ptF n31.mem B 0xC60 = tbl2 P0 6 := by rw [m31]; exact p30_c60
  have p31_cc0 : ptF n31.mem B 0xCC0 = tbl2 P0 7 := by rw [m31]; exact p30_cc0
  have p31_1020 : ptF n31.mem B 0x1020 = tbl2 P0 0 := by rw [m31]; exact p30_1020
  have p31_1080 : ptF n31.mem B 0x1080 = tbl2 P0 1 := by rw [m31]; exact p30_1080
  have p31_10e0 : ptF n31.mem B 0x10E0 = tbl2 P0 2 := by rw [m31]; exact p30_10e0
  have p31_1140 : ptF n31.mem B 0x1140 = tbl2 P0 3 := by rw [m31]; exact p30_1140
  have p31_11a0 : ptF n31.mem B 0x11A0 = tbl2 P0 4 := by rw [m31]; exact p30_11a0
  have p31_1200 : ptF n31.mem B 0x1200 = tbl2 P0 5 := by rw [m31]; exact p30_1200
  have p31_1260 : ptF n31.mem B 0x1260 = tbl2 P0 6 := by rw [m31]; exact p30_1260
  have p31_12c0 : ptF n31.mem B 0x12C0 = tbl2 P0 7 := by rw [m31]; exact p30_12c0
  have p31_1320 : ptF n31.mem B 0x1320 = ptDbl2 P0 := by rw [m31]; exact p30_1320
  have p31_1380 : ptF n31.mem B 0x1380 = P1 := by rw [m31]; exact p30_1380
  have p31_1480 : ptF n31.mem B 0x1480 = P0 := by rw [m31]; exact p30_1480
  have p31_1500 : ptF n31.mem B 0x1500 = P1 := by rw [m31]; exact p30_1500
  clear q30_660 p30_1500 p30_1480 p30_1380 p30_1320 p30_12c0 p30_1260 p30_1200 p30_11a0 p30_1140 p30_10e0 p30_1080 p30_1020 p30_cc0 p30_c60 p30_c00 p30_ba0 p30_b40 p30_ae0 p30_a80 p30_a20 p30_6c0 p30_3a0 p30_320 a30_1560 a30_14e0 a30_13e0 a30_400 a30_380 a30_2e0 a30_2c0 a30_2a0 a30_280 a30_260 a30_240 q30_600 q30_5a0 q30_540 q30_4e0 q30_480 q30_420 b30_14a0 b30_1040 b30_a40 w30_130 w30_12c w30_128 w30_124 w30_120 w30_11c w30_118 w30_114 w30_110 w30_10c w30_108 w30_104 w30_100 w30_fc w30_f8 w30_f4 w30_f0 w30_ec w30_e8 w30_e4 w30_e0 w30_dc w30_d8 w30_d4 w30_d0 w30_cc w30_c8 w30_c4 w30_c0 w30_bc w30_b8 w30_b4 w30_b0 w30_ac w30_a8 w30_a4 w30_a0 w30_9c w30_98 w30_94 w30_90 w30_8c w30_88 w30_84 w30_80 w30_7c w30_78 w30_70 w30_6c w30_68 w30_64 w30_60 w30_5c w30_58 w30_54 w30_50 w30_4c w30_48 w30_44 w30_40 w30_3c w30_38 w30_34 w30_30 w30_2c w30_28 w30_24 g30_27 g30_26 g30_25 g30_24 g30_23 g30_22 g30_21 g30_20 g30_19 g30_18 g30_9 g30_8 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 s30 X30 K30 P30
  -- 0x16C8: branch, taken
  obtain ⟨n32, d32, u32⟩ := s31.taken E31.self 0x16B2 sv_at_16c8
    (by decide) (by rw [g31_9, s31.zero]; decide)
  have s32 : St n32.mem SV n32 0x16B2 (reg n32) := ⟨u32.pc, rfl, fun _ => rfl⟩
  have m32 : n32.mem = n31.mem := u32.mem
  have fr32 : ∀ x, SvR B x → n32.mem x = n31.mem x := fun x _ => by rw [m32]
  have t32 : Steps n0 n32 := t31.trans (.single d32)
  have fR32 : ∀ x, SvR B x → n32.mem x = M0 x := fun x hx => (fr32 x hx).trans (fR31 x hx)
  have E32 : SvCode n32.mem := E31.fr F fr32
  have V32 : SvSaves B n32.mem v := V31.same m32
  have g32_2 : reg n32 sp = B + 0x21A0 := by rw [u32.regs, g31_2]
  have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u32.regs, g31_3]
  have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u32.regs, g31_4]
  have g32_8 : reg n32 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x6C0 := by rw [u32.regs, g31_8]
  have g32_9 : reg n32 (9 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u32.regs, g31_9]
  have g32_18 : reg n32 (18 : Fin 32) = out := by rw [u32.regs, g31_18]
  have g32_19 : reg n32 (19 : Fin 32) = bp := by rw [u32.regs, g31_19]
  have g32_20 : reg n32 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u32.regs, g31_20]
  have g32_21 : reg n32 (21 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u32.regs, g31_21]
  have g32_22 : reg n32 (22 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [u32.regs, g31_22]
  have g32_23 : reg n32 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1500 := by rw [u32.regs, g31_23]
  have g32_24 : reg n32 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u32.regs, g31_24]
  have g32_25 : reg n32 (25 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [u32.regs, g31_25]
  have g32_26 : reg n32 (26 : Fin 32) = x26 := by rw [u32.regs, g31_26]
  have g32_27 : reg n32 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u32.regs, g31_27]
  have keep_kk32 : SvKeepL B n0.mem n32.mem [(0x1380, 0x80), (0x420, 0x60), (0x480, 0x60), (0x4E0, 0x60), (0x540, 0x60), (0x5A0, 0x60), (0x600, 0x60), (0x660, 0x60)] := by rw [m32]; exact keep_kk31
  clear keep_kk31
  have w32_24 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m32]; exact w31_24
  have w32_28 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m32]; exact w31_28
  have w32_2c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m32]; exact w31_2c
  have w32_30 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m32]; exact w31_30
  have w32_34 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m32]; exact w31_34
  have w32_38 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m32]; exact w31_38
  have w32_3c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m32]; exact w31_3c
  have w32_40 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m32]; exact w31_40
  have w32_44 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m32]; exact w31_44
  have w32_48 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m32]; exact w31_48
  have w32_4c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m32]; exact w31_4c
  have w32_50 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m32]; exact w31_50
  have w32_54 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m32]; exact w31_54
  have w32_58 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m32]; exact w31_58
  have w32_5c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m32]; exact w31_5c
  have w32_60 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m32]; exact w31_60
  have w32_64 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m32]; exact w31_64
  have w32_68 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m32]; exact w31_68
  have w32_6c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m32]; exact w31_6c
  have w32_70 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m32]; exact w31_70
  have w32_78 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m32]; exact w31_78
  have w32_7c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m32]; exact w31_7c
  have w32_80 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m32]; exact w31_80
  have w32_84 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m32]; exact w31_84
  have w32_88 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m32]; exact w31_88
  have w32_8c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m32]; exact w31_8c
  have w32_90 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m32]; exact w31_90
  have w32_94 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m32]; exact w31_94
  have w32_98 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m32]; exact w31_98
  have w32_9c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m32]; exact w31_9c
  have w32_a0 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m32]; exact w31_a0
  have w32_a4 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m32]; exact w31_a4
  have w32_a8 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m32]; exact w31_a8
  have w32_ac : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m32]; exact w31_ac
  have w32_b0 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m32]; exact w31_b0
  have w32_b4 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m32]; exact w31_b4
  have w32_b8 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m32]; exact w31_b8
  have w32_bc : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m32]; exact w31_bc
  have w32_c0 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m32]; exact w31_c0
  have w32_c4 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m32]; exact w31_c4
  have w32_c8 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m32]; exact w31_c8
  have w32_cc : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m32]; exact w31_cc
  have w32_d0 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m32]; exact w31_d0
  have w32_d4 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m32]; exact w31_d4
  have w32_d8 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m32]; exact w31_d8
  have w32_dc : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m32]; exact w31_dc
  have w32_e0 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m32]; exact w31_e0
  have w32_e4 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m32]; exact w31_e4
  have w32_e8 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m32]; exact w31_e8
  have w32_ec : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m32]; exact w31_ec
  have w32_f0 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m32]; exact w31_f0
  have w32_f4 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m32]; exact w31_f4
  have w32_f8 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m32]; exact w31_f8
  have w32_fc : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m32]; exact w31_fc
  have w32_100 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m32]; exact w31_100
  have w32_104 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m32]; exact w31_104
  have w32_108 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m32]; exact w31_108
  have w32_10c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m32]; exact w31_10c
  have w32_110 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m32]; exact w31_110
  have w32_114 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m32]; exact w31_114
  have w32_118 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m32]; exact w31_118
  have w32_11c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m32]; exact w31_11c
  have w32_120 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m32]; exact w31_120
  have w32_124 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m32]; exact w31_124
  have w32_128 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m32]; exact w31_128
  have w32_12c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m32]; exact w31_12c
  have w32_130 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m32]; exact w31_130
  have b32_a40 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = gs := by rw [m32]; exact b31_a40
  have b32_1040 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = gs := by rw [m32]; exact b31_1040
  have b32_14a0 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := by rw [m32]; exact b31_14a0
  have q32_420 : ∀ j, j < 96 → n32.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m32]; exact q31_420 j hj
  have q32_480 : ∀ j, j < 96 → n32.mem (B + 0x21A0 + BitVec.ofNat 32 (0x480 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m32]; exact q31_480 j hj
  have q32_4e0 : ∀ j, j < 96 → n32.mem (B + 0x21A0 + BitVec.ofNat 32 (0x4E0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m32]; exact q31_4e0 j hj
  have q32_540 : ∀ j, j < 96 → n32.mem (B + 0x21A0 + BitVec.ofNat 32 (0x540 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m32]; exact q31_540 j hj
  have q32_5a0 : ∀ j, j < 96 → n32.mem (B + 0x21A0 + BitVec.ofNat 32 (0x5A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m32]; exact q31_5a0 j hj
  have q32_600 : ∀ j, j < 96 → n32.mem (B + 0x21A0 + BitVec.ofNat 32 (0x600 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m32]; exact q31_600 j hj
  have q32_660 : ∀ j, j < 96 → n32.mem (B + 0x21A0 + BitVec.ofNat 32 (0x660 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m32]; exact q31_660 j hj
  have a32_240 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m32]; exact a31_240
  have a32_260 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m32]; exact a31_260
  have a32_280 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m32]; exact a31_280
  have a32_2a0 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m32]; exact a31_2a0
  have a32_2c0 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m32]; exact a31_2c0
  have a32_2e0 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m32]; exact a31_2e0
  have a32_380 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m32]; exact a31_380
  have a32_400 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m32]; exact a31_400
  have a32_13e0 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U2 := by rw [m32]; exact a31_13e0
  have a32_14e0 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x14E0) 8 = U1 := by rw [m32]; exact a31_14e0
  have a32_1560 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1560) 8 = U2 := by rw [m32]; exact a31_1560
  have p32_320 : ptF n32.mem B 0x320 = P0 := by rw [m32]; exact p31_320
  have p32_3a0 : ptF n32.mem B 0x3A0 = P1 := by rw [m32]; exact p31_3a0
  have p32_6c0 : ptF n32.mem B 0x6C0 = tbl2 P0 7 := by rw [m32]; exact p31_6c0
  have p32_a20 : ptF n32.mem B 0xA20 = tbl2 P0 0 := by rw [m32]; exact p31_a20
  have p32_a80 : ptF n32.mem B 0xA80 = tbl2 P0 1 := by rw [m32]; exact p31_a80
  have p32_ae0 : ptF n32.mem B 0xAE0 = tbl2 P0 2 := by rw [m32]; exact p31_ae0
  have p32_b40 : ptF n32.mem B 0xB40 = tbl2 P0 3 := by rw [m32]; exact p31_b40
  have p32_ba0 : ptF n32.mem B 0xBA0 = tbl2 P0 4 := by rw [m32]; exact p31_ba0
  have p32_c00 : ptF n32.mem B 0xC00 = tbl2 P0 5 := by rw [m32]; exact p31_c00
  have p32_c60 : ptF n32.mem B 0xC60 = tbl2 P0 6 := by rw [m32]; exact p31_c60
  have p32_cc0 : ptF n32.mem B 0xCC0 = tbl2 P0 7 := by rw [m32]; exact p31_cc0
  have p32_1020 : ptF n32.mem B 0x1020 = tbl2 P0 0 := by rw [m32]; exact p31_1020
  have p32_1080 : ptF n32.mem B 0x1080 = tbl2 P0 1 := by rw [m32]; exact p31_1080
  have p32_10e0 : ptF n32.mem B 0x10E0 = tbl2 P0 2 := by rw [m32]; exact p31_10e0
  have p32_1140 : ptF n32.mem B 0x1140 = tbl2 P0 3 := by rw [m32]; exact p31_1140
  have p32_11a0 : ptF n32.mem B 0x11A0 = tbl2 P0 4 := by rw [m32]; exact p31_11a0
  have p32_1200 : ptF n32.mem B 0x1200 = tbl2 P0 5 := by rw [m32]; exact p31_1200
  have p32_1260 : ptF n32.mem B 0x1260 = tbl2 P0 6 := by rw [m32]; exact p31_1260
  have p32_12c0 : ptF n32.mem B 0x12C0 = tbl2 P0 7 := by rw [m32]; exact p31_12c0
  have p32_1320 : ptF n32.mem B 0x1320 = ptDbl2 P0 := by rw [m32]; exact p31_1320
  have p32_1380 : ptF n32.mem B 0x1380 = P1 := by rw [m32]; exact p31_1380
  have p32_1480 : ptF n32.mem B 0x1480 = P0 := by rw [m32]; exact p31_1480
  have p32_1500 : ptF n32.mem B 0x1500 = P1 := by rw [m32]; exact p31_1500
  clear p31_1500 p31_1480 p31_1380 p31_1320 p31_12c0 p31_1260 p31_1200 p31_11a0 p31_1140 p31_10e0 p31_1080 p31_1020 p31_cc0 p31_c60 p31_c00 p31_ba0 p31_b40 p31_ae0 p31_a80 p31_a20 p31_6c0 p31_3a0 p31_320 a31_1560 a31_14e0 a31_13e0 a31_400 a31_380 a31_2e0 a31_2c0 a31_2a0 a31_280 a31_260 a31_240 q31_660 q31_600 q31_5a0 q31_540 q31_4e0 q31_480 q31_420 b31_14a0 b31_1040 b31_a40 w31_130 w31_12c w31_128 w31_124 w31_120 w31_11c w31_118 w31_114 w31_110 w31_10c w31_108 w31_104 w31_100 w31_fc w31_f8 w31_f4 w31_f0 w31_ec w31_e8 w31_e4 w31_e0 w31_dc w31_d8 w31_d4 w31_d0 w31_cc w31_c8 w31_c4 w31_c0 w31_bc w31_b8 w31_b4 w31_b0 w31_ac w31_a8 w31_a4 w31_a0 w31_9c w31_98 w31_94 w31_90 w31_8c w31_88 w31_84 w31_80 w31_7c w31_78 w31_70 w31_6c w31_68 w31_64 w31_60 w31_5c w31_58 w31_54 w31_50 w31_4c w31_48 w31_44 w31_40 w31_3c w31_38 w31_34 w31_30 w31_2c w31_28 w31_24 g31_9 g31_8 g31_27 g31_26 g31_25 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 rb31 s31 m31 u31 c31
  -- 0x16B2
  obtain ⟨n33, c33, u33⟩ := s32.block svEcT1a16b2 E32.self svEcT1a16b2_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m33 : n33.mem = n32.mem := u33.mem
  have s33 : St n33.mem SV n33 0x16BA (reg n33) := ⟨u33.pc, rfl, fun _ => rfl⟩
  have rb33 : ∀ q, reg n33 q = (runBlock svEcT1a16b2 (n32.mem, reg n32)).2 q := fun q => by rw [u33.regs]
  have fr33 : ∀ x, SvR B x → n33.mem x = n32.mem x := fun x _ => by rw [m33]
  have t33 : Steps n0 n33 := t32.trans c33
  have fR33 : ∀ x, SvR B x → n33.mem x = M0 x := fun x hx => (fr33 x hx).trans (fR32 x hx)
  have E33 : SvCode n33.mem := E32.fr F fr33
  have V33 : SvSaves B n33.mem v := V32.same m33
  have g33_2 : reg n33 sp = B + 0x21A0 := by
    rw [rb33, runBlock_reg _ _ _ sp s32.zero (by decide), g32_2]
  have g33_3 : reg n33 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb33, runBlock_reg _ _ _ (3 : Fin 32) s32.zero (by decide), g32_3]
  have g33_4 : reg n33 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb33, runBlock_reg _ _ _ (4 : Fin 32) s32.zero (by decide), g32_4]
  have g33_8 : reg n33 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x6C0 := by
    rw [rb33, runBlock_reg _ _ _ (8 : Fin 32) s32.zero (by decide), g32_8]
  have g33_9 : reg n33 (9 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb33, runBlock_reg _ _ _ (9 : Fin 32) s32.zero (by decide), g32_9]
  have g33_18 : reg n33 (18 : Fin 32) = out := by
    rw [rb33, runBlock_reg _ _ _ (18 : Fin 32) s32.zero (by decide), g32_18]
  have g33_19 : reg n33 (19 : Fin 32) = bp := by
    rw [rb33, runBlock_reg _ _ _ (19 : Fin 32) s32.zero (by decide), g32_19]
  have g33_20 : reg n33 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb33, runBlock_reg _ _ _ (20 : Fin 32) s32.zero (by decide), g32_20]
  have g33_21 : reg n33 (21 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb33, runBlock_reg _ _ _ (21 : Fin 32) s32.zero (by decide), g32_21]
  have g33_22 : reg n33 (22 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb33, runBlock_reg _ _ _ (22 : Fin 32) s32.zero (by decide), g32_22]
  have g33_23 : reg n33 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1500 := by
    rw [rb33, runBlock_reg _ _ _ (23 : Fin 32) s32.zero (by decide), g32_23]
  have g33_24 : reg n33 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb33, runBlock_reg _ _ _ (24 : Fin 32) s32.zero (by decide), g32_24]
  have g33_25 : reg n33 (25 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb33, runBlock_reg _ _ _ (25 : Fin 32) s32.zero (by decide), g32_25]
  have g33_26 : reg n33 (26 : Fin 32) = x26 := by
    rw [rb33, runBlock_reg _ _ _ (26 : Fin 32) s32.zero (by decide), g32_26]
  have g33_27 : reg n33 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb33, runBlock_reg _ _ _ (27 : Fin 32) s32.zero (by decide), g32_27]
  have g33_10 : reg n33 a0 = B + 0x21A0 + BitVec.ofNat 32 0x6C0 := by
    rw [rb33]; simp +decide only [runBlock, BInstr.run, svEcT1a16b2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g32_2, g32_3, g32_4, g32_8, g32_9, g32_18, g32_19, g32_20, g32_21, g32_22, g32_23, g32_24, g32_25, g32_26, g32_27, s32.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g33_11 : reg n33 a1 = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb33]; simp +decide only [runBlock, BInstr.run, svEcT1a16b2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g32_2, g32_3, g32_4, g32_8, g32_9, g32_18, g32_19, g32_20, g32_21, g32_22, g32_23, g32_24, g32_25, g32_26, g32_27, s32.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g33_12 : reg n33 a2 = BitVec.ofNat 32 0x60 := by
    rw [rb33]; simp +decide only [runBlock, BInstr.run, svEcT1a16b2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g32_2, g32_3, g32_4, g32_8, g32_9, g32_18, g32_19, g32_20, g32_21, g32_22, g32_23, g32_24, g32_25, g32_26, g32_27, s32.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk33 : SvKeepL B n0.mem n33.mem [(0x1380, 0x80), (0x420, 0x60), (0x480, 0x60), (0x4E0, 0x60), (0x540, 0x60), (0x5A0, 0x60), (0x600, 0x60), (0x660, 0x60)] := by rw [m33]; exact keep_kk32
  clear keep_kk32
  have w33_24 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m33]; exact w32_24
  have w33_28 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m33]; exact w32_28
  have w33_2c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m33]; exact w32_2c
  have w33_30 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m33]; exact w32_30
  have w33_34 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m33]; exact w32_34
  have w33_38 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m33]; exact w32_38
  have w33_3c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m33]; exact w32_3c
  have w33_40 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m33]; exact w32_40
  have w33_44 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m33]; exact w32_44
  have w33_48 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m33]; exact w32_48
  have w33_4c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m33]; exact w32_4c
  have w33_50 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m33]; exact w32_50
  have w33_54 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m33]; exact w32_54
  have w33_58 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m33]; exact w32_58
  have w33_5c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m33]; exact w32_5c
  have w33_60 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m33]; exact w32_60
  have w33_64 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m33]; exact w32_64
  have w33_68 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m33]; exact w32_68
  have w33_6c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m33]; exact w32_6c
  have w33_70 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m33]; exact w32_70
  have w33_78 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m33]; exact w32_78
  have w33_7c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m33]; exact w32_7c
  have w33_80 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m33]; exact w32_80
  have w33_84 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m33]; exact w32_84
  have w33_88 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m33]; exact w32_88
  have w33_8c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m33]; exact w32_8c
  have w33_90 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m33]; exact w32_90
  have w33_94 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m33]; exact w32_94
  have w33_98 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m33]; exact w32_98
  have w33_9c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m33]; exact w32_9c
  have w33_a0 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m33]; exact w32_a0
  have w33_a4 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m33]; exact w32_a4
  have w33_a8 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m33]; exact w32_a8
  have w33_ac : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m33]; exact w32_ac
  have w33_b0 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m33]; exact w32_b0
  have w33_b4 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m33]; exact w32_b4
  have w33_b8 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m33]; exact w32_b8
  have w33_bc : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m33]; exact w32_bc
  have w33_c0 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m33]; exact w32_c0
  have w33_c4 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m33]; exact w32_c4
  have w33_c8 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m33]; exact w32_c8
  have w33_cc : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m33]; exact w32_cc
  have w33_d0 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m33]; exact w32_d0
  have w33_d4 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m33]; exact w32_d4
  have w33_d8 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m33]; exact w32_d8
  have w33_dc : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m33]; exact w32_dc
  have w33_e0 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m33]; exact w32_e0
  have w33_e4 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m33]; exact w32_e4
  have w33_e8 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m33]; exact w32_e8
  have w33_ec : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m33]; exact w32_ec
  have w33_f0 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m33]; exact w32_f0
  have w33_f4 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m33]; exact w32_f4
  have w33_f8 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m33]; exact w32_f8
  have w33_fc : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m33]; exact w32_fc
  have w33_100 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m33]; exact w32_100
  have w33_104 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m33]; exact w32_104
  have w33_108 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m33]; exact w32_108
  have w33_10c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m33]; exact w32_10c
  have w33_110 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m33]; exact w32_110
  have w33_114 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m33]; exact w32_114
  have w33_118 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m33]; exact w32_118
  have w33_11c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m33]; exact w32_11c
  have w33_120 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m33]; exact w32_120
  have w33_124 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m33]; exact w32_124
  have w33_128 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m33]; exact w32_128
  have w33_12c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m33]; exact w32_12c
  have w33_130 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m33]; exact w32_130
  have b33_a40 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = gs := by rw [m33]; exact b32_a40
  have b33_1040 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = gs := by rw [m33]; exact b32_1040
  have b33_14a0 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := by rw [m33]; exact b32_14a0
  have q33_420 : ∀ j, j < 96 → n33.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m33]; exact q32_420 j hj
  have q33_480 : ∀ j, j < 96 → n33.mem (B + 0x21A0 + BitVec.ofNat 32 (0x480 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m33]; exact q32_480 j hj
  have q33_4e0 : ∀ j, j < 96 → n33.mem (B + 0x21A0 + BitVec.ofNat 32 (0x4E0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m33]; exact q32_4e0 j hj
  have q33_540 : ∀ j, j < 96 → n33.mem (B + 0x21A0 + BitVec.ofNat 32 (0x540 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m33]; exact q32_540 j hj
  have q33_5a0 : ∀ j, j < 96 → n33.mem (B + 0x21A0 + BitVec.ofNat 32 (0x5A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m33]; exact q32_5a0 j hj
  have q33_600 : ∀ j, j < 96 → n33.mem (B + 0x21A0 + BitVec.ofNat 32 (0x600 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m33]; exact q32_600 j hj
  have q33_660 : ∀ j, j < 96 → n33.mem (B + 0x21A0 + BitVec.ofNat 32 (0x660 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m33]; exact q32_660 j hj
  have a33_240 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m33]; exact a32_240
  have a33_260 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m33]; exact a32_260
  have a33_280 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m33]; exact a32_280
  have a33_2a0 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m33]; exact a32_2a0
  have a33_2c0 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m33]; exact a32_2c0
  have a33_2e0 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m33]; exact a32_2e0
  have a33_380 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m33]; exact a32_380
  have a33_400 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m33]; exact a32_400
  have a33_13e0 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U2 := by rw [m33]; exact a32_13e0
  have a33_14e0 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x14E0) 8 = U1 := by rw [m33]; exact a32_14e0
  have a33_1560 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x1560) 8 = U2 := by rw [m33]; exact a32_1560
  have p33_320 : ptF n33.mem B 0x320 = P0 := by rw [m33]; exact p32_320
  have p33_3a0 : ptF n33.mem B 0x3A0 = P1 := by rw [m33]; exact p32_3a0
  have p33_6c0 : ptF n33.mem B 0x6C0 = tbl2 P0 7 := by rw [m33]; exact p32_6c0
  have p33_a20 : ptF n33.mem B 0xA20 = tbl2 P0 0 := by rw [m33]; exact p32_a20
  have p33_a80 : ptF n33.mem B 0xA80 = tbl2 P0 1 := by rw [m33]; exact p32_a80
  have p33_ae0 : ptF n33.mem B 0xAE0 = tbl2 P0 2 := by rw [m33]; exact p32_ae0
  have p33_b40 : ptF n33.mem B 0xB40 = tbl2 P0 3 := by rw [m33]; exact p32_b40
  have p33_ba0 : ptF n33.mem B 0xBA0 = tbl2 P0 4 := by rw [m33]; exact p32_ba0
  have p33_c00 : ptF n33.mem B 0xC00 = tbl2 P0 5 := by rw [m33]; exact p32_c00
  have p33_c60 : ptF n33.mem B 0xC60 = tbl2 P0 6 := by rw [m33]; exact p32_c60
  have p33_cc0 : ptF n33.mem B 0xCC0 = tbl2 P0 7 := by rw [m33]; exact p32_cc0
  have p33_1020 : ptF n33.mem B 0x1020 = tbl2 P0 0 := by rw [m33]; exact p32_1020
  have p33_1080 : ptF n33.mem B 0x1080 = tbl2 P0 1 := by rw [m33]; exact p32_1080
  have p33_10e0 : ptF n33.mem B 0x10E0 = tbl2 P0 2 := by rw [m33]; exact p32_10e0
  have p33_1140 : ptF n33.mem B 0x1140 = tbl2 P0 3 := by rw [m33]; exact p32_1140
  have p33_11a0 : ptF n33.mem B 0x11A0 = tbl2 P0 4 := by rw [m33]; exact p32_11a0
  have p33_1200 : ptF n33.mem B 0x1200 = tbl2 P0 5 := by rw [m33]; exact p32_1200
  have p33_1260 : ptF n33.mem B 0x1260 = tbl2 P0 6 := by rw [m33]; exact p32_1260
  have p33_12c0 : ptF n33.mem B 0x12C0 = tbl2 P0 7 := by rw [m33]; exact p32_12c0
  have p33_1320 : ptF n33.mem B 0x1320 = ptDbl2 P0 := by rw [m33]; exact p32_1320
  have p33_1380 : ptF n33.mem B 0x1380 = P1 := by rw [m33]; exact p32_1380
  have p33_1480 : ptF n33.mem B 0x1480 = P0 := by rw [m33]; exact p32_1480
  have p33_1500 : ptF n33.mem B 0x1500 = P1 := by rw [m33]; exact p32_1500
  clear p32_1500 p32_1480 p32_1380 p32_1320 p32_12c0 p32_1260 p32_1200 p32_11a0 p32_1140 p32_10e0 p32_1080 p32_1020 p32_cc0 p32_c60 p32_c00 p32_ba0 p32_b40 p32_ae0 p32_a80 p32_a20 p32_6c0 p32_3a0 p32_320 a32_1560 a32_14e0 a32_13e0 a32_400 a32_380 a32_2e0 a32_2c0 a32_2a0 a32_280 a32_260 a32_240 q32_660 q32_600 q32_5a0 q32_540 q32_4e0 q32_480 q32_420 b32_14a0 b32_1040 b32_a40 w32_130 w32_12c w32_128 w32_124 w32_120 w32_11c w32_118 w32_114 w32_110 w32_10c w32_108 w32_104 w32_100 w32_fc w32_f8 w32_f4 w32_f0 w32_ec w32_e8 w32_e4 w32_e0 w32_dc w32_d8 w32_d4 w32_d0 w32_cc w32_c8 w32_c4 w32_c0 w32_bc w32_b8 w32_b4 w32_b0 w32_ac w32_a8 w32_a4 w32_a0 w32_9c w32_98 w32_94 w32_90 w32_8c w32_88 w32_84 w32_80 w32_7c w32_78 w32_70 w32_6c w32_68 w32_64 w32_60 w32_5c w32_58 w32_54 w32_50 w32_4c w32_48 w32_44 w32_40 w32_3c w32_38 w32_34 w32_30 w32_2c w32_28 w32_24 g32_27 g32_26 g32_25 g32_24 g32_23 g32_22 g32_21 g32_20 g32_19 g32_18 g32_9 g32_8 g32_4 g32_3 g32_2 V32 E32 fR32 t32 fr32 m32 s32 u32 d32
  -- 0x16BA: memcpy from outside the stack
  obtain ⟨n34, P34, K34, X34⟩ := sv_mcRo2 (c := 0x6C0) (N := 0x60) F RS E33 s33 sv_at_16ba sv_at_16be
    (by decide) (by decide) g33_2 g33_10 g33_11 g33_12 (by decide) (Or.inr ⟨by decide, by decide⟩)
  have s34 := P34.st
  have fr34 := P34.fr
  have t34 : Steps n0 n34 := t33.trans P34.steps
  have fR34 : ∀ x, SvR B x → n34.mem x = M0 x := fun x hx => (fr34 x hx).trans (fR33 x hx)
  have E34 : SvCode n34.mem := E33.fr F fr34
  have V34 : SvSaves B n34.mem v := V33.keep K34 (by decide)
  have g34_2 : reg n34 sp = B + 0x21A0 := by rw [P34.regs sp (by decide), g33_2]
  have g34_3 : reg n34 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P34.regs (3 : Fin 32) (by decide), g33_3]
  have g34_4 : reg n34 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P34.regs (4 : Fin 32) (by decide), g33_4]
  have g34_8 : reg n34 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x6C0 := by rw [P34.regs (8 : Fin 32) (by decide), g33_8]
  have g34_9 : reg n34 (9 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P34.regs (9 : Fin 32) (by decide), g33_9]
  have g34_18 : reg n34 (18 : Fin 32) = out := by rw [P34.regs (18 : Fin 32) (by decide), g33_18]
  have g34_19 : reg n34 (19 : Fin 32) = bp := by rw [P34.regs (19 : Fin 32) (by decide), g33_19]
  have g34_20 : reg n34 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P34.regs (20 : Fin 32) (by decide), g33_20]
  have g34_21 : reg n34 (21 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P34.regs (21 : Fin 32) (by decide), g33_21]
  have g34_22 : reg n34 (22 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [P34.regs (22 : Fin 32) (by decide), g33_22]
  have g34_23 : reg n34 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1500 := by rw [P34.regs (23 : Fin 32) (by decide), g33_23]
  have g34_24 : reg n34 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P34.regs (24 : Fin 32) (by decide), g33_24]
  have g34_25 : reg n34 (25 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [P34.regs (25 : Fin 32) (by decide), g33_25]
  have g34_26 : reg n34 (26 : Fin 32) = x26 := by rw [P34.regs (26 : Fin 32) (by decide), g33_26]
  have g34_27 : reg n34 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P34.regs (27 : Fin 32) (by decide), g33_27]
  have keep_kk34 : SvKeepL B n0.mem n34.mem [(0x1380, 0x80), (0x420, 0x60), (0x480, 0x60), (0x4E0, 0x60), (0x540, 0x60), (0x5A0, 0x60), (0x600, 0x60), (0x660, 0x60), (0x6C0, 0x60)] := keep_kk33.trans K34.toL
  clear keep_kk33
  have w34_24 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K34.w32 (by decide) (by decide)).trans w33_24
  have w34_28 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K34.w32 (by decide) (by decide)).trans w33_28
  have w34_2c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K34.w32 (by decide) (by decide)).trans w33_2c
  have w34_30 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K34.w32 (by decide) (by decide)).trans w33_30
  have w34_34 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K34.w32 (by decide) (by decide)).trans w33_34
  have w34_38 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K34.w32 (by decide) (by decide)).trans w33_38
  have w34_3c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K34.w32 (by decide) (by decide)).trans w33_3c
  have w34_40 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K34.w32 (by decide) (by decide)).trans w33_40
  have w34_44 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K34.w32 (by decide) (by decide)).trans w33_44
  have w34_48 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K34.w32 (by decide) (by decide)).trans w33_48
  have w34_4c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K34.w32 (by decide) (by decide)).trans w33_4c
  have w34_50 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K34.w32 (by decide) (by decide)).trans w33_50
  have w34_54 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K34.w32 (by decide) (by decide)).trans w33_54
  have w34_58 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K34.w32 (by decide) (by decide)).trans w33_58
  have w34_5c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K34.w32 (by decide) (by decide)).trans w33_5c
  have w34_60 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K34.w32 (by decide) (by decide)).trans w33_60
  have w34_64 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K34.w32 (by decide) (by decide)).trans w33_64
  have w34_68 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K34.w32 (by decide) (by decide)).trans w33_68
  have w34_6c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K34.w32 (by decide) (by decide)).trans w33_6c
  have w34_70 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K34.w32 (by decide) (by decide)).trans w33_70
  have w34_78 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := (K34.w32 (by decide) (by decide)).trans w33_78
  have w34_7c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K34.w32 (by decide) (by decide)).trans w33_7c
  have w34_80 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K34.w32 (by decide) (by decide)).trans w33_80
  have w34_84 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K34.w32 (by decide) (by decide)).trans w33_84
  have w34_88 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K34.w32 (by decide) (by decide)).trans w33_88
  have w34_8c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K34.w32 (by decide) (by decide)).trans w33_8c
  have w34_90 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K34.w32 (by decide) (by decide)).trans w33_90
  have w34_94 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K34.w32 (by decide) (by decide)).trans w33_94
  have w34_98 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K34.w32 (by decide) (by decide)).trans w33_98
  have w34_9c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K34.w32 (by decide) (by decide)).trans w33_9c
  have w34_a0 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K34.w32 (by decide) (by decide)).trans w33_a0
  have w34_a4 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K34.w32 (by decide) (by decide)).trans w33_a4
  have w34_a8 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K34.w32 (by decide) (by decide)).trans w33_a8
  have w34_ac : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K34.w32 (by decide) (by decide)).trans w33_ac
  have w34_b0 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K34.w32 (by decide) (by decide)).trans w33_b0
  have w34_b4 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K34.w32 (by decide) (by decide)).trans w33_b4
  have w34_b8 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K34.w32 (by decide) (by decide)).trans w33_b8
  have w34_bc : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K34.w32 (by decide) (by decide)).trans w33_bc
  have w34_c0 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K34.w32 (by decide) (by decide)).trans w33_c0
  have w34_c4 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K34.w32 (by decide) (by decide)).trans w33_c4
  have w34_c8 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K34.w32 (by decide) (by decide)).trans w33_c8
  have w34_cc : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K34.w32 (by decide) (by decide)).trans w33_cc
  have w34_d0 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K34.w32 (by decide) (by decide)).trans w33_d0
  have w34_d4 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K34.w32 (by decide) (by decide)).trans w33_d4
  have w34_d8 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K34.w32 (by decide) (by decide)).trans w33_d8
  have w34_dc : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K34.w32 (by decide) (by decide)).trans w33_dc
  have w34_e0 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K34.w32 (by decide) (by decide)).trans w33_e0
  have w34_e4 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K34.w32 (by decide) (by decide)).trans w33_e4
  have w34_e8 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K34.w32 (by decide) (by decide)).trans w33_e8
  have w34_ec : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K34.w32 (by decide) (by decide)).trans w33_ec
  have w34_f0 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K34.w32 (by decide) (by decide)).trans w33_f0
  have w34_f4 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K34.w32 (by decide) (by decide)).trans w33_f4
  have w34_f8 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K34.w32 (by decide) (by decide)).trans w33_f8
  have w34_fc : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K34.w32 (by decide) (by decide)).trans w33_fc
  have w34_100 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K34.w32 (by decide) (by decide)).trans w33_100
  have w34_104 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K34.w32 (by decide) (by decide)).trans w33_104
  have w34_108 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K34.w32 (by decide) (by decide)).trans w33_108
  have w34_10c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K34.w32 (by decide) (by decide)).trans w33_10c
  have w34_110 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K34.w32 (by decide) (by decide)).trans w33_110
  have w34_114 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K34.w32 (by decide) (by decide)).trans w33_114
  have w34_118 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K34.w32 (by decide) (by decide)).trans w33_118
  have w34_11c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K34.w32 (by decide) (by decide)).trans w33_11c
  have w34_120 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K34.w32 (by decide) (by decide)).trans w33_120
  have w34_124 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K34.w32 (by decide) (by decide)).trans w33_124
  have w34_128 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K34.w32 (by decide) (by decide)).trans w33_128
  have w34_12c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K34.w32 (by decide) (by decide)).trans w33_12c
  have w34_130 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K34.w32 (by decide) (by decide)).trans w33_130
  have b34_a40 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = gs := (K34.b8 (by decide) (by decide)).trans b33_a40
  have b34_1040 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = gs := (K34.b8 (by decide) (by decide)).trans b33_1040
  have b34_14a0 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := (K34.b8 (by decide) (by decide)).trans b33_14a0
  have q34_420 : ∀ j, j < 96 → n34.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K34.range (by decide) (by decide) j hj).trans (q33_420 j hj)
  have q34_480 : ∀ j, j < 96 → n34.mem (B + 0x21A0 + BitVec.ofNat 32 (0x480 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K34.range (by decide) (by decide) j hj).trans (q33_480 j hj)
  have q34_4e0 : ∀ j, j < 96 → n34.mem (B + 0x21A0 + BitVec.ofNat 32 (0x4E0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K34.range (by decide) (by decide) j hj).trans (q33_4e0 j hj)
  have q34_540 : ∀ j, j < 96 → n34.mem (B + 0x21A0 + BitVec.ofNat 32 (0x540 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K34.range (by decide) (by decide) j hj).trans (q33_540 j hj)
  have q34_5a0 : ∀ j, j < 96 → n34.mem (B + 0x21A0 + BitVec.ofNat 32 (0x5A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K34.range (by decide) (by decide) j hj).trans (q33_5a0 j hj)
  have q34_600 : ∀ j, j < 96 → n34.mem (B + 0x21A0 + BitVec.ofNat 32 (0x600 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K34.range (by decide) (by decide) j hj).trans (q33_600 j hj)
  have q34_660 : ∀ j, j < 96 → n34.mem (B + 0x21A0 + BitVec.ofNat 32 (0x660 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K34.range (by decide) (by decide) j hj).trans (q33_660 j hj)
  have a34_240 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := (K34.acc (by decide) (by decide)).trans a33_240
  have a34_260 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := (K34.acc (by decide) (by decide)).trans a33_260
  have a34_280 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := (K34.acc (by decide) (by decide)).trans a33_280
  have a34_2a0 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K34.acc (by decide) (by decide)).trans a33_2a0
  have a34_2c0 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K34.acc (by decide) (by decide)).trans a33_2c0
  have a34_2e0 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K34.acc (by decide) (by decide)).trans a33_2e0
  have a34_380 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := (K34.acc (by decide) (by decide)).trans a33_380
  have a34_400 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := (K34.acc (by decide) (by decide)).trans a33_400
  have a34_13e0 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U2 := (K34.acc (by decide) (by decide)).trans a33_13e0
  have a34_14e0 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x14E0) 8 = U1 := (K34.acc (by decide) (by decide)).trans a33_14e0
  have a34_1560 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x1560) 8 = U2 := (K34.acc (by decide) (by decide)).trans a33_1560
  have p34_320 : ptF n34.mem B 0x320 = P0 := (K34.pt (by decide) (by decide)).trans p33_320
  have p34_3a0 : ptF n34.mem B 0x3A0 = P1 := (K34.pt (by decide) (by decide)).trans p33_3a0
  have p34_a20 : ptF n34.mem B 0xA20 = tbl2 P0 0 := (K34.pt (by decide) (by decide)).trans p33_a20
  have p34_a80 : ptF n34.mem B 0xA80 = tbl2 P0 1 := (K34.pt (by decide) (by decide)).trans p33_a80
  have p34_ae0 : ptF n34.mem B 0xAE0 = tbl2 P0 2 := (K34.pt (by decide) (by decide)).trans p33_ae0
  have p34_b40 : ptF n34.mem B 0xB40 = tbl2 P0 3 := (K34.pt (by decide) (by decide)).trans p33_b40
  have p34_ba0 : ptF n34.mem B 0xBA0 = tbl2 P0 4 := (K34.pt (by decide) (by decide)).trans p33_ba0
  have p34_c00 : ptF n34.mem B 0xC00 = tbl2 P0 5 := (K34.pt (by decide) (by decide)).trans p33_c00
  have p34_c60 : ptF n34.mem B 0xC60 = tbl2 P0 6 := (K34.pt (by decide) (by decide)).trans p33_c60
  have p34_cc0 : ptF n34.mem B 0xCC0 = tbl2 P0 7 := (K34.pt (by decide) (by decide)).trans p33_cc0
  have p34_1020 : ptF n34.mem B 0x1020 = tbl2 P0 0 := (K34.pt (by decide) (by decide)).trans p33_1020
  have p34_1080 : ptF n34.mem B 0x1080 = tbl2 P0 1 := (K34.pt (by decide) (by decide)).trans p33_1080
  have p34_10e0 : ptF n34.mem B 0x10E0 = tbl2 P0 2 := (K34.pt (by decide) (by decide)).trans p33_10e0
  have p34_1140 : ptF n34.mem B 0x1140 = tbl2 P0 3 := (K34.pt (by decide) (by decide)).trans p33_1140
  have p34_11a0 : ptF n34.mem B 0x11A0 = tbl2 P0 4 := (K34.pt (by decide) (by decide)).trans p33_11a0
  have p34_1200 : ptF n34.mem B 0x1200 = tbl2 P0 5 := (K34.pt (by decide) (by decide)).trans p33_1200
  have p34_1260 : ptF n34.mem B 0x1260 = tbl2 P0 6 := (K34.pt (by decide) (by decide)).trans p33_1260
  have p34_12c0 : ptF n34.mem B 0x12C0 = tbl2 P0 7 := (K34.pt (by decide) (by decide)).trans p33_12c0
  have p34_1320 : ptF n34.mem B 0x1320 = ptDbl2 P0 := (K34.pt (by decide) (by decide)).trans p33_1320
  have p34_1380 : ptF n34.mem B 0x1380 = P1 := (K34.pt (by decide) (by decide)).trans p33_1380
  have p34_1480 : ptF n34.mem B 0x1480 = P0 := (K34.pt (by decide) (by decide)).trans p33_1480
  have p34_1500 : ptF n34.mem B 0x1500 = P1 := (K34.pt (by decide) (by decide)).trans p33_1500
  have q34_6c0 : ∀ j, j < 96 → n34.mem (B + 0x21A0 + BitVec.ofNat 32 (0x6C0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) :=
    fun j hj => (X34 j hj).trans (fR33 _ (SvRo2.r RS (Or.inr ⟨by decide, by decide⟩) hj))
  clear p33_1500 p33_1480 p33_1380 p33_1320 p33_12c0 p33_1260 p33_1200 p33_11a0 p33_1140 p33_10e0 p33_1080 p33_1020 p33_cc0 p33_c60 p33_c00 p33_ba0 p33_b40 p33_ae0 p33_a80 p33_a20 p33_6c0 p33_3a0 p33_320 a33_1560 a33_14e0 a33_13e0 a33_400 a33_380 a33_2e0 a33_2c0 a33_2a0 a33_280 a33_260 a33_240 q33_660 q33_600 q33_5a0 q33_540 q33_4e0 q33_480 q33_420 b33_14a0 b33_1040 b33_a40 w33_130 w33_12c w33_128 w33_124 w33_120 w33_11c w33_118 w33_114 w33_110 w33_10c w33_108 w33_104 w33_100 w33_fc w33_f8 w33_f4 w33_f0 w33_ec w33_e8 w33_e4 w33_e0 w33_dc w33_d8 w33_d4 w33_d0 w33_cc w33_c8 w33_c4 w33_c0 w33_bc w33_b8 w33_b4 w33_b0 w33_ac w33_a8 w33_a4 w33_a0 w33_9c w33_98 w33_94 w33_90 w33_8c w33_88 w33_84 w33_80 w33_7c w33_78 w33_70 w33_6c w33_68 w33_64 w33_60 w33_5c w33_58 w33_54 w33_50 w33_4c w33_48 w33_44 w33_40 w33_3c w33_38 w33_34 w33_30 w33_2c w33_28 w33_24 g33_12 g33_11 g33_10 g33_27 g33_26 g33_25 g33_24 g33_23 g33_22 g33_21 g33_20 g33_19 g33_18 g33_9 g33_8 g33_4 g33_3 g33_2 V33 E33 fR33 t33 fr33 rb33 s33 m33 u33 c33
  -- 0x16C2
  obtain ⟨n35, c35, u35⟩ := s34.block svEcT1a16c2 E34.self svEcT1a16c2_end
    ⟨trivial, trivial, trivial⟩
  have m35 : n35.mem = n34.mem := u35.mem
  have s35 : St n35.mem SV n35 0x16C8 (reg n35) := ⟨u35.pc, rfl, fun _ => rfl⟩
  have rb35 : ∀ q, reg n35 q = (runBlock svEcT1a16c2 (n34.mem, reg n34)).2 q := fun q => by rw [u35.regs]
  have fr35 : ∀ x, SvR B x → n35.mem x = n34.mem x := fun x _ => by rw [m35]
  have t35 : Steps n0 n35 := t34.trans c35
  have fR35 : ∀ x, SvR B x → n35.mem x = M0 x := fun x hx => (fr35 x hx).trans (fR34 x hx)
  have E35 : SvCode n35.mem := E34.fr F fr35
  have V35 : SvSaves B n35.mem v := V34.same m35
  have g35_2 : reg n35 sp = B + 0x21A0 := by
    rw [rb35, runBlock_reg _ _ _ sp s34.zero (by decide), g34_2]
  have g35_3 : reg n35 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb35, runBlock_reg _ _ _ (3 : Fin 32) s34.zero (by decide), g34_3]
  have g35_4 : reg n35 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb35, runBlock_reg _ _ _ (4 : Fin 32) s34.zero (by decide), g34_4]
  have g35_18 : reg n35 (18 : Fin 32) = out := by
    rw [rb35, runBlock_reg _ _ _ (18 : Fin 32) s34.zero (by decide), g34_18]
  have g35_19 : reg n35 (19 : Fin 32) = bp := by
    rw [rb35, runBlock_reg _ _ _ (19 : Fin 32) s34.zero (by decide), g34_19]
  have g35_20 : reg n35 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb35, runBlock_reg _ _ _ (20 : Fin 32) s34.zero (by decide), g34_20]
  have g35_21 : reg n35 (21 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb35, runBlock_reg _ _ _ (21 : Fin 32) s34.zero (by decide), g34_21]
  have g35_22 : reg n35 (22 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb35, runBlock_reg _ _ _ (22 : Fin 32) s34.zero (by decide), g34_22]
  have g35_23 : reg n35 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1500 := by
    rw [rb35, runBlock_reg _ _ _ (23 : Fin 32) s34.zero (by decide), g34_23]
  have g35_24 : reg n35 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb35, runBlock_reg _ _ _ (24 : Fin 32) s34.zero (by decide), g34_24]
  have g35_25 : reg n35 (25 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb35, runBlock_reg _ _ _ (25 : Fin 32) s34.zero (by decide), g34_25]
  have g35_26 : reg n35 (26 : Fin 32) = x26 := by
    rw [rb35, runBlock_reg _ _ _ (26 : Fin 32) s34.zero (by decide), g34_26]
  have g35_27 : reg n35 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb35, runBlock_reg _ _ _ (27 : Fin 32) s34.zero (by decide), g34_27]
  have g35_8 : reg n35 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x720 := by
    rw [rb35]; simp +decide only [runBlock, BInstr.run, svEcT1a16c2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g34_2, g34_3, g34_4, g34_8, g34_9, g34_18, g34_19, g34_20, g34_21, g34_22, g34_23, g34_24, g34_25, g34_26, g34_27, s34.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g35_9 : reg n35 (9 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb35]; simp +decide only [runBlock, BInstr.run, svEcT1a16c2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g34_2, g34_3, g34_4, g34_8, g34_9, g34_18, g34_19, g34_20, g34_21, g34_22, g34_23, g34_24, g34_25, g34_26, g34_27, s34.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk35 : SvKeepL B n0.mem n35.mem [(0x1380, 0x80), (0x420, 0x60), (0x480, 0x60), (0x4E0, 0x60), (0x540, 0x60), (0x5A0, 0x60), (0x600, 0x60), (0x660, 0x60), (0x6C0, 0x60)] := by rw [m35]; exact keep_kk34
  clear keep_kk34
  have w35_24 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m35]; exact w34_24
  have w35_28 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m35]; exact w34_28
  have w35_2c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m35]; exact w34_2c
  have w35_30 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m35]; exact w34_30
  have w35_34 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m35]; exact w34_34
  have w35_38 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m35]; exact w34_38
  have w35_3c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m35]; exact w34_3c
  have w35_40 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m35]; exact w34_40
  have w35_44 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m35]; exact w34_44
  have w35_48 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m35]; exact w34_48
  have w35_4c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m35]; exact w34_4c
  have w35_50 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m35]; exact w34_50
  have w35_54 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m35]; exact w34_54
  have w35_58 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m35]; exact w34_58
  have w35_5c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m35]; exact w34_5c
  have w35_60 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m35]; exact w34_60
  have w35_64 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m35]; exact w34_64
  have w35_68 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m35]; exact w34_68
  have w35_6c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m35]; exact w34_6c
  have w35_70 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m35]; exact w34_70
  have w35_78 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m35]; exact w34_78
  have w35_7c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m35]; exact w34_7c
  have w35_80 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m35]; exact w34_80
  have w35_84 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m35]; exact w34_84
  have w35_88 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m35]; exact w34_88
  have w35_8c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m35]; exact w34_8c
  have w35_90 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m35]; exact w34_90
  have w35_94 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m35]; exact w34_94
  have w35_98 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m35]; exact w34_98
  have w35_9c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m35]; exact w34_9c
  have w35_a0 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m35]; exact w34_a0
  have w35_a4 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m35]; exact w34_a4
  have w35_a8 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m35]; exact w34_a8
  have w35_ac : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m35]; exact w34_ac
  have w35_b0 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m35]; exact w34_b0
  have w35_b4 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m35]; exact w34_b4
  have w35_b8 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m35]; exact w34_b8
  have w35_bc : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m35]; exact w34_bc
  have w35_c0 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m35]; exact w34_c0
  have w35_c4 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m35]; exact w34_c4
  have w35_c8 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m35]; exact w34_c8
  have w35_cc : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m35]; exact w34_cc
  have w35_d0 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m35]; exact w34_d0
  have w35_d4 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m35]; exact w34_d4
  have w35_d8 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m35]; exact w34_d8
  have w35_dc : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m35]; exact w34_dc
  have w35_e0 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m35]; exact w34_e0
  have w35_e4 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m35]; exact w34_e4
  have w35_e8 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m35]; exact w34_e8
  have w35_ec : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m35]; exact w34_ec
  have w35_f0 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m35]; exact w34_f0
  have w35_f4 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m35]; exact w34_f4
  have w35_f8 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m35]; exact w34_f8
  have w35_fc : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m35]; exact w34_fc
  have w35_100 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m35]; exact w34_100
  have w35_104 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m35]; exact w34_104
  have w35_108 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m35]; exact w34_108
  have w35_10c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m35]; exact w34_10c
  have w35_110 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m35]; exact w34_110
  have w35_114 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m35]; exact w34_114
  have w35_118 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m35]; exact w34_118
  have w35_11c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m35]; exact w34_11c
  have w35_120 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m35]; exact w34_120
  have w35_124 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m35]; exact w34_124
  have w35_128 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m35]; exact w34_128
  have w35_12c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m35]; exact w34_12c
  have w35_130 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m35]; exact w34_130
  have b35_a40 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = gs := by rw [m35]; exact b34_a40
  have b35_1040 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = gs := by rw [m35]; exact b34_1040
  have b35_14a0 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := by rw [m35]; exact b34_14a0
  have q35_420 : ∀ j, j < 96 → n35.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m35]; exact q34_420 j hj
  have q35_480 : ∀ j, j < 96 → n35.mem (B + 0x21A0 + BitVec.ofNat 32 (0x480 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m35]; exact q34_480 j hj
  have q35_4e0 : ∀ j, j < 96 → n35.mem (B + 0x21A0 + BitVec.ofNat 32 (0x4E0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m35]; exact q34_4e0 j hj
  have q35_540 : ∀ j, j < 96 → n35.mem (B + 0x21A0 + BitVec.ofNat 32 (0x540 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m35]; exact q34_540 j hj
  have q35_5a0 : ∀ j, j < 96 → n35.mem (B + 0x21A0 + BitVec.ofNat 32 (0x5A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m35]; exact q34_5a0 j hj
  have q35_600 : ∀ j, j < 96 → n35.mem (B + 0x21A0 + BitVec.ofNat 32 (0x600 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m35]; exact q34_600 j hj
  have q35_660 : ∀ j, j < 96 → n35.mem (B + 0x21A0 + BitVec.ofNat 32 (0x660 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m35]; exact q34_660 j hj
  have q35_6c0 : ∀ j, j < 96 → n35.mem (B + 0x21A0 + BitVec.ofNat 32 (0x6C0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m35]; exact q34_6c0 j hj
  have a35_240 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m35]; exact a34_240
  have a35_260 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m35]; exact a34_260
  have a35_280 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m35]; exact a34_280
  have a35_2a0 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m35]; exact a34_2a0
  have a35_2c0 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m35]; exact a34_2c0
  have a35_2e0 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m35]; exact a34_2e0
  have a35_380 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m35]; exact a34_380
  have a35_400 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m35]; exact a34_400
  have a35_13e0 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U2 := by rw [m35]; exact a34_13e0
  have a35_14e0 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x14E0) 8 = U1 := by rw [m35]; exact a34_14e0
  have a35_1560 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x1560) 8 = U2 := by rw [m35]; exact a34_1560
  have p35_320 : ptF n35.mem B 0x320 = P0 := by rw [m35]; exact p34_320
  have p35_3a0 : ptF n35.mem B 0x3A0 = P1 := by rw [m35]; exact p34_3a0
  have p35_a20 : ptF n35.mem B 0xA20 = tbl2 P0 0 := by rw [m35]; exact p34_a20
  have p35_a80 : ptF n35.mem B 0xA80 = tbl2 P0 1 := by rw [m35]; exact p34_a80
  have p35_ae0 : ptF n35.mem B 0xAE0 = tbl2 P0 2 := by rw [m35]; exact p34_ae0
  have p35_b40 : ptF n35.mem B 0xB40 = tbl2 P0 3 := by rw [m35]; exact p34_b40
  have p35_ba0 : ptF n35.mem B 0xBA0 = tbl2 P0 4 := by rw [m35]; exact p34_ba0
  have p35_c00 : ptF n35.mem B 0xC00 = tbl2 P0 5 := by rw [m35]; exact p34_c00
  have p35_c60 : ptF n35.mem B 0xC60 = tbl2 P0 6 := by rw [m35]; exact p34_c60
  have p35_cc0 : ptF n35.mem B 0xCC0 = tbl2 P0 7 := by rw [m35]; exact p34_cc0
  have p35_1020 : ptF n35.mem B 0x1020 = tbl2 P0 0 := by rw [m35]; exact p34_1020
  have p35_1080 : ptF n35.mem B 0x1080 = tbl2 P0 1 := by rw [m35]; exact p34_1080
  have p35_10e0 : ptF n35.mem B 0x10E0 = tbl2 P0 2 := by rw [m35]; exact p34_10e0
  have p35_1140 : ptF n35.mem B 0x1140 = tbl2 P0 3 := by rw [m35]; exact p34_1140
  have p35_11a0 : ptF n35.mem B 0x11A0 = tbl2 P0 4 := by rw [m35]; exact p34_11a0
  have p35_1200 : ptF n35.mem B 0x1200 = tbl2 P0 5 := by rw [m35]; exact p34_1200
  have p35_1260 : ptF n35.mem B 0x1260 = tbl2 P0 6 := by rw [m35]; exact p34_1260
  have p35_12c0 : ptF n35.mem B 0x12C0 = tbl2 P0 7 := by rw [m35]; exact p34_12c0
  have p35_1320 : ptF n35.mem B 0x1320 = ptDbl2 P0 := by rw [m35]; exact p34_1320
  have p35_1380 : ptF n35.mem B 0x1380 = P1 := by rw [m35]; exact p34_1380
  have p35_1480 : ptF n35.mem B 0x1480 = P0 := by rw [m35]; exact p34_1480
  have p35_1500 : ptF n35.mem B 0x1500 = P1 := by rw [m35]; exact p34_1500
  clear q34_6c0 p34_1500 p34_1480 p34_1380 p34_1320 p34_12c0 p34_1260 p34_1200 p34_11a0 p34_1140 p34_10e0 p34_1080 p34_1020 p34_cc0 p34_c60 p34_c00 p34_ba0 p34_b40 p34_ae0 p34_a80 p34_a20 p34_3a0 p34_320 a34_1560 a34_14e0 a34_13e0 a34_400 a34_380 a34_2e0 a34_2c0 a34_2a0 a34_280 a34_260 a34_240 q34_660 q34_600 q34_5a0 q34_540 q34_4e0 q34_480 q34_420 b34_14a0 b34_1040 b34_a40 w34_130 w34_12c w34_128 w34_124 w34_120 w34_11c w34_118 w34_114 w34_110 w34_10c w34_108 w34_104 w34_100 w34_fc w34_f8 w34_f4 w34_f0 w34_ec w34_e8 w34_e4 w34_e0 w34_dc w34_d8 w34_d4 w34_d0 w34_cc w34_c8 w34_c4 w34_c0 w34_bc w34_b8 w34_b4 w34_b0 w34_ac w34_a8 w34_a4 w34_a0 w34_9c w34_98 w34_94 w34_90 w34_8c w34_88 w34_84 w34_80 w34_7c w34_78 w34_70 w34_6c w34_68 w34_64 w34_60 w34_5c w34_58 w34_54 w34_50 w34_4c w34_48 w34_44 w34_40 w34_3c w34_38 w34_34 w34_30 w34_2c w34_28 w34_24 g34_27 g34_26 g34_25 g34_24 g34_23 g34_22 g34_21 g34_20 g34_19 g34_18 g34_9 g34_8 g34_4 g34_3 g34_2 V34 E34 fR34 t34 fr34 s34 X34 K34 P34
  -- 0x16C8: branch, not taken
  obtain ⟨n36, d36, u36⟩ := s35.notTaken E35.self 0x16CA sv_at_16c8
    (by decide) (by rw [g35_9, s35.zero]; decide)
  have s36 : St n36.mem SV n36 0x16CA (reg n36) := ⟨u36.pc, rfl, fun _ => rfl⟩
  have m36 : n36.mem = n35.mem := u36.mem
  have fr36 : ∀ x, SvR B x → n36.mem x = n35.mem x := fun x _ => by rw [m36]
  have t36 : Steps n0 n36 := t35.trans (.single d36)
  have fR36 : ∀ x, SvR B x → n36.mem x = M0 x := fun x hx => (fr36 x hx).trans (fR35 x hx)
  have E36 : SvCode n36.mem := E35.fr F fr36
  have V36 : SvSaves B n36.mem v := V35.same m36
  have g36_2 : reg n36 sp = B + 0x21A0 := by rw [u36.regs, g35_2]
  have g36_3 : reg n36 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u36.regs, g35_3]
  have g36_4 : reg n36 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u36.regs, g35_4]
  have g36_8 : reg n36 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x720 := by rw [u36.regs, g35_8]
  have g36_9 : reg n36 (9 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u36.regs, g35_9]
  have g36_18 : reg n36 (18 : Fin 32) = out := by rw [u36.regs, g35_18]
  have g36_19 : reg n36 (19 : Fin 32) = bp := by rw [u36.regs, g35_19]
  have g36_20 : reg n36 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u36.regs, g35_20]
  have g36_21 : reg n36 (21 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u36.regs, g35_21]
  have g36_22 : reg n36 (22 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [u36.regs, g35_22]
  have g36_23 : reg n36 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1500 := by rw [u36.regs, g35_23]
  have g36_24 : reg n36 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u36.regs, g35_24]
  have g36_25 : reg n36 (25 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [u36.regs, g35_25]
  have g36_26 : reg n36 (26 : Fin 32) = x26 := by rw [u36.regs, g35_26]
  have g36_27 : reg n36 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u36.regs, g35_27]
  have keep_kk36 : SvKeepL B n0.mem n36.mem [(0x1380, 0x80), (0x420, 0x60), (0x480, 0x60), (0x4E0, 0x60), (0x540, 0x60), (0x5A0, 0x60), (0x600, 0x60), (0x660, 0x60), (0x6C0, 0x60)] := by rw [m36]; exact keep_kk35
  clear keep_kk35
  have w36_24 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m36]; exact w35_24
  have w36_28 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m36]; exact w35_28
  have w36_2c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m36]; exact w35_2c
  have w36_30 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m36]; exact w35_30
  have w36_34 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m36]; exact w35_34
  have w36_38 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m36]; exact w35_38
  have w36_3c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m36]; exact w35_3c
  have w36_40 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m36]; exact w35_40
  have w36_44 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m36]; exact w35_44
  have w36_48 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m36]; exact w35_48
  have w36_4c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m36]; exact w35_4c
  have w36_50 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m36]; exact w35_50
  have w36_54 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m36]; exact w35_54
  have w36_58 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m36]; exact w35_58
  have w36_5c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m36]; exact w35_5c
  have w36_60 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m36]; exact w35_60
  have w36_64 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m36]; exact w35_64
  have w36_68 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m36]; exact w35_68
  have w36_6c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m36]; exact w35_6c
  have w36_70 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m36]; exact w35_70
  have w36_78 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m36]; exact w35_78
  have w36_7c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m36]; exact w35_7c
  have w36_80 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m36]; exact w35_80
  have w36_84 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m36]; exact w35_84
  have w36_88 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m36]; exact w35_88
  have w36_8c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m36]; exact w35_8c
  have w36_90 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m36]; exact w35_90
  have w36_94 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m36]; exact w35_94
  have w36_98 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m36]; exact w35_98
  have w36_9c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m36]; exact w35_9c
  have w36_a0 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m36]; exact w35_a0
  have w36_a4 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m36]; exact w35_a4
  have w36_a8 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m36]; exact w35_a8
  have w36_ac : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m36]; exact w35_ac
  have w36_b0 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m36]; exact w35_b0
  have w36_b4 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m36]; exact w35_b4
  have w36_b8 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m36]; exact w35_b8
  have w36_bc : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m36]; exact w35_bc
  have w36_c0 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m36]; exact w35_c0
  have w36_c4 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m36]; exact w35_c4
  have w36_c8 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m36]; exact w35_c8
  have w36_cc : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m36]; exact w35_cc
  have w36_d0 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m36]; exact w35_d0
  have w36_d4 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m36]; exact w35_d4
  have w36_d8 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m36]; exact w35_d8
  have w36_dc : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m36]; exact w35_dc
  have w36_e0 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m36]; exact w35_e0
  have w36_e4 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m36]; exact w35_e4
  have w36_e8 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m36]; exact w35_e8
  have w36_ec : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m36]; exact w35_ec
  have w36_f0 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m36]; exact w35_f0
  have w36_f4 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m36]; exact w35_f4
  have w36_f8 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m36]; exact w35_f8
  have w36_fc : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m36]; exact w35_fc
  have w36_100 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m36]; exact w35_100
  have w36_104 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m36]; exact w35_104
  have w36_108 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m36]; exact w35_108
  have w36_10c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m36]; exact w35_10c
  have w36_110 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m36]; exact w35_110
  have w36_114 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m36]; exact w35_114
  have w36_118 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m36]; exact w35_118
  have w36_11c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m36]; exact w35_11c
  have w36_120 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m36]; exact w35_120
  have w36_124 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m36]; exact w35_124
  have w36_128 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m36]; exact w35_128
  have w36_12c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m36]; exact w35_12c
  have w36_130 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m36]; exact w35_130
  have b36_a40 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = gs := by rw [m36]; exact b35_a40
  have b36_1040 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = gs := by rw [m36]; exact b35_1040
  have b36_14a0 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := by rw [m36]; exact b35_14a0
  have q36_420 : ∀ j, j < 96 → n36.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m36]; exact q35_420 j hj
  have q36_480 : ∀ j, j < 96 → n36.mem (B + 0x21A0 + BitVec.ofNat 32 (0x480 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m36]; exact q35_480 j hj
  have q36_4e0 : ∀ j, j < 96 → n36.mem (B + 0x21A0 + BitVec.ofNat 32 (0x4E0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m36]; exact q35_4e0 j hj
  have q36_540 : ∀ j, j < 96 → n36.mem (B + 0x21A0 + BitVec.ofNat 32 (0x540 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m36]; exact q35_540 j hj
  have q36_5a0 : ∀ j, j < 96 → n36.mem (B + 0x21A0 + BitVec.ofNat 32 (0x5A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m36]; exact q35_5a0 j hj
  have q36_600 : ∀ j, j < 96 → n36.mem (B + 0x21A0 + BitVec.ofNat 32 (0x600 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m36]; exact q35_600 j hj
  have q36_660 : ∀ j, j < 96 → n36.mem (B + 0x21A0 + BitVec.ofNat 32 (0x660 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m36]; exact q35_660 j hj
  have q36_6c0 : ∀ j, j < 96 → n36.mem (B + 0x21A0 + BitVec.ofNat 32 (0x6C0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m36]; exact q35_6c0 j hj
  have a36_240 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m36]; exact a35_240
  have a36_260 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m36]; exact a35_260
  have a36_280 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m36]; exact a35_280
  have a36_2a0 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m36]; exact a35_2a0
  have a36_2c0 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m36]; exact a35_2c0
  have a36_2e0 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m36]; exact a35_2e0
  have a36_380 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m36]; exact a35_380
  have a36_400 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m36]; exact a35_400
  have a36_13e0 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U2 := by rw [m36]; exact a35_13e0
  have a36_14e0 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x14E0) 8 = U1 := by rw [m36]; exact a35_14e0
  have a36_1560 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x1560) 8 = U2 := by rw [m36]; exact a35_1560
  have p36_320 : ptF n36.mem B 0x320 = P0 := by rw [m36]; exact p35_320
  have p36_3a0 : ptF n36.mem B 0x3A0 = P1 := by rw [m36]; exact p35_3a0
  have p36_a20 : ptF n36.mem B 0xA20 = tbl2 P0 0 := by rw [m36]; exact p35_a20
  have p36_a80 : ptF n36.mem B 0xA80 = tbl2 P0 1 := by rw [m36]; exact p35_a80
  have p36_ae0 : ptF n36.mem B 0xAE0 = tbl2 P0 2 := by rw [m36]; exact p35_ae0
  have p36_b40 : ptF n36.mem B 0xB40 = tbl2 P0 3 := by rw [m36]; exact p35_b40
  have p36_ba0 : ptF n36.mem B 0xBA0 = tbl2 P0 4 := by rw [m36]; exact p35_ba0
  have p36_c00 : ptF n36.mem B 0xC00 = tbl2 P0 5 := by rw [m36]; exact p35_c00
  have p36_c60 : ptF n36.mem B 0xC60 = tbl2 P0 6 := by rw [m36]; exact p35_c60
  have p36_cc0 : ptF n36.mem B 0xCC0 = tbl2 P0 7 := by rw [m36]; exact p35_cc0
  have p36_1020 : ptF n36.mem B 0x1020 = tbl2 P0 0 := by rw [m36]; exact p35_1020
  have p36_1080 : ptF n36.mem B 0x1080 = tbl2 P0 1 := by rw [m36]; exact p35_1080
  have p36_10e0 : ptF n36.mem B 0x10E0 = tbl2 P0 2 := by rw [m36]; exact p35_10e0
  have p36_1140 : ptF n36.mem B 0x1140 = tbl2 P0 3 := by rw [m36]; exact p35_1140
  have p36_11a0 : ptF n36.mem B 0x11A0 = tbl2 P0 4 := by rw [m36]; exact p35_11a0
  have p36_1200 : ptF n36.mem B 0x1200 = tbl2 P0 5 := by rw [m36]; exact p35_1200
  have p36_1260 : ptF n36.mem B 0x1260 = tbl2 P0 6 := by rw [m36]; exact p35_1260
  have p36_12c0 : ptF n36.mem B 0x12C0 = tbl2 P0 7 := by rw [m36]; exact p35_12c0
  have p36_1320 : ptF n36.mem B 0x1320 = ptDbl2 P0 := by rw [m36]; exact p35_1320
  have p36_1380 : ptF n36.mem B 0x1380 = P1 := by rw [m36]; exact p35_1380
  have p36_1480 : ptF n36.mem B 0x1480 = P0 := by rw [m36]; exact p35_1480
  have p36_1500 : ptF n36.mem B 0x1500 = P1 := by rw [m36]; exact p35_1500
  clear p35_1500 p35_1480 p35_1380 p35_1320 p35_12c0 p35_1260 p35_1200 p35_11a0 p35_1140 p35_10e0 p35_1080 p35_1020 p35_cc0 p35_c60 p35_c00 p35_ba0 p35_b40 p35_ae0 p35_a80 p35_a20 p35_3a0 p35_320 a35_1560 a35_14e0 a35_13e0 a35_400 a35_380 a35_2e0 a35_2c0 a35_2a0 a35_280 a35_260 a35_240 q35_6c0 q35_660 q35_600 q35_5a0 q35_540 q35_4e0 q35_480 q35_420 b35_14a0 b35_1040 b35_a40 w35_130 w35_12c w35_128 w35_124 w35_120 w35_11c w35_118 w35_114 w35_110 w35_10c w35_108 w35_104 w35_100 w35_fc w35_f8 w35_f4 w35_f0 w35_ec w35_e8 w35_e4 w35_e0 w35_dc w35_d8 w35_d4 w35_d0 w35_cc w35_c8 w35_c4 w35_c0 w35_bc w35_b8 w35_b4 w35_b0 w35_ac w35_a8 w35_a4 w35_a0 w35_9c w35_98 w35_94 w35_90 w35_8c w35_88 w35_84 w35_80 w35_7c w35_78 w35_70 w35_6c w35_68 w35_64 w35_60 w35_5c w35_58 w35_54 w35_50 w35_4c w35_48 w35_44 w35_40 w35_3c w35_38 w35_34 w35_30 w35_2c w35_28 w35_24 g35_9 g35_8 g35_27 g35_26 g35_25 g35_24 g35_23 g35_22 g35_21 g35_20 g35_19 g35_18 g35_4 g35_3 g35_2 V35 E35 fR35 t35 fr35 rb35 s35 m35 u35 c35
  -- 0x16CA
  obtain ⟨n37, c37, u37⟩ := s36.block svEcT1a16ca E36.self svEcT1a16ca_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m37 : n37.mem = n36.mem := u37.mem
  have s37 : St n37.mem SV n37 0x16E8 (reg n37) := ⟨u37.pc, rfl, fun _ => rfl⟩
  have rb37 : ∀ q, reg n37 q = (runBlock svEcT1a16ca (n36.mem, reg n36)).2 q := fun q => by rw [u37.regs]
  have fr37 : ∀ x, SvR B x → n37.mem x = n36.mem x := fun x _ => by rw [m37]
  have t37 : Steps n0 n37 := t36.trans c37
  have fR37 : ∀ x, SvR B x → n37.mem x = M0 x := fun x hx => (fr37 x hx).trans (fR36 x hx)
  have E37 : SvCode n37.mem := E36.fr F fr37
  have V37 : SvSaves B n37.mem v := V36.same m37
  have g37_2 : reg n37 sp = B + 0x21A0 := by
    rw [rb37, runBlock_reg _ _ _ sp s36.zero (by decide), g36_2]
  have g37_3 : reg n37 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb37, runBlock_reg _ _ _ (3 : Fin 32) s36.zero (by decide), g36_3]
  have g37_4 : reg n37 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb37, runBlock_reg _ _ _ (4 : Fin 32) s36.zero (by decide), g36_4]
  have g37_18 : reg n37 (18 : Fin 32) = out := by
    rw [rb37, runBlock_reg _ _ _ (18 : Fin 32) s36.zero (by decide), g36_18]
  have g37_19 : reg n37 (19 : Fin 32) = bp := by
    rw [rb37, runBlock_reg _ _ _ (19 : Fin 32) s36.zero (by decide), g36_19]
  have g37_20 : reg n37 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb37, runBlock_reg _ _ _ (20 : Fin 32) s36.zero (by decide), g36_20]
  have g37_21 : reg n37 (21 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb37, runBlock_reg _ _ _ (21 : Fin 32) s36.zero (by decide), g36_21]
  have g37_22 : reg n37 (22 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by
    rw [rb37, runBlock_reg _ _ _ (22 : Fin 32) s36.zero (by decide), g36_22]
  have g37_23 : reg n37 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1500 := by
    rw [rb37, runBlock_reg _ _ _ (23 : Fin 32) s36.zero (by decide), g36_23]
  have g37_24 : reg n37 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb37, runBlock_reg _ _ _ (24 : Fin 32) s36.zero (by decide), g36_24]
  have g37_25 : reg n37 (25 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb37, runBlock_reg _ _ _ (25 : Fin 32) s36.zero (by decide), g36_25]
  have g37_26 : reg n37 (26 : Fin 32) = x26 := by
    rw [rb37, runBlock_reg _ _ _ (26 : Fin 32) s36.zero (by decide), g36_26]
  have g37_27 : reg n37 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb37, runBlock_reg _ _ _ (27 : Fin 32) s36.zero (by decide), g36_27]
  have g37_8 : reg n37 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1020 := by
    rw [rb37]; simp +decide only [runBlock, BInstr.run, svEcT1a16ca, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g36_2, g36_3, g36_4, g36_8, g36_9, g36_18, g36_19, g36_20, g36_21, g36_22, g36_23, g36_24, g36_25, g36_26, g36_27, s36.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g37_9 : reg n37 (9 : Fin 32) = BitVec.ofNat 32 0x300 := by
    rw [rb37]; simp +decide only [runBlock, BInstr.run, svEcT1a16ca, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g36_2, g36_3, g36_4, g36_8, g36_9, g36_18, g36_19, g36_20, g36_21, g36_22, g36_23, g36_24, g36_25, g36_26, g36_27, s36.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g37_10 : reg n37 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1020 := by
    rw [rb37]; simp +decide only [runBlock, BInstr.run, svEcT1a16ca, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g36_2, g36_3, g36_4, g36_8, g36_9, g36_18, g36_19, g36_20, g36_21, g36_22, g36_23, g36_24, g36_25, g36_26, g36_27, s36.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g37_11 : reg n37 a1 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb37]; simp +decide only [runBlock, BInstr.run, svEcT1a16ca, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g36_2, g36_3, g36_4, g36_8, g36_9, g36_18, g36_19, g36_20, g36_21, g36_22, g36_23, g36_24, g36_25, g36_26, g36_27, s36.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g37_12 : reg n37 a2 = BitVec.ofNat 32 0x300 := by
    rw [rb37]; simp +decide only [runBlock, BInstr.run, svEcT1a16ca, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g36_2, g36_3, g36_4, g36_8, g36_9, g36_18, g36_19, g36_20, g36_21, g36_22, g36_23, g36_24, g36_25, g36_26, g36_27, s36.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g37_13 : reg n37 a3 = BitVec.ofNat 32 0x1020 := by
    rw [rb37]; simp +decide only [runBlock, BInstr.run, svEcT1a16ca, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g36_2, g36_3, g36_4, g36_8, g36_9, g36_18, g36_19, g36_20, g36_21, g36_22, g36_23, g36_24, g36_25, g36_26, g36_27, s36.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk37 : SvKeepL B n0.mem n37.mem [(0x1380, 0x80), (0x420, 0x60), (0x480, 0x60), (0x4E0, 0x60), (0x540, 0x60), (0x5A0, 0x60), (0x600, 0x60), (0x660, 0x60), (0x6C0, 0x60)] := by rw [m37]; exact keep_kk36
  clear keep_kk36
  have w37_24 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m37]; exact w36_24
  have w37_28 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m37]; exact w36_28
  have w37_2c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m37]; exact w36_2c
  have w37_30 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m37]; exact w36_30
  have w37_34 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m37]; exact w36_34
  have w37_38 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m37]; exact w36_38
  have w37_3c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m37]; exact w36_3c
  have w37_40 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m37]; exact w36_40
  have w37_44 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m37]; exact w36_44
  have w37_48 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m37]; exact w36_48
  have w37_4c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m37]; exact w36_4c
  have w37_50 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m37]; exact w36_50
  have w37_54 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m37]; exact w36_54
  have w37_58 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m37]; exact w36_58
  have w37_5c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m37]; exact w36_5c
  have w37_60 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m37]; exact w36_60
  have w37_64 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m37]; exact w36_64
  have w37_68 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m37]; exact w36_68
  have w37_6c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m37]; exact w36_6c
  have w37_70 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m37]; exact w36_70
  have w37_78 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m37]; exact w36_78
  have w37_7c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m37]; exact w36_7c
  have w37_80 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m37]; exact w36_80
  have w37_84 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m37]; exact w36_84
  have w37_88 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m37]; exact w36_88
  have w37_8c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m37]; exact w36_8c
  have w37_90 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m37]; exact w36_90
  have w37_94 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m37]; exact w36_94
  have w37_98 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m37]; exact w36_98
  have w37_9c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m37]; exact w36_9c
  have w37_a0 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m37]; exact w36_a0
  have w37_a4 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m37]; exact w36_a4
  have w37_a8 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m37]; exact w36_a8
  have w37_ac : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m37]; exact w36_ac
  have w37_b0 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m37]; exact w36_b0
  have w37_b4 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m37]; exact w36_b4
  have w37_b8 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m37]; exact w36_b8
  have w37_bc : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m37]; exact w36_bc
  have w37_c0 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m37]; exact w36_c0
  have w37_c4 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m37]; exact w36_c4
  have w37_c8 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m37]; exact w36_c8
  have w37_cc : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m37]; exact w36_cc
  have w37_d0 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m37]; exact w36_d0
  have w37_d4 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m37]; exact w36_d4
  have w37_d8 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m37]; exact w36_d8
  have w37_dc : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m37]; exact w36_dc
  have w37_e0 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m37]; exact w36_e0
  have w37_e4 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m37]; exact w36_e4
  have w37_e8 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m37]; exact w36_e8
  have w37_ec : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m37]; exact w36_ec
  have w37_f0 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m37]; exact w36_f0
  have w37_f4 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m37]; exact w36_f4
  have w37_f8 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m37]; exact w36_f8
  have w37_fc : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m37]; exact w36_fc
  have w37_100 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m37]; exact w36_100
  have w37_104 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m37]; exact w36_104
  have w37_108 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m37]; exact w36_108
  have w37_10c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m37]; exact w36_10c
  have w37_110 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m37]; exact w36_110
  have w37_114 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m37]; exact w36_114
  have w37_118 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m37]; exact w36_118
  have w37_11c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m37]; exact w36_11c
  have w37_120 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m37]; exact w36_120
  have w37_124 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m37]; exact w36_124
  have w37_128 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m37]; exact w36_128
  have w37_12c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m37]; exact w36_12c
  have w37_130 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m37]; exact w36_130
  have b37_a40 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = gs := by rw [m37]; exact b36_a40
  have b37_1040 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = gs := by rw [m37]; exact b36_1040
  have b37_14a0 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := by rw [m37]; exact b36_14a0
  have q37_420 : ∀ j, j < 96 → n37.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m37]; exact q36_420 j hj
  have q37_480 : ∀ j, j < 96 → n37.mem (B + 0x21A0 + BitVec.ofNat 32 (0x480 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m37]; exact q36_480 j hj
  have q37_4e0 : ∀ j, j < 96 → n37.mem (B + 0x21A0 + BitVec.ofNat 32 (0x4E0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m37]; exact q36_4e0 j hj
  have q37_540 : ∀ j, j < 96 → n37.mem (B + 0x21A0 + BitVec.ofNat 32 (0x540 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m37]; exact q36_540 j hj
  have q37_5a0 : ∀ j, j < 96 → n37.mem (B + 0x21A0 + BitVec.ofNat 32 (0x5A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m37]; exact q36_5a0 j hj
  have q37_600 : ∀ j, j < 96 → n37.mem (B + 0x21A0 + BitVec.ofNat 32 (0x600 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m37]; exact q36_600 j hj
  have q37_660 : ∀ j, j < 96 → n37.mem (B + 0x21A0 + BitVec.ofNat 32 (0x660 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m37]; exact q36_660 j hj
  have q37_6c0 : ∀ j, j < 96 → n37.mem (B + 0x21A0 + BitVec.ofNat 32 (0x6C0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by rw [m37]; exact q36_6c0 j hj
  have a37_240 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m37]; exact a36_240
  have a37_260 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m37]; exact a36_260
  have a37_280 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m37]; exact a36_280
  have a37_2a0 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m37]; exact a36_2a0
  have a37_2c0 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m37]; exact a36_2c0
  have a37_2e0 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m37]; exact a36_2e0
  have a37_380 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m37]; exact a36_380
  have a37_400 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m37]; exact a36_400
  have a37_13e0 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U2 := by rw [m37]; exact a36_13e0
  have a37_14e0 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x14E0) 8 = U1 := by rw [m37]; exact a36_14e0
  have a37_1560 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x1560) 8 = U2 := by rw [m37]; exact a36_1560
  have p37_320 : ptF n37.mem B 0x320 = P0 := by rw [m37]; exact p36_320
  have p37_3a0 : ptF n37.mem B 0x3A0 = P1 := by rw [m37]; exact p36_3a0
  have p37_a20 : ptF n37.mem B 0xA20 = tbl2 P0 0 := by rw [m37]; exact p36_a20
  have p37_a80 : ptF n37.mem B 0xA80 = tbl2 P0 1 := by rw [m37]; exact p36_a80
  have p37_ae0 : ptF n37.mem B 0xAE0 = tbl2 P0 2 := by rw [m37]; exact p36_ae0
  have p37_b40 : ptF n37.mem B 0xB40 = tbl2 P0 3 := by rw [m37]; exact p36_b40
  have p37_ba0 : ptF n37.mem B 0xBA0 = tbl2 P0 4 := by rw [m37]; exact p36_ba0
  have p37_c00 : ptF n37.mem B 0xC00 = tbl2 P0 5 := by rw [m37]; exact p36_c00
  have p37_c60 : ptF n37.mem B 0xC60 = tbl2 P0 6 := by rw [m37]; exact p36_c60
  have p37_cc0 : ptF n37.mem B 0xCC0 = tbl2 P0 7 := by rw [m37]; exact p36_cc0
  have p37_1020 : ptF n37.mem B 0x1020 = tbl2 P0 0 := by rw [m37]; exact p36_1020
  have p37_1080 : ptF n37.mem B 0x1080 = tbl2 P0 1 := by rw [m37]; exact p36_1080
  have p37_10e0 : ptF n37.mem B 0x10E0 = tbl2 P0 2 := by rw [m37]; exact p36_10e0
  have p37_1140 : ptF n37.mem B 0x1140 = tbl2 P0 3 := by rw [m37]; exact p36_1140
  have p37_11a0 : ptF n37.mem B 0x11A0 = tbl2 P0 4 := by rw [m37]; exact p36_11a0
  have p37_1200 : ptF n37.mem B 0x1200 = tbl2 P0 5 := by rw [m37]; exact p36_1200
  have p37_1260 : ptF n37.mem B 0x1260 = tbl2 P0 6 := by rw [m37]; exact p36_1260
  have p37_12c0 : ptF n37.mem B 0x12C0 = tbl2 P0 7 := by rw [m37]; exact p36_12c0
  have p37_1320 : ptF n37.mem B 0x1320 = ptDbl2 P0 := by rw [m37]; exact p36_1320
  have p37_1380 : ptF n37.mem B 0x1380 = P1 := by rw [m37]; exact p36_1380
  have p37_1480 : ptF n37.mem B 0x1480 = P0 := by rw [m37]; exact p36_1480
  have p37_1500 : ptF n37.mem B 0x1500 = P1 := by rw [m37]; exact p36_1500
  clear p36_1500 p36_1480 p36_1380 p36_1320 p36_12c0 p36_1260 p36_1200 p36_11a0 p36_1140 p36_10e0 p36_1080 p36_1020 p36_cc0 p36_c60 p36_c00 p36_ba0 p36_b40 p36_ae0 p36_a80 p36_a20 p36_3a0 p36_320 a36_1560 a36_14e0 a36_13e0 a36_400 a36_380 a36_2e0 a36_2c0 a36_2a0 a36_280 a36_260 a36_240 q36_6c0 q36_660 q36_600 q36_5a0 q36_540 q36_4e0 q36_480 q36_420 b36_14a0 b36_1040 b36_a40 w36_130 w36_12c w36_128 w36_124 w36_120 w36_11c w36_118 w36_114 w36_110 w36_10c w36_108 w36_104 w36_100 w36_fc w36_f8 w36_f4 w36_f0 w36_ec w36_e8 w36_e4 w36_e0 w36_dc w36_d8 w36_d4 w36_d0 w36_cc w36_c8 w36_c4 w36_c0 w36_bc w36_b8 w36_b4 w36_b0 w36_ac w36_a8 w36_a4 w36_a0 w36_9c w36_98 w36_94 w36_90 w36_8c w36_88 w36_84 w36_80 w36_7c w36_78 w36_70 w36_6c w36_68 w36_64 w36_60 w36_5c w36_58 w36_54 w36_50 w36_4c w36_48 w36_44 w36_40 w36_3c w36_38 w36_34 w36_30 w36_2c w36_28 w36_24 g36_27 g36_26 g36_25 g36_24 g36_23 g36_22 g36_21 g36_20 g36_19 g36_18 g36_9 g36_8 g36_4 g36_3 g36_2 V36 E36 fR36 t36 fr36 m36 s36 u36 d36
  -- 0x16E8: memcpy
  obtain ⟨n38, P38, K38, X38⟩ := sv_mc (c := 0x1020) (d := 0x420) (N := 0x300) F E37 s37 sv_at_16e8 sv_at_16ec
    (by decide) (by decide) g37_2 g37_10 g37_11 g37_12
    (by decide) (by decide) (by decide)
  have s38 := P38.st
  have fr38 := P38.fr
  have t38 : Steps n0 n38 := t37.trans P38.steps
  have fR38 : ∀ x, SvR B x → n38.mem x = M0 x := fun x hx => (fr38 x hx).trans (fR37 x hx)
  have E38 : SvCode n38.mem := E37.fr F fr38
  have V38 : SvSaves B n38.mem v := V37.keep K38 (by decide)
  have g38_2 : reg n38 sp = B + 0x21A0 := by rw [P38.regs sp (by decide), g37_2]
  have g38_3 : reg n38 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P38.regs (3 : Fin 32) (by decide), g37_3]
  have g38_4 : reg n38 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P38.regs (4 : Fin 32) (by decide), g37_4]
  have g38_8 : reg n38 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1020 := by rw [P38.regs (8 : Fin 32) (by decide), g37_8]
  have g38_9 : reg n38 (9 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [P38.regs (9 : Fin 32) (by decide), g37_9]
  have g38_18 : reg n38 (18 : Fin 32) = out := by rw [P38.regs (18 : Fin 32) (by decide), g37_18]
  have g38_19 : reg n38 (19 : Fin 32) = bp := by rw [P38.regs (19 : Fin 32) (by decide), g37_19]
  have g38_20 : reg n38 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P38.regs (20 : Fin 32) (by decide), g37_20]
  have g38_21 : reg n38 (21 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P38.regs (21 : Fin 32) (by decide), g37_21]
  have g38_22 : reg n38 (22 : Fin 32) = BitVec.ofNat 32 (img% p256GMontAddress) := by rw [P38.regs (22 : Fin 32) (by decide), g37_22]
  have g38_23 : reg n38 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1500 := by rw [P38.regs (23 : Fin 32) (by decide), g37_23]
  have g38_24 : reg n38 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P38.regs (24 : Fin 32) (by decide), g37_24]
  have g38_25 : reg n38 (25 : Fin 32) = BitVec.ofNat 32 0x300 := by rw [P38.regs (25 : Fin 32) (by decide), g37_25]
  have g38_26 : reg n38 (26 : Fin 32) = x26 := by rw [P38.regs (26 : Fin 32) (by decide), g37_26]
  have g38_27 : reg n38 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P38.regs (27 : Fin 32) (by decide), g37_27]
  have keep_kk38 : SvKeepL B n0.mem n38.mem [(0x1380, 0x80), (0x420, 0x60), (0x480, 0x60), (0x4E0, 0x60), (0x540, 0x60), (0x5A0, 0x60), (0x600, 0x60), (0x660, 0x60), (0x6C0, 0x60), (0x1020, 0x300)] := keep_kk37.trans K38.toL
  clear keep_kk37
  have w38_24 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K38.w32 (by decide) (by decide)).trans w37_24
  have w38_28 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K38.w32 (by decide) (by decide)).trans w37_28
  have w38_2c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K38.w32 (by decide) (by decide)).trans w37_2c
  have w38_30 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K38.w32 (by decide) (by decide)).trans w37_30
  have w38_34 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K38.w32 (by decide) (by decide)).trans w37_34
  have w38_38 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K38.w32 (by decide) (by decide)).trans w37_38
  have w38_3c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K38.w32 (by decide) (by decide)).trans w37_3c
  have w38_40 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K38.w32 (by decide) (by decide)).trans w37_40
  have w38_44 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K38.w32 (by decide) (by decide)).trans w37_44
  have w38_48 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K38.w32 (by decide) (by decide)).trans w37_48
  have w38_4c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K38.w32 (by decide) (by decide)).trans w37_4c
  have w38_50 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K38.w32 (by decide) (by decide)).trans w37_50
  have w38_54 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K38.w32 (by decide) (by decide)).trans w37_54
  have w38_58 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K38.w32 (by decide) (by decide)).trans w37_58
  have w38_5c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K38.w32 (by decide) (by decide)).trans w37_5c
  have w38_60 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K38.w32 (by decide) (by decide)).trans w37_60
  have w38_64 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K38.w32 (by decide) (by decide)).trans w37_64
  have w38_68 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K38.w32 (by decide) (by decide)).trans w37_68
  have w38_6c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K38.w32 (by decide) (by decide)).trans w37_6c
  have w38_70 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K38.w32 (by decide) (by decide)).trans w37_70
  have w38_78 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := (K38.w32 (by decide) (by decide)).trans w37_78
  have w38_7c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K38.w32 (by decide) (by decide)).trans w37_7c
  have w38_80 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K38.w32 (by decide) (by decide)).trans w37_80
  have w38_84 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K38.w32 (by decide) (by decide)).trans w37_84
  have w38_88 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K38.w32 (by decide) (by decide)).trans w37_88
  have w38_8c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K38.w32 (by decide) (by decide)).trans w37_8c
  have w38_90 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K38.w32 (by decide) (by decide)).trans w37_90
  have w38_94 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K38.w32 (by decide) (by decide)).trans w37_94
  have w38_98 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K38.w32 (by decide) (by decide)).trans w37_98
  have w38_9c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K38.w32 (by decide) (by decide)).trans w37_9c
  have w38_a0 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K38.w32 (by decide) (by decide)).trans w37_a0
  have w38_a4 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K38.w32 (by decide) (by decide)).trans w37_a4
  have w38_a8 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K38.w32 (by decide) (by decide)).trans w37_a8
  have w38_ac : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K38.w32 (by decide) (by decide)).trans w37_ac
  have w38_b0 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K38.w32 (by decide) (by decide)).trans w37_b0
  have w38_b4 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K38.w32 (by decide) (by decide)).trans w37_b4
  have w38_b8 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K38.w32 (by decide) (by decide)).trans w37_b8
  have w38_bc : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K38.w32 (by decide) (by decide)).trans w37_bc
  have w38_c0 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K38.w32 (by decide) (by decide)).trans w37_c0
  have w38_c4 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K38.w32 (by decide) (by decide)).trans w37_c4
  have w38_c8 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K38.w32 (by decide) (by decide)).trans w37_c8
  have w38_cc : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K38.w32 (by decide) (by decide)).trans w37_cc
  have w38_d0 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K38.w32 (by decide) (by decide)).trans w37_d0
  have w38_d4 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K38.w32 (by decide) (by decide)).trans w37_d4
  have w38_d8 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K38.w32 (by decide) (by decide)).trans w37_d8
  have w38_dc : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K38.w32 (by decide) (by decide)).trans w37_dc
  have w38_e0 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K38.w32 (by decide) (by decide)).trans w37_e0
  have w38_e4 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K38.w32 (by decide) (by decide)).trans w37_e4
  have w38_e8 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K38.w32 (by decide) (by decide)).trans w37_e8
  have w38_ec : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K38.w32 (by decide) (by decide)).trans w37_ec
  have w38_f0 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K38.w32 (by decide) (by decide)).trans w37_f0
  have w38_f4 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K38.w32 (by decide) (by decide)).trans w37_f4
  have w38_f8 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K38.w32 (by decide) (by decide)).trans w37_f8
  have w38_fc : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K38.w32 (by decide) (by decide)).trans w37_fc
  have w38_100 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K38.w32 (by decide) (by decide)).trans w37_100
  have w38_104 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K38.w32 (by decide) (by decide)).trans w37_104
  have w38_108 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K38.w32 (by decide) (by decide)).trans w37_108
  have w38_10c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K38.w32 (by decide) (by decide)).trans w37_10c
  have w38_110 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K38.w32 (by decide) (by decide)).trans w37_110
  have w38_114 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K38.w32 (by decide) (by decide)).trans w37_114
  have w38_118 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K38.w32 (by decide) (by decide)).trans w37_118
  have w38_11c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K38.w32 (by decide) (by decide)).trans w37_11c
  have w38_120 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K38.w32 (by decide) (by decide)).trans w37_120
  have w38_124 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K38.w32 (by decide) (by decide)).trans w37_124
  have w38_128 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K38.w32 (by decide) (by decide)).trans w37_128
  have w38_12c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K38.w32 (by decide) (by decide)).trans w37_12c
  have w38_130 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K38.w32 (by decide) (by decide)).trans w37_130
  have b38_a40 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = gs := (K38.b8 (by decide) (by decide)).trans b37_a40
  have b38_14a0 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := (K38.b8 (by decide) (by decide)).trans b37_14a0
  have q38_420 : ∀ j, j < 96 → n38.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K38.range (by decide) (by decide) j hj).trans (q37_420 j hj)
  have q38_480 : ∀ j, j < 96 → n38.mem (B + 0x21A0 + BitVec.ofNat 32 (0x480 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K38.range (by decide) (by decide) j hj).trans (q37_480 j hj)
  have q38_4e0 : ∀ j, j < 96 → n38.mem (B + 0x21A0 + BitVec.ofNat 32 (0x4E0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K38.range (by decide) (by decide) j hj).trans (q37_4e0 j hj)
  have q38_540 : ∀ j, j < 96 → n38.mem (B + 0x21A0 + BitVec.ofNat 32 (0x540 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K38.range (by decide) (by decide) j hj).trans (q37_540 j hj)
  have q38_5a0 : ∀ j, j < 96 → n38.mem (B + 0x21A0 + BitVec.ofNat 32 (0x5A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K38.range (by decide) (by decide) j hj).trans (q37_5a0 j hj)
  have q38_600 : ∀ j, j < 96 → n38.mem (B + 0x21A0 + BitVec.ofNat 32 (0x600 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K38.range (by decide) (by decide) j hj).trans (q37_600 j hj)
  have q38_660 : ∀ j, j < 96 → n38.mem (B + 0x21A0 + BitVec.ofNat 32 (0x660 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K38.range (by decide) (by decide) j hj).trans (q37_660 j hj)
  have q38_6c0 : ∀ j, j < 96 → n38.mem (B + 0x21A0 + BitVec.ofNat 32 (0x6C0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => (K38.range (by decide) (by decide) j hj).trans (q37_6c0 j hj)
  have a38_240 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := (K38.acc (by decide) (by decide)).trans a37_240
  have a38_260 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := (K38.acc (by decide) (by decide)).trans a37_260
  have a38_280 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := (K38.acc (by decide) (by decide)).trans a37_280
  have a38_2a0 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K38.acc (by decide) (by decide)).trans a37_2a0
  have a38_2c0 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K38.acc (by decide) (by decide)).trans a37_2c0
  have a38_2e0 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K38.acc (by decide) (by decide)).trans a37_2e0
  have a38_380 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := (K38.acc (by decide) (by decide)).trans a37_380
  have a38_400 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := (K38.acc (by decide) (by decide)).trans a37_400
  have a38_13e0 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U2 := (K38.acc (by decide) (by decide)).trans a37_13e0
  have a38_14e0 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x14E0) 8 = U1 := (K38.acc (by decide) (by decide)).trans a37_14e0
  have a38_1560 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x1560) 8 = U2 := (K38.acc (by decide) (by decide)).trans a37_1560
  have p38_320 : ptF n38.mem B 0x320 = P0 := (K38.pt (by decide) (by decide)).trans p37_320
  have p38_3a0 : ptF n38.mem B 0x3A0 = P1 := (K38.pt (by decide) (by decide)).trans p37_3a0
  have p38_a20 : ptF n38.mem B 0xA20 = tbl2 P0 0 := (K38.pt (by decide) (by decide)).trans p37_a20
  have p38_a80 : ptF n38.mem B 0xA80 = tbl2 P0 1 := (K38.pt (by decide) (by decide)).trans p37_a80
  have p38_ae0 : ptF n38.mem B 0xAE0 = tbl2 P0 2 := (K38.pt (by decide) (by decide)).trans p37_ae0
  have p38_b40 : ptF n38.mem B 0xB40 = tbl2 P0 3 := (K38.pt (by decide) (by decide)).trans p37_b40
  have p38_ba0 : ptF n38.mem B 0xBA0 = tbl2 P0 4 := (K38.pt (by decide) (by decide)).trans p37_ba0
  have p38_c00 : ptF n38.mem B 0xC00 = tbl2 P0 5 := (K38.pt (by decide) (by decide)).trans p37_c00
  have p38_c60 : ptF n38.mem B 0xC60 = tbl2 P0 6 := (K38.pt (by decide) (by decide)).trans p37_c60
  have p38_cc0 : ptF n38.mem B 0xCC0 = tbl2 P0 7 := (K38.pt (by decide) (by decide)).trans p37_cc0
  have p38_1320 : ptF n38.mem B 0x1320 = ptDbl2 P0 := (K38.pt (by decide) (by decide)).trans p37_1320
  have p38_1380 : ptF n38.mem B 0x1380 = P1 := (K38.pt (by decide) (by decide)).trans p37_1380
  have p38_1480 : ptF n38.mem B 0x1480 = P0 := (K38.pt (by decide) (by decide)).trans p37_1480
  have p38_1500 : ptF n38.mem B 0x1500 = P1 := (K38.pt (by decide) (by decide)).trans p37_1500
  have q38_1020 : ∀ j, j < 96 → n38.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1020 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by
    rw [show 0x1020 + j = 0x1020 + (0x0 + j) by omega, X38 (0x0 + j) (by omega),
      show 0x420 + (0x0 + j) = 0x420 + j by omega]; exact q37_420 j (by omega)
  have q38_1080 : ∀ j, j < 96 → n38.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1080 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by
    rw [show 0x1080 + j = 0x1020 + (0x60 + j) by omega, X38 (0x60 + j) (by omega),
      show 0x420 + (0x60 + j) = 0x480 + j by omega]; exact q37_480 j (by omega)
  have q38_10e0 : ∀ j, j < 96 → n38.mem (B + 0x21A0 + BitVec.ofNat 32 (0x10E0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by
    rw [show 0x10E0 + j = 0x1020 + (0xC0 + j) by omega, X38 (0xC0 + j) (by omega),
      show 0x420 + (0xC0 + j) = 0x4E0 + j by omega]; exact q37_4e0 j (by omega)
  have q38_1140 : ∀ j, j < 96 → n38.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1140 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by
    rw [show 0x1140 + j = 0x1020 + (0x120 + j) by omega, X38 (0x120 + j) (by omega),
      show 0x420 + (0x120 + j) = 0x540 + j by omega]; exact q37_540 j (by omega)
  have q38_11a0 : ∀ j, j < 96 → n38.mem (B + 0x21A0 + BitVec.ofNat 32 (0x11A0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by
    rw [show 0x11A0 + j = 0x1020 + (0x180 + j) by omega, X38 (0x180 + j) (by omega),
      show 0x420 + (0x180 + j) = 0x5A0 + j by omega]; exact q37_5a0 j (by omega)
  have q38_1200 : ∀ j, j < 96 → n38.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1200 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by
    rw [show 0x1200 + j = 0x1020 + (0x1E0 + j) by omega, X38 (0x1E0 + j) (by omega),
      show 0x420 + (0x1E0 + j) = 0x600 + j by omega]; exact q37_600 j (by omega)
  have q38_1260 : ∀ j, j < 96 → n38.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1260 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by
    rw [show 0x1260 + j = 0x1020 + (0x240 + j) by omega, X38 (0x240 + j) (by omega),
      show 0x420 + (0x240 + j) = 0x660 + j by omega]; exact q37_660 j (by omega)
  have q38_12c0 : ∀ j, j < 96 → n38.mem (B + 0x21A0 + BitVec.ofNat 32 (0x12C0 + j)) = M0 ((BitVec.ofNat 32 (img% p256GMontAddress)) + BitVec.ofNat 32 j) := fun j hj => by
    rw [show 0x12C0 + j = 0x1020 + (0x2A0 + j) by omega, X38 (0x2A0 + j) (by omega),
      show 0x420 + (0x2A0 + j) = 0x6C0 + j by omega]; exact q37_6c0 j (by omega)
  clear p37_1500 p37_1480 p37_1380 p37_1320 p37_12c0 p37_1260 p37_1200 p37_11a0 p37_1140 p37_10e0 p37_1080 p37_1020 p37_cc0 p37_c60 p37_c00 p37_ba0 p37_b40 p37_ae0 p37_a80 p37_a20 p37_3a0 p37_320 a37_1560 a37_14e0 a37_13e0 a37_400 a37_380 a37_2e0 a37_2c0 a37_2a0 a37_280 a37_260 a37_240 q37_6c0 q37_660 q37_600 q37_5a0 q37_540 q37_4e0 q37_480 q37_420 b37_14a0 b37_1040 b37_a40 w37_130 w37_12c w37_128 w37_124 w37_120 w37_11c w37_118 w37_114 w37_110 w37_10c w37_108 w37_104 w37_100 w37_fc w37_f8 w37_f4 w37_f0 w37_ec w37_e8 w37_e4 w37_e0 w37_dc w37_d8 w37_d4 w37_d0 w37_cc w37_c8 w37_c4 w37_c0 w37_bc w37_b8 w37_b4 w37_b0 w37_ac w37_a8 w37_a4 w37_a0 w37_9c w37_98 w37_94 w37_90 w37_8c w37_88 w37_84 w37_80 w37_7c w37_78 w37_70 w37_6c w37_68 w37_64 w37_60 w37_5c w37_58 w37_54 w37_50 w37_4c w37_48 w37_44 w37_40 w37_3c w37_38 w37_34 w37_30 w37_2c w37_28 w37_24 g37_13 g37_12 g37_11 g37_10 g37_9 g37_8 g37_27 g37_26 g37_25 g37_24 g37_23 g37_22 g37_21 g37_20 g37_19 g37_18 g37_4 g37_3 g37_2 V37 E37 fR37 t37 fr37 rb37 s37 m37 u37 c37
  exact .inr ⟨n38, t38, s38, E38, V38, fR38, g38_2, g38_3, g38_4, g38_8, g38_9, g38_18, g38_19, g38_20, g38_21, g38_22, g38_23, g38_24, g38_25, g38_26, g38_27, w38_24, w38_28, w38_2c, w38_30, w38_34, w38_38, w38_3c, w38_40, w38_44, w38_48, w38_4c, w38_50, w38_54, w38_58, w38_5c, w38_60, w38_64, w38_68, w38_6c, w38_70, w38_78, w38_7c, w38_80, w38_84, w38_88, w38_8c, w38_90, w38_94, w38_98, w38_9c, w38_a0, w38_a4, w38_a8, w38_ac, w38_b0, w38_b4, w38_b8, w38_bc, w38_c0, w38_c4, w38_c8, w38_cc, w38_d0, w38_d4, w38_d8, w38_dc, w38_e0, w38_e4, w38_e8, w38_ec, w38_f0, w38_f4, w38_f8, w38_fc, w38_100, w38_104, w38_108, w38_10c, w38_110, w38_114, w38_118, w38_11c, w38_120, w38_124, w38_128, w38_12c, w38_130, b38_a40, b38_14a0, q38_420, q38_480, q38_4e0, q38_540, q38_5a0, q38_600, q38_660, q38_6c0, q38_1020, q38_1080, q38_10e0, q38_1140, q38_11a0, q38_1200, q38_1260, q38_12c0, a38_240, a38_260, a38_280, a38_2a0, a38_2c0, a38_2e0, a38_380, a38_400, a38_13e0, a38_14e0, a38_1560, p38_320, p38_3a0, p38_a20, p38_a80, p38_ae0, p38_b40, p38_ba0, p38_c00, p38_c60, p38_cc0, p38_1320, p38_1380, p38_1480, p38_1500, keep_kk38.mono (by decide)⟩

end C3.RV32.Sv
