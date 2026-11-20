import C3BootProofs.Proofs.SvEcW
import C3BootProofs.Proofs.SvEcT1b

/-!
# `sigstore::verify`: the wNAF digits of `u₁` and `u₂`

From 0x178A to 0x18F8: the tables move to offset 0x420, and `wnaf_form` writes the width-5 NAF digits of `u₁` and `u₂`, which end up in records at 0x1020 and 0x1128 with their lengths.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svEcW178a : List BInstr :=
  [.aluImm .add a0 sp 0x420, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x221, .aluImm .add a2 x0 0x600, .aluImm .add (20 : Fin 32) sp 0x7FF, .aluImm .add (20 : Fin 32) (20 : Fin 32) 0x221]
set_option maxRecDepth 100000 in
theorem svEcW178a_end : blockEnd sigstoreVerifyCode 0x178A svEcW178a = some 0x17A2 := by decide

def svEcW17aa : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x380, .alu .add a0 a0 sp, .aluImm .add a1 sp 0x320, .aluImm .add a2 x0 0x100, .lui a3 0x1000, .aluImm .add a3 a3 0x380, .alu .add (9 : Fin 32) sp a3]
set_option maxRecDepth 100000 in
theorem svEcW17aa_end : blockEnd sigstoreVerifyCode 0x17AA svEcW17aa = some 0x17C2 := by decide

def svEcW17ca : List BInstr :=
  [.aluImm .add (8 : Fin 32) x0 0x0, .lui a0 0x1000, .aluImm .add a0 a0 0x24, .alu .add (23 : Fin 32) sp a0, .aluImm .add (25 : Fin 32) x0 0x2, .aluImm .add (22 : Fin 32) x0 0x108]
set_option maxRecDepth 100000 in
theorem svEcW17ca_end : blockEnd sigstoreVerifyCode 0x17CA svEcW17ca = some 0x17DC := by decide

def svEcW17e0 : List BInstr :=
  [.aluImm .add a1 (9 : Fin 32) 0x60, .lui a0 0x1000, .aluImm .add a0 a0 0x588, .alu .add a0 a0 sp, .aluImm .add a2 x0 0x20]
set_option maxRecDepth 100000 in
theorem svEcW17e0_end : blockEnd sigstoreVerifyCode 0x17E0 svEcW17e0 = some 0x17F0 := by decide

def svEcW17f8 : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x480, .alu .add a0 a0 sp, .lui a1 0x1000, .aluImm .add a1 a1 0x588, .alu .add a1 a1 sp]
set_option maxRecDepth 100000 in
theorem svEcW17f8_end : blockEnd sigstoreVerifyCode 0x17F8 svEcW17f8 = some 0x1808 := by decide

def svEcW1810 : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x480, .alu .add a0 a0 sp, .aluImm .add a1 x0 0x20]
set_option maxRecDepth 100000 in
theorem svEcW1810_end : blockEnd sigstoreVerifyCode 0x1810 svEcW1810 = some 0x181C := by decide

def svEcW1824 : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x320, .alu .add a0 a0 sp, .lui a1 0x1000, .aluImm .add a1 a1 0x480, .alu .add a1 a1 sp, .aluImm .add a2 x0 0x20]
set_option maxRecDepth 100000 in
theorem svEcW1824_end : blockEnd sigstoreVerifyCode 0x1824 svEcW1824 = some 0x1838 := by decide

def svEcW1840 : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x480, .alu .add a0 a0 sp, .aluImm .add a1 x0 0x101]
set_option maxRecDepth 100000 in
theorem svEcW1840_end : blockEnd sigstoreVerifyCode 0x1840 svEcW1840 = some 0x184C := by decide

def svEcW1858 : List BInstr :=
  [.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x80, .lui a0 0x1000, .aluImm .add a0 a0 0x480, .alu .add a1 sp a0, .aluImm .add a2 x0 0x101, .alu .add a0 x0 (23 : Fin 32)]
set_option maxRecDepth 100000 in
theorem svEcW1858_end : blockEnd sigstoreVerifyCode 0x1858 svEcW1858 = some 0x186C := by decide

def svEcW1874 : List BInstr :=
  [.aluImm .add a1 x0 0x101, .lui a0 0x1000, .aluImm .add a0 a0 0x320, .alu .add a2 sp a0, .aluImm .add a3 x0 0x20, .aluImm .add a4 x0 0x100, .alu .add a0 x0 (23 : Fin 32)]
set_option maxRecDepth 100000 in
theorem svEcW1874_end : blockEnd sigstoreVerifyCode 0x1874 svEcW1874 = some 0x188C := by decide

def svEcW1898 : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x480, .alu .add a0 a0 sp, .lui a1 0x1000, .aluImm .add a1 a1 0x20, .alu .add a1 a1 sp, .aluImm .add a2 x0 0x108]
set_option maxRecDepth 100000 in
theorem svEcW1898_end : blockEnd sigstoreVerifyCode 0x1898 svEcW1898 = some 0x18AC := by decide

def svEcW18b4 : List BInstr :=
  [.alu .mul a0 (8 : Fin 32) (22 : Fin 32), .alu .add a0 a0 (20 : Fin 32), .lui a1 0x1000, .aluImm .add a1 a1 0x480, .alu .add a1 a1 sp, .aluImm .add a2 x0 0x108]
set_option maxRecDepth 100000 in
theorem svEcW18b4_end : blockEnd sigstoreVerifyCode 0x18B4 svEcW18b4 = some 0x18C6 := by decide

def svEcW18ce : List BInstr :=
  [.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x1]
set_option maxRecDepth 100000 in
theorem svEcW18ce_end : blockEnd sigstoreVerifyCode 0x18CE svEcW18ce = some 0x18D0 := by decide

def svEcW18d4 : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x20, .alu .add a0 a0 sp, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x221, .aluImm .add a2 x0 0x210]
set_option maxRecDepth 100000 in
theorem svEcW18d4_end : blockEnd sigstoreVerifyCode 0x18D4 svEcW18d4 = some 0x18E8 := by decide

set_option maxHeartbeats 0 in
theorem sv_ecw {B out bp x21 x26 s5v s8v dlo dhi rem : Word} {er es : Bytes} {U1 U2 : Nat} {P0 P1 : Pt2} {qx qy qz rv sv zv fv gv dv ev : Nat} {w24 w28 w2c w30 w34 w38 w3c w40 w44 w48 w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w7c w80 w84 w88 w8c w90 w94 w98 w9c wa0 wa4 wa8 wac wb0 wb4 wb8 wbc wc0 wc4 wc8 wcc wd0 wd4 wd8 wdc we0 we4 we8 wec wf0 wf4 wf8 wfc w100 w104 w108 w10c w110 w114 w118 w11c w120 w124 w128 w12c w130 : Word} {v : Nat → Word} {n0 : Machine}
    (F : Fr B 0x3830) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x178A (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_21 : reg n0 (21 : Fin 32) = s5v)
    (g0_23 : reg n0 (23 : Fin 32) = dlo)
    (g0_24 : reg n0 (24 : Fin 32) = s8v)
    (g0_25 : reg n0 (25 : Fin 32) = dhi)
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
    (a0_2a0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv)
    (a0_2c0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv)
    (a0_2e0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv)
    (IC0 : SvIvCode M0)
    (EC0 : SvEcCode M0)
    (g0_20 : reg n0 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20)
    (p0_320 : ptF n0.mem B 0x320 = P0)
    (p0_3a0 : ptF n0.mem B 0x3A0 = P1)
    (a0_380 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1)
    (a0_400 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2)
    (p0_a20 : ptF n0.mem B 0xA20 = tbl2 P0 0)
    (p0_a80 : ptF n0.mem B 0xA80 = tbl2 P0 1)
    (p0_ae0 : ptF n0.mem B 0xAE0 = tbl2 P0 2)
    (p0_b40 : ptF n0.mem B 0xB40 = tbl2 P0 3)
    (p0_ba0 : ptF n0.mem B 0xBA0 = tbl2 P0 4)
    (p0_c00 : ptF n0.mem B 0xC00 = tbl2 P0 5)
    (p0_c60 : ptF n0.mem B 0xC60 = tbl2 P0 6)
    (p0_cc0 : ptF n0.mem B 0xCC0 = tbl2 P0 7)
    (p0_d20 : ptF n0.mem B 0xD20 = tbl2 P1 0)
    (p0_d80 : ptF n0.mem B 0xD80 = tbl2 P1 1)
    (p0_de0 : ptF n0.mem B 0xDE0 = tbl2 P1 2)
    (p0_e40 : ptF n0.mem B 0xE40 = tbl2 P1 3)
    (p0_ea0 : ptF n0.mem B 0xEA0 = tbl2 P1 4)
    (p0_f00 : ptF n0.mem B 0xF00 = tbl2 P1 5)
    (p0_f60 : ptF n0.mem B 0xF60 = tbl2 P1 6)
    (p0_fc0 : ptF n0.mem B 0xFC0 = tbl2 P1 7)
    (WN0 : SvWnCode M0) :
    (¬ (True) ∧ SvErrRet B out v n0) ∨
    (∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x18F8 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (9 : Fin 32) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length ∧
        reg n' a0 = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
        reg n' (21 : Fin 32) = s5v ∧
        reg n' (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 ∧
        reg n' (24 : Fin 32) = s8v ∧
        reg n' (25 : Fin 32) = BitVec.ofNat 32 0x2 ∧
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
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB28) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1128) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U2 ∧
        ptF n'.mem B 0x320 = P0 ∧
        ptF n'.mem B 0x3A0 = P1 ∧
        ptF n'.mem B 0x420 = tbl2 P0 0 ∧
        ptF n'.mem B 0x480 = tbl2 P0 1 ∧
        ptF n'.mem B 0x4E0 = tbl2 P0 2 ∧
        ptF n'.mem B 0x540 = tbl2 P0 3 ∧
        ptF n'.mem B 0x5A0 = tbl2 P0 4 ∧
        ptF n'.mem B 0x600 = tbl2 P0 5 ∧
        ptF n'.mem B 0x660 = tbl2 P0 6 ∧
        ptF n'.mem B 0x6C0 = tbl2 P0 7 ∧
        ptF n'.mem B 0x720 = tbl2 P1 0 ∧
        ptF n'.mem B 0x780 = tbl2 P1 1 ∧
        ptF n'.mem B 0x7E0 = tbl2 P1 2 ∧
        ptF n'.mem B 0x840 = tbl2 P1 3 ∧
        ptF n'.mem B 0x8A0 = tbl2 P1 4 ∧
        ptF n'.mem B 0x900 = tbl2 P1 5 ∧
        ptF n'.mem B 0x960 = tbl2 P1 6 ∧
        ptF n'.mem B 0x9C0 = tbl2 P1 7 ∧
        ptF n'.mem B 0xC60 = tbl2 P0 6 ∧
        ptF n'.mem B 0xCC0 = tbl2 P0 7 ∧
        ptF n'.mem B 0xD20 = tbl2 P1 0 ∧
        ptF n'.mem B 0xD80 = tbl2 P1 1 ∧
        ptF n'.mem B 0xDE0 = tbl2 P1 2 ∧
        ptF n'.mem B 0xE40 = tbl2 P1 3 ∧
        ptF n'.mem B 0xEA0 = tbl2 P1 4 ∧
        ptF n'.mem B 0xF00 = tbl2 P1 5 ∧
        ptF n'.mem B 0xF60 = tbl2 P1 6 ∧
        ptF n'.mem B 0xFC0 = tbl2 P1 7 ∧
        ptF n'.mem B 0x1380 = P0 ∧
        ptF n'.mem B 0x1400 = P1 ∧
        memBytes n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 ∧
        memBytes n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB2C) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 ∧
        memBytes n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 ∧
        memBytes n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x112C) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 ∧
        leN (memBytes n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U2 ∧
        memBytes n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101) := by
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x178A
  obtain ⟨n1, c1, u1⟩ := s0.block svEcW178a E0.self svEcW178a_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have s1 : St n1.mem SV n1 0x17A2 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have rb1 : ∀ q, reg n1 q = (runBlock svEcW178a (n0.mem, reg n0)).2 q := fun q => by rw [u1.regs]
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
  have g1_18 : reg n1 (18 : Fin 32) = out := by
    rw [rb1, runBlock_reg _ _ _ (18 : Fin 32) s0.zero (by decide), g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = bp := by
    rw [rb1, runBlock_reg _ _ _ (19 : Fin 32) s0.zero (by decide), g0_19]
  have g1_21 : reg n1 (21 : Fin 32) = s5v := by
    rw [rb1, runBlock_reg _ _ _ (21 : Fin 32) s0.zero (by decide), g0_21]
  have g1_23 : reg n1 (23 : Fin 32) = dlo := by
    rw [rb1, runBlock_reg _ _ _ (23 : Fin 32) s0.zero (by decide), g0_23]
  have g1_24 : reg n1 (24 : Fin 32) = s8v := by
    rw [rb1, runBlock_reg _ _ _ (24 : Fin 32) s0.zero (by decide), g0_24]
  have g1_25 : reg n1 (25 : Fin 32) = dhi := by
    rw [rb1, runBlock_reg _ _ _ (25 : Fin 32) s0.zero (by decide), g0_25]
  have g1_26 : reg n1 (26 : Fin 32) = x26 := by
    rw [rb1, runBlock_reg _ _ _ (26 : Fin 32) s0.zero (by decide), g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb1, runBlock_reg _ _ _ (27 : Fin 32) s0.zero (by decide), g0_27]
  have g1_10 : reg n1 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svEcW178a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_18, g0_19, g0_20, g0_21, g0_23, g0_24, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g1_11 : reg n1 a1 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svEcW178a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_18, g0_19, g0_20, g0_21, g0_23, g0_24, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g1_12 : reg n1 a2 = BitVec.ofNat 32 0x600 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svEcW178a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_18, g0_19, g0_20, g0_21, g0_23, g0_24, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g1_20 : reg n1 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svEcW178a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_18, g0_19, g0_20, g0_21, g0_23, g0_24, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
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
  have a1_2a0 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m1]; exact a0_2a0
  have a1_2c0 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m1]; exact a0_2c0
  have a1_2e0 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m1]; exact a0_2e0
  have a1_380 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m1]; exact a0_380
  have a1_400 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m1]; exact a0_400
  have p1_320 : ptF n1.mem B 0x320 = P0 := by rw [m1]; exact p0_320
  have p1_3a0 : ptF n1.mem B 0x3A0 = P1 := by rw [m1]; exact p0_3a0
  have p1_a20 : ptF n1.mem B 0xA20 = tbl2 P0 0 := by rw [m1]; exact p0_a20
  have p1_a80 : ptF n1.mem B 0xA80 = tbl2 P0 1 := by rw [m1]; exact p0_a80
  have p1_ae0 : ptF n1.mem B 0xAE0 = tbl2 P0 2 := by rw [m1]; exact p0_ae0
  have p1_b40 : ptF n1.mem B 0xB40 = tbl2 P0 3 := by rw [m1]; exact p0_b40
  have p1_ba0 : ptF n1.mem B 0xBA0 = tbl2 P0 4 := by rw [m1]; exact p0_ba0
  have p1_c00 : ptF n1.mem B 0xC00 = tbl2 P0 5 := by rw [m1]; exact p0_c00
  have p1_c60 : ptF n1.mem B 0xC60 = tbl2 P0 6 := by rw [m1]; exact p0_c60
  have p1_cc0 : ptF n1.mem B 0xCC0 = tbl2 P0 7 := by rw [m1]; exact p0_cc0
  have p1_d20 : ptF n1.mem B 0xD20 = tbl2 P1 0 := by rw [m1]; exact p0_d20
  have p1_d80 : ptF n1.mem B 0xD80 = tbl2 P1 1 := by rw [m1]; exact p0_d80
  have p1_de0 : ptF n1.mem B 0xDE0 = tbl2 P1 2 := by rw [m1]; exact p0_de0
  have p1_e40 : ptF n1.mem B 0xE40 = tbl2 P1 3 := by rw [m1]; exact p0_e40
  have p1_ea0 : ptF n1.mem B 0xEA0 = tbl2 P1 4 := by rw [m1]; exact p0_ea0
  have p1_f00 : ptF n1.mem B 0xF00 = tbl2 P1 5 := by rw [m1]; exact p0_f00
  have p1_f60 : ptF n1.mem B 0xF60 = tbl2 P1 6 := by rw [m1]; exact p0_f60
  have p1_fc0 : ptF n1.mem B 0xFC0 = tbl2 P1 7 := by rw [m1]; exact p0_fc0
  -- 0x17A2: memcpy
  obtain ⟨n2, P2, K2, X2⟩ := sv_mc (c := 0x420) (d := 0xA20) (N := 0x600) F E1 s1 sv_at_17a2 sv_at_17a6
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
  have g2_18 : reg n2 (18 : Fin 32) = out := by rw [P2.regs (18 : Fin 32) (by decide), g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [P2.regs (19 : Fin 32) (by decide), g1_19]
  have g2_20 : reg n2 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P2.regs (20 : Fin 32) (by decide), g1_20]
  have g2_21 : reg n2 (21 : Fin 32) = s5v := by rw [P2.regs (21 : Fin 32) (by decide), g1_21]
  have g2_23 : reg n2 (23 : Fin 32) = dlo := by rw [P2.regs (23 : Fin 32) (by decide), g1_23]
  have g2_24 : reg n2 (24 : Fin 32) = s8v := by rw [P2.regs (24 : Fin 32) (by decide), g1_24]
  have g2_25 : reg n2 (25 : Fin 32) = dhi := by rw [P2.regs (25 : Fin 32) (by decide), g1_25]
  have g2_26 : reg n2 (26 : Fin 32) = x26 := by rw [P2.regs (26 : Fin 32) (by decide), g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P2.regs (27 : Fin 32) (by decide), g1_27]
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
  have a2_2a0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K2.acc (by decide) (by decide)).trans a1_2a0
  have a2_2c0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K2.acc (by decide) (by decide)).trans a1_2c0
  have a2_2e0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K2.acc (by decide) (by decide)).trans a1_2e0
  have a2_380 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := (K2.acc (by decide) (by decide)).trans a1_380
  have a2_400 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := (K2.acc (by decide) (by decide)).trans a1_400
  have p2_320 : ptF n2.mem B 0x320 = P0 := (K2.pt (by decide) (by decide)).trans p1_320
  have p2_3a0 : ptF n2.mem B 0x3A0 = P1 := (K2.pt (by decide) (by decide)).trans p1_3a0
  have p2_a20 : ptF n2.mem B 0xA20 = tbl2 P0 0 := (K2.pt (by decide) (by decide)).trans p1_a20
  have p2_a80 : ptF n2.mem B 0xA80 = tbl2 P0 1 := (K2.pt (by decide) (by decide)).trans p1_a80
  have p2_ae0 : ptF n2.mem B 0xAE0 = tbl2 P0 2 := (K2.pt (by decide) (by decide)).trans p1_ae0
  have p2_b40 : ptF n2.mem B 0xB40 = tbl2 P0 3 := (K2.pt (by decide) (by decide)).trans p1_b40
  have p2_ba0 : ptF n2.mem B 0xBA0 = tbl2 P0 4 := (K2.pt (by decide) (by decide)).trans p1_ba0
  have p2_c00 : ptF n2.mem B 0xC00 = tbl2 P0 5 := (K2.pt (by decide) (by decide)).trans p1_c00
  have p2_c60 : ptF n2.mem B 0xC60 = tbl2 P0 6 := (K2.pt (by decide) (by decide)).trans p1_c60
  have p2_cc0 : ptF n2.mem B 0xCC0 = tbl2 P0 7 := (K2.pt (by decide) (by decide)).trans p1_cc0
  have p2_d20 : ptF n2.mem B 0xD20 = tbl2 P1 0 := (K2.pt (by decide) (by decide)).trans p1_d20
  have p2_d80 : ptF n2.mem B 0xD80 = tbl2 P1 1 := (K2.pt (by decide) (by decide)).trans p1_d80
  have p2_de0 : ptF n2.mem B 0xDE0 = tbl2 P1 2 := (K2.pt (by decide) (by decide)).trans p1_de0
  have p2_e40 : ptF n2.mem B 0xE40 = tbl2 P1 3 := (K2.pt (by decide) (by decide)).trans p1_e40
  have p2_ea0 : ptF n2.mem B 0xEA0 = tbl2 P1 4 := (K2.pt (by decide) (by decide)).trans p1_ea0
  have p2_f00 : ptF n2.mem B 0xF00 = tbl2 P1 5 := (K2.pt (by decide) (by decide)).trans p1_f00
  have p2_f60 : ptF n2.mem B 0xF60 = tbl2 P1 6 := (K2.pt (by decide) (by decide)).trans p1_f60
  have p2_fc0 : ptF n2.mem B 0xFC0 = tbl2 P1 7 := (K2.pt (by decide) (by decide)).trans p1_fc0
  have p2_420 : ptF n2.mem B 0x420 = tbl2 P0 0 := (ptF_cp X2 (by decide) (by decide) (by decide)).trans p1_a20
  have p2_480 : ptF n2.mem B 0x480 = tbl2 P0 1 := (ptF_cp X2 (by decide) (by decide) (by decide)).trans p1_a80
  have p2_4e0 : ptF n2.mem B 0x4E0 = tbl2 P0 2 := (ptF_cp X2 (by decide) (by decide) (by decide)).trans p1_ae0
  have p2_540 : ptF n2.mem B 0x540 = tbl2 P0 3 := (ptF_cp X2 (by decide) (by decide) (by decide)).trans p1_b40
  have p2_5a0 : ptF n2.mem B 0x5A0 = tbl2 P0 4 := (ptF_cp X2 (by decide) (by decide) (by decide)).trans p1_ba0
  have p2_600 : ptF n2.mem B 0x600 = tbl2 P0 5 := (ptF_cp X2 (by decide) (by decide) (by decide)).trans p1_c00
  have p2_660 : ptF n2.mem B 0x660 = tbl2 P0 6 := (ptF_cp X2 (by decide) (by decide) (by decide)).trans p1_c60
  have p2_6c0 : ptF n2.mem B 0x6C0 = tbl2 P0 7 := (ptF_cp X2 (by decide) (by decide) (by decide)).trans p1_cc0
  have p2_720 : ptF n2.mem B 0x720 = tbl2 P1 0 := (ptF_cp X2 (by decide) (by decide) (by decide)).trans p1_d20
  have p2_780 : ptF n2.mem B 0x780 = tbl2 P1 1 := (ptF_cp X2 (by decide) (by decide) (by decide)).trans p1_d80
  have p2_7e0 : ptF n2.mem B 0x7E0 = tbl2 P1 2 := (ptF_cp X2 (by decide) (by decide) (by decide)).trans p1_de0
  have p2_840 : ptF n2.mem B 0x840 = tbl2 P1 3 := (ptF_cp X2 (by decide) (by decide) (by decide)).trans p1_e40
  have p2_8a0 : ptF n2.mem B 0x8A0 = tbl2 P1 4 := (ptF_cp X2 (by decide) (by decide) (by decide)).trans p1_ea0
  have p2_900 : ptF n2.mem B 0x900 = tbl2 P1 5 := (ptF_cp X2 (by decide) (by decide) (by decide)).trans p1_f00
  have p2_960 : ptF n2.mem B 0x960 = tbl2 P1 6 := (ptF_cp X2 (by decide) (by decide) (by decide)).trans p1_f60
  have p2_9c0 : ptF n2.mem B 0x9C0 = tbl2 P1 7 := (ptF_cp X2 (by decide) (by decide) (by decide)).trans p1_fc0
  clear p1_fc0 p1_f60 p1_f00 p1_ea0 p1_e40 p1_de0 p1_d80 p1_d20 p1_cc0 p1_c60 p1_c00 p1_ba0 p1_b40 p1_ae0 p1_a80 p1_a20 p1_3a0 p1_320 a1_400 a1_380 a1_2e0 a1_2c0 a1_2a0 w1_130 w1_12c w1_128 w1_124 w1_120 w1_11c w1_118 w1_114 w1_110 w1_10c w1_108 w1_104 w1_100 w1_fc w1_f8 w1_f4 w1_f0 w1_ec w1_e8 w1_e4 w1_e0 w1_dc w1_d8 w1_d4 w1_d0 w1_cc w1_c8 w1_c4 w1_c0 w1_bc w1_b8 w1_b4 w1_b0 w1_ac w1_a8 w1_a4 w1_a0 w1_9c w1_98 w1_94 w1_90 w1_8c w1_88 w1_84 w1_80 w1_7c w1_78 w1_70 w1_6c w1_68 w1_64 w1_60 w1_5c w1_58 w1_54 w1_50 w1_4c w1_48 w1_44 w1_40 w1_3c w1_38 w1_34 w1_30 w1_2c w1_28 w1_24 g1_20 g1_12 g1_11 g1_10 g1_27 g1_26 g1_25 g1_24 g1_23 g1_21 g1_19 g1_18 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
  -- 0x17AA
  obtain ⟨n3, c3, u3⟩ := s2.block svEcW17aa E2.self svEcW17aa_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have s3 : St n3.mem SV n3 0x17C2 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have rb3 : ∀ q, reg n3 q = (runBlock svEcW17aa (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
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
  have g3_21 : reg n3 (21 : Fin 32) = s5v := by
    rw [rb3, runBlock_reg _ _ _ (21 : Fin 32) s2.zero (by decide), g2_21]
  have g3_23 : reg n3 (23 : Fin 32) = dlo := by
    rw [rb3, runBlock_reg _ _ _ (23 : Fin 32) s2.zero (by decide), g2_23]
  have g3_24 : reg n3 (24 : Fin 32) = s8v := by
    rw [rb3, runBlock_reg _ _ _ (24 : Fin 32) s2.zero (by decide), g2_24]
  have g3_25 : reg n3 (25 : Fin 32) = dhi := by
    rw [rb3, runBlock_reg _ _ _ (25 : Fin 32) s2.zero (by decide), g2_25]
  have g3_26 : reg n3 (26 : Fin 32) = x26 := by
    rw [rb3, runBlock_reg _ _ _ (26 : Fin 32) s2.zero (by decide), g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb3, runBlock_reg _ _ _ (27 : Fin 32) s2.zero (by decide), g2_27]
  have g3_9 : reg n3 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1380 := by
    rw [rb3]; simp +decide only [runBlock, BInstr.run, svEcW17aa, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g2_2, g2_3, g2_4, g2_18, g2_19, g2_20, g2_21, g2_23, g2_24, g2_25, g2_26, g2_27, s2.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g3_10 : reg n3 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1380 := by
    rw [rb3]; simp +decide only [runBlock, BInstr.run, svEcW17aa, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g2_2, g2_3, g2_4, g2_18, g2_19, g2_20, g2_21, g2_23, g2_24, g2_25, g2_26, g2_27, s2.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g3_11 : reg n3 a1 = B + 0x21A0 + BitVec.ofNat 32 0x320 := by
    rw [rb3]; simp +decide only [runBlock, BInstr.run, svEcW17aa, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g2_2, g2_3, g2_4, g2_18, g2_19, g2_20, g2_21, g2_23, g2_24, g2_25, g2_26, g2_27, s2.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g3_12 : reg n3 a2 = BitVec.ofNat 32 0x100 := by
    rw [rb3]; simp +decide only [runBlock, BInstr.run, svEcW17aa, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g2_2, g2_3, g2_4, g2_18, g2_19, g2_20, g2_21, g2_23, g2_24, g2_25, g2_26, g2_27, s2.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g3_13 : reg n3 a3 = BitVec.ofNat 32 0x1380 := by
    rw [rb3]; simp +decide only [runBlock, BInstr.run, svEcW17aa, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g2_2, g2_3, g2_4, g2_18, g2_19, g2_20, g2_21, g2_23, g2_24, g2_25, g2_26, g2_27, s2.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
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
  have a3_2a0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m3]; exact a2_2a0
  have a3_2c0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m3]; exact a2_2c0
  have a3_2e0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m3]; exact a2_2e0
  have a3_380 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m3]; exact a2_380
  have a3_400 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m3]; exact a2_400
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
  have p3_720 : ptF n3.mem B 0x720 = tbl2 P1 0 := by rw [m3]; exact p2_720
  have p3_780 : ptF n3.mem B 0x780 = tbl2 P1 1 := by rw [m3]; exact p2_780
  have p3_7e0 : ptF n3.mem B 0x7E0 = tbl2 P1 2 := by rw [m3]; exact p2_7e0
  have p3_840 : ptF n3.mem B 0x840 = tbl2 P1 3 := by rw [m3]; exact p2_840
  have p3_8a0 : ptF n3.mem B 0x8A0 = tbl2 P1 4 := by rw [m3]; exact p2_8a0
  have p3_900 : ptF n3.mem B 0x900 = tbl2 P1 5 := by rw [m3]; exact p2_900
  have p3_960 : ptF n3.mem B 0x960 = tbl2 P1 6 := by rw [m3]; exact p2_960
  have p3_9c0 : ptF n3.mem B 0x9C0 = tbl2 P1 7 := by rw [m3]; exact p2_9c0
  have p3_a20 : ptF n3.mem B 0xA20 = tbl2 P0 0 := by rw [m3]; exact p2_a20
  have p3_a80 : ptF n3.mem B 0xA80 = tbl2 P0 1 := by rw [m3]; exact p2_a80
  have p3_ae0 : ptF n3.mem B 0xAE0 = tbl2 P0 2 := by rw [m3]; exact p2_ae0
  have p3_b40 : ptF n3.mem B 0xB40 = tbl2 P0 3 := by rw [m3]; exact p2_b40
  have p3_ba0 : ptF n3.mem B 0xBA0 = tbl2 P0 4 := by rw [m3]; exact p2_ba0
  have p3_c00 : ptF n3.mem B 0xC00 = tbl2 P0 5 := by rw [m3]; exact p2_c00
  have p3_c60 : ptF n3.mem B 0xC60 = tbl2 P0 6 := by rw [m3]; exact p2_c60
  have p3_cc0 : ptF n3.mem B 0xCC0 = tbl2 P0 7 := by rw [m3]; exact p2_cc0
  have p3_d20 : ptF n3.mem B 0xD20 = tbl2 P1 0 := by rw [m3]; exact p2_d20
  have p3_d80 : ptF n3.mem B 0xD80 = tbl2 P1 1 := by rw [m3]; exact p2_d80
  have p3_de0 : ptF n3.mem B 0xDE0 = tbl2 P1 2 := by rw [m3]; exact p2_de0
  have p3_e40 : ptF n3.mem B 0xE40 = tbl2 P1 3 := by rw [m3]; exact p2_e40
  have p3_ea0 : ptF n3.mem B 0xEA0 = tbl2 P1 4 := by rw [m3]; exact p2_ea0
  have p3_f00 : ptF n3.mem B 0xF00 = tbl2 P1 5 := by rw [m3]; exact p2_f00
  have p3_f60 : ptF n3.mem B 0xF60 = tbl2 P1 6 := by rw [m3]; exact p2_f60
  have p3_fc0 : ptF n3.mem B 0xFC0 = tbl2 P1 7 := by rw [m3]; exact p2_fc0
  clear p2_9c0 p2_960 p2_900 p2_8a0 p2_840 p2_7e0 p2_780 p2_720 p2_6c0 p2_660 p2_600 p2_5a0 p2_540 p2_4e0 p2_480 p2_420 p2_fc0 p2_f60 p2_f00 p2_ea0 p2_e40 p2_de0 p2_d80 p2_d20 p2_cc0 p2_c60 p2_c00 p2_ba0 p2_b40 p2_ae0 p2_a80 p2_a20 p2_3a0 p2_320 a2_400 a2_380 a2_2e0 a2_2c0 a2_2a0 w2_130 w2_12c w2_128 w2_124 w2_120 w2_11c w2_118 w2_114 w2_110 w2_10c w2_108 w2_104 w2_100 w2_fc w2_f8 w2_f4 w2_f0 w2_ec w2_e8 w2_e4 w2_e0 w2_dc w2_d8 w2_d4 w2_d0 w2_cc w2_c8 w2_c4 w2_c0 w2_bc w2_b8 w2_b4 w2_b0 w2_ac w2_a8 w2_a4 w2_a0 w2_9c w2_98 w2_94 w2_90 w2_8c w2_88 w2_84 w2_80 w2_7c w2_78 w2_70 w2_6c w2_68 w2_64 w2_60 w2_5c w2_58 w2_54 w2_50 w2_4c w2_48 w2_44 w2_40 w2_3c w2_38 w2_34 w2_30 w2_2c w2_28 w2_24 g2_27 g2_26 g2_25 g2_24 g2_23 g2_21 g2_20 g2_19 g2_18 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 s2 X2 K2 P2
  -- 0x17C2: memcpy
  obtain ⟨n4, P4, K4, X4⟩ := sv_mc (c := 0x1380) (d := 0x320) (N := 0x100) F E3 s3 sv_at_17c2 sv_at_17c6
    (by decide) (by decide) g3_2 g3_10 g3_11 g3_12
    (by decide) (by decide) (by decide)
  have s4 := P4.st
  have fr4 := P4.fr
  have t4 : Steps n0 n4 := t3.trans P4.steps
  have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : SvCode n4.mem := E3.fr F fr4
  have V4 : SvSaves B n4.mem v := V3.keep K4 (by decide)
  have g4_2 : reg n4 sp = B + 0x21A0 := by rw [P4.regs sp (by decide), g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P4.regs (3 : Fin 32) (by decide), g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P4.regs (4 : Fin 32) (by decide), g3_4]
  have g4_9 : reg n4 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1380 := by rw [P4.regs (9 : Fin 32) (by decide), g3_9]
  have g4_18 : reg n4 (18 : Fin 32) = out := by rw [P4.regs (18 : Fin 32) (by decide), g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [P4.regs (19 : Fin 32) (by decide), g3_19]
  have g4_20 : reg n4 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P4.regs (20 : Fin 32) (by decide), g3_20]
  have g4_21 : reg n4 (21 : Fin 32) = s5v := by rw [P4.regs (21 : Fin 32) (by decide), g3_21]
  have g4_23 : reg n4 (23 : Fin 32) = dlo := by rw [P4.regs (23 : Fin 32) (by decide), g3_23]
  have g4_24 : reg n4 (24 : Fin 32) = s8v := by rw [P4.regs (24 : Fin 32) (by decide), g3_24]
  have g4_25 : reg n4 (25 : Fin 32) = dhi := by rw [P4.regs (25 : Fin 32) (by decide), g3_25]
  have g4_26 : reg n4 (26 : Fin 32) = x26 := by rw [P4.regs (26 : Fin 32) (by decide), g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P4.regs (27 : Fin 32) (by decide), g3_27]
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
  have w4_78 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := (K4.w32 (by decide) (by decide)).trans w3_78
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
  have a4_2a0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K4.acc (by decide) (by decide)).trans a3_2a0
  have a4_2c0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K4.acc (by decide) (by decide)).trans a3_2c0
  have a4_2e0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K4.acc (by decide) (by decide)).trans a3_2e0
  have a4_380 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := (K4.acc (by decide) (by decide)).trans a3_380
  have a4_400 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := (K4.acc (by decide) (by decide)).trans a3_400
  have p4_320 : ptF n4.mem B 0x320 = P0 := (K4.pt (by decide) (by decide)).trans p3_320
  have p4_3a0 : ptF n4.mem B 0x3A0 = P1 := (K4.pt (by decide) (by decide)).trans p3_3a0
  have p4_420 : ptF n4.mem B 0x420 = tbl2 P0 0 := (K4.pt (by decide) (by decide)).trans p3_420
  have p4_480 : ptF n4.mem B 0x480 = tbl2 P0 1 := (K4.pt (by decide) (by decide)).trans p3_480
  have p4_4e0 : ptF n4.mem B 0x4E0 = tbl2 P0 2 := (K4.pt (by decide) (by decide)).trans p3_4e0
  have p4_540 : ptF n4.mem B 0x540 = tbl2 P0 3 := (K4.pt (by decide) (by decide)).trans p3_540
  have p4_5a0 : ptF n4.mem B 0x5A0 = tbl2 P0 4 := (K4.pt (by decide) (by decide)).trans p3_5a0
  have p4_600 : ptF n4.mem B 0x600 = tbl2 P0 5 := (K4.pt (by decide) (by decide)).trans p3_600
  have p4_660 : ptF n4.mem B 0x660 = tbl2 P0 6 := (K4.pt (by decide) (by decide)).trans p3_660
  have p4_6c0 : ptF n4.mem B 0x6C0 = tbl2 P0 7 := (K4.pt (by decide) (by decide)).trans p3_6c0
  have p4_720 : ptF n4.mem B 0x720 = tbl2 P1 0 := (K4.pt (by decide) (by decide)).trans p3_720
  have p4_780 : ptF n4.mem B 0x780 = tbl2 P1 1 := (K4.pt (by decide) (by decide)).trans p3_780
  have p4_7e0 : ptF n4.mem B 0x7E0 = tbl2 P1 2 := (K4.pt (by decide) (by decide)).trans p3_7e0
  have p4_840 : ptF n4.mem B 0x840 = tbl2 P1 3 := (K4.pt (by decide) (by decide)).trans p3_840
  have p4_8a0 : ptF n4.mem B 0x8A0 = tbl2 P1 4 := (K4.pt (by decide) (by decide)).trans p3_8a0
  have p4_900 : ptF n4.mem B 0x900 = tbl2 P1 5 := (K4.pt (by decide) (by decide)).trans p3_900
  have p4_960 : ptF n4.mem B 0x960 = tbl2 P1 6 := (K4.pt (by decide) (by decide)).trans p3_960
  have p4_9c0 : ptF n4.mem B 0x9C0 = tbl2 P1 7 := (K4.pt (by decide) (by decide)).trans p3_9c0
  have p4_a20 : ptF n4.mem B 0xA20 = tbl2 P0 0 := (K4.pt (by decide) (by decide)).trans p3_a20
  have p4_a80 : ptF n4.mem B 0xA80 = tbl2 P0 1 := (K4.pt (by decide) (by decide)).trans p3_a80
  have p4_ae0 : ptF n4.mem B 0xAE0 = tbl2 P0 2 := (K4.pt (by decide) (by decide)).trans p3_ae0
  have p4_b40 : ptF n4.mem B 0xB40 = tbl2 P0 3 := (K4.pt (by decide) (by decide)).trans p3_b40
  have p4_ba0 : ptF n4.mem B 0xBA0 = tbl2 P0 4 := (K4.pt (by decide) (by decide)).trans p3_ba0
  have p4_c00 : ptF n4.mem B 0xC00 = tbl2 P0 5 := (K4.pt (by decide) (by decide)).trans p3_c00
  have p4_c60 : ptF n4.mem B 0xC60 = tbl2 P0 6 := (K4.pt (by decide) (by decide)).trans p3_c60
  have p4_cc0 : ptF n4.mem B 0xCC0 = tbl2 P0 7 := (K4.pt (by decide) (by decide)).trans p3_cc0
  have p4_d20 : ptF n4.mem B 0xD20 = tbl2 P1 0 := (K4.pt (by decide) (by decide)).trans p3_d20
  have p4_d80 : ptF n4.mem B 0xD80 = tbl2 P1 1 := (K4.pt (by decide) (by decide)).trans p3_d80
  have p4_de0 : ptF n4.mem B 0xDE0 = tbl2 P1 2 := (K4.pt (by decide) (by decide)).trans p3_de0
  have p4_e40 : ptF n4.mem B 0xE40 = tbl2 P1 3 := (K4.pt (by decide) (by decide)).trans p3_e40
  have p4_ea0 : ptF n4.mem B 0xEA0 = tbl2 P1 4 := (K4.pt (by decide) (by decide)).trans p3_ea0
  have p4_f00 : ptF n4.mem B 0xF00 = tbl2 P1 5 := (K4.pt (by decide) (by decide)).trans p3_f00
  have p4_f60 : ptF n4.mem B 0xF60 = tbl2 P1 6 := (K4.pt (by decide) (by decide)).trans p3_f60
  have p4_fc0 : ptF n4.mem B 0xFC0 = tbl2 P1 7 := (K4.pt (by decide) (by decide)).trans p3_fc0
  have p4_1380 : ptF n4.mem B 0x1380 = P0 := (ptF_cp X4 (by decide) (by decide) (by decide)).trans p3_320
  have p4_1400 : ptF n4.mem B 0x1400 = P1 := (ptF_cp X4 (by decide) (by decide) (by decide)).trans p3_3a0
  have a4_13e0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := (accV_S 8 fun q hq => by
    rw [show 0x13E0 + q = 0x1380 + (0x60 + q) by omega, X4 (0x60 + q) (by omega),
      show 0x320 + (0x60 + q) = 0x380 + q by omega]).trans a3_380
  have a4_1460 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := (accV_S 8 fun q hq => by
    rw [show 0x1460 + q = 0x1380 + (0xE0 + q) by omega, X4 (0xE0 + q) (by omega),
      show 0x320 + (0xE0 + q) = 0x400 + q by omega]).trans a3_400
  clear p3_fc0 p3_f60 p3_f00 p3_ea0 p3_e40 p3_de0 p3_d80 p3_d20 p3_cc0 p3_c60 p3_c00 p3_ba0 p3_b40 p3_ae0 p3_a80 p3_a20 p3_9c0 p3_960 p3_900 p3_8a0 p3_840 p3_7e0 p3_780 p3_720 p3_6c0 p3_660 p3_600 p3_5a0 p3_540 p3_4e0 p3_480 p3_420 p3_3a0 p3_320 a3_400 a3_380 a3_2e0 a3_2c0 a3_2a0 w3_130 w3_12c w3_128 w3_124 w3_120 w3_11c w3_118 w3_114 w3_110 w3_10c w3_108 w3_104 w3_100 w3_fc w3_f8 w3_f4 w3_f0 w3_ec w3_e8 w3_e4 w3_e0 w3_dc w3_d8 w3_d4 w3_d0 w3_cc w3_c8 w3_c4 w3_c0 w3_bc w3_b8 w3_b4 w3_b0 w3_ac w3_a8 w3_a4 w3_a0 w3_9c w3_98 w3_94 w3_90 w3_8c w3_88 w3_84 w3_80 w3_7c w3_78 w3_70 w3_6c w3_68 w3_64 w3_60 w3_5c w3_58 w3_54 w3_50 w3_4c w3_48 w3_44 w3_40 w3_3c w3_38 w3_34 w3_30 w3_2c w3_28 w3_24 g3_13 g3_12 g3_11 g3_10 g3_9 g3_27 g3_26 g3_25 g3_24 g3_23 g3_21 g3_20 g3_19 g3_18 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 rb3 s3 m3 u3 c3
  -- 0x17CA
  obtain ⟨n5, c5, u5⟩ := s4.block svEcW17ca E4.self svEcW17ca_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have s5 : St n5.mem SV n5 0x17DC (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have rb5 : ∀ q, reg n5 q = (runBlock svEcW17ca (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
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
  have g5_9 : reg n5 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1380 := by
    rw [rb5, runBlock_reg _ _ _ (9 : Fin 32) s4.zero (by decide), g4_9]
  have g5_18 : reg n5 (18 : Fin 32) = out := by
    rw [rb5, runBlock_reg _ _ _ (18 : Fin 32) s4.zero (by decide), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by
    rw [rb5, runBlock_reg _ _ _ (19 : Fin 32) s4.zero (by decide), g4_19]
  have g5_20 : reg n5 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb5, runBlock_reg _ _ _ (20 : Fin 32) s4.zero (by decide), g4_20]
  have g5_21 : reg n5 (21 : Fin 32) = s5v := by
    rw [rb5, runBlock_reg _ _ _ (21 : Fin 32) s4.zero (by decide), g4_21]
  have g5_24 : reg n5 (24 : Fin 32) = s8v := by
    rw [rb5, runBlock_reg _ _ _ (24 : Fin 32) s4.zero (by decide), g4_24]
  have g5_26 : reg n5 (26 : Fin 32) = x26 := by
    rw [rb5, runBlock_reg _ _ _ (26 : Fin 32) s4.zero (by decide), g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb5, runBlock_reg _ _ _ (27 : Fin 32) s4.zero (by decide), g4_27]
  have g5_8 : reg n5 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, svEcW17ca, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_9, g4_18, g4_19, g4_20, g4_21, g4_23, g4_24, g4_25, g4_26, g4_27, s4.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g5_10 : reg n5 a0 = BitVec.ofNat 32 0x1024 := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, svEcW17ca, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_9, g4_18, g4_19, g4_20, g4_21, g4_23, g4_24, g4_25, g4_26, g4_27, s4.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g5_22 : reg n5 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, svEcW17ca, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_9, g4_18, g4_19, g4_20, g4_21, g4_23, g4_24, g4_25, g4_26, g4_27, s4.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g5_23 : reg n5 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, svEcW17ca, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_9, g4_18, g4_19, g4_20, g4_21, g4_23, g4_24, g4_25, g4_26, g4_27, s4.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g5_25 : reg n5 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, svEcW17ca, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_9, g4_18, g4_19, g4_20, g4_21, g4_23, g4_24, g4_25, g4_26, g4_27, s4.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
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
  have a5_2a0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m5]; exact a4_2a0
  have a5_2c0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m5]; exact a4_2c0
  have a5_2e0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m5]; exact a4_2e0
  have a5_380 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m5]; exact a4_380
  have a5_400 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m5]; exact a4_400
  have a5_13e0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := by rw [m5]; exact a4_13e0
  have a5_1460 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := by rw [m5]; exact a4_1460
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
  have p5_720 : ptF n5.mem B 0x720 = tbl2 P1 0 := by rw [m5]; exact p4_720
  have p5_780 : ptF n5.mem B 0x780 = tbl2 P1 1 := by rw [m5]; exact p4_780
  have p5_7e0 : ptF n5.mem B 0x7E0 = tbl2 P1 2 := by rw [m5]; exact p4_7e0
  have p5_840 : ptF n5.mem B 0x840 = tbl2 P1 3 := by rw [m5]; exact p4_840
  have p5_8a0 : ptF n5.mem B 0x8A0 = tbl2 P1 4 := by rw [m5]; exact p4_8a0
  have p5_900 : ptF n5.mem B 0x900 = tbl2 P1 5 := by rw [m5]; exact p4_900
  have p5_960 : ptF n5.mem B 0x960 = tbl2 P1 6 := by rw [m5]; exact p4_960
  have p5_9c0 : ptF n5.mem B 0x9C0 = tbl2 P1 7 := by rw [m5]; exact p4_9c0
  have p5_a20 : ptF n5.mem B 0xA20 = tbl2 P0 0 := by rw [m5]; exact p4_a20
  have p5_a80 : ptF n5.mem B 0xA80 = tbl2 P0 1 := by rw [m5]; exact p4_a80
  have p5_ae0 : ptF n5.mem B 0xAE0 = tbl2 P0 2 := by rw [m5]; exact p4_ae0
  have p5_b40 : ptF n5.mem B 0xB40 = tbl2 P0 3 := by rw [m5]; exact p4_b40
  have p5_ba0 : ptF n5.mem B 0xBA0 = tbl2 P0 4 := by rw [m5]; exact p4_ba0
  have p5_c00 : ptF n5.mem B 0xC00 = tbl2 P0 5 := by rw [m5]; exact p4_c00
  have p5_c60 : ptF n5.mem B 0xC60 = tbl2 P0 6 := by rw [m5]; exact p4_c60
  have p5_cc0 : ptF n5.mem B 0xCC0 = tbl2 P0 7 := by rw [m5]; exact p4_cc0
  have p5_d20 : ptF n5.mem B 0xD20 = tbl2 P1 0 := by rw [m5]; exact p4_d20
  have p5_d80 : ptF n5.mem B 0xD80 = tbl2 P1 1 := by rw [m5]; exact p4_d80
  have p5_de0 : ptF n5.mem B 0xDE0 = tbl2 P1 2 := by rw [m5]; exact p4_de0
  have p5_e40 : ptF n5.mem B 0xE40 = tbl2 P1 3 := by rw [m5]; exact p4_e40
  have p5_ea0 : ptF n5.mem B 0xEA0 = tbl2 P1 4 := by rw [m5]; exact p4_ea0
  have p5_f00 : ptF n5.mem B 0xF00 = tbl2 P1 5 := by rw [m5]; exact p4_f00
  have p5_f60 : ptF n5.mem B 0xF60 = tbl2 P1 6 := by rw [m5]; exact p4_f60
  have p5_fc0 : ptF n5.mem B 0xFC0 = tbl2 P1 7 := by rw [m5]; exact p4_fc0
  have p5_1380 : ptF n5.mem B 0x1380 = P0 := by rw [m5]; exact p4_1380
  have p5_1400 : ptF n5.mem B 0x1400 = P1 := by rw [m5]; exact p4_1400
  clear a4_1460 a4_13e0 p4_1400 p4_1380 p4_fc0 p4_f60 p4_f00 p4_ea0 p4_e40 p4_de0 p4_d80 p4_d20 p4_cc0 p4_c60 p4_c00 p4_ba0 p4_b40 p4_ae0 p4_a80 p4_a20 p4_9c0 p4_960 p4_900 p4_8a0 p4_840 p4_7e0 p4_780 p4_720 p4_6c0 p4_660 p4_600 p4_5a0 p4_540 p4_4e0 p4_480 p4_420 p4_3a0 p4_320 a4_400 a4_380 a4_2e0 a4_2c0 a4_2a0 w4_130 w4_12c w4_128 w4_124 w4_120 w4_11c w4_118 w4_114 w4_110 w4_10c w4_108 w4_104 w4_100 w4_fc w4_f8 w4_f4 w4_f0 w4_ec w4_e8 w4_e4 w4_e0 w4_dc w4_d8 w4_d4 w4_d0 w4_cc w4_c8 w4_c4 w4_c0 w4_bc w4_b8 w4_b4 w4_b0 w4_ac w4_a8 w4_a4 w4_a0 w4_9c w4_98 w4_94 w4_90 w4_8c w4_88 w4_84 w4_80 w4_7c w4_78 w4_70 w4_6c w4_68 w4_64 w4_60 w4_5c w4_58 w4_54 w4_50 w4_4c w4_48 w4_44 w4_40 w4_3c w4_38 w4_34 w4_30 w4_2c w4_28 w4_24 g4_27 g4_26 g4_25 g4_24 g4_23 g4_21 g4_20 g4_19 g4_18 g4_9 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 s4 X4 K4 P4
  -- 0x17DC: branch, not taken
  obtain ⟨n6, d6, u6⟩ := s5.notTaken E5.self 0x17E0 sv_at_17dc
    (by decide) (by rw [g5_25, s5.zero]; decide)
  have s6 : St n6.mem SV n6 0x17E0 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have fr6 : ∀ x, SvR B x → n6.mem x = n5.mem x := fun x _ => by rw [m6]
  have t6 : Steps n0 n6 := t5.trans (.single d6)
  have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : SvCode n6.mem := E5.fr F fr6
  have V6 : SvSaves B n6.mem v := V5.same m6
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [u6.regs, g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u6.regs, g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u6.regs, g5_4]
  have g6_8 : reg n6 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u6.regs, g5_8]
  have g6_9 : reg n6 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1380 := by rw [u6.regs, g5_9]
  have g6_10 : reg n6 a0 = BitVec.ofNat 32 0x1024 := by rw [u6.regs, g5_10]
  have g6_18 : reg n6 (18 : Fin 32) = out := by rw [u6.regs, g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [u6.regs, g5_19]
  have g6_20 : reg n6 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u6.regs, g5_20]
  have g6_21 : reg n6 (21 : Fin 32) = s5v := by rw [u6.regs, g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [u6.regs, g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by rw [u6.regs, g5_23]
  have g6_24 : reg n6 (24 : Fin 32) = s8v := by rw [u6.regs, g5_24]
  have g6_25 : reg n6 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u6.regs, g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = x26 := by rw [u6.regs, g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u6.regs, g5_27]
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
  have w6_78 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m6]; exact w5_78
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
  have a6_2a0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m6]; exact a5_2a0
  have a6_2c0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m6]; exact a5_2c0
  have a6_2e0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m6]; exact a5_2e0
  have a6_380 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m6]; exact a5_380
  have a6_400 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m6]; exact a5_400
  have a6_13e0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := by rw [m6]; exact a5_13e0
  have a6_1460 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := by rw [m6]; exact a5_1460
  have p6_320 : ptF n6.mem B 0x320 = P0 := by rw [m6]; exact p5_320
  have p6_3a0 : ptF n6.mem B 0x3A0 = P1 := by rw [m6]; exact p5_3a0
  have p6_420 : ptF n6.mem B 0x420 = tbl2 P0 0 := by rw [m6]; exact p5_420
  have p6_480 : ptF n6.mem B 0x480 = tbl2 P0 1 := by rw [m6]; exact p5_480
  have p6_4e0 : ptF n6.mem B 0x4E0 = tbl2 P0 2 := by rw [m6]; exact p5_4e0
  have p6_540 : ptF n6.mem B 0x540 = tbl2 P0 3 := by rw [m6]; exact p5_540
  have p6_5a0 : ptF n6.mem B 0x5A0 = tbl2 P0 4 := by rw [m6]; exact p5_5a0
  have p6_600 : ptF n6.mem B 0x600 = tbl2 P0 5 := by rw [m6]; exact p5_600
  have p6_660 : ptF n6.mem B 0x660 = tbl2 P0 6 := by rw [m6]; exact p5_660
  have p6_6c0 : ptF n6.mem B 0x6C0 = tbl2 P0 7 := by rw [m6]; exact p5_6c0
  have p6_720 : ptF n6.mem B 0x720 = tbl2 P1 0 := by rw [m6]; exact p5_720
  have p6_780 : ptF n6.mem B 0x780 = tbl2 P1 1 := by rw [m6]; exact p5_780
  have p6_7e0 : ptF n6.mem B 0x7E0 = tbl2 P1 2 := by rw [m6]; exact p5_7e0
  have p6_840 : ptF n6.mem B 0x840 = tbl2 P1 3 := by rw [m6]; exact p5_840
  have p6_8a0 : ptF n6.mem B 0x8A0 = tbl2 P1 4 := by rw [m6]; exact p5_8a0
  have p6_900 : ptF n6.mem B 0x900 = tbl2 P1 5 := by rw [m6]; exact p5_900
  have p6_960 : ptF n6.mem B 0x960 = tbl2 P1 6 := by rw [m6]; exact p5_960
  have p6_9c0 : ptF n6.mem B 0x9C0 = tbl2 P1 7 := by rw [m6]; exact p5_9c0
  have p6_a20 : ptF n6.mem B 0xA20 = tbl2 P0 0 := by rw [m6]; exact p5_a20
  have p6_a80 : ptF n6.mem B 0xA80 = tbl2 P0 1 := by rw [m6]; exact p5_a80
  have p6_ae0 : ptF n6.mem B 0xAE0 = tbl2 P0 2 := by rw [m6]; exact p5_ae0
  have p6_b40 : ptF n6.mem B 0xB40 = tbl2 P0 3 := by rw [m6]; exact p5_b40
  have p6_ba0 : ptF n6.mem B 0xBA0 = tbl2 P0 4 := by rw [m6]; exact p5_ba0
  have p6_c00 : ptF n6.mem B 0xC00 = tbl2 P0 5 := by rw [m6]; exact p5_c00
  have p6_c60 : ptF n6.mem B 0xC60 = tbl2 P0 6 := by rw [m6]; exact p5_c60
  have p6_cc0 : ptF n6.mem B 0xCC0 = tbl2 P0 7 := by rw [m6]; exact p5_cc0
  have p6_d20 : ptF n6.mem B 0xD20 = tbl2 P1 0 := by rw [m6]; exact p5_d20
  have p6_d80 : ptF n6.mem B 0xD80 = tbl2 P1 1 := by rw [m6]; exact p5_d80
  have p6_de0 : ptF n6.mem B 0xDE0 = tbl2 P1 2 := by rw [m6]; exact p5_de0
  have p6_e40 : ptF n6.mem B 0xE40 = tbl2 P1 3 := by rw [m6]; exact p5_e40
  have p6_ea0 : ptF n6.mem B 0xEA0 = tbl2 P1 4 := by rw [m6]; exact p5_ea0
  have p6_f00 : ptF n6.mem B 0xF00 = tbl2 P1 5 := by rw [m6]; exact p5_f00
  have p6_f60 : ptF n6.mem B 0xF60 = tbl2 P1 6 := by rw [m6]; exact p5_f60
  have p6_fc0 : ptF n6.mem B 0xFC0 = tbl2 P1 7 := by rw [m6]; exact p5_fc0
  have p6_1380 : ptF n6.mem B 0x1380 = P0 := by rw [m6]; exact p5_1380
  have p6_1400 : ptF n6.mem B 0x1400 = P1 := by rw [m6]; exact p5_1400
  clear p5_1400 p5_1380 p5_fc0 p5_f60 p5_f00 p5_ea0 p5_e40 p5_de0 p5_d80 p5_d20 p5_cc0 p5_c60 p5_c00 p5_ba0 p5_b40 p5_ae0 p5_a80 p5_a20 p5_9c0 p5_960 p5_900 p5_8a0 p5_840 p5_7e0 p5_780 p5_720 p5_6c0 p5_660 p5_600 p5_5a0 p5_540 p5_4e0 p5_480 p5_420 p5_3a0 p5_320 a5_1460 a5_13e0 a5_400 a5_380 a5_2e0 a5_2c0 a5_2a0 w5_130 w5_12c w5_128 w5_124 w5_120 w5_11c w5_118 w5_114 w5_110 w5_10c w5_108 w5_104 w5_100 w5_fc w5_f8 w5_f4 w5_f0 w5_ec w5_e8 w5_e4 w5_e0 w5_dc w5_d8 w5_d4 w5_d0 w5_cc w5_c8 w5_c4 w5_c0 w5_bc w5_b8 w5_b4 w5_b0 w5_ac w5_a8 w5_a4 w5_a0 w5_9c w5_98 w5_94 w5_90 w5_8c w5_88 w5_84 w5_80 w5_7c w5_78 w5_70 w5_6c w5_68 w5_64 w5_60 w5_5c w5_58 w5_54 w5_50 w5_4c w5_48 w5_44 w5_40 w5_3c w5_38 w5_34 w5_30 w5_2c w5_28 w5_24 g5_25 g5_23 g5_22 g5_10 g5_8 g5_27 g5_26 g5_24 g5_21 g5_20 g5_19 g5_18 g5_9 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 rb5 s5 m5 u5 c5
  -- 0x17E0
  obtain ⟨n7, c7, u7⟩ := s6.block svEcW17e0 E6.self svEcW17e0_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have s7 : St n7.mem SV n7 0x17F0 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have rb7 : ∀ q, reg n7 q = (runBlock svEcW17e0 (n6.mem, reg n6)).2 q := fun q => by rw [u7.regs]
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
  have g7_8 : reg n7 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb7, runBlock_reg _ _ _ (8 : Fin 32) s6.zero (by decide), g6_8]
  have g7_9 : reg n7 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1380 := by
    rw [rb7, runBlock_reg _ _ _ (9 : Fin 32) s6.zero (by decide), g6_9]
  have g7_18 : reg n7 (18 : Fin 32) = out := by
    rw [rb7, runBlock_reg _ _ _ (18 : Fin 32) s6.zero (by decide), g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = bp := by
    rw [rb7, runBlock_reg _ _ _ (19 : Fin 32) s6.zero (by decide), g6_19]
  have g7_20 : reg n7 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb7, runBlock_reg _ _ _ (20 : Fin 32) s6.zero (by decide), g6_20]
  have g7_21 : reg n7 (21 : Fin 32) = s5v := by
    rw [rb7, runBlock_reg _ _ _ (21 : Fin 32) s6.zero (by decide), g6_21]
  have g7_22 : reg n7 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by
    rw [rb7, runBlock_reg _ _ _ (22 : Fin 32) s6.zero (by decide), g6_22]
  have g7_23 : reg n7 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by
    rw [rb7, runBlock_reg _ _ _ (23 : Fin 32) s6.zero (by decide), g6_23]
  have g7_24 : reg n7 (24 : Fin 32) = s8v := by
    rw [rb7, runBlock_reg _ _ _ (24 : Fin 32) s6.zero (by decide), g6_24]
  have g7_25 : reg n7 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb7, runBlock_reg _ _ _ (25 : Fin 32) s6.zero (by decide), g6_25]
  have g7_26 : reg n7 (26 : Fin 32) = x26 := by
    rw [rb7, runBlock_reg _ _ _ (26 : Fin 32) s6.zero (by decide), g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb7, runBlock_reg _ _ _ (27 : Fin 32) s6.zero (by decide), g6_27]
  have g7_10 : reg n7 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1588 := by
    rw [rb7]; simp +decide only [runBlock, BInstr.run, svEcW17e0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g6_2, g6_3, g6_4, g6_8, g6_9, g6_10, g6_18, g6_19, g6_20, g6_21, g6_22, g6_23, g6_24, g6_25, g6_26, g6_27, s6.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g7_11 : reg n7 a1 = B + 0x21A0 + BitVec.ofNat 32 0x13E0 := by
    rw [rb7]; simp +decide only [runBlock, BInstr.run, svEcW17e0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g6_2, g6_3, g6_4, g6_8, g6_9, g6_10, g6_18, g6_19, g6_20, g6_21, g6_22, g6_23, g6_24, g6_25, g6_26, g6_27, s6.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g7_12 : reg n7 a2 = BitVec.ofNat 32 0x20 := by
    rw [rb7]; simp +decide only [runBlock, BInstr.run, svEcW17e0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g6_2, g6_3, g6_4, g6_8, g6_9, g6_10, g6_18, g6_19, g6_20, g6_21, g6_22, g6_23, g6_24, g6_25, g6_26, g6_27, s6.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
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
  have a7_2a0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m7]; exact a6_2a0
  have a7_2c0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m7]; exact a6_2c0
  have a7_2e0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m7]; exact a6_2e0
  have a7_380 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m7]; exact a6_380
  have a7_400 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m7]; exact a6_400
  have a7_13e0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := by rw [m7]; exact a6_13e0
  have a7_1460 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := by rw [m7]; exact a6_1460
  have p7_320 : ptF n7.mem B 0x320 = P0 := by rw [m7]; exact p6_320
  have p7_3a0 : ptF n7.mem B 0x3A0 = P1 := by rw [m7]; exact p6_3a0
  have p7_420 : ptF n7.mem B 0x420 = tbl2 P0 0 := by rw [m7]; exact p6_420
  have p7_480 : ptF n7.mem B 0x480 = tbl2 P0 1 := by rw [m7]; exact p6_480
  have p7_4e0 : ptF n7.mem B 0x4E0 = tbl2 P0 2 := by rw [m7]; exact p6_4e0
  have p7_540 : ptF n7.mem B 0x540 = tbl2 P0 3 := by rw [m7]; exact p6_540
  have p7_5a0 : ptF n7.mem B 0x5A0 = tbl2 P0 4 := by rw [m7]; exact p6_5a0
  have p7_600 : ptF n7.mem B 0x600 = tbl2 P0 5 := by rw [m7]; exact p6_600
  have p7_660 : ptF n7.mem B 0x660 = tbl2 P0 6 := by rw [m7]; exact p6_660
  have p7_6c0 : ptF n7.mem B 0x6C0 = tbl2 P0 7 := by rw [m7]; exact p6_6c0
  have p7_720 : ptF n7.mem B 0x720 = tbl2 P1 0 := by rw [m7]; exact p6_720
  have p7_780 : ptF n7.mem B 0x780 = tbl2 P1 1 := by rw [m7]; exact p6_780
  have p7_7e0 : ptF n7.mem B 0x7E0 = tbl2 P1 2 := by rw [m7]; exact p6_7e0
  have p7_840 : ptF n7.mem B 0x840 = tbl2 P1 3 := by rw [m7]; exact p6_840
  have p7_8a0 : ptF n7.mem B 0x8A0 = tbl2 P1 4 := by rw [m7]; exact p6_8a0
  have p7_900 : ptF n7.mem B 0x900 = tbl2 P1 5 := by rw [m7]; exact p6_900
  have p7_960 : ptF n7.mem B 0x960 = tbl2 P1 6 := by rw [m7]; exact p6_960
  have p7_9c0 : ptF n7.mem B 0x9C0 = tbl2 P1 7 := by rw [m7]; exact p6_9c0
  have p7_a20 : ptF n7.mem B 0xA20 = tbl2 P0 0 := by rw [m7]; exact p6_a20
  have p7_a80 : ptF n7.mem B 0xA80 = tbl2 P0 1 := by rw [m7]; exact p6_a80
  have p7_ae0 : ptF n7.mem B 0xAE0 = tbl2 P0 2 := by rw [m7]; exact p6_ae0
  have p7_b40 : ptF n7.mem B 0xB40 = tbl2 P0 3 := by rw [m7]; exact p6_b40
  have p7_ba0 : ptF n7.mem B 0xBA0 = tbl2 P0 4 := by rw [m7]; exact p6_ba0
  have p7_c00 : ptF n7.mem B 0xC00 = tbl2 P0 5 := by rw [m7]; exact p6_c00
  have p7_c60 : ptF n7.mem B 0xC60 = tbl2 P0 6 := by rw [m7]; exact p6_c60
  have p7_cc0 : ptF n7.mem B 0xCC0 = tbl2 P0 7 := by rw [m7]; exact p6_cc0
  have p7_d20 : ptF n7.mem B 0xD20 = tbl2 P1 0 := by rw [m7]; exact p6_d20
  have p7_d80 : ptF n7.mem B 0xD80 = tbl2 P1 1 := by rw [m7]; exact p6_d80
  have p7_de0 : ptF n7.mem B 0xDE0 = tbl2 P1 2 := by rw [m7]; exact p6_de0
  have p7_e40 : ptF n7.mem B 0xE40 = tbl2 P1 3 := by rw [m7]; exact p6_e40
  have p7_ea0 : ptF n7.mem B 0xEA0 = tbl2 P1 4 := by rw [m7]; exact p6_ea0
  have p7_f00 : ptF n7.mem B 0xF00 = tbl2 P1 5 := by rw [m7]; exact p6_f00
  have p7_f60 : ptF n7.mem B 0xF60 = tbl2 P1 6 := by rw [m7]; exact p6_f60
  have p7_fc0 : ptF n7.mem B 0xFC0 = tbl2 P1 7 := by rw [m7]; exact p6_fc0
  have p7_1380 : ptF n7.mem B 0x1380 = P0 := by rw [m7]; exact p6_1380
  have p7_1400 : ptF n7.mem B 0x1400 = P1 := by rw [m7]; exact p6_1400
  clear p6_1400 p6_1380 p6_fc0 p6_f60 p6_f00 p6_ea0 p6_e40 p6_de0 p6_d80 p6_d20 p6_cc0 p6_c60 p6_c00 p6_ba0 p6_b40 p6_ae0 p6_a80 p6_a20 p6_9c0 p6_960 p6_900 p6_8a0 p6_840 p6_7e0 p6_780 p6_720 p6_6c0 p6_660 p6_600 p6_5a0 p6_540 p6_4e0 p6_480 p6_420 p6_3a0 p6_320 a6_1460 a6_13e0 a6_400 a6_380 a6_2e0 a6_2c0 a6_2a0 w6_130 w6_12c w6_128 w6_124 w6_120 w6_11c w6_118 w6_114 w6_110 w6_10c w6_108 w6_104 w6_100 w6_fc w6_f8 w6_f4 w6_f0 w6_ec w6_e8 w6_e4 w6_e0 w6_dc w6_d8 w6_d4 w6_d0 w6_cc w6_c8 w6_c4 w6_c0 w6_bc w6_b8 w6_b4 w6_b0 w6_ac w6_a8 w6_a4 w6_a0 w6_9c w6_98 w6_94 w6_90 w6_8c w6_88 w6_84 w6_80 w6_7c w6_78 w6_70 w6_6c w6_68 w6_64 w6_60 w6_5c w6_58 w6_54 w6_50 w6_4c w6_48 w6_44 w6_40 w6_3c w6_38 w6_34 w6_30 w6_2c w6_28 w6_24 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_10 g6_9 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 m6 s6 u6 d6
  -- 0x17F0: memcpy
  obtain ⟨n8, P8, K8, X8⟩ := sv_mc (c := 0x1588) (d := 0x13E0) (N := 0x20) F E7 s7 sv_at_17f0 sv_at_17f4
    (by decide) (by decide) g7_2 g7_10 g7_11 g7_12
    (by decide) (by decide) (by decide)
  have s8 := P8.st
  have fr8 := P8.fr
  have t8 : Steps n0 n8 := t7.trans P8.steps
  have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : SvCode n8.mem := E7.fr F fr8
  have V8 : SvSaves B n8.mem v := V7.keep K8 (by decide)
  have g8_2 : reg n8 sp = B + 0x21A0 := by rw [P8.regs sp (by decide), g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P8.regs (3 : Fin 32) (by decide), g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P8.regs (4 : Fin 32) (by decide), g7_4]
  have g8_8 : reg n8 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [P8.regs (8 : Fin 32) (by decide), g7_8]
  have g8_9 : reg n8 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1380 := by rw [P8.regs (9 : Fin 32) (by decide), g7_9]
  have g8_18 : reg n8 (18 : Fin 32) = out := by rw [P8.regs (18 : Fin 32) (by decide), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [P8.regs (19 : Fin 32) (by decide), g7_19]
  have g8_20 : reg n8 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P8.regs (20 : Fin 32) (by decide), g7_20]
  have g8_21 : reg n8 (21 : Fin 32) = s5v := by rw [P8.regs (21 : Fin 32) (by decide), g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [P8.regs (22 : Fin 32) (by decide), g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by rw [P8.regs (23 : Fin 32) (by decide), g7_23]
  have g8_24 : reg n8 (24 : Fin 32) = s8v := by rw [P8.regs (24 : Fin 32) (by decide), g7_24]
  have g8_25 : reg n8 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P8.regs (25 : Fin 32) (by decide), g7_25]
  have g8_26 : reg n8 (26 : Fin 32) = x26 := by rw [P8.regs (26 : Fin 32) (by decide), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P8.regs (27 : Fin 32) (by decide), g7_27]
  have w8_24 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K8.w32 (by decide) (by decide)).trans w7_24
  have w8_28 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K8.w32 (by decide) (by decide)).trans w7_28
  have w8_2c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K8.w32 (by decide) (by decide)).trans w7_2c
  have w8_30 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K8.w32 (by decide) (by decide)).trans w7_30
  have w8_34 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K8.w32 (by decide) (by decide)).trans w7_34
  have w8_38 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K8.w32 (by decide) (by decide)).trans w7_38
  have w8_3c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K8.w32 (by decide) (by decide)).trans w7_3c
  have w8_40 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K8.w32 (by decide) (by decide)).trans w7_40
  have w8_44 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K8.w32 (by decide) (by decide)).trans w7_44
  have w8_48 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K8.w32 (by decide) (by decide)).trans w7_48
  have w8_4c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K8.w32 (by decide) (by decide)).trans w7_4c
  have w8_50 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K8.w32 (by decide) (by decide)).trans w7_50
  have w8_54 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K8.w32 (by decide) (by decide)).trans w7_54
  have w8_58 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K8.w32 (by decide) (by decide)).trans w7_58
  have w8_5c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K8.w32 (by decide) (by decide)).trans w7_5c
  have w8_60 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K8.w32 (by decide) (by decide)).trans w7_60
  have w8_64 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K8.w32 (by decide) (by decide)).trans w7_64
  have w8_68 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K8.w32 (by decide) (by decide)).trans w7_68
  have w8_6c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K8.w32 (by decide) (by decide)).trans w7_6c
  have w8_70 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K8.w32 (by decide) (by decide)).trans w7_70
  have w8_78 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := (K8.w32 (by decide) (by decide)).trans w7_78
  have w8_7c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K8.w32 (by decide) (by decide)).trans w7_7c
  have w8_80 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K8.w32 (by decide) (by decide)).trans w7_80
  have w8_84 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K8.w32 (by decide) (by decide)).trans w7_84
  have w8_88 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K8.w32 (by decide) (by decide)).trans w7_88
  have w8_8c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K8.w32 (by decide) (by decide)).trans w7_8c
  have w8_90 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K8.w32 (by decide) (by decide)).trans w7_90
  have w8_94 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K8.w32 (by decide) (by decide)).trans w7_94
  have w8_98 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K8.w32 (by decide) (by decide)).trans w7_98
  have w8_9c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K8.w32 (by decide) (by decide)).trans w7_9c
  have w8_a0 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K8.w32 (by decide) (by decide)).trans w7_a0
  have w8_a4 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K8.w32 (by decide) (by decide)).trans w7_a4
  have w8_a8 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K8.w32 (by decide) (by decide)).trans w7_a8
  have w8_ac : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K8.w32 (by decide) (by decide)).trans w7_ac
  have w8_b0 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K8.w32 (by decide) (by decide)).trans w7_b0
  have w8_b4 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K8.w32 (by decide) (by decide)).trans w7_b4
  have w8_b8 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K8.w32 (by decide) (by decide)).trans w7_b8
  have w8_bc : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K8.w32 (by decide) (by decide)).trans w7_bc
  have w8_c0 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K8.w32 (by decide) (by decide)).trans w7_c0
  have w8_c4 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K8.w32 (by decide) (by decide)).trans w7_c4
  have w8_c8 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K8.w32 (by decide) (by decide)).trans w7_c8
  have w8_cc : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K8.w32 (by decide) (by decide)).trans w7_cc
  have w8_d0 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K8.w32 (by decide) (by decide)).trans w7_d0
  have w8_d4 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K8.w32 (by decide) (by decide)).trans w7_d4
  have w8_d8 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K8.w32 (by decide) (by decide)).trans w7_d8
  have w8_dc : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K8.w32 (by decide) (by decide)).trans w7_dc
  have w8_e0 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K8.w32 (by decide) (by decide)).trans w7_e0
  have w8_e4 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K8.w32 (by decide) (by decide)).trans w7_e4
  have w8_e8 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K8.w32 (by decide) (by decide)).trans w7_e8
  have w8_ec : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K8.w32 (by decide) (by decide)).trans w7_ec
  have w8_f0 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K8.w32 (by decide) (by decide)).trans w7_f0
  have w8_f4 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K8.w32 (by decide) (by decide)).trans w7_f4
  have w8_f8 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K8.w32 (by decide) (by decide)).trans w7_f8
  have w8_fc : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K8.w32 (by decide) (by decide)).trans w7_fc
  have w8_100 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K8.w32 (by decide) (by decide)).trans w7_100
  have w8_104 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K8.w32 (by decide) (by decide)).trans w7_104
  have w8_108 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K8.w32 (by decide) (by decide)).trans w7_108
  have w8_10c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K8.w32 (by decide) (by decide)).trans w7_10c
  have w8_110 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K8.w32 (by decide) (by decide)).trans w7_110
  have w8_114 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K8.w32 (by decide) (by decide)).trans w7_114
  have w8_118 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K8.w32 (by decide) (by decide)).trans w7_118
  have w8_11c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K8.w32 (by decide) (by decide)).trans w7_11c
  have w8_120 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K8.w32 (by decide) (by decide)).trans w7_120
  have w8_124 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K8.w32 (by decide) (by decide)).trans w7_124
  have w8_128 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K8.w32 (by decide) (by decide)).trans w7_128
  have w8_12c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K8.w32 (by decide) (by decide)).trans w7_12c
  have w8_130 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K8.w32 (by decide) (by decide)).trans w7_130
  have a8_2a0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K8.acc (by decide) (by decide)).trans a7_2a0
  have a8_2c0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K8.acc (by decide) (by decide)).trans a7_2c0
  have a8_2e0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K8.acc (by decide) (by decide)).trans a7_2e0
  have a8_380 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := (K8.acc (by decide) (by decide)).trans a7_380
  have a8_400 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := (K8.acc (by decide) (by decide)).trans a7_400
  have a8_13e0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := (K8.acc (by decide) (by decide)).trans a7_13e0
  have a8_1460 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := (K8.acc (by decide) (by decide)).trans a7_1460
  have p8_320 : ptF n8.mem B 0x320 = P0 := (K8.pt (by decide) (by decide)).trans p7_320
  have p8_3a0 : ptF n8.mem B 0x3A0 = P1 := (K8.pt (by decide) (by decide)).trans p7_3a0
  have p8_420 : ptF n8.mem B 0x420 = tbl2 P0 0 := (K8.pt (by decide) (by decide)).trans p7_420
  have p8_480 : ptF n8.mem B 0x480 = tbl2 P0 1 := (K8.pt (by decide) (by decide)).trans p7_480
  have p8_4e0 : ptF n8.mem B 0x4E0 = tbl2 P0 2 := (K8.pt (by decide) (by decide)).trans p7_4e0
  have p8_540 : ptF n8.mem B 0x540 = tbl2 P0 3 := (K8.pt (by decide) (by decide)).trans p7_540
  have p8_5a0 : ptF n8.mem B 0x5A0 = tbl2 P0 4 := (K8.pt (by decide) (by decide)).trans p7_5a0
  have p8_600 : ptF n8.mem B 0x600 = tbl2 P0 5 := (K8.pt (by decide) (by decide)).trans p7_600
  have p8_660 : ptF n8.mem B 0x660 = tbl2 P0 6 := (K8.pt (by decide) (by decide)).trans p7_660
  have p8_6c0 : ptF n8.mem B 0x6C0 = tbl2 P0 7 := (K8.pt (by decide) (by decide)).trans p7_6c0
  have p8_720 : ptF n8.mem B 0x720 = tbl2 P1 0 := (K8.pt (by decide) (by decide)).trans p7_720
  have p8_780 : ptF n8.mem B 0x780 = tbl2 P1 1 := (K8.pt (by decide) (by decide)).trans p7_780
  have p8_7e0 : ptF n8.mem B 0x7E0 = tbl2 P1 2 := (K8.pt (by decide) (by decide)).trans p7_7e0
  have p8_840 : ptF n8.mem B 0x840 = tbl2 P1 3 := (K8.pt (by decide) (by decide)).trans p7_840
  have p8_8a0 : ptF n8.mem B 0x8A0 = tbl2 P1 4 := (K8.pt (by decide) (by decide)).trans p7_8a0
  have p8_900 : ptF n8.mem B 0x900 = tbl2 P1 5 := (K8.pt (by decide) (by decide)).trans p7_900
  have p8_960 : ptF n8.mem B 0x960 = tbl2 P1 6 := (K8.pt (by decide) (by decide)).trans p7_960
  have p8_9c0 : ptF n8.mem B 0x9C0 = tbl2 P1 7 := (K8.pt (by decide) (by decide)).trans p7_9c0
  have p8_a20 : ptF n8.mem B 0xA20 = tbl2 P0 0 := (K8.pt (by decide) (by decide)).trans p7_a20
  have p8_a80 : ptF n8.mem B 0xA80 = tbl2 P0 1 := (K8.pt (by decide) (by decide)).trans p7_a80
  have p8_ae0 : ptF n8.mem B 0xAE0 = tbl2 P0 2 := (K8.pt (by decide) (by decide)).trans p7_ae0
  have p8_b40 : ptF n8.mem B 0xB40 = tbl2 P0 3 := (K8.pt (by decide) (by decide)).trans p7_b40
  have p8_ba0 : ptF n8.mem B 0xBA0 = tbl2 P0 4 := (K8.pt (by decide) (by decide)).trans p7_ba0
  have p8_c00 : ptF n8.mem B 0xC00 = tbl2 P0 5 := (K8.pt (by decide) (by decide)).trans p7_c00
  have p8_c60 : ptF n8.mem B 0xC60 = tbl2 P0 6 := (K8.pt (by decide) (by decide)).trans p7_c60
  have p8_cc0 : ptF n8.mem B 0xCC0 = tbl2 P0 7 := (K8.pt (by decide) (by decide)).trans p7_cc0
  have p8_d20 : ptF n8.mem B 0xD20 = tbl2 P1 0 := (K8.pt (by decide) (by decide)).trans p7_d20
  have p8_d80 : ptF n8.mem B 0xD80 = tbl2 P1 1 := (K8.pt (by decide) (by decide)).trans p7_d80
  have p8_de0 : ptF n8.mem B 0xDE0 = tbl2 P1 2 := (K8.pt (by decide) (by decide)).trans p7_de0
  have p8_e40 : ptF n8.mem B 0xE40 = tbl2 P1 3 := (K8.pt (by decide) (by decide)).trans p7_e40
  have p8_ea0 : ptF n8.mem B 0xEA0 = tbl2 P1 4 := (K8.pt (by decide) (by decide)).trans p7_ea0
  have p8_f00 : ptF n8.mem B 0xF00 = tbl2 P1 5 := (K8.pt (by decide) (by decide)).trans p7_f00
  have p8_f60 : ptF n8.mem B 0xF60 = tbl2 P1 6 := (K8.pt (by decide) (by decide)).trans p7_f60
  have p8_fc0 : ptF n8.mem B 0xFC0 = tbl2 P1 7 := (K8.pt (by decide) (by decide)).trans p7_fc0
  have p8_1380 : ptF n8.mem B 0x1380 = P0 := (K8.pt (by decide) (by decide)).trans p7_1380
  have p8_1400 : ptF n8.mem B 0x1400 = P1 := (K8.pt (by decide) (by decide)).trans p7_1400
  have a8_1588 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U1 := (accV_S 8 fun q hq => by
    rw [show 0x1588 + q = 0x1588 + (0x0 + q) by omega, X8 (0x0 + q) (by omega),
      show 0x13E0 + (0x0 + q) = 0x13E0 + q by omega]).trans a7_13e0
  clear p7_1400 p7_1380 p7_fc0 p7_f60 p7_f00 p7_ea0 p7_e40 p7_de0 p7_d80 p7_d20 p7_cc0 p7_c60 p7_c00 p7_ba0 p7_b40 p7_ae0 p7_a80 p7_a20 p7_9c0 p7_960 p7_900 p7_8a0 p7_840 p7_7e0 p7_780 p7_720 p7_6c0 p7_660 p7_600 p7_5a0 p7_540 p7_4e0 p7_480 p7_420 p7_3a0 p7_320 a7_1460 a7_13e0 a7_400 a7_380 a7_2e0 a7_2c0 a7_2a0 w7_130 w7_12c w7_128 w7_124 w7_120 w7_11c w7_118 w7_114 w7_110 w7_10c w7_108 w7_104 w7_100 w7_fc w7_f8 w7_f4 w7_f0 w7_ec w7_e8 w7_e4 w7_e0 w7_dc w7_d8 w7_d4 w7_d0 w7_cc w7_c8 w7_c4 w7_c0 w7_bc w7_b8 w7_b4 w7_b0 w7_ac w7_a8 w7_a4 w7_a0 w7_9c w7_98 w7_94 w7_90 w7_8c w7_88 w7_84 w7_80 w7_7c w7_78 w7_70 w7_6c w7_68 w7_64 w7_60 w7_5c w7_58 w7_54 w7_50 w7_4c w7_48 w7_44 w7_40 w7_3c w7_38 w7_34 w7_30 w7_2c w7_28 w7_24 g7_12 g7_11 g7_10 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_9 g7_8 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 rb7 s7 m7 u7 c7
  -- 0x17F8
  obtain ⟨n9, c9, u9⟩ := s8.block svEcW17f8 E8.self svEcW17f8_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m9 : n9.mem = n8.mem := u9.mem
  have s9 : St n9.mem SV n9 0x1808 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have rb9 : ∀ q, reg n9 q = (runBlock svEcW17f8 (n8.mem, reg n8)).2 q := fun q => by rw [u9.regs]
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
  have g9_8 : reg n9 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb9, runBlock_reg _ _ _ (8 : Fin 32) s8.zero (by decide), g8_8]
  have g9_9 : reg n9 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1380 := by
    rw [rb9, runBlock_reg _ _ _ (9 : Fin 32) s8.zero (by decide), g8_9]
  have g9_18 : reg n9 (18 : Fin 32) = out := by
    rw [rb9, runBlock_reg _ _ _ (18 : Fin 32) s8.zero (by decide), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by
    rw [rb9, runBlock_reg _ _ _ (19 : Fin 32) s8.zero (by decide), g8_19]
  have g9_20 : reg n9 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb9, runBlock_reg _ _ _ (20 : Fin 32) s8.zero (by decide), g8_20]
  have g9_21 : reg n9 (21 : Fin 32) = s5v := by
    rw [rb9, runBlock_reg _ _ _ (21 : Fin 32) s8.zero (by decide), g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by
    rw [rb9, runBlock_reg _ _ _ (22 : Fin 32) s8.zero (by decide), g8_22]
  have g9_23 : reg n9 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by
    rw [rb9, runBlock_reg _ _ _ (23 : Fin 32) s8.zero (by decide), g8_23]
  have g9_24 : reg n9 (24 : Fin 32) = s8v := by
    rw [rb9, runBlock_reg _ _ _ (24 : Fin 32) s8.zero (by decide), g8_24]
  have g9_25 : reg n9 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb9, runBlock_reg _ _ _ (25 : Fin 32) s8.zero (by decide), g8_25]
  have g9_26 : reg n9 (26 : Fin 32) = x26 := by
    rw [rb9, runBlock_reg _ _ _ (26 : Fin 32) s8.zero (by decide), g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb9, runBlock_reg _ _ _ (27 : Fin 32) s8.zero (by decide), g8_27]
  have g9_10 : reg n9 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, svEcW17f8, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g8_2, g8_3, g8_4, g8_8, g8_9, g8_18, g8_19, g8_20, g8_21, g8_22, g8_23, g8_24, g8_25, g8_26, g8_27, s8.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g9_11 : reg n9 a1 = B + 0x21A0 + BitVec.ofNat 32 0x1588 := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, svEcW17f8, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g8_2, g8_3, g8_4, g8_8, g8_9, g8_18, g8_19, g8_20, g8_21, g8_22, g8_23, g8_24, g8_25, g8_26, g8_27, s8.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
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
  have a9_2a0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m9]; exact a8_2a0
  have a9_2c0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m9]; exact a8_2c0
  have a9_2e0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m9]; exact a8_2e0
  have a9_380 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m9]; exact a8_380
  have a9_400 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m9]; exact a8_400
  have a9_13e0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := by rw [m9]; exact a8_13e0
  have a9_1460 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := by rw [m9]; exact a8_1460
  have a9_1588 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U1 := by rw [m9]; exact a8_1588
  have p9_320 : ptF n9.mem B 0x320 = P0 := by rw [m9]; exact p8_320
  have p9_3a0 : ptF n9.mem B 0x3A0 = P1 := by rw [m9]; exact p8_3a0
  have p9_420 : ptF n9.mem B 0x420 = tbl2 P0 0 := by rw [m9]; exact p8_420
  have p9_480 : ptF n9.mem B 0x480 = tbl2 P0 1 := by rw [m9]; exact p8_480
  have p9_4e0 : ptF n9.mem B 0x4E0 = tbl2 P0 2 := by rw [m9]; exact p8_4e0
  have p9_540 : ptF n9.mem B 0x540 = tbl2 P0 3 := by rw [m9]; exact p8_540
  have p9_5a0 : ptF n9.mem B 0x5A0 = tbl2 P0 4 := by rw [m9]; exact p8_5a0
  have p9_600 : ptF n9.mem B 0x600 = tbl2 P0 5 := by rw [m9]; exact p8_600
  have p9_660 : ptF n9.mem B 0x660 = tbl2 P0 6 := by rw [m9]; exact p8_660
  have p9_6c0 : ptF n9.mem B 0x6C0 = tbl2 P0 7 := by rw [m9]; exact p8_6c0
  have p9_720 : ptF n9.mem B 0x720 = tbl2 P1 0 := by rw [m9]; exact p8_720
  have p9_780 : ptF n9.mem B 0x780 = tbl2 P1 1 := by rw [m9]; exact p8_780
  have p9_7e0 : ptF n9.mem B 0x7E0 = tbl2 P1 2 := by rw [m9]; exact p8_7e0
  have p9_840 : ptF n9.mem B 0x840 = tbl2 P1 3 := by rw [m9]; exact p8_840
  have p9_8a0 : ptF n9.mem B 0x8A0 = tbl2 P1 4 := by rw [m9]; exact p8_8a0
  have p9_900 : ptF n9.mem B 0x900 = tbl2 P1 5 := by rw [m9]; exact p8_900
  have p9_960 : ptF n9.mem B 0x960 = tbl2 P1 6 := by rw [m9]; exact p8_960
  have p9_9c0 : ptF n9.mem B 0x9C0 = tbl2 P1 7 := by rw [m9]; exact p8_9c0
  have p9_a20 : ptF n9.mem B 0xA20 = tbl2 P0 0 := by rw [m9]; exact p8_a20
  have p9_a80 : ptF n9.mem B 0xA80 = tbl2 P0 1 := by rw [m9]; exact p8_a80
  have p9_ae0 : ptF n9.mem B 0xAE0 = tbl2 P0 2 := by rw [m9]; exact p8_ae0
  have p9_b40 : ptF n9.mem B 0xB40 = tbl2 P0 3 := by rw [m9]; exact p8_b40
  have p9_ba0 : ptF n9.mem B 0xBA0 = tbl2 P0 4 := by rw [m9]; exact p8_ba0
  have p9_c00 : ptF n9.mem B 0xC00 = tbl2 P0 5 := by rw [m9]; exact p8_c00
  have p9_c60 : ptF n9.mem B 0xC60 = tbl2 P0 6 := by rw [m9]; exact p8_c60
  have p9_cc0 : ptF n9.mem B 0xCC0 = tbl2 P0 7 := by rw [m9]; exact p8_cc0
  have p9_d20 : ptF n9.mem B 0xD20 = tbl2 P1 0 := by rw [m9]; exact p8_d20
  have p9_d80 : ptF n9.mem B 0xD80 = tbl2 P1 1 := by rw [m9]; exact p8_d80
  have p9_de0 : ptF n9.mem B 0xDE0 = tbl2 P1 2 := by rw [m9]; exact p8_de0
  have p9_e40 : ptF n9.mem B 0xE40 = tbl2 P1 3 := by rw [m9]; exact p8_e40
  have p9_ea0 : ptF n9.mem B 0xEA0 = tbl2 P1 4 := by rw [m9]; exact p8_ea0
  have p9_f00 : ptF n9.mem B 0xF00 = tbl2 P1 5 := by rw [m9]; exact p8_f00
  have p9_f60 : ptF n9.mem B 0xF60 = tbl2 P1 6 := by rw [m9]; exact p8_f60
  have p9_fc0 : ptF n9.mem B 0xFC0 = tbl2 P1 7 := by rw [m9]; exact p8_fc0
  have p9_1380 : ptF n9.mem B 0x1380 = P0 := by rw [m9]; exact p8_1380
  have p9_1400 : ptF n9.mem B 0x1400 = P1 := by rw [m9]; exact p8_1400
  clear a8_1588 p8_1400 p8_1380 p8_fc0 p8_f60 p8_f00 p8_ea0 p8_e40 p8_de0 p8_d80 p8_d20 p8_cc0 p8_c60 p8_c00 p8_ba0 p8_b40 p8_ae0 p8_a80 p8_a20 p8_9c0 p8_960 p8_900 p8_8a0 p8_840 p8_7e0 p8_780 p8_720 p8_6c0 p8_660 p8_600 p8_5a0 p8_540 p8_4e0 p8_480 p8_420 p8_3a0 p8_320 a8_1460 a8_13e0 a8_400 a8_380 a8_2e0 a8_2c0 a8_2a0 w8_130 w8_12c w8_128 w8_124 w8_120 w8_11c w8_118 w8_114 w8_110 w8_10c w8_108 w8_104 w8_100 w8_fc w8_f8 w8_f4 w8_f0 w8_ec w8_e8 w8_e4 w8_e0 w8_dc w8_d8 w8_d4 w8_d0 w8_cc w8_c8 w8_c4 w8_c0 w8_bc w8_b8 w8_b4 w8_b0 w8_ac w8_a8 w8_a4 w8_a0 w8_9c w8_98 w8_94 w8_90 w8_8c w8_88 w8_84 w8_80 w8_7c w8_78 w8_70 w8_6c w8_68 w8_64 w8_60 w8_5c w8_58 w8_54 w8_50 w8_4c w8_48 w8_44 w8_40 w8_3c w8_38 w8_34 w8_30 w8_2c w8_28 w8_24 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_9 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 s8 X8 K8 P8
  -- 0x1808: to_be_byte_array
  obtain ⟨n10, P10, K10, L10⟩ := sv_tbb8 (co := 0x1480) (cx := 0x1588) F E9 (WN0.sv F fR9) s9
    sv_at_1808 sv_at_180c (by decide) (by decide) g9_2 g9_10 g9_11
    (by decide) (by decide) (by decide)
  rw [a9_1588] at L10
  have s10 := P10.st
  have fr10 := P10.fr
  have t10 : Steps n0 n10 := t9.trans P10.steps
  have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : SvCode n10.mem := E9.fr F fr10
  have V10 : SvSaves B n10.mem v := V9.keep K10 (by decide)
  have g10_2 : reg n10 sp = B + 0x21A0 := by rw [P10.regs sp (by decide), g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P10.regs (3 : Fin 32) (by decide), g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P10.regs (4 : Fin 32) (by decide), g9_4]
  have g10_8 : reg n10 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [P10.regs (8 : Fin 32) (by decide), g9_8]
  have g10_9 : reg n10 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1380 := by rw [P10.regs (9 : Fin 32) (by decide), g9_9]
  have g10_18 : reg n10 (18 : Fin 32) = out := by rw [P10.regs (18 : Fin 32) (by decide), g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [P10.regs (19 : Fin 32) (by decide), g9_19]
  have g10_20 : reg n10 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P10.regs (20 : Fin 32) (by decide), g9_20]
  have g10_21 : reg n10 (21 : Fin 32) = s5v := by rw [P10.regs (21 : Fin 32) (by decide), g9_21]
  have g10_22 : reg n10 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [P10.regs (22 : Fin 32) (by decide), g9_22]
  have g10_23 : reg n10 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by rw [P10.regs (23 : Fin 32) (by decide), g9_23]
  have g10_24 : reg n10 (24 : Fin 32) = s8v := by rw [P10.regs (24 : Fin 32) (by decide), g9_24]
  have g10_25 : reg n10 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P10.regs (25 : Fin 32) (by decide), g9_25]
  have g10_26 : reg n10 (26 : Fin 32) = x26 := by rw [P10.regs (26 : Fin 32) (by decide), g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P10.regs (27 : Fin 32) (by decide), g9_27]
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
  have a10_2a0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K10.acc (by decide) (by decide)).trans a9_2a0
  have a10_2c0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K10.acc (by decide) (by decide)).trans a9_2c0
  have a10_2e0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K10.acc (by decide) (by decide)).trans a9_2e0
  have a10_380 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := (K10.acc (by decide) (by decide)).trans a9_380
  have a10_400 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := (K10.acc (by decide) (by decide)).trans a9_400
  have a10_13e0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := (K10.acc (by decide) (by decide)).trans a9_13e0
  have a10_1460 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := (K10.acc (by decide) (by decide)).trans a9_1460
  have a10_1588 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U1 := (K10.acc (by decide) (by decide)).trans a9_1588
  have p10_320 : ptF n10.mem B 0x320 = P0 := (K10.pt (by decide) (by decide)).trans p9_320
  have p10_3a0 : ptF n10.mem B 0x3A0 = P1 := (K10.pt (by decide) (by decide)).trans p9_3a0
  have p10_420 : ptF n10.mem B 0x420 = tbl2 P0 0 := (K10.pt (by decide) (by decide)).trans p9_420
  have p10_480 : ptF n10.mem B 0x480 = tbl2 P0 1 := (K10.pt (by decide) (by decide)).trans p9_480
  have p10_4e0 : ptF n10.mem B 0x4E0 = tbl2 P0 2 := (K10.pt (by decide) (by decide)).trans p9_4e0
  have p10_540 : ptF n10.mem B 0x540 = tbl2 P0 3 := (K10.pt (by decide) (by decide)).trans p9_540
  have p10_5a0 : ptF n10.mem B 0x5A0 = tbl2 P0 4 := (K10.pt (by decide) (by decide)).trans p9_5a0
  have p10_600 : ptF n10.mem B 0x600 = tbl2 P0 5 := (K10.pt (by decide) (by decide)).trans p9_600
  have p10_660 : ptF n10.mem B 0x660 = tbl2 P0 6 := (K10.pt (by decide) (by decide)).trans p9_660
  have p10_6c0 : ptF n10.mem B 0x6C0 = tbl2 P0 7 := (K10.pt (by decide) (by decide)).trans p9_6c0
  have p10_720 : ptF n10.mem B 0x720 = tbl2 P1 0 := (K10.pt (by decide) (by decide)).trans p9_720
  have p10_780 : ptF n10.mem B 0x780 = tbl2 P1 1 := (K10.pt (by decide) (by decide)).trans p9_780
  have p10_7e0 : ptF n10.mem B 0x7E0 = tbl2 P1 2 := (K10.pt (by decide) (by decide)).trans p9_7e0
  have p10_840 : ptF n10.mem B 0x840 = tbl2 P1 3 := (K10.pt (by decide) (by decide)).trans p9_840
  have p10_8a0 : ptF n10.mem B 0x8A0 = tbl2 P1 4 := (K10.pt (by decide) (by decide)).trans p9_8a0
  have p10_900 : ptF n10.mem B 0x900 = tbl2 P1 5 := (K10.pt (by decide) (by decide)).trans p9_900
  have p10_960 : ptF n10.mem B 0x960 = tbl2 P1 6 := (K10.pt (by decide) (by decide)).trans p9_960
  have p10_9c0 : ptF n10.mem B 0x9C0 = tbl2 P1 7 := (K10.pt (by decide) (by decide)).trans p9_9c0
  have p10_a20 : ptF n10.mem B 0xA20 = tbl2 P0 0 := (K10.pt (by decide) (by decide)).trans p9_a20
  have p10_a80 : ptF n10.mem B 0xA80 = tbl2 P0 1 := (K10.pt (by decide) (by decide)).trans p9_a80
  have p10_ae0 : ptF n10.mem B 0xAE0 = tbl2 P0 2 := (K10.pt (by decide) (by decide)).trans p9_ae0
  have p10_b40 : ptF n10.mem B 0xB40 = tbl2 P0 3 := (K10.pt (by decide) (by decide)).trans p9_b40
  have p10_ba0 : ptF n10.mem B 0xBA0 = tbl2 P0 4 := (K10.pt (by decide) (by decide)).trans p9_ba0
  have p10_c00 : ptF n10.mem B 0xC00 = tbl2 P0 5 := (K10.pt (by decide) (by decide)).trans p9_c00
  have p10_c60 : ptF n10.mem B 0xC60 = tbl2 P0 6 := (K10.pt (by decide) (by decide)).trans p9_c60
  have p10_cc0 : ptF n10.mem B 0xCC0 = tbl2 P0 7 := (K10.pt (by decide) (by decide)).trans p9_cc0
  have p10_d20 : ptF n10.mem B 0xD20 = tbl2 P1 0 := (K10.pt (by decide) (by decide)).trans p9_d20
  have p10_d80 : ptF n10.mem B 0xD80 = tbl2 P1 1 := (K10.pt (by decide) (by decide)).trans p9_d80
  have p10_de0 : ptF n10.mem B 0xDE0 = tbl2 P1 2 := (K10.pt (by decide) (by decide)).trans p9_de0
  have p10_e40 : ptF n10.mem B 0xE40 = tbl2 P1 3 := (K10.pt (by decide) (by decide)).trans p9_e40
  have p10_ea0 : ptF n10.mem B 0xEA0 = tbl2 P1 4 := (K10.pt (by decide) (by decide)).trans p9_ea0
  have p10_f00 : ptF n10.mem B 0xF00 = tbl2 P1 5 := (K10.pt (by decide) (by decide)).trans p9_f00
  have p10_f60 : ptF n10.mem B 0xF60 = tbl2 P1 6 := (K10.pt (by decide) (by decide)).trans p9_f60
  have p10_fc0 : ptF n10.mem B 0xFC0 = tbl2 P1 7 := (K10.pt (by decide) (by decide)).trans p9_fc0
  have p10_1380 : ptF n10.mem B 0x1380 = P0 := (K10.pt (by decide) (by decide)).trans p9_1380
  have p10_1400 : ptF n10.mem B 0x1400 = P1 := (K10.pt (by decide) (by decide)).trans p9_1400
  have mb10_1480 : leN (memBytes n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 0x20).reverse = U1 := L10
  clear p9_1400 p9_1380 p9_fc0 p9_f60 p9_f00 p9_ea0 p9_e40 p9_de0 p9_d80 p9_d20 p9_cc0 p9_c60 p9_c00 p9_ba0 p9_b40 p9_ae0 p9_a80 p9_a20 p9_9c0 p9_960 p9_900 p9_8a0 p9_840 p9_7e0 p9_780 p9_720 p9_6c0 p9_660 p9_600 p9_5a0 p9_540 p9_4e0 p9_480 p9_420 p9_3a0 p9_320 a9_1588 a9_1460 a9_13e0 a9_400 a9_380 a9_2e0 a9_2c0 a9_2a0 w9_130 w9_12c w9_128 w9_124 w9_120 w9_11c w9_118 w9_114 w9_110 w9_10c w9_108 w9_104 w9_100 w9_fc w9_f8 w9_f4 w9_f0 w9_ec w9_e8 w9_e4 w9_e0 w9_dc w9_d8 w9_d4 w9_d0 w9_cc w9_c8 w9_c4 w9_c0 w9_bc w9_b8 w9_b4 w9_b0 w9_ac w9_a8 w9_a4 w9_a0 w9_9c w9_98 w9_94 w9_90 w9_8c w9_88 w9_84 w9_80 w9_7c w9_78 w9_70 w9_6c w9_68 w9_64 w9_60 w9_5c w9_58 w9_54 w9_50 w9_4c w9_48 w9_44 w9_40 w9_3c w9_38 w9_34 w9_30 w9_2c w9_28 w9_24 g9_11 g9_10 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 rb9 s9 m9 u9 c9
  -- 0x1810
  obtain ⟨n11, c11, u11⟩ := s10.block svEcW1810 E10.self svEcW1810_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have s11 : St n11.mem SV n11 0x181C (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have rb11 : ∀ q, reg n11 q = (runBlock svEcW1810 (n10.mem, reg n10)).2 q := fun q => by rw [u11.regs]
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
  have g11_8 : reg n11 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb11, runBlock_reg _ _ _ (8 : Fin 32) s10.zero (by decide), g10_8]
  have g11_9 : reg n11 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1380 := by
    rw [rb11, runBlock_reg _ _ _ (9 : Fin 32) s10.zero (by decide), g10_9]
  have g11_18 : reg n11 (18 : Fin 32) = out := by
    rw [rb11, runBlock_reg _ _ _ (18 : Fin 32) s10.zero (by decide), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by
    rw [rb11, runBlock_reg _ _ _ (19 : Fin 32) s10.zero (by decide), g10_19]
  have g11_20 : reg n11 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb11, runBlock_reg _ _ _ (20 : Fin 32) s10.zero (by decide), g10_20]
  have g11_21 : reg n11 (21 : Fin 32) = s5v := by
    rw [rb11, runBlock_reg _ _ _ (21 : Fin 32) s10.zero (by decide), g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by
    rw [rb11, runBlock_reg _ _ _ (22 : Fin 32) s10.zero (by decide), g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by
    rw [rb11, runBlock_reg _ _ _ (23 : Fin 32) s10.zero (by decide), g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = s8v := by
    rw [rb11, runBlock_reg _ _ _ (24 : Fin 32) s10.zero (by decide), g10_24]
  have g11_25 : reg n11 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb11, runBlock_reg _ _ _ (25 : Fin 32) s10.zero (by decide), g10_25]
  have g11_26 : reg n11 (26 : Fin 32) = x26 := by
    rw [rb11, runBlock_reg _ _ _ (26 : Fin 32) s10.zero (by decide), g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb11, runBlock_reg _ _ _ (27 : Fin 32) s10.zero (by decide), g10_27]
  have g11_10 : reg n11 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by
    rw [rb11]; simp +decide only [runBlock, BInstr.run, svEcW1810, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g10_2, g10_3, g10_4, g10_8, g10_9, g10_18, g10_19, g10_20, g10_21, g10_22, g10_23, g10_24, g10_25, g10_26, g10_27, s10.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g11_11 : reg n11 a1 = BitVec.ofNat 32 0x20 := by
    rw [rb11]; simp +decide only [runBlock, BInstr.run, svEcW1810, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g10_2, g10_3, g10_4, g10_8, g10_9, g10_18, g10_19, g10_20, g10_21, g10_22, g10_23, g10_24, g10_25, g10_26, g10_27, s10.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
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
  have a11_2a0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m11]; exact a10_2a0
  have a11_2c0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m11]; exact a10_2c0
  have a11_2e0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m11]; exact a10_2e0
  have a11_380 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m11]; exact a10_380
  have a11_400 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m11]; exact a10_400
  have a11_13e0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := by rw [m11]; exact a10_13e0
  have a11_1460 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := by rw [m11]; exact a10_1460
  have a11_1588 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U1 := by rw [m11]; exact a10_1588
  have p11_320 : ptF n11.mem B 0x320 = P0 := by rw [m11]; exact p10_320
  have p11_3a0 : ptF n11.mem B 0x3A0 = P1 := by rw [m11]; exact p10_3a0
  have p11_420 : ptF n11.mem B 0x420 = tbl2 P0 0 := by rw [m11]; exact p10_420
  have p11_480 : ptF n11.mem B 0x480 = tbl2 P0 1 := by rw [m11]; exact p10_480
  have p11_4e0 : ptF n11.mem B 0x4E0 = tbl2 P0 2 := by rw [m11]; exact p10_4e0
  have p11_540 : ptF n11.mem B 0x540 = tbl2 P0 3 := by rw [m11]; exact p10_540
  have p11_5a0 : ptF n11.mem B 0x5A0 = tbl2 P0 4 := by rw [m11]; exact p10_5a0
  have p11_600 : ptF n11.mem B 0x600 = tbl2 P0 5 := by rw [m11]; exact p10_600
  have p11_660 : ptF n11.mem B 0x660 = tbl2 P0 6 := by rw [m11]; exact p10_660
  have p11_6c0 : ptF n11.mem B 0x6C0 = tbl2 P0 7 := by rw [m11]; exact p10_6c0
  have p11_720 : ptF n11.mem B 0x720 = tbl2 P1 0 := by rw [m11]; exact p10_720
  have p11_780 : ptF n11.mem B 0x780 = tbl2 P1 1 := by rw [m11]; exact p10_780
  have p11_7e0 : ptF n11.mem B 0x7E0 = tbl2 P1 2 := by rw [m11]; exact p10_7e0
  have p11_840 : ptF n11.mem B 0x840 = tbl2 P1 3 := by rw [m11]; exact p10_840
  have p11_8a0 : ptF n11.mem B 0x8A0 = tbl2 P1 4 := by rw [m11]; exact p10_8a0
  have p11_900 : ptF n11.mem B 0x900 = tbl2 P1 5 := by rw [m11]; exact p10_900
  have p11_960 : ptF n11.mem B 0x960 = tbl2 P1 6 := by rw [m11]; exact p10_960
  have p11_9c0 : ptF n11.mem B 0x9C0 = tbl2 P1 7 := by rw [m11]; exact p10_9c0
  have p11_a20 : ptF n11.mem B 0xA20 = tbl2 P0 0 := by rw [m11]; exact p10_a20
  have p11_a80 : ptF n11.mem B 0xA80 = tbl2 P0 1 := by rw [m11]; exact p10_a80
  have p11_ae0 : ptF n11.mem B 0xAE0 = tbl2 P0 2 := by rw [m11]; exact p10_ae0
  have p11_b40 : ptF n11.mem B 0xB40 = tbl2 P0 3 := by rw [m11]; exact p10_b40
  have p11_ba0 : ptF n11.mem B 0xBA0 = tbl2 P0 4 := by rw [m11]; exact p10_ba0
  have p11_c00 : ptF n11.mem B 0xC00 = tbl2 P0 5 := by rw [m11]; exact p10_c00
  have p11_c60 : ptF n11.mem B 0xC60 = tbl2 P0 6 := by rw [m11]; exact p10_c60
  have p11_cc0 : ptF n11.mem B 0xCC0 = tbl2 P0 7 := by rw [m11]; exact p10_cc0
  have p11_d20 : ptF n11.mem B 0xD20 = tbl2 P1 0 := by rw [m11]; exact p10_d20
  have p11_d80 : ptF n11.mem B 0xD80 = tbl2 P1 1 := by rw [m11]; exact p10_d80
  have p11_de0 : ptF n11.mem B 0xDE0 = tbl2 P1 2 := by rw [m11]; exact p10_de0
  have p11_e40 : ptF n11.mem B 0xE40 = tbl2 P1 3 := by rw [m11]; exact p10_e40
  have p11_ea0 : ptF n11.mem B 0xEA0 = tbl2 P1 4 := by rw [m11]; exact p10_ea0
  have p11_f00 : ptF n11.mem B 0xF00 = tbl2 P1 5 := by rw [m11]; exact p10_f00
  have p11_f60 : ptF n11.mem B 0xF60 = tbl2 P1 6 := by rw [m11]; exact p10_f60
  have p11_fc0 : ptF n11.mem B 0xFC0 = tbl2 P1 7 := by rw [m11]; exact p10_fc0
  have p11_1380 : ptF n11.mem B 0x1380 = P0 := by rw [m11]; exact p10_1380
  have p11_1400 : ptF n11.mem B 0x1400 = P1 := by rw [m11]; exact p10_1400
  have mb11_1480 : leN (memBytes n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 0x20).reverse = U1 := by rw [m11]; exact mb10_1480
  clear mb10_1480 p10_1400 p10_1380 p10_fc0 p10_f60 p10_f00 p10_ea0 p10_e40 p10_de0 p10_d80 p10_d20 p10_cc0 p10_c60 p10_c00 p10_ba0 p10_b40 p10_ae0 p10_a80 p10_a20 p10_9c0 p10_960 p10_900 p10_8a0 p10_840 p10_7e0 p10_780 p10_720 p10_6c0 p10_660 p10_600 p10_5a0 p10_540 p10_4e0 p10_480 p10_420 p10_3a0 p10_320 a10_1588 a10_1460 a10_13e0 a10_400 a10_380 a10_2e0 a10_2c0 a10_2a0 w10_130 w10_12c w10_128 w10_124 w10_120 w10_11c w10_118 w10_114 w10_110 w10_10c w10_108 w10_104 w10_100 w10_fc w10_f8 w10_f4 w10_f0 w10_ec w10_e8 w10_e4 w10_e0 w10_dc w10_d8 w10_d4 w10_d0 w10_cc w10_c8 w10_c4 w10_c0 w10_bc w10_b8 w10_b4 w10_b0 w10_ac w10_a8 w10_a4 w10_a0 w10_9c w10_98 w10_94 w10_90 w10_8c w10_88 w10_84 w10_80 w10_7c w10_78 w10_70 w10_6c w10_68 w10_64 w10_60 w10_5c w10_58 w10_54 w10_50 w10_4c w10_48 w10_44 w10_40 w10_3c w10_38 w10_34 w10_30 w10_2c w10_28 w10_24 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 s10 L10 K10 P10
  -- 0x181C: reverse
  obtain ⟨n12, P12, K12, R12⟩ := sv_rev (c := 0x1480) (N := 0x20) F E11 (WN0.sv F fR11) s11
    sv_at_181c sv_at_1820 (by decide) (by decide) g11_10 g11_11 (by decide)
  have mbr12 := mb11_1480
  have s12 := P12.st
  have fr12 := P12.fr
  have t12 : Steps n0 n12 := t11.trans P12.steps
  have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : SvCode n12.mem := E11.fr F fr12
  have V12 : SvSaves B n12.mem v := V11.keep K12 (by decide)
  have g12_2 : reg n12 sp = B + 0x21A0 := by rw [P12.regs sp (by decide), g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P12.regs (3 : Fin 32) (by decide), g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P12.regs (4 : Fin 32) (by decide), g11_4]
  have g12_8 : reg n12 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [P12.regs (8 : Fin 32) (by decide), g11_8]
  have g12_9 : reg n12 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1380 := by rw [P12.regs (9 : Fin 32) (by decide), g11_9]
  have g12_18 : reg n12 (18 : Fin 32) = out := by rw [P12.regs (18 : Fin 32) (by decide), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [P12.regs (19 : Fin 32) (by decide), g11_19]
  have g12_20 : reg n12 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P12.regs (20 : Fin 32) (by decide), g11_20]
  have g12_21 : reg n12 (21 : Fin 32) = s5v := by rw [P12.regs (21 : Fin 32) (by decide), g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [P12.regs (22 : Fin 32) (by decide), g11_22]
  have g12_23 : reg n12 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by rw [P12.regs (23 : Fin 32) (by decide), g11_23]
  have g12_24 : reg n12 (24 : Fin 32) = s8v := by rw [P12.regs (24 : Fin 32) (by decide), g11_24]
  have g12_25 : reg n12 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P12.regs (25 : Fin 32) (by decide), g11_25]
  have g12_26 : reg n12 (26 : Fin 32) = x26 := by rw [P12.regs (26 : Fin 32) (by decide), g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P12.regs (27 : Fin 32) (by decide), g11_27]
  have w12_24 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K12.w32 (by decide) (by decide)).trans w11_24
  have w12_28 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K12.w32 (by decide) (by decide)).trans w11_28
  have w12_2c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K12.w32 (by decide) (by decide)).trans w11_2c
  have w12_30 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K12.w32 (by decide) (by decide)).trans w11_30
  have w12_34 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K12.w32 (by decide) (by decide)).trans w11_34
  have w12_38 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K12.w32 (by decide) (by decide)).trans w11_38
  have w12_3c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K12.w32 (by decide) (by decide)).trans w11_3c
  have w12_40 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K12.w32 (by decide) (by decide)).trans w11_40
  have w12_44 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K12.w32 (by decide) (by decide)).trans w11_44
  have w12_48 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K12.w32 (by decide) (by decide)).trans w11_48
  have w12_4c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K12.w32 (by decide) (by decide)).trans w11_4c
  have w12_50 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K12.w32 (by decide) (by decide)).trans w11_50
  have w12_54 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K12.w32 (by decide) (by decide)).trans w11_54
  have w12_58 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K12.w32 (by decide) (by decide)).trans w11_58
  have w12_5c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K12.w32 (by decide) (by decide)).trans w11_5c
  have w12_60 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K12.w32 (by decide) (by decide)).trans w11_60
  have w12_64 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K12.w32 (by decide) (by decide)).trans w11_64
  have w12_68 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K12.w32 (by decide) (by decide)).trans w11_68
  have w12_6c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K12.w32 (by decide) (by decide)).trans w11_6c
  have w12_70 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K12.w32 (by decide) (by decide)).trans w11_70
  have w12_78 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := (K12.w32 (by decide) (by decide)).trans w11_78
  have w12_7c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K12.w32 (by decide) (by decide)).trans w11_7c
  have w12_80 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K12.w32 (by decide) (by decide)).trans w11_80
  have w12_84 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K12.w32 (by decide) (by decide)).trans w11_84
  have w12_88 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K12.w32 (by decide) (by decide)).trans w11_88
  have w12_8c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K12.w32 (by decide) (by decide)).trans w11_8c
  have w12_90 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K12.w32 (by decide) (by decide)).trans w11_90
  have w12_94 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K12.w32 (by decide) (by decide)).trans w11_94
  have w12_98 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K12.w32 (by decide) (by decide)).trans w11_98
  have w12_9c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K12.w32 (by decide) (by decide)).trans w11_9c
  have w12_a0 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K12.w32 (by decide) (by decide)).trans w11_a0
  have w12_a4 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K12.w32 (by decide) (by decide)).trans w11_a4
  have w12_a8 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K12.w32 (by decide) (by decide)).trans w11_a8
  have w12_ac : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K12.w32 (by decide) (by decide)).trans w11_ac
  have w12_b0 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K12.w32 (by decide) (by decide)).trans w11_b0
  have w12_b4 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K12.w32 (by decide) (by decide)).trans w11_b4
  have w12_b8 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K12.w32 (by decide) (by decide)).trans w11_b8
  have w12_bc : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K12.w32 (by decide) (by decide)).trans w11_bc
  have w12_c0 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K12.w32 (by decide) (by decide)).trans w11_c0
  have w12_c4 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K12.w32 (by decide) (by decide)).trans w11_c4
  have w12_c8 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K12.w32 (by decide) (by decide)).trans w11_c8
  have w12_cc : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K12.w32 (by decide) (by decide)).trans w11_cc
  have w12_d0 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K12.w32 (by decide) (by decide)).trans w11_d0
  have w12_d4 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K12.w32 (by decide) (by decide)).trans w11_d4
  have w12_d8 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K12.w32 (by decide) (by decide)).trans w11_d8
  have w12_dc : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K12.w32 (by decide) (by decide)).trans w11_dc
  have w12_e0 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K12.w32 (by decide) (by decide)).trans w11_e0
  have w12_e4 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K12.w32 (by decide) (by decide)).trans w11_e4
  have w12_e8 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K12.w32 (by decide) (by decide)).trans w11_e8
  have w12_ec : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K12.w32 (by decide) (by decide)).trans w11_ec
  have w12_f0 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K12.w32 (by decide) (by decide)).trans w11_f0
  have w12_f4 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K12.w32 (by decide) (by decide)).trans w11_f4
  have w12_f8 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K12.w32 (by decide) (by decide)).trans w11_f8
  have w12_fc : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K12.w32 (by decide) (by decide)).trans w11_fc
  have w12_100 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K12.w32 (by decide) (by decide)).trans w11_100
  have w12_104 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K12.w32 (by decide) (by decide)).trans w11_104
  have w12_108 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K12.w32 (by decide) (by decide)).trans w11_108
  have w12_10c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K12.w32 (by decide) (by decide)).trans w11_10c
  have w12_110 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K12.w32 (by decide) (by decide)).trans w11_110
  have w12_114 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K12.w32 (by decide) (by decide)).trans w11_114
  have w12_118 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K12.w32 (by decide) (by decide)).trans w11_118
  have w12_11c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K12.w32 (by decide) (by decide)).trans w11_11c
  have w12_120 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K12.w32 (by decide) (by decide)).trans w11_120
  have w12_124 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K12.w32 (by decide) (by decide)).trans w11_124
  have w12_128 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K12.w32 (by decide) (by decide)).trans w11_128
  have w12_12c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K12.w32 (by decide) (by decide)).trans w11_12c
  have w12_130 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K12.w32 (by decide) (by decide)).trans w11_130
  have a12_2a0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K12.acc (by decide) (by decide)).trans a11_2a0
  have a12_2c0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K12.acc (by decide) (by decide)).trans a11_2c0
  have a12_2e0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K12.acc (by decide) (by decide)).trans a11_2e0
  have a12_380 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := (K12.acc (by decide) (by decide)).trans a11_380
  have a12_400 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := (K12.acc (by decide) (by decide)).trans a11_400
  have a12_13e0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := (K12.acc (by decide) (by decide)).trans a11_13e0
  have a12_1460 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := (K12.acc (by decide) (by decide)).trans a11_1460
  have a12_1588 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U1 := (K12.acc (by decide) (by decide)).trans a11_1588
  have p12_320 : ptF n12.mem B 0x320 = P0 := (K12.pt (by decide) (by decide)).trans p11_320
  have p12_3a0 : ptF n12.mem B 0x3A0 = P1 := (K12.pt (by decide) (by decide)).trans p11_3a0
  have p12_420 : ptF n12.mem B 0x420 = tbl2 P0 0 := (K12.pt (by decide) (by decide)).trans p11_420
  have p12_480 : ptF n12.mem B 0x480 = tbl2 P0 1 := (K12.pt (by decide) (by decide)).trans p11_480
  have p12_4e0 : ptF n12.mem B 0x4E0 = tbl2 P0 2 := (K12.pt (by decide) (by decide)).trans p11_4e0
  have p12_540 : ptF n12.mem B 0x540 = tbl2 P0 3 := (K12.pt (by decide) (by decide)).trans p11_540
  have p12_5a0 : ptF n12.mem B 0x5A0 = tbl2 P0 4 := (K12.pt (by decide) (by decide)).trans p11_5a0
  have p12_600 : ptF n12.mem B 0x600 = tbl2 P0 5 := (K12.pt (by decide) (by decide)).trans p11_600
  have p12_660 : ptF n12.mem B 0x660 = tbl2 P0 6 := (K12.pt (by decide) (by decide)).trans p11_660
  have p12_6c0 : ptF n12.mem B 0x6C0 = tbl2 P0 7 := (K12.pt (by decide) (by decide)).trans p11_6c0
  have p12_720 : ptF n12.mem B 0x720 = tbl2 P1 0 := (K12.pt (by decide) (by decide)).trans p11_720
  have p12_780 : ptF n12.mem B 0x780 = tbl2 P1 1 := (K12.pt (by decide) (by decide)).trans p11_780
  have p12_7e0 : ptF n12.mem B 0x7E0 = tbl2 P1 2 := (K12.pt (by decide) (by decide)).trans p11_7e0
  have p12_840 : ptF n12.mem B 0x840 = tbl2 P1 3 := (K12.pt (by decide) (by decide)).trans p11_840
  have p12_8a0 : ptF n12.mem B 0x8A0 = tbl2 P1 4 := (K12.pt (by decide) (by decide)).trans p11_8a0
  have p12_900 : ptF n12.mem B 0x900 = tbl2 P1 5 := (K12.pt (by decide) (by decide)).trans p11_900
  have p12_960 : ptF n12.mem B 0x960 = tbl2 P1 6 := (K12.pt (by decide) (by decide)).trans p11_960
  have p12_9c0 : ptF n12.mem B 0x9C0 = tbl2 P1 7 := (K12.pt (by decide) (by decide)).trans p11_9c0
  have p12_a20 : ptF n12.mem B 0xA20 = tbl2 P0 0 := (K12.pt (by decide) (by decide)).trans p11_a20
  have p12_a80 : ptF n12.mem B 0xA80 = tbl2 P0 1 := (K12.pt (by decide) (by decide)).trans p11_a80
  have p12_ae0 : ptF n12.mem B 0xAE0 = tbl2 P0 2 := (K12.pt (by decide) (by decide)).trans p11_ae0
  have p12_b40 : ptF n12.mem B 0xB40 = tbl2 P0 3 := (K12.pt (by decide) (by decide)).trans p11_b40
  have p12_ba0 : ptF n12.mem B 0xBA0 = tbl2 P0 4 := (K12.pt (by decide) (by decide)).trans p11_ba0
  have p12_c00 : ptF n12.mem B 0xC00 = tbl2 P0 5 := (K12.pt (by decide) (by decide)).trans p11_c00
  have p12_c60 : ptF n12.mem B 0xC60 = tbl2 P0 6 := (K12.pt (by decide) (by decide)).trans p11_c60
  have p12_cc0 : ptF n12.mem B 0xCC0 = tbl2 P0 7 := (K12.pt (by decide) (by decide)).trans p11_cc0
  have p12_d20 : ptF n12.mem B 0xD20 = tbl2 P1 0 := (K12.pt (by decide) (by decide)).trans p11_d20
  have p12_d80 : ptF n12.mem B 0xD80 = tbl2 P1 1 := (K12.pt (by decide) (by decide)).trans p11_d80
  have p12_de0 : ptF n12.mem B 0xDE0 = tbl2 P1 2 := (K12.pt (by decide) (by decide)).trans p11_de0
  have p12_e40 : ptF n12.mem B 0xE40 = tbl2 P1 3 := (K12.pt (by decide) (by decide)).trans p11_e40
  have p12_ea0 : ptF n12.mem B 0xEA0 = tbl2 P1 4 := (K12.pt (by decide) (by decide)).trans p11_ea0
  have p12_f00 : ptF n12.mem B 0xF00 = tbl2 P1 5 := (K12.pt (by decide) (by decide)).trans p11_f00
  have p12_f60 : ptF n12.mem B 0xF60 = tbl2 P1 6 := (K12.pt (by decide) (by decide)).trans p11_f60
  have p12_fc0 : ptF n12.mem B 0xFC0 = tbl2 P1 7 := (K12.pt (by decide) (by decide)).trans p11_fc0
  have p12_1380 : ptF n12.mem B 0x1380 = P0 := (K12.pt (by decide) (by decide)).trans p11_1380
  have p12_1400 : ptF n12.mem B 0x1400 = P1 := (K12.pt (by decide) (by decide)).trans p11_1400
  have mb12_1480 : leN (memBytes n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 0x20) = U1 := by rw [R12]; exact mbr12
  clear mb11_1480 p11_1400 p11_1380 p11_fc0 p11_f60 p11_f00 p11_ea0 p11_e40 p11_de0 p11_d80 p11_d20 p11_cc0 p11_c60 p11_c00 p11_ba0 p11_b40 p11_ae0 p11_a80 p11_a20 p11_9c0 p11_960 p11_900 p11_8a0 p11_840 p11_7e0 p11_780 p11_720 p11_6c0 p11_660 p11_600 p11_5a0 p11_540 p11_4e0 p11_480 p11_420 p11_3a0 p11_320 a11_1588 a11_1460 a11_13e0 a11_400 a11_380 a11_2e0 a11_2c0 a11_2a0 w11_130 w11_12c w11_128 w11_124 w11_120 w11_11c w11_118 w11_114 w11_110 w11_10c w11_108 w11_104 w11_100 w11_fc w11_f8 w11_f4 w11_f0 w11_ec w11_e8 w11_e4 w11_e0 w11_dc w11_d8 w11_d4 w11_d0 w11_cc w11_c8 w11_c4 w11_c0 w11_bc w11_b8 w11_b4 w11_b0 w11_ac w11_a8 w11_a4 w11_a0 w11_9c w11_98 w11_94 w11_90 w11_8c w11_88 w11_84 w11_80 w11_7c w11_78 w11_70 w11_6c w11_68 w11_64 w11_60 w11_5c w11_58 w11_54 w11_50 w11_4c w11_48 w11_44 w11_40 w11_3c w11_38 w11_34 w11_30 w11_2c w11_28 w11_24 g11_11 g11_10 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_9 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 rb11 s11 m11 u11 c11
  -- 0x1824
  obtain ⟨n13, c13, u13⟩ := s12.block svEcW1824 E12.self svEcW1824_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m13 : n13.mem = n12.mem := u13.mem
  have s13 : St n13.mem SV n13 0x1838 (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
  have rb13 : ∀ q, reg n13 q = (runBlock svEcW1824 (n12.mem, reg n12)).2 q := fun q => by rw [u13.regs]
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
  have g13_8 : reg n13 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb13, runBlock_reg _ _ _ (8 : Fin 32) s12.zero (by decide), g12_8]
  have g13_9 : reg n13 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1380 := by
    rw [rb13, runBlock_reg _ _ _ (9 : Fin 32) s12.zero (by decide), g12_9]
  have g13_18 : reg n13 (18 : Fin 32) = out := by
    rw [rb13, runBlock_reg _ _ _ (18 : Fin 32) s12.zero (by decide), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = bp := by
    rw [rb13, runBlock_reg _ _ _ (19 : Fin 32) s12.zero (by decide), g12_19]
  have g13_20 : reg n13 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb13, runBlock_reg _ _ _ (20 : Fin 32) s12.zero (by decide), g12_20]
  have g13_21 : reg n13 (21 : Fin 32) = s5v := by
    rw [rb13, runBlock_reg _ _ _ (21 : Fin 32) s12.zero (by decide), g12_21]
  have g13_22 : reg n13 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by
    rw [rb13, runBlock_reg _ _ _ (22 : Fin 32) s12.zero (by decide), g12_22]
  have g13_23 : reg n13 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by
    rw [rb13, runBlock_reg _ _ _ (23 : Fin 32) s12.zero (by decide), g12_23]
  have g13_24 : reg n13 (24 : Fin 32) = s8v := by
    rw [rb13, runBlock_reg _ _ _ (24 : Fin 32) s12.zero (by decide), g12_24]
  have g13_25 : reg n13 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb13, runBlock_reg _ _ _ (25 : Fin 32) s12.zero (by decide), g12_25]
  have g13_26 : reg n13 (26 : Fin 32) = x26 := by
    rw [rb13, runBlock_reg _ _ _ (26 : Fin 32) s12.zero (by decide), g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb13, runBlock_reg _ _ _ (27 : Fin 32) s12.zero (by decide), g12_27]
  have g13_10 : reg n13 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
    rw [rb13]; simp +decide only [runBlock, BInstr.run, svEcW1824, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g12_2, g12_3, g12_4, g12_8, g12_9, g12_18, g12_19, g12_20, g12_21, g12_22, g12_23, g12_24, g12_25, g12_26, g12_27, s12.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g13_11 : reg n13 a1 = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by
    rw [rb13]; simp +decide only [runBlock, BInstr.run, svEcW1824, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g12_2, g12_3, g12_4, g12_8, g12_9, g12_18, g12_19, g12_20, g12_21, g12_22, g12_23, g12_24, g12_25, g12_26, g12_27, s12.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g13_12 : reg n13 a2 = BitVec.ofNat 32 0x20 := by
    rw [rb13]; simp +decide only [runBlock, BInstr.run, svEcW1824, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g12_2, g12_3, g12_4, g12_8, g12_9, g12_18, g12_19, g12_20, g12_21, g12_22, g12_23, g12_24, g12_25, g12_26, g12_27, s12.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
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
  have a13_2a0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m13]; exact a12_2a0
  have a13_2c0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m13]; exact a12_2c0
  have a13_2e0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m13]; exact a12_2e0
  have a13_380 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m13]; exact a12_380
  have a13_400 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m13]; exact a12_400
  have a13_13e0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := by rw [m13]; exact a12_13e0
  have a13_1460 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := by rw [m13]; exact a12_1460
  have a13_1588 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U1 := by rw [m13]; exact a12_1588
  have p13_320 : ptF n13.mem B 0x320 = P0 := by rw [m13]; exact p12_320
  have p13_3a0 : ptF n13.mem B 0x3A0 = P1 := by rw [m13]; exact p12_3a0
  have p13_420 : ptF n13.mem B 0x420 = tbl2 P0 0 := by rw [m13]; exact p12_420
  have p13_480 : ptF n13.mem B 0x480 = tbl2 P0 1 := by rw [m13]; exact p12_480
  have p13_4e0 : ptF n13.mem B 0x4E0 = tbl2 P0 2 := by rw [m13]; exact p12_4e0
  have p13_540 : ptF n13.mem B 0x540 = tbl2 P0 3 := by rw [m13]; exact p12_540
  have p13_5a0 : ptF n13.mem B 0x5A0 = tbl2 P0 4 := by rw [m13]; exact p12_5a0
  have p13_600 : ptF n13.mem B 0x600 = tbl2 P0 5 := by rw [m13]; exact p12_600
  have p13_660 : ptF n13.mem B 0x660 = tbl2 P0 6 := by rw [m13]; exact p12_660
  have p13_6c0 : ptF n13.mem B 0x6C0 = tbl2 P0 7 := by rw [m13]; exact p12_6c0
  have p13_720 : ptF n13.mem B 0x720 = tbl2 P1 0 := by rw [m13]; exact p12_720
  have p13_780 : ptF n13.mem B 0x780 = tbl2 P1 1 := by rw [m13]; exact p12_780
  have p13_7e0 : ptF n13.mem B 0x7E0 = tbl2 P1 2 := by rw [m13]; exact p12_7e0
  have p13_840 : ptF n13.mem B 0x840 = tbl2 P1 3 := by rw [m13]; exact p12_840
  have p13_8a0 : ptF n13.mem B 0x8A0 = tbl2 P1 4 := by rw [m13]; exact p12_8a0
  have p13_900 : ptF n13.mem B 0x900 = tbl2 P1 5 := by rw [m13]; exact p12_900
  have p13_960 : ptF n13.mem B 0x960 = tbl2 P1 6 := by rw [m13]; exact p12_960
  have p13_9c0 : ptF n13.mem B 0x9C0 = tbl2 P1 7 := by rw [m13]; exact p12_9c0
  have p13_a20 : ptF n13.mem B 0xA20 = tbl2 P0 0 := by rw [m13]; exact p12_a20
  have p13_a80 : ptF n13.mem B 0xA80 = tbl2 P0 1 := by rw [m13]; exact p12_a80
  have p13_ae0 : ptF n13.mem B 0xAE0 = tbl2 P0 2 := by rw [m13]; exact p12_ae0
  have p13_b40 : ptF n13.mem B 0xB40 = tbl2 P0 3 := by rw [m13]; exact p12_b40
  have p13_ba0 : ptF n13.mem B 0xBA0 = tbl2 P0 4 := by rw [m13]; exact p12_ba0
  have p13_c00 : ptF n13.mem B 0xC00 = tbl2 P0 5 := by rw [m13]; exact p12_c00
  have p13_c60 : ptF n13.mem B 0xC60 = tbl2 P0 6 := by rw [m13]; exact p12_c60
  have p13_cc0 : ptF n13.mem B 0xCC0 = tbl2 P0 7 := by rw [m13]; exact p12_cc0
  have p13_d20 : ptF n13.mem B 0xD20 = tbl2 P1 0 := by rw [m13]; exact p12_d20
  have p13_d80 : ptF n13.mem B 0xD80 = tbl2 P1 1 := by rw [m13]; exact p12_d80
  have p13_de0 : ptF n13.mem B 0xDE0 = tbl2 P1 2 := by rw [m13]; exact p12_de0
  have p13_e40 : ptF n13.mem B 0xE40 = tbl2 P1 3 := by rw [m13]; exact p12_e40
  have p13_ea0 : ptF n13.mem B 0xEA0 = tbl2 P1 4 := by rw [m13]; exact p12_ea0
  have p13_f00 : ptF n13.mem B 0xF00 = tbl2 P1 5 := by rw [m13]; exact p12_f00
  have p13_f60 : ptF n13.mem B 0xF60 = tbl2 P1 6 := by rw [m13]; exact p12_f60
  have p13_fc0 : ptF n13.mem B 0xFC0 = tbl2 P1 7 := by rw [m13]; exact p12_fc0
  have p13_1380 : ptF n13.mem B 0x1380 = P0 := by rw [m13]; exact p12_1380
  have p13_1400 : ptF n13.mem B 0x1400 = P1 := by rw [m13]; exact p12_1400
  have mb13_1480 : leN (memBytes n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 0x20) = U1 := by rw [m13]; exact mb12_1480
  clear mb12_1480 p12_1400 p12_1380 p12_fc0 p12_f60 p12_f00 p12_ea0 p12_e40 p12_de0 p12_d80 p12_d20 p12_cc0 p12_c60 p12_c00 p12_ba0 p12_b40 p12_ae0 p12_a80 p12_a20 p12_9c0 p12_960 p12_900 p12_8a0 p12_840 p12_7e0 p12_780 p12_720 p12_6c0 p12_660 p12_600 p12_5a0 p12_540 p12_4e0 p12_480 p12_420 p12_3a0 p12_320 a12_1588 a12_1460 a12_13e0 a12_400 a12_380 a12_2e0 a12_2c0 a12_2a0 w12_130 w12_12c w12_128 w12_124 w12_120 w12_11c w12_118 w12_114 w12_110 w12_10c w12_108 w12_104 w12_100 w12_fc w12_f8 w12_f4 w12_f0 w12_ec w12_e8 w12_e4 w12_e0 w12_dc w12_d8 w12_d4 w12_d0 w12_cc w12_c8 w12_c4 w12_c0 w12_bc w12_b8 w12_b4 w12_b0 w12_ac w12_a8 w12_a4 w12_a0 w12_9c w12_98 w12_94 w12_90 w12_8c w12_88 w12_84 w12_80 w12_7c w12_78 w12_70 w12_6c w12_68 w12_64 w12_60 w12_5c w12_58 w12_54 w12_50 w12_4c w12_48 w12_44 w12_40 w12_3c w12_38 w12_34 w12_30 w12_2c w12_28 w12_24 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_9 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 s12 mbr12 R12 K12 P12
  -- 0x1838: memcpy
  obtain ⟨n14, P14, K14, X14⟩ := sv_mc (c := 0x1320) (d := 0x1480) (N := 0x20) F E13 s13 sv_at_1838 sv_at_183c
    (by decide) (by decide) g13_2 g13_10 g13_11 g13_12
    (by decide) (by decide) (by decide)
  have s14 := P14.st
  have fr14 := P14.fr
  have t14 : Steps n0 n14 := t13.trans P14.steps
  have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : SvCode n14.mem := E13.fr F fr14
  have V14 : SvSaves B n14.mem v := V13.keep K14 (by decide)
  have g14_2 : reg n14 sp = B + 0x21A0 := by rw [P14.regs sp (by decide), g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P14.regs (3 : Fin 32) (by decide), g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P14.regs (4 : Fin 32) (by decide), g13_4]
  have g14_8 : reg n14 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [P14.regs (8 : Fin 32) (by decide), g13_8]
  have g14_9 : reg n14 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1380 := by rw [P14.regs (9 : Fin 32) (by decide), g13_9]
  have g14_18 : reg n14 (18 : Fin 32) = out := by rw [P14.regs (18 : Fin 32) (by decide), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [P14.regs (19 : Fin 32) (by decide), g13_19]
  have g14_20 : reg n14 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P14.regs (20 : Fin 32) (by decide), g13_20]
  have g14_21 : reg n14 (21 : Fin 32) = s5v := by rw [P14.regs (21 : Fin 32) (by decide), g13_21]
  have g14_22 : reg n14 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [P14.regs (22 : Fin 32) (by decide), g13_22]
  have g14_23 : reg n14 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by rw [P14.regs (23 : Fin 32) (by decide), g13_23]
  have g14_24 : reg n14 (24 : Fin 32) = s8v := by rw [P14.regs (24 : Fin 32) (by decide), g13_24]
  have g14_25 : reg n14 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P14.regs (25 : Fin 32) (by decide), g13_25]
  have g14_26 : reg n14 (26 : Fin 32) = x26 := by rw [P14.regs (26 : Fin 32) (by decide), g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P14.regs (27 : Fin 32) (by decide), g13_27]
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
  have a14_2a0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K14.acc (by decide) (by decide)).trans a13_2a0
  have a14_2c0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K14.acc (by decide) (by decide)).trans a13_2c0
  have a14_2e0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K14.acc (by decide) (by decide)).trans a13_2e0
  have a14_380 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := (K14.acc (by decide) (by decide)).trans a13_380
  have a14_400 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := (K14.acc (by decide) (by decide)).trans a13_400
  have a14_13e0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := (K14.acc (by decide) (by decide)).trans a13_13e0
  have a14_1460 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := (K14.acc (by decide) (by decide)).trans a13_1460
  have a14_1588 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U1 := (K14.acc (by decide) (by decide)).trans a13_1588
  have p14_320 : ptF n14.mem B 0x320 = P0 := (K14.pt (by decide) (by decide)).trans p13_320
  have p14_3a0 : ptF n14.mem B 0x3A0 = P1 := (K14.pt (by decide) (by decide)).trans p13_3a0
  have p14_420 : ptF n14.mem B 0x420 = tbl2 P0 0 := (K14.pt (by decide) (by decide)).trans p13_420
  have p14_480 : ptF n14.mem B 0x480 = tbl2 P0 1 := (K14.pt (by decide) (by decide)).trans p13_480
  have p14_4e0 : ptF n14.mem B 0x4E0 = tbl2 P0 2 := (K14.pt (by decide) (by decide)).trans p13_4e0
  have p14_540 : ptF n14.mem B 0x540 = tbl2 P0 3 := (K14.pt (by decide) (by decide)).trans p13_540
  have p14_5a0 : ptF n14.mem B 0x5A0 = tbl2 P0 4 := (K14.pt (by decide) (by decide)).trans p13_5a0
  have p14_600 : ptF n14.mem B 0x600 = tbl2 P0 5 := (K14.pt (by decide) (by decide)).trans p13_600
  have p14_660 : ptF n14.mem B 0x660 = tbl2 P0 6 := (K14.pt (by decide) (by decide)).trans p13_660
  have p14_6c0 : ptF n14.mem B 0x6C0 = tbl2 P0 7 := (K14.pt (by decide) (by decide)).trans p13_6c0
  have p14_720 : ptF n14.mem B 0x720 = tbl2 P1 0 := (K14.pt (by decide) (by decide)).trans p13_720
  have p14_780 : ptF n14.mem B 0x780 = tbl2 P1 1 := (K14.pt (by decide) (by decide)).trans p13_780
  have p14_7e0 : ptF n14.mem B 0x7E0 = tbl2 P1 2 := (K14.pt (by decide) (by decide)).trans p13_7e0
  have p14_840 : ptF n14.mem B 0x840 = tbl2 P1 3 := (K14.pt (by decide) (by decide)).trans p13_840
  have p14_8a0 : ptF n14.mem B 0x8A0 = tbl2 P1 4 := (K14.pt (by decide) (by decide)).trans p13_8a0
  have p14_900 : ptF n14.mem B 0x900 = tbl2 P1 5 := (K14.pt (by decide) (by decide)).trans p13_900
  have p14_960 : ptF n14.mem B 0x960 = tbl2 P1 6 := (K14.pt (by decide) (by decide)).trans p13_960
  have p14_9c0 : ptF n14.mem B 0x9C0 = tbl2 P1 7 := (K14.pt (by decide) (by decide)).trans p13_9c0
  have p14_a20 : ptF n14.mem B 0xA20 = tbl2 P0 0 := (K14.pt (by decide) (by decide)).trans p13_a20
  have p14_a80 : ptF n14.mem B 0xA80 = tbl2 P0 1 := (K14.pt (by decide) (by decide)).trans p13_a80
  have p14_ae0 : ptF n14.mem B 0xAE0 = tbl2 P0 2 := (K14.pt (by decide) (by decide)).trans p13_ae0
  have p14_b40 : ptF n14.mem B 0xB40 = tbl2 P0 3 := (K14.pt (by decide) (by decide)).trans p13_b40
  have p14_ba0 : ptF n14.mem B 0xBA0 = tbl2 P0 4 := (K14.pt (by decide) (by decide)).trans p13_ba0
  have p14_c00 : ptF n14.mem B 0xC00 = tbl2 P0 5 := (K14.pt (by decide) (by decide)).trans p13_c00
  have p14_c60 : ptF n14.mem B 0xC60 = tbl2 P0 6 := (K14.pt (by decide) (by decide)).trans p13_c60
  have p14_cc0 : ptF n14.mem B 0xCC0 = tbl2 P0 7 := (K14.pt (by decide) (by decide)).trans p13_cc0
  have p14_d20 : ptF n14.mem B 0xD20 = tbl2 P1 0 := (K14.pt (by decide) (by decide)).trans p13_d20
  have p14_d80 : ptF n14.mem B 0xD80 = tbl2 P1 1 := (K14.pt (by decide) (by decide)).trans p13_d80
  have p14_de0 : ptF n14.mem B 0xDE0 = tbl2 P1 2 := (K14.pt (by decide) (by decide)).trans p13_de0
  have p14_e40 : ptF n14.mem B 0xE40 = tbl2 P1 3 := (K14.pt (by decide) (by decide)).trans p13_e40
  have p14_ea0 : ptF n14.mem B 0xEA0 = tbl2 P1 4 := (K14.pt (by decide) (by decide)).trans p13_ea0
  have p14_f00 : ptF n14.mem B 0xF00 = tbl2 P1 5 := (K14.pt (by decide) (by decide)).trans p13_f00
  have p14_f60 : ptF n14.mem B 0xF60 = tbl2 P1 6 := (K14.pt (by decide) (by decide)).trans p13_f60
  have p14_fc0 : ptF n14.mem B 0xFC0 = tbl2 P1 7 := (K14.pt (by decide) (by decide)).trans p13_fc0
  have p14_1380 : ptF n14.mem B 0x1380 = P0 := (K14.pt (by decide) (by decide)).trans p13_1380
  have p14_1400 : ptF n14.mem B 0x1400 = P1 := (K14.pt (by decide) (by decide)).trans p13_1400
  have mb14_1480 : leN (memBytes n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 0x20) = U1 := by rw [K14.mb (by decide) (by decide)]; exact mb13_1480
  have mb14_1320 : leN (memBytes n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U1 := by
    rw [memBytes_cp (S := B + 0x21A0) (c := 0x1320) (d := 0x1480) (N := 0x20) fun q hq => by
      rw [show 0x1320 + q = 0x1320 + (0x0 + q) by omega, X14 (0x0 + q) (by omega),
        show 0x1480 + (0x0 + q) = 0x1480 + q by omega]]; exact mb13_1480
  clear mb13_1480 p13_1400 p13_1380 p13_fc0 p13_f60 p13_f00 p13_ea0 p13_e40 p13_de0 p13_d80 p13_d20 p13_cc0 p13_c60 p13_c00 p13_ba0 p13_b40 p13_ae0 p13_a80 p13_a20 p13_9c0 p13_960 p13_900 p13_8a0 p13_840 p13_7e0 p13_780 p13_720 p13_6c0 p13_660 p13_600 p13_5a0 p13_540 p13_4e0 p13_480 p13_420 p13_3a0 p13_320 a13_1588 a13_1460 a13_13e0 a13_400 a13_380 a13_2e0 a13_2c0 a13_2a0 w13_130 w13_12c w13_128 w13_124 w13_120 w13_11c w13_118 w13_114 w13_110 w13_10c w13_108 w13_104 w13_100 w13_fc w13_f8 w13_f4 w13_f0 w13_ec w13_e8 w13_e4 w13_e0 w13_dc w13_d8 w13_d4 w13_d0 w13_cc w13_c8 w13_c4 w13_c0 w13_bc w13_b8 w13_b4 w13_b0 w13_ac w13_a8 w13_a4 w13_a0 w13_9c w13_98 w13_94 w13_90 w13_8c w13_88 w13_84 w13_80 w13_7c w13_78 w13_70 w13_6c w13_68 w13_64 w13_60 w13_5c w13_58 w13_54 w13_50 w13_4c w13_48 w13_44 w13_40 w13_3c w13_38 w13_34 w13_30 w13_2c w13_28 w13_24 g13_12 g13_11 g13_10 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_9 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 rb13 s13 m13 u13 c13
  -- 0x1840
  obtain ⟨n15, c15, u15⟩ := s14.block svEcW1840 E14.self svEcW1840_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m15 : n15.mem = n14.mem := u15.mem
  have s15 : St n15.mem SV n15 0x184C (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
  have rb15 : ∀ q, reg n15 q = (runBlock svEcW1840 (n14.mem, reg n14)).2 q := fun q => by rw [u15.regs]
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
  have g15_8 : reg n15 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb15, runBlock_reg _ _ _ (8 : Fin 32) s14.zero (by decide), g14_8]
  have g15_9 : reg n15 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1380 := by
    rw [rb15, runBlock_reg _ _ _ (9 : Fin 32) s14.zero (by decide), g14_9]
  have g15_18 : reg n15 (18 : Fin 32) = out := by
    rw [rb15, runBlock_reg _ _ _ (18 : Fin 32) s14.zero (by decide), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by
    rw [rb15, runBlock_reg _ _ _ (19 : Fin 32) s14.zero (by decide), g14_19]
  have g15_20 : reg n15 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb15, runBlock_reg _ _ _ (20 : Fin 32) s14.zero (by decide), g14_20]
  have g15_21 : reg n15 (21 : Fin 32) = s5v := by
    rw [rb15, runBlock_reg _ _ _ (21 : Fin 32) s14.zero (by decide), g14_21]
  have g15_22 : reg n15 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by
    rw [rb15, runBlock_reg _ _ _ (22 : Fin 32) s14.zero (by decide), g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by
    rw [rb15, runBlock_reg _ _ _ (23 : Fin 32) s14.zero (by decide), g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = s8v := by
    rw [rb15, runBlock_reg _ _ _ (24 : Fin 32) s14.zero (by decide), g14_24]
  have g15_25 : reg n15 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb15, runBlock_reg _ _ _ (25 : Fin 32) s14.zero (by decide), g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = x26 := by
    rw [rb15, runBlock_reg _ _ _ (26 : Fin 32) s14.zero (by decide), g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb15, runBlock_reg _ _ _ (27 : Fin 32) s14.zero (by decide), g14_27]
  have g15_10 : reg n15 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by
    rw [rb15]; simp +decide only [runBlock, BInstr.run, svEcW1840, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g14_2, g14_3, g14_4, g14_8, g14_9, g14_18, g14_19, g14_20, g14_21, g14_22, g14_23, g14_24, g14_25, g14_26, g14_27, s14.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g15_11 : reg n15 a1 = BitVec.ofNat 32 0x101 := by
    rw [rb15]; simp +decide only [runBlock, BInstr.run, svEcW1840, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g14_2, g14_3, g14_4, g14_8, g14_9, g14_18, g14_19, g14_20, g14_21, g14_22, g14_23, g14_24, g14_25, g14_26, g14_27, s14.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
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
  have a15_2a0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m15]; exact a14_2a0
  have a15_2c0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m15]; exact a14_2c0
  have a15_2e0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m15]; exact a14_2e0
  have a15_380 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m15]; exact a14_380
  have a15_400 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m15]; exact a14_400
  have a15_13e0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := by rw [m15]; exact a14_13e0
  have a15_1460 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := by rw [m15]; exact a14_1460
  have a15_1588 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U1 := by rw [m15]; exact a14_1588
  have p15_320 : ptF n15.mem B 0x320 = P0 := by rw [m15]; exact p14_320
  have p15_3a0 : ptF n15.mem B 0x3A0 = P1 := by rw [m15]; exact p14_3a0
  have p15_420 : ptF n15.mem B 0x420 = tbl2 P0 0 := by rw [m15]; exact p14_420
  have p15_480 : ptF n15.mem B 0x480 = tbl2 P0 1 := by rw [m15]; exact p14_480
  have p15_4e0 : ptF n15.mem B 0x4E0 = tbl2 P0 2 := by rw [m15]; exact p14_4e0
  have p15_540 : ptF n15.mem B 0x540 = tbl2 P0 3 := by rw [m15]; exact p14_540
  have p15_5a0 : ptF n15.mem B 0x5A0 = tbl2 P0 4 := by rw [m15]; exact p14_5a0
  have p15_600 : ptF n15.mem B 0x600 = tbl2 P0 5 := by rw [m15]; exact p14_600
  have p15_660 : ptF n15.mem B 0x660 = tbl2 P0 6 := by rw [m15]; exact p14_660
  have p15_6c0 : ptF n15.mem B 0x6C0 = tbl2 P0 7 := by rw [m15]; exact p14_6c0
  have p15_720 : ptF n15.mem B 0x720 = tbl2 P1 0 := by rw [m15]; exact p14_720
  have p15_780 : ptF n15.mem B 0x780 = tbl2 P1 1 := by rw [m15]; exact p14_780
  have p15_7e0 : ptF n15.mem B 0x7E0 = tbl2 P1 2 := by rw [m15]; exact p14_7e0
  have p15_840 : ptF n15.mem B 0x840 = tbl2 P1 3 := by rw [m15]; exact p14_840
  have p15_8a0 : ptF n15.mem B 0x8A0 = tbl2 P1 4 := by rw [m15]; exact p14_8a0
  have p15_900 : ptF n15.mem B 0x900 = tbl2 P1 5 := by rw [m15]; exact p14_900
  have p15_960 : ptF n15.mem B 0x960 = tbl2 P1 6 := by rw [m15]; exact p14_960
  have p15_9c0 : ptF n15.mem B 0x9C0 = tbl2 P1 7 := by rw [m15]; exact p14_9c0
  have p15_a20 : ptF n15.mem B 0xA20 = tbl2 P0 0 := by rw [m15]; exact p14_a20
  have p15_a80 : ptF n15.mem B 0xA80 = tbl2 P0 1 := by rw [m15]; exact p14_a80
  have p15_ae0 : ptF n15.mem B 0xAE0 = tbl2 P0 2 := by rw [m15]; exact p14_ae0
  have p15_b40 : ptF n15.mem B 0xB40 = tbl2 P0 3 := by rw [m15]; exact p14_b40
  have p15_ba0 : ptF n15.mem B 0xBA0 = tbl2 P0 4 := by rw [m15]; exact p14_ba0
  have p15_c00 : ptF n15.mem B 0xC00 = tbl2 P0 5 := by rw [m15]; exact p14_c00
  have p15_c60 : ptF n15.mem B 0xC60 = tbl2 P0 6 := by rw [m15]; exact p14_c60
  have p15_cc0 : ptF n15.mem B 0xCC0 = tbl2 P0 7 := by rw [m15]; exact p14_cc0
  have p15_d20 : ptF n15.mem B 0xD20 = tbl2 P1 0 := by rw [m15]; exact p14_d20
  have p15_d80 : ptF n15.mem B 0xD80 = tbl2 P1 1 := by rw [m15]; exact p14_d80
  have p15_de0 : ptF n15.mem B 0xDE0 = tbl2 P1 2 := by rw [m15]; exact p14_de0
  have p15_e40 : ptF n15.mem B 0xE40 = tbl2 P1 3 := by rw [m15]; exact p14_e40
  have p15_ea0 : ptF n15.mem B 0xEA0 = tbl2 P1 4 := by rw [m15]; exact p14_ea0
  have p15_f00 : ptF n15.mem B 0xF00 = tbl2 P1 5 := by rw [m15]; exact p14_f00
  have p15_f60 : ptF n15.mem B 0xF60 = tbl2 P1 6 := by rw [m15]; exact p14_f60
  have p15_fc0 : ptF n15.mem B 0xFC0 = tbl2 P1 7 := by rw [m15]; exact p14_fc0
  have p15_1380 : ptF n15.mem B 0x1380 = P0 := by rw [m15]; exact p14_1380
  have p15_1400 : ptF n15.mem B 0x1400 = P1 := by rw [m15]; exact p14_1400
  have mb15_1320 : leN (memBytes n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U1 := by rw [m15]; exact mb14_1320
  have mb15_1480 : leN (memBytes n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 0x20) = U1 := by rw [m15]; exact mb14_1480
  clear mb14_1320 mb14_1480 p14_1400 p14_1380 p14_fc0 p14_f60 p14_f00 p14_ea0 p14_e40 p14_de0 p14_d80 p14_d20 p14_cc0 p14_c60 p14_c00 p14_ba0 p14_b40 p14_ae0 p14_a80 p14_a20 p14_9c0 p14_960 p14_900 p14_8a0 p14_840 p14_7e0 p14_780 p14_720 p14_6c0 p14_660 p14_600 p14_5a0 p14_540 p14_4e0 p14_480 p14_420 p14_3a0 p14_320 a14_1588 a14_1460 a14_13e0 a14_400 a14_380 a14_2e0 a14_2c0 a14_2a0 w14_130 w14_12c w14_128 w14_124 w14_120 w14_11c w14_118 w14_114 w14_110 w14_10c w14_108 w14_104 w14_100 w14_fc w14_f8 w14_f4 w14_f0 w14_ec w14_e8 w14_e4 w14_e0 w14_dc w14_d8 w14_d4 w14_d0 w14_cc w14_c8 w14_c4 w14_c0 w14_bc w14_b8 w14_b4 w14_b0 w14_ac w14_a8 w14_a4 w14_a0 w14_9c w14_98 w14_94 w14_90 w14_8c w14_88 w14_84 w14_80 w14_7c w14_78 w14_70 w14_6c w14_68 w14_64 w14_60 w14_5c w14_58 w14_54 w14_50 w14_4c w14_48 w14_44 w14_40 w14_3c w14_38 w14_34 w14_30 w14_2c w14_28 w14_24 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_9 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 s14 X14 K14 P14
  -- 0x184C: branch, not taken
  obtain ⟨n16, d16, u16⟩ := s15.notTaken E15.self 0x184E sv_at_184c
    (by decide) (by rw [g15_11, s15.zero]; decide)
  have s16 : St n16.mem SV n16 0x184E (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
  have m16 : n16.mem = n15.mem := u16.mem
  have fr16 : ∀ x, SvR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
  have t16 : Steps n0 n16 := t15.trans (.single d16)
  have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : SvCode n16.mem := E15.fr F fr16
  have V16 : SvSaves B n16.mem v := V15.same m16
  have g16_2 : reg n16 sp = B + 0x21A0 := by rw [u16.regs, g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u16.regs, g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u16.regs, g15_4]
  have g16_8 : reg n16 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u16.regs, g15_8]
  have g16_9 : reg n16 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1380 := by rw [u16.regs, g15_9]
  have g16_10 : reg n16 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by rw [u16.regs, g15_10]
  have g16_11 : reg n16 a1 = BitVec.ofNat 32 0x101 := by rw [u16.regs, g15_11]
  have g16_18 : reg n16 (18 : Fin 32) = out := by rw [u16.regs, g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [u16.regs, g15_19]
  have g16_20 : reg n16 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u16.regs, g15_20]
  have g16_21 : reg n16 (21 : Fin 32) = s5v := by rw [u16.regs, g15_21]
  have g16_22 : reg n16 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [u16.regs, g15_22]
  have g16_23 : reg n16 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by rw [u16.regs, g15_23]
  have g16_24 : reg n16 (24 : Fin 32) = s8v := by rw [u16.regs, g15_24]
  have g16_25 : reg n16 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u16.regs, g15_25]
  have g16_26 : reg n16 (26 : Fin 32) = x26 := by rw [u16.regs, g15_26]
  have g16_27 : reg n16 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u16.regs, g15_27]
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
  have a16_2a0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m16]; exact a15_2a0
  have a16_2c0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m16]; exact a15_2c0
  have a16_2e0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m16]; exact a15_2e0
  have a16_380 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m16]; exact a15_380
  have a16_400 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m16]; exact a15_400
  have a16_13e0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := by rw [m16]; exact a15_13e0
  have a16_1460 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := by rw [m16]; exact a15_1460
  have a16_1588 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U1 := by rw [m16]; exact a15_1588
  have p16_320 : ptF n16.mem B 0x320 = P0 := by rw [m16]; exact p15_320
  have p16_3a0 : ptF n16.mem B 0x3A0 = P1 := by rw [m16]; exact p15_3a0
  have p16_420 : ptF n16.mem B 0x420 = tbl2 P0 0 := by rw [m16]; exact p15_420
  have p16_480 : ptF n16.mem B 0x480 = tbl2 P0 1 := by rw [m16]; exact p15_480
  have p16_4e0 : ptF n16.mem B 0x4E0 = tbl2 P0 2 := by rw [m16]; exact p15_4e0
  have p16_540 : ptF n16.mem B 0x540 = tbl2 P0 3 := by rw [m16]; exact p15_540
  have p16_5a0 : ptF n16.mem B 0x5A0 = tbl2 P0 4 := by rw [m16]; exact p15_5a0
  have p16_600 : ptF n16.mem B 0x600 = tbl2 P0 5 := by rw [m16]; exact p15_600
  have p16_660 : ptF n16.mem B 0x660 = tbl2 P0 6 := by rw [m16]; exact p15_660
  have p16_6c0 : ptF n16.mem B 0x6C0 = tbl2 P0 7 := by rw [m16]; exact p15_6c0
  have p16_720 : ptF n16.mem B 0x720 = tbl2 P1 0 := by rw [m16]; exact p15_720
  have p16_780 : ptF n16.mem B 0x780 = tbl2 P1 1 := by rw [m16]; exact p15_780
  have p16_7e0 : ptF n16.mem B 0x7E0 = tbl2 P1 2 := by rw [m16]; exact p15_7e0
  have p16_840 : ptF n16.mem B 0x840 = tbl2 P1 3 := by rw [m16]; exact p15_840
  have p16_8a0 : ptF n16.mem B 0x8A0 = tbl2 P1 4 := by rw [m16]; exact p15_8a0
  have p16_900 : ptF n16.mem B 0x900 = tbl2 P1 5 := by rw [m16]; exact p15_900
  have p16_960 : ptF n16.mem B 0x960 = tbl2 P1 6 := by rw [m16]; exact p15_960
  have p16_9c0 : ptF n16.mem B 0x9C0 = tbl2 P1 7 := by rw [m16]; exact p15_9c0
  have p16_a20 : ptF n16.mem B 0xA20 = tbl2 P0 0 := by rw [m16]; exact p15_a20
  have p16_a80 : ptF n16.mem B 0xA80 = tbl2 P0 1 := by rw [m16]; exact p15_a80
  have p16_ae0 : ptF n16.mem B 0xAE0 = tbl2 P0 2 := by rw [m16]; exact p15_ae0
  have p16_b40 : ptF n16.mem B 0xB40 = tbl2 P0 3 := by rw [m16]; exact p15_b40
  have p16_ba0 : ptF n16.mem B 0xBA0 = tbl2 P0 4 := by rw [m16]; exact p15_ba0
  have p16_c00 : ptF n16.mem B 0xC00 = tbl2 P0 5 := by rw [m16]; exact p15_c00
  have p16_c60 : ptF n16.mem B 0xC60 = tbl2 P0 6 := by rw [m16]; exact p15_c60
  have p16_cc0 : ptF n16.mem B 0xCC0 = tbl2 P0 7 := by rw [m16]; exact p15_cc0
  have p16_d20 : ptF n16.mem B 0xD20 = tbl2 P1 0 := by rw [m16]; exact p15_d20
  have p16_d80 : ptF n16.mem B 0xD80 = tbl2 P1 1 := by rw [m16]; exact p15_d80
  have p16_de0 : ptF n16.mem B 0xDE0 = tbl2 P1 2 := by rw [m16]; exact p15_de0
  have p16_e40 : ptF n16.mem B 0xE40 = tbl2 P1 3 := by rw [m16]; exact p15_e40
  have p16_ea0 : ptF n16.mem B 0xEA0 = tbl2 P1 4 := by rw [m16]; exact p15_ea0
  have p16_f00 : ptF n16.mem B 0xF00 = tbl2 P1 5 := by rw [m16]; exact p15_f00
  have p16_f60 : ptF n16.mem B 0xF60 = tbl2 P1 6 := by rw [m16]; exact p15_f60
  have p16_fc0 : ptF n16.mem B 0xFC0 = tbl2 P1 7 := by rw [m16]; exact p15_fc0
  have p16_1380 : ptF n16.mem B 0x1380 = P0 := by rw [m16]; exact p15_1380
  have p16_1400 : ptF n16.mem B 0x1400 = P1 := by rw [m16]; exact p15_1400
  have mb16_1320 : leN (memBytes n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U1 := by rw [m16]; exact mb15_1320
  have mb16_1480 : leN (memBytes n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 0x20) = U1 := by rw [m16]; exact mb15_1480
  clear mb15_1480 mb15_1320 p15_1400 p15_1380 p15_fc0 p15_f60 p15_f00 p15_ea0 p15_e40 p15_de0 p15_d80 p15_d20 p15_cc0 p15_c60 p15_c00 p15_ba0 p15_b40 p15_ae0 p15_a80 p15_a20 p15_9c0 p15_960 p15_900 p15_8a0 p15_840 p15_7e0 p15_780 p15_720 p15_6c0 p15_660 p15_600 p15_5a0 p15_540 p15_4e0 p15_480 p15_420 p15_3a0 p15_320 a15_1588 a15_1460 a15_13e0 a15_400 a15_380 a15_2e0 a15_2c0 a15_2a0 w15_130 w15_12c w15_128 w15_124 w15_120 w15_11c w15_118 w15_114 w15_110 w15_10c w15_108 w15_104 w15_100 w15_fc w15_f8 w15_f4 w15_f0 w15_ec w15_e8 w15_e4 w15_e0 w15_dc w15_d8 w15_d4 w15_d0 w15_cc w15_c8 w15_c4 w15_c0 w15_bc w15_b8 w15_b4 w15_b0 w15_ac w15_a8 w15_a4 w15_a0 w15_9c w15_98 w15_94 w15_90 w15_8c w15_88 w15_84 w15_80 w15_7c w15_78 w15_70 w15_6c w15_68 w15_64 w15_60 w15_5c w15_58 w15_54 w15_50 w15_4c w15_48 w15_44 w15_40 w15_3c w15_38 w15_34 w15_30 w15_2c w15_28 w15_24 g15_11 g15_10 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_9 g15_8 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 rb15 s15 m15 u15 c15
  -- 0x184E: clear 0x101 bytes
  obtain ⟨n17, Z17, c17, s17', C17, rk17, z17, fz17⟩ := ec_zloop F (c := 0x1480) (N := 0x101) (by decide)
    0x101 0 (by decide) (by decide) E16.self s16 (by rw [g16_10]; try rfl) g16_11
  have s17 : St n17.mem SV n17 0x1858 (reg n17) := ⟨s17'.pc, rfl, fun _ => rfl⟩
  have fr17 : ∀ x, SvR B x → n17.mem x = n16.mem x := fun x hx => by
    rw [s17'.mem]; exact fz17 x (svR_hi (c := 0x1480 + 0) hx (by decide))
  have K17 : SvKeep B n16.mem n17.mem 0x1480 0x101 := fun e he hh => by
    rw [s17'.mem]; exact fz17 _ (sepS (B + 0x21A0) (c := 0x1480 + 0) (n := 0x101) (d := e) (k := 1) (by omega) (by omega) (by omega))
  have t17 : Steps n0 n17 := t16.trans c17
  have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
  have E17 : SvCode n17.mem := E16.fr F fr17
  have V17 : SvSaves B n17.mem v := V16.keep K17 (by decide)
  have g17_2 : reg n17 sp = B + 0x21A0 := by rw [rk17 sp (by decide) (by decide), g16_2]
  have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk17 (3 : Fin 32) (by decide) (by decide), g16_3]
  have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk17 (4 : Fin 32) (by decide) (by decide), g16_4]
  have g17_8 : reg n17 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rk17 (8 : Fin 32) (by decide) (by decide), g16_8]
  have g17_9 : reg n17 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1380 := by rw [rk17 (9 : Fin 32) (by decide) (by decide), g16_9]
  have g17_18 : reg n17 (18 : Fin 32) = out := by rw [rk17 (18 : Fin 32) (by decide) (by decide), g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [rk17 (19 : Fin 32) (by decide) (by decide), g16_19]
  have g17_20 : reg n17 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk17 (20 : Fin 32) (by decide) (by decide), g16_20]
  have g17_21 : reg n17 (21 : Fin 32) = s5v := by rw [rk17 (21 : Fin 32) (by decide) (by decide), g16_21]
  have g17_22 : reg n17 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [rk17 (22 : Fin 32) (by decide) (by decide), g16_22]
  have g17_23 : reg n17 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by rw [rk17 (23 : Fin 32) (by decide) (by decide), g16_23]
  have g17_24 : reg n17 (24 : Fin 32) = s8v := by rw [rk17 (24 : Fin 32) (by decide) (by decide), g16_24]
  have g17_25 : reg n17 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [rk17 (25 : Fin 32) (by decide) (by decide), g16_25]
  have g17_26 : reg n17 (26 : Fin 32) = x26 := by rw [rk17 (26 : Fin 32) (by decide) (by decide), g16_26]
  have g17_27 : reg n17 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk17 (27 : Fin 32) (by decide) (by decide), g16_27]
  have w17_24 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K17.w32 (by decide) (by decide)).trans w16_24
  have w17_28 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K17.w32 (by decide) (by decide)).trans w16_28
  have w17_2c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K17.w32 (by decide) (by decide)).trans w16_2c
  have w17_30 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K17.w32 (by decide) (by decide)).trans w16_30
  have w17_34 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K17.w32 (by decide) (by decide)).trans w16_34
  have w17_38 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K17.w32 (by decide) (by decide)).trans w16_38
  have w17_3c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K17.w32 (by decide) (by decide)).trans w16_3c
  have w17_40 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K17.w32 (by decide) (by decide)).trans w16_40
  have w17_44 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K17.w32 (by decide) (by decide)).trans w16_44
  have w17_48 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K17.w32 (by decide) (by decide)).trans w16_48
  have w17_4c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K17.w32 (by decide) (by decide)).trans w16_4c
  have w17_50 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K17.w32 (by decide) (by decide)).trans w16_50
  have w17_54 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K17.w32 (by decide) (by decide)).trans w16_54
  have w17_58 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K17.w32 (by decide) (by decide)).trans w16_58
  have w17_5c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K17.w32 (by decide) (by decide)).trans w16_5c
  have w17_60 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K17.w32 (by decide) (by decide)).trans w16_60
  have w17_64 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K17.w32 (by decide) (by decide)).trans w16_64
  have w17_68 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K17.w32 (by decide) (by decide)).trans w16_68
  have w17_6c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K17.w32 (by decide) (by decide)).trans w16_6c
  have w17_70 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K17.w32 (by decide) (by decide)).trans w16_70
  have w17_78 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := (K17.w32 (by decide) (by decide)).trans w16_78
  have w17_7c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K17.w32 (by decide) (by decide)).trans w16_7c
  have w17_80 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K17.w32 (by decide) (by decide)).trans w16_80
  have w17_84 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K17.w32 (by decide) (by decide)).trans w16_84
  have w17_88 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K17.w32 (by decide) (by decide)).trans w16_88
  have w17_8c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K17.w32 (by decide) (by decide)).trans w16_8c
  have w17_90 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K17.w32 (by decide) (by decide)).trans w16_90
  have w17_94 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K17.w32 (by decide) (by decide)).trans w16_94
  have w17_98 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K17.w32 (by decide) (by decide)).trans w16_98
  have w17_9c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K17.w32 (by decide) (by decide)).trans w16_9c
  have w17_a0 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K17.w32 (by decide) (by decide)).trans w16_a0
  have w17_a4 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K17.w32 (by decide) (by decide)).trans w16_a4
  have w17_a8 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K17.w32 (by decide) (by decide)).trans w16_a8
  have w17_ac : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K17.w32 (by decide) (by decide)).trans w16_ac
  have w17_b0 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K17.w32 (by decide) (by decide)).trans w16_b0
  have w17_b4 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K17.w32 (by decide) (by decide)).trans w16_b4
  have w17_b8 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K17.w32 (by decide) (by decide)).trans w16_b8
  have w17_bc : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K17.w32 (by decide) (by decide)).trans w16_bc
  have w17_c0 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K17.w32 (by decide) (by decide)).trans w16_c0
  have w17_c4 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K17.w32 (by decide) (by decide)).trans w16_c4
  have w17_c8 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K17.w32 (by decide) (by decide)).trans w16_c8
  have w17_cc : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K17.w32 (by decide) (by decide)).trans w16_cc
  have w17_d0 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K17.w32 (by decide) (by decide)).trans w16_d0
  have w17_d4 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K17.w32 (by decide) (by decide)).trans w16_d4
  have w17_d8 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K17.w32 (by decide) (by decide)).trans w16_d8
  have w17_dc : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K17.w32 (by decide) (by decide)).trans w16_dc
  have w17_e0 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K17.w32 (by decide) (by decide)).trans w16_e0
  have w17_e4 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K17.w32 (by decide) (by decide)).trans w16_e4
  have w17_e8 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K17.w32 (by decide) (by decide)).trans w16_e8
  have w17_ec : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K17.w32 (by decide) (by decide)).trans w16_ec
  have w17_f0 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K17.w32 (by decide) (by decide)).trans w16_f0
  have w17_f4 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K17.w32 (by decide) (by decide)).trans w16_f4
  have w17_f8 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K17.w32 (by decide) (by decide)).trans w16_f8
  have w17_fc : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K17.w32 (by decide) (by decide)).trans w16_fc
  have w17_100 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K17.w32 (by decide) (by decide)).trans w16_100
  have w17_104 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K17.w32 (by decide) (by decide)).trans w16_104
  have w17_108 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K17.w32 (by decide) (by decide)).trans w16_108
  have w17_10c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K17.w32 (by decide) (by decide)).trans w16_10c
  have w17_110 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K17.w32 (by decide) (by decide)).trans w16_110
  have w17_114 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K17.w32 (by decide) (by decide)).trans w16_114
  have w17_118 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K17.w32 (by decide) (by decide)).trans w16_118
  have w17_11c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K17.w32 (by decide) (by decide)).trans w16_11c
  have w17_120 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K17.w32 (by decide) (by decide)).trans w16_120
  have w17_124 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K17.w32 (by decide) (by decide)).trans w16_124
  have w17_128 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K17.w32 (by decide) (by decide)).trans w16_128
  have w17_12c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K17.w32 (by decide) (by decide)).trans w16_12c
  have w17_130 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K17.w32 (by decide) (by decide)).trans w16_130
  have a17_2a0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K17.acc (by decide) (by decide)).trans a16_2a0
  have a17_2c0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K17.acc (by decide) (by decide)).trans a16_2c0
  have a17_2e0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K17.acc (by decide) (by decide)).trans a16_2e0
  have a17_380 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := (K17.acc (by decide) (by decide)).trans a16_380
  have a17_400 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := (K17.acc (by decide) (by decide)).trans a16_400
  have a17_13e0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := (K17.acc (by decide) (by decide)).trans a16_13e0
  have a17_1460 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := (K17.acc (by decide) (by decide)).trans a16_1460
  have a17_1588 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U1 := (K17.acc (by decide) (by decide)).trans a16_1588
  have p17_320 : ptF n17.mem B 0x320 = P0 := (K17.pt (by decide) (by decide)).trans p16_320
  have p17_3a0 : ptF n17.mem B 0x3A0 = P1 := (K17.pt (by decide) (by decide)).trans p16_3a0
  have p17_420 : ptF n17.mem B 0x420 = tbl2 P0 0 := (K17.pt (by decide) (by decide)).trans p16_420
  have p17_480 : ptF n17.mem B 0x480 = tbl2 P0 1 := (K17.pt (by decide) (by decide)).trans p16_480
  have p17_4e0 : ptF n17.mem B 0x4E0 = tbl2 P0 2 := (K17.pt (by decide) (by decide)).trans p16_4e0
  have p17_540 : ptF n17.mem B 0x540 = tbl2 P0 3 := (K17.pt (by decide) (by decide)).trans p16_540
  have p17_5a0 : ptF n17.mem B 0x5A0 = tbl2 P0 4 := (K17.pt (by decide) (by decide)).trans p16_5a0
  have p17_600 : ptF n17.mem B 0x600 = tbl2 P0 5 := (K17.pt (by decide) (by decide)).trans p16_600
  have p17_660 : ptF n17.mem B 0x660 = tbl2 P0 6 := (K17.pt (by decide) (by decide)).trans p16_660
  have p17_6c0 : ptF n17.mem B 0x6C0 = tbl2 P0 7 := (K17.pt (by decide) (by decide)).trans p16_6c0
  have p17_720 : ptF n17.mem B 0x720 = tbl2 P1 0 := (K17.pt (by decide) (by decide)).trans p16_720
  have p17_780 : ptF n17.mem B 0x780 = tbl2 P1 1 := (K17.pt (by decide) (by decide)).trans p16_780
  have p17_7e0 : ptF n17.mem B 0x7E0 = tbl2 P1 2 := (K17.pt (by decide) (by decide)).trans p16_7e0
  have p17_840 : ptF n17.mem B 0x840 = tbl2 P1 3 := (K17.pt (by decide) (by decide)).trans p16_840
  have p17_8a0 : ptF n17.mem B 0x8A0 = tbl2 P1 4 := (K17.pt (by decide) (by decide)).trans p16_8a0
  have p17_900 : ptF n17.mem B 0x900 = tbl2 P1 5 := (K17.pt (by decide) (by decide)).trans p16_900
  have p17_960 : ptF n17.mem B 0x960 = tbl2 P1 6 := (K17.pt (by decide) (by decide)).trans p16_960
  have p17_9c0 : ptF n17.mem B 0x9C0 = tbl2 P1 7 := (K17.pt (by decide) (by decide)).trans p16_9c0
  have p17_a20 : ptF n17.mem B 0xA20 = tbl2 P0 0 := (K17.pt (by decide) (by decide)).trans p16_a20
  have p17_a80 : ptF n17.mem B 0xA80 = tbl2 P0 1 := (K17.pt (by decide) (by decide)).trans p16_a80
  have p17_ae0 : ptF n17.mem B 0xAE0 = tbl2 P0 2 := (K17.pt (by decide) (by decide)).trans p16_ae0
  have p17_b40 : ptF n17.mem B 0xB40 = tbl2 P0 3 := (K17.pt (by decide) (by decide)).trans p16_b40
  have p17_ba0 : ptF n17.mem B 0xBA0 = tbl2 P0 4 := (K17.pt (by decide) (by decide)).trans p16_ba0
  have p17_c00 : ptF n17.mem B 0xC00 = tbl2 P0 5 := (K17.pt (by decide) (by decide)).trans p16_c00
  have p17_c60 : ptF n17.mem B 0xC60 = tbl2 P0 6 := (K17.pt (by decide) (by decide)).trans p16_c60
  have p17_cc0 : ptF n17.mem B 0xCC0 = tbl2 P0 7 := (K17.pt (by decide) (by decide)).trans p16_cc0
  have p17_d20 : ptF n17.mem B 0xD20 = tbl2 P1 0 := (K17.pt (by decide) (by decide)).trans p16_d20
  have p17_d80 : ptF n17.mem B 0xD80 = tbl2 P1 1 := (K17.pt (by decide) (by decide)).trans p16_d80
  have p17_de0 : ptF n17.mem B 0xDE0 = tbl2 P1 2 := (K17.pt (by decide) (by decide)).trans p16_de0
  have p17_e40 : ptF n17.mem B 0xE40 = tbl2 P1 3 := (K17.pt (by decide) (by decide)).trans p16_e40
  have p17_ea0 : ptF n17.mem B 0xEA0 = tbl2 P1 4 := (K17.pt (by decide) (by decide)).trans p16_ea0
  have p17_f00 : ptF n17.mem B 0xF00 = tbl2 P1 5 := (K17.pt (by decide) (by decide)).trans p16_f00
  have p17_f60 : ptF n17.mem B 0xF60 = tbl2 P1 6 := (K17.pt (by decide) (by decide)).trans p16_f60
  have p17_fc0 : ptF n17.mem B 0xFC0 = tbl2 P1 7 := (K17.pt (by decide) (by decide)).trans p16_fc0
  have p17_1380 : ptF n17.mem B 0x1380 = P0 := (K17.pt (by decide) (by decide)).trans p16_1380
  have p17_1400 : ptF n17.mem B 0x1400 = P1 := (K17.pt (by decide) (by decide)).trans p16_1400
  have mb17_1320 : leN (memBytes n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U1 := by rw [K17.mb (by decide) (by decide)]; exact mb16_1320
  have mb17_1480 : memBytes n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 0x101 = List.replicate 0x101 0 :=
    Pv.memBytes_zero fun j hj => by rw [s17'.mem]; have := z17 j hj; rwa [Nat.add_zero] at this
  clear mb16_1480 mb16_1320 p16_1400 p16_1380 p16_fc0 p16_f60 p16_f00 p16_ea0 p16_e40 p16_de0 p16_d80 p16_d20 p16_cc0 p16_c60 p16_c00 p16_ba0 p16_b40 p16_ae0 p16_a80 p16_a20 p16_9c0 p16_960 p16_900 p16_8a0 p16_840 p16_7e0 p16_780 p16_720 p16_6c0 p16_660 p16_600 p16_5a0 p16_540 p16_4e0 p16_480 p16_420 p16_3a0 p16_320 a16_1588 a16_1460 a16_13e0 a16_400 a16_380 a16_2e0 a16_2c0 a16_2a0 w16_130 w16_12c w16_128 w16_124 w16_120 w16_11c w16_118 w16_114 w16_110 w16_10c w16_108 w16_104 w16_100 w16_fc w16_f8 w16_f4 w16_f0 w16_ec w16_e8 w16_e4 w16_e0 w16_dc w16_d8 w16_d4 w16_d0 w16_cc w16_c8 w16_c4 w16_c0 w16_bc w16_b8 w16_b4 w16_b0 w16_ac w16_a8 w16_a4 w16_a0 w16_9c w16_98 w16_94 w16_90 w16_8c w16_88 w16_84 w16_80 w16_7c w16_78 w16_70 w16_6c w16_68 w16_64 w16_60 w16_5c w16_58 w16_54 w16_50 w16_4c w16_48 w16_44 w16_40 w16_3c w16_38 w16_34 w16_30 w16_2c w16_28 w16_24 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_11 g16_10 g16_9 g16_8 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 m16 s16 u16 d16
  -- 0x1858
  obtain ⟨n18, c18, u18⟩ := s17.block svEcW1858 E17.self svEcW1858_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m18 : n18.mem = n17.mem := u18.mem
  have s18 : St n18.mem SV n18 0x186C (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
  have rb18 : ∀ q, reg n18 q = (runBlock svEcW1858 (n17.mem, reg n17)).2 q := fun q => by rw [u18.regs]
  have fr18 : ∀ x, SvR B x → n18.mem x = n17.mem x := fun x _ => by rw [m18]
  have t18 : Steps n0 n18 := t17.trans c18
  have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : SvCode n18.mem := E17.fr F fr18
  have V18 : SvSaves B n18.mem v := V17.same m18
  have g18_2 : reg n18 sp = B + 0x21A0 := by
    rw [rb18, runBlock_reg _ _ _ sp s17.zero (by decide), g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb18, runBlock_reg _ _ _ (3 : Fin 32) s17.zero (by decide), g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb18, runBlock_reg _ _ _ (4 : Fin 32) s17.zero (by decide), g17_4]
  have g18_8 : reg n18 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb18, runBlock_reg _ _ _ (8 : Fin 32) s17.zero (by decide), g17_8]
  have g18_18 : reg n18 (18 : Fin 32) = out := by
    rw [rb18, runBlock_reg _ _ _ (18 : Fin 32) s17.zero (by decide), g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = bp := by
    rw [rb18, runBlock_reg _ _ _ (19 : Fin 32) s17.zero (by decide), g17_19]
  have g18_20 : reg n18 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb18, runBlock_reg _ _ _ (20 : Fin 32) s17.zero (by decide), g17_20]
  have g18_21 : reg n18 (21 : Fin 32) = s5v := by
    rw [rb18, runBlock_reg _ _ _ (21 : Fin 32) s17.zero (by decide), g17_21]
  have g18_22 : reg n18 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by
    rw [rb18, runBlock_reg _ _ _ (22 : Fin 32) s17.zero (by decide), g17_22]
  have g18_23 : reg n18 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by
    rw [rb18, runBlock_reg _ _ _ (23 : Fin 32) s17.zero (by decide), g17_23]
  have g18_24 : reg n18 (24 : Fin 32) = s8v := by
    rw [rb18, runBlock_reg _ _ _ (24 : Fin 32) s17.zero (by decide), g17_24]
  have g18_25 : reg n18 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb18, runBlock_reg _ _ _ (25 : Fin 32) s17.zero (by decide), g17_25]
  have g18_26 : reg n18 (26 : Fin 32) = x26 := by
    rw [rb18, runBlock_reg _ _ _ (26 : Fin 32) s17.zero (by decide), g17_26]
  have g18_27 : reg n18 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb18, runBlock_reg _ _ _ (27 : Fin 32) s17.zero (by decide), g17_27]
  have g18_9 : reg n18 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1400 := by
    rw [rb18]; simp +decide only [runBlock, BInstr.run, svEcW1858, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g17_2, g17_3, g17_4, g17_8, g17_9, g17_18, g17_19, g17_20, g17_21, g17_22, g17_23, g17_24, g17_25, g17_26, g17_27, s17.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g18_10 : reg n18 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by
    rw [rb18]; simp +decide only [runBlock, BInstr.run, svEcW1858, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g17_2, g17_3, g17_4, g17_8, g17_9, g17_18, g17_19, g17_20, g17_21, g17_22, g17_23, g17_24, g17_25, g17_26, g17_27, s17.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g18_11 : reg n18 a1 = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by
    rw [rb18]; simp +decide only [runBlock, BInstr.run, svEcW1858, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g17_2, g17_3, g17_4, g17_8, g17_9, g17_18, g17_19, g17_20, g17_21, g17_22, g17_23, g17_24, g17_25, g17_26, g17_27, s17.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g18_12 : reg n18 a2 = BitVec.ofNat 32 0x101 := by
    rw [rb18]; simp +decide only [runBlock, BInstr.run, svEcW1858, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g17_2, g17_3, g17_4, g17_8, g17_9, g17_18, g17_19, g17_20, g17_21, g17_22, g17_23, g17_24, g17_25, g17_26, g17_27, s17.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w18_24 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m18]; exact w17_24
  have w18_28 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m18]; exact w17_28
  have w18_2c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m18]; exact w17_2c
  have w18_30 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m18]; exact w17_30
  have w18_34 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m18]; exact w17_34
  have w18_38 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m18]; exact w17_38
  have w18_3c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m18]; exact w17_3c
  have w18_40 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m18]; exact w17_40
  have w18_44 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m18]; exact w17_44
  have w18_48 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m18]; exact w17_48
  have w18_4c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m18]; exact w17_4c
  have w18_50 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m18]; exact w17_50
  have w18_54 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m18]; exact w17_54
  have w18_58 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m18]; exact w17_58
  have w18_5c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m18]; exact w17_5c
  have w18_60 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m18]; exact w17_60
  have w18_64 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m18]; exact w17_64
  have w18_68 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m18]; exact w17_68
  have w18_6c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m18]; exact w17_6c
  have w18_70 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m18]; exact w17_70
  have w18_78 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m18]; exact w17_78
  have w18_7c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m18]; exact w17_7c
  have w18_80 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m18]; exact w17_80
  have w18_84 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m18]; exact w17_84
  have w18_88 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m18]; exact w17_88
  have w18_8c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m18]; exact w17_8c
  have w18_90 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m18]; exact w17_90
  have w18_94 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m18]; exact w17_94
  have w18_98 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m18]; exact w17_98
  have w18_9c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m18]; exact w17_9c
  have w18_a0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m18]; exact w17_a0
  have w18_a4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m18]; exact w17_a4
  have w18_a8 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m18]; exact w17_a8
  have w18_ac : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m18]; exact w17_ac
  have w18_b0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m18]; exact w17_b0
  have w18_b4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m18]; exact w17_b4
  have w18_b8 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m18]; exact w17_b8
  have w18_bc : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m18]; exact w17_bc
  have w18_c0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m18]; exact w17_c0
  have w18_c4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m18]; exact w17_c4
  have w18_c8 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m18]; exact w17_c8
  have w18_cc : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m18]; exact w17_cc
  have w18_d0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m18]; exact w17_d0
  have w18_d4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m18]; exact w17_d4
  have w18_d8 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m18]; exact w17_d8
  have w18_dc : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m18]; exact w17_dc
  have w18_e0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m18]; exact w17_e0
  have w18_e4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m18]; exact w17_e4
  have w18_e8 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m18]; exact w17_e8
  have w18_ec : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m18]; exact w17_ec
  have w18_f0 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m18]; exact w17_f0
  have w18_f4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m18]; exact w17_f4
  have w18_f8 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m18]; exact w17_f8
  have w18_fc : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m18]; exact w17_fc
  have w18_100 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m18]; exact w17_100
  have w18_104 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m18]; exact w17_104
  have w18_108 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m18]; exact w17_108
  have w18_10c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m18]; exact w17_10c
  have w18_110 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m18]; exact w17_110
  have w18_114 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m18]; exact w17_114
  have w18_118 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m18]; exact w17_118
  have w18_11c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m18]; exact w17_11c
  have w18_120 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m18]; exact w17_120
  have w18_124 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m18]; exact w17_124
  have w18_128 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m18]; exact w17_128
  have w18_12c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m18]; exact w17_12c
  have w18_130 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m18]; exact w17_130
  have a18_2a0 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m18]; exact a17_2a0
  have a18_2c0 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m18]; exact a17_2c0
  have a18_2e0 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m18]; exact a17_2e0
  have a18_380 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m18]; exact a17_380
  have a18_400 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m18]; exact a17_400
  have a18_13e0 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := by rw [m18]; exact a17_13e0
  have a18_1460 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := by rw [m18]; exact a17_1460
  have a18_1588 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U1 := by rw [m18]; exact a17_1588
  have p18_320 : ptF n18.mem B 0x320 = P0 := by rw [m18]; exact p17_320
  have p18_3a0 : ptF n18.mem B 0x3A0 = P1 := by rw [m18]; exact p17_3a0
  have p18_420 : ptF n18.mem B 0x420 = tbl2 P0 0 := by rw [m18]; exact p17_420
  have p18_480 : ptF n18.mem B 0x480 = tbl2 P0 1 := by rw [m18]; exact p17_480
  have p18_4e0 : ptF n18.mem B 0x4E0 = tbl2 P0 2 := by rw [m18]; exact p17_4e0
  have p18_540 : ptF n18.mem B 0x540 = tbl2 P0 3 := by rw [m18]; exact p17_540
  have p18_5a0 : ptF n18.mem B 0x5A0 = tbl2 P0 4 := by rw [m18]; exact p17_5a0
  have p18_600 : ptF n18.mem B 0x600 = tbl2 P0 5 := by rw [m18]; exact p17_600
  have p18_660 : ptF n18.mem B 0x660 = tbl2 P0 6 := by rw [m18]; exact p17_660
  have p18_6c0 : ptF n18.mem B 0x6C0 = tbl2 P0 7 := by rw [m18]; exact p17_6c0
  have p18_720 : ptF n18.mem B 0x720 = tbl2 P1 0 := by rw [m18]; exact p17_720
  have p18_780 : ptF n18.mem B 0x780 = tbl2 P1 1 := by rw [m18]; exact p17_780
  have p18_7e0 : ptF n18.mem B 0x7E0 = tbl2 P1 2 := by rw [m18]; exact p17_7e0
  have p18_840 : ptF n18.mem B 0x840 = tbl2 P1 3 := by rw [m18]; exact p17_840
  have p18_8a0 : ptF n18.mem B 0x8A0 = tbl2 P1 4 := by rw [m18]; exact p17_8a0
  have p18_900 : ptF n18.mem B 0x900 = tbl2 P1 5 := by rw [m18]; exact p17_900
  have p18_960 : ptF n18.mem B 0x960 = tbl2 P1 6 := by rw [m18]; exact p17_960
  have p18_9c0 : ptF n18.mem B 0x9C0 = tbl2 P1 7 := by rw [m18]; exact p17_9c0
  have p18_a20 : ptF n18.mem B 0xA20 = tbl2 P0 0 := by rw [m18]; exact p17_a20
  have p18_a80 : ptF n18.mem B 0xA80 = tbl2 P0 1 := by rw [m18]; exact p17_a80
  have p18_ae0 : ptF n18.mem B 0xAE0 = tbl2 P0 2 := by rw [m18]; exact p17_ae0
  have p18_b40 : ptF n18.mem B 0xB40 = tbl2 P0 3 := by rw [m18]; exact p17_b40
  have p18_ba0 : ptF n18.mem B 0xBA0 = tbl2 P0 4 := by rw [m18]; exact p17_ba0
  have p18_c00 : ptF n18.mem B 0xC00 = tbl2 P0 5 := by rw [m18]; exact p17_c00
  have p18_c60 : ptF n18.mem B 0xC60 = tbl2 P0 6 := by rw [m18]; exact p17_c60
  have p18_cc0 : ptF n18.mem B 0xCC0 = tbl2 P0 7 := by rw [m18]; exact p17_cc0
  have p18_d20 : ptF n18.mem B 0xD20 = tbl2 P1 0 := by rw [m18]; exact p17_d20
  have p18_d80 : ptF n18.mem B 0xD80 = tbl2 P1 1 := by rw [m18]; exact p17_d80
  have p18_de0 : ptF n18.mem B 0xDE0 = tbl2 P1 2 := by rw [m18]; exact p17_de0
  have p18_e40 : ptF n18.mem B 0xE40 = tbl2 P1 3 := by rw [m18]; exact p17_e40
  have p18_ea0 : ptF n18.mem B 0xEA0 = tbl2 P1 4 := by rw [m18]; exact p17_ea0
  have p18_f00 : ptF n18.mem B 0xF00 = tbl2 P1 5 := by rw [m18]; exact p17_f00
  have p18_f60 : ptF n18.mem B 0xF60 = tbl2 P1 6 := by rw [m18]; exact p17_f60
  have p18_fc0 : ptF n18.mem B 0xFC0 = tbl2 P1 7 := by rw [m18]; exact p17_fc0
  have p18_1380 : ptF n18.mem B 0x1380 = P0 := by rw [m18]; exact p17_1380
  have p18_1400 : ptF n18.mem B 0x1400 = P1 := by rw [m18]; exact p17_1400
  have mb18_1320 : leN (memBytes n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U1 := by rw [m18]; exact mb17_1320
  have mb18_1480 : memBytes n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 0x101 = List.replicate 0x101 0 := by rw [m18]; exact mb17_1480
  clear mb17_1480 mb17_1320 p17_1400 p17_1380 p17_fc0 p17_f60 p17_f00 p17_ea0 p17_e40 p17_de0 p17_d80 p17_d20 p17_cc0 p17_c60 p17_c00 p17_ba0 p17_b40 p17_ae0 p17_a80 p17_a20 p17_9c0 p17_960 p17_900 p17_8a0 p17_840 p17_7e0 p17_780 p17_720 p17_6c0 p17_660 p17_600 p17_5a0 p17_540 p17_4e0 p17_480 p17_420 p17_3a0 p17_320 a17_1588 a17_1460 a17_13e0 a17_400 a17_380 a17_2e0 a17_2c0 a17_2a0 w17_130 w17_12c w17_128 w17_124 w17_120 w17_11c w17_118 w17_114 w17_110 w17_10c w17_108 w17_104 w17_100 w17_fc w17_f8 w17_f4 w17_f0 w17_ec w17_e8 w17_e4 w17_e0 w17_dc w17_d8 w17_d4 w17_d0 w17_cc w17_c8 w17_c4 w17_c0 w17_bc w17_b8 w17_b4 w17_b0 w17_ac w17_a8 w17_a4 w17_a0 w17_9c w17_98 w17_94 w17_90 w17_8c w17_88 w17_84 w17_80 w17_7c w17_78 w17_70 w17_6c w17_68 w17_64 w17_60 w17_5c w17_58 w17_54 w17_50 w17_4c w17_48 w17_44 w17_40 w17_3c w17_38 w17_34 w17_30 w17_2c w17_28 w17_24 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_9 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 K17 fr17 s17 fz17 z17 rk17 C17 s17' c17 Z17
  -- 0x186C: memcpy
  obtain ⟨n19, P19, K19, X19⟩ := sv_mc (c := 0x1024) (d := 0x1480) (N := 0x101) F E18 s18 sv_at_186c sv_at_1870
    (by decide) (by decide) g18_2 g18_10 g18_11 g18_12
    (by decide) (by decide) (by decide)
  have s19 := P19.st
  have fr19 := P19.fr
  have t19 : Steps n0 n19 := t18.trans P19.steps
  have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
  have E19 : SvCode n19.mem := E18.fr F fr19
  have V19 : SvSaves B n19.mem v := V18.keep K19 (by decide)
  have g19_2 : reg n19 sp = B + 0x21A0 := by rw [P19.regs sp (by decide), g18_2]
  have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P19.regs (3 : Fin 32) (by decide), g18_3]
  have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P19.regs (4 : Fin 32) (by decide), g18_4]
  have g19_8 : reg n19 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [P19.regs (8 : Fin 32) (by decide), g18_8]
  have g19_9 : reg n19 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1400 := by rw [P19.regs (9 : Fin 32) (by decide), g18_9]
  have g19_18 : reg n19 (18 : Fin 32) = out := by rw [P19.regs (18 : Fin 32) (by decide), g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [P19.regs (19 : Fin 32) (by decide), g18_19]
  have g19_20 : reg n19 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P19.regs (20 : Fin 32) (by decide), g18_20]
  have g19_21 : reg n19 (21 : Fin 32) = s5v := by rw [P19.regs (21 : Fin 32) (by decide), g18_21]
  have g19_22 : reg n19 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [P19.regs (22 : Fin 32) (by decide), g18_22]
  have g19_23 : reg n19 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by rw [P19.regs (23 : Fin 32) (by decide), g18_23]
  have g19_24 : reg n19 (24 : Fin 32) = s8v := by rw [P19.regs (24 : Fin 32) (by decide), g18_24]
  have g19_25 : reg n19 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P19.regs (25 : Fin 32) (by decide), g18_25]
  have g19_26 : reg n19 (26 : Fin 32) = x26 := by rw [P19.regs (26 : Fin 32) (by decide), g18_26]
  have g19_27 : reg n19 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P19.regs (27 : Fin 32) (by decide), g18_27]
  have w19_24 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K19.w32 (by decide) (by decide)).trans w18_24
  have w19_28 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K19.w32 (by decide) (by decide)).trans w18_28
  have w19_2c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K19.w32 (by decide) (by decide)).trans w18_2c
  have w19_30 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K19.w32 (by decide) (by decide)).trans w18_30
  have w19_34 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K19.w32 (by decide) (by decide)).trans w18_34
  have w19_38 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K19.w32 (by decide) (by decide)).trans w18_38
  have w19_3c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K19.w32 (by decide) (by decide)).trans w18_3c
  have w19_40 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K19.w32 (by decide) (by decide)).trans w18_40
  have w19_44 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K19.w32 (by decide) (by decide)).trans w18_44
  have w19_48 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K19.w32 (by decide) (by decide)).trans w18_48
  have w19_4c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K19.w32 (by decide) (by decide)).trans w18_4c
  have w19_50 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K19.w32 (by decide) (by decide)).trans w18_50
  have w19_54 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K19.w32 (by decide) (by decide)).trans w18_54
  have w19_58 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K19.w32 (by decide) (by decide)).trans w18_58
  have w19_5c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K19.w32 (by decide) (by decide)).trans w18_5c
  have w19_60 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K19.w32 (by decide) (by decide)).trans w18_60
  have w19_64 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K19.w32 (by decide) (by decide)).trans w18_64
  have w19_68 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K19.w32 (by decide) (by decide)).trans w18_68
  have w19_6c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K19.w32 (by decide) (by decide)).trans w18_6c
  have w19_70 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K19.w32 (by decide) (by decide)).trans w18_70
  have w19_78 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := (K19.w32 (by decide) (by decide)).trans w18_78
  have w19_7c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K19.w32 (by decide) (by decide)).trans w18_7c
  have w19_80 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K19.w32 (by decide) (by decide)).trans w18_80
  have w19_84 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K19.w32 (by decide) (by decide)).trans w18_84
  have w19_88 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K19.w32 (by decide) (by decide)).trans w18_88
  have w19_8c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K19.w32 (by decide) (by decide)).trans w18_8c
  have w19_90 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K19.w32 (by decide) (by decide)).trans w18_90
  have w19_94 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K19.w32 (by decide) (by decide)).trans w18_94
  have w19_98 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K19.w32 (by decide) (by decide)).trans w18_98
  have w19_9c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K19.w32 (by decide) (by decide)).trans w18_9c
  have w19_a0 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K19.w32 (by decide) (by decide)).trans w18_a0
  have w19_a4 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K19.w32 (by decide) (by decide)).trans w18_a4
  have w19_a8 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K19.w32 (by decide) (by decide)).trans w18_a8
  have w19_ac : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K19.w32 (by decide) (by decide)).trans w18_ac
  have w19_b0 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K19.w32 (by decide) (by decide)).trans w18_b0
  have w19_b4 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K19.w32 (by decide) (by decide)).trans w18_b4
  have w19_b8 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K19.w32 (by decide) (by decide)).trans w18_b8
  have w19_bc : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K19.w32 (by decide) (by decide)).trans w18_bc
  have w19_c0 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K19.w32 (by decide) (by decide)).trans w18_c0
  have w19_c4 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K19.w32 (by decide) (by decide)).trans w18_c4
  have w19_c8 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K19.w32 (by decide) (by decide)).trans w18_c8
  have w19_cc : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K19.w32 (by decide) (by decide)).trans w18_cc
  have w19_d0 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K19.w32 (by decide) (by decide)).trans w18_d0
  have w19_d4 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K19.w32 (by decide) (by decide)).trans w18_d4
  have w19_d8 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K19.w32 (by decide) (by decide)).trans w18_d8
  have w19_dc : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K19.w32 (by decide) (by decide)).trans w18_dc
  have w19_e0 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K19.w32 (by decide) (by decide)).trans w18_e0
  have w19_e4 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K19.w32 (by decide) (by decide)).trans w18_e4
  have w19_e8 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K19.w32 (by decide) (by decide)).trans w18_e8
  have w19_ec : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K19.w32 (by decide) (by decide)).trans w18_ec
  have w19_f0 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K19.w32 (by decide) (by decide)).trans w18_f0
  have w19_f4 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K19.w32 (by decide) (by decide)).trans w18_f4
  have w19_f8 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K19.w32 (by decide) (by decide)).trans w18_f8
  have w19_fc : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K19.w32 (by decide) (by decide)).trans w18_fc
  have w19_100 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K19.w32 (by decide) (by decide)).trans w18_100
  have w19_104 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K19.w32 (by decide) (by decide)).trans w18_104
  have w19_108 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K19.w32 (by decide) (by decide)).trans w18_108
  have w19_10c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K19.w32 (by decide) (by decide)).trans w18_10c
  have w19_110 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K19.w32 (by decide) (by decide)).trans w18_110
  have w19_114 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K19.w32 (by decide) (by decide)).trans w18_114
  have w19_118 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K19.w32 (by decide) (by decide)).trans w18_118
  have w19_11c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K19.w32 (by decide) (by decide)).trans w18_11c
  have w19_120 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K19.w32 (by decide) (by decide)).trans w18_120
  have w19_124 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K19.w32 (by decide) (by decide)).trans w18_124
  have w19_128 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K19.w32 (by decide) (by decide)).trans w18_128
  have w19_12c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K19.w32 (by decide) (by decide)).trans w18_12c
  have w19_130 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K19.w32 (by decide) (by decide)).trans w18_130
  have a19_2a0 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K19.acc (by decide) (by decide)).trans a18_2a0
  have a19_2c0 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K19.acc (by decide) (by decide)).trans a18_2c0
  have a19_2e0 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K19.acc (by decide) (by decide)).trans a18_2e0
  have a19_380 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := (K19.acc (by decide) (by decide)).trans a18_380
  have a19_400 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := (K19.acc (by decide) (by decide)).trans a18_400
  have a19_13e0 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := (K19.acc (by decide) (by decide)).trans a18_13e0
  have a19_1460 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := (K19.acc (by decide) (by decide)).trans a18_1460
  have a19_1588 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U1 := (K19.acc (by decide) (by decide)).trans a18_1588
  have p19_320 : ptF n19.mem B 0x320 = P0 := (K19.pt (by decide) (by decide)).trans p18_320
  have p19_3a0 : ptF n19.mem B 0x3A0 = P1 := (K19.pt (by decide) (by decide)).trans p18_3a0
  have p19_420 : ptF n19.mem B 0x420 = tbl2 P0 0 := (K19.pt (by decide) (by decide)).trans p18_420
  have p19_480 : ptF n19.mem B 0x480 = tbl2 P0 1 := (K19.pt (by decide) (by decide)).trans p18_480
  have p19_4e0 : ptF n19.mem B 0x4E0 = tbl2 P0 2 := (K19.pt (by decide) (by decide)).trans p18_4e0
  have p19_540 : ptF n19.mem B 0x540 = tbl2 P0 3 := (K19.pt (by decide) (by decide)).trans p18_540
  have p19_5a0 : ptF n19.mem B 0x5A0 = tbl2 P0 4 := (K19.pt (by decide) (by decide)).trans p18_5a0
  have p19_600 : ptF n19.mem B 0x600 = tbl2 P0 5 := (K19.pt (by decide) (by decide)).trans p18_600
  have p19_660 : ptF n19.mem B 0x660 = tbl2 P0 6 := (K19.pt (by decide) (by decide)).trans p18_660
  have p19_6c0 : ptF n19.mem B 0x6C0 = tbl2 P0 7 := (K19.pt (by decide) (by decide)).trans p18_6c0
  have p19_720 : ptF n19.mem B 0x720 = tbl2 P1 0 := (K19.pt (by decide) (by decide)).trans p18_720
  have p19_780 : ptF n19.mem B 0x780 = tbl2 P1 1 := (K19.pt (by decide) (by decide)).trans p18_780
  have p19_7e0 : ptF n19.mem B 0x7E0 = tbl2 P1 2 := (K19.pt (by decide) (by decide)).trans p18_7e0
  have p19_840 : ptF n19.mem B 0x840 = tbl2 P1 3 := (K19.pt (by decide) (by decide)).trans p18_840
  have p19_8a0 : ptF n19.mem B 0x8A0 = tbl2 P1 4 := (K19.pt (by decide) (by decide)).trans p18_8a0
  have p19_900 : ptF n19.mem B 0x900 = tbl2 P1 5 := (K19.pt (by decide) (by decide)).trans p18_900
  have p19_960 : ptF n19.mem B 0x960 = tbl2 P1 6 := (K19.pt (by decide) (by decide)).trans p18_960
  have p19_9c0 : ptF n19.mem B 0x9C0 = tbl2 P1 7 := (K19.pt (by decide) (by decide)).trans p18_9c0
  have p19_a20 : ptF n19.mem B 0xA20 = tbl2 P0 0 := (K19.pt (by decide) (by decide)).trans p18_a20
  have p19_a80 : ptF n19.mem B 0xA80 = tbl2 P0 1 := (K19.pt (by decide) (by decide)).trans p18_a80
  have p19_ae0 : ptF n19.mem B 0xAE0 = tbl2 P0 2 := (K19.pt (by decide) (by decide)).trans p18_ae0
  have p19_b40 : ptF n19.mem B 0xB40 = tbl2 P0 3 := (K19.pt (by decide) (by decide)).trans p18_b40
  have p19_ba0 : ptF n19.mem B 0xBA0 = tbl2 P0 4 := (K19.pt (by decide) (by decide)).trans p18_ba0
  have p19_c00 : ptF n19.mem B 0xC00 = tbl2 P0 5 := (K19.pt (by decide) (by decide)).trans p18_c00
  have p19_c60 : ptF n19.mem B 0xC60 = tbl2 P0 6 := (K19.pt (by decide) (by decide)).trans p18_c60
  have p19_cc0 : ptF n19.mem B 0xCC0 = tbl2 P0 7 := (K19.pt (by decide) (by decide)).trans p18_cc0
  have p19_d20 : ptF n19.mem B 0xD20 = tbl2 P1 0 := (K19.pt (by decide) (by decide)).trans p18_d20
  have p19_d80 : ptF n19.mem B 0xD80 = tbl2 P1 1 := (K19.pt (by decide) (by decide)).trans p18_d80
  have p19_de0 : ptF n19.mem B 0xDE0 = tbl2 P1 2 := (K19.pt (by decide) (by decide)).trans p18_de0
  have p19_e40 : ptF n19.mem B 0xE40 = tbl2 P1 3 := (K19.pt (by decide) (by decide)).trans p18_e40
  have p19_ea0 : ptF n19.mem B 0xEA0 = tbl2 P1 4 := (K19.pt (by decide) (by decide)).trans p18_ea0
  have p19_f00 : ptF n19.mem B 0xF00 = tbl2 P1 5 := (K19.pt (by decide) (by decide)).trans p18_f00
  have p19_f60 : ptF n19.mem B 0xF60 = tbl2 P1 6 := (K19.pt (by decide) (by decide)).trans p18_f60
  have p19_fc0 : ptF n19.mem B 0xFC0 = tbl2 P1 7 := (K19.pt (by decide) (by decide)).trans p18_fc0
  have p19_1380 : ptF n19.mem B 0x1380 = P0 := (K19.pt (by decide) (by decide)).trans p18_1380
  have p19_1400 : ptF n19.mem B 0x1400 = P1 := (K19.pt (by decide) (by decide)).trans p18_1400
  have mb19_1320 : leN (memBytes n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U1 := by rw [K19.mb (by decide) (by decide)]; exact mb18_1320
  have mb19_1480 : memBytes n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 0x101 = List.replicate 0x101 0 := by rw [K19.mb (by decide) (by decide)]; exact mb18_1480
  have mb19_1024 : memBytes n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) 0x101 = List.replicate 0x101 0 := by
    rw [memBytes_cp (S := B + 0x21A0) (c := 0x1024) (d := 0x1480) (N := 0x101) fun q hq => by
      rw [show 0x1024 + q = 0x1024 + (0x0 + q) by omega, X19 (0x0 + q) (by omega),
        show 0x1480 + (0x0 + q) = 0x1480 + q by omega]]; exact mb18_1480
  clear mb18_1480 mb18_1320 p18_1400 p18_1380 p18_fc0 p18_f60 p18_f00 p18_ea0 p18_e40 p18_de0 p18_d80 p18_d20 p18_cc0 p18_c60 p18_c00 p18_ba0 p18_b40 p18_ae0 p18_a80 p18_a20 p18_9c0 p18_960 p18_900 p18_8a0 p18_840 p18_7e0 p18_780 p18_720 p18_6c0 p18_660 p18_600 p18_5a0 p18_540 p18_4e0 p18_480 p18_420 p18_3a0 p18_320 a18_1588 a18_1460 a18_13e0 a18_400 a18_380 a18_2e0 a18_2c0 a18_2a0 w18_130 w18_12c w18_128 w18_124 w18_120 w18_11c w18_118 w18_114 w18_110 w18_10c w18_108 w18_104 w18_100 w18_fc w18_f8 w18_f4 w18_f0 w18_ec w18_e8 w18_e4 w18_e0 w18_dc w18_d8 w18_d4 w18_d0 w18_cc w18_c8 w18_c4 w18_c0 w18_bc w18_b8 w18_b4 w18_b0 w18_ac w18_a8 w18_a4 w18_a0 w18_9c w18_98 w18_94 w18_90 w18_8c w18_88 w18_84 w18_80 w18_7c w18_78 w18_70 w18_6c w18_68 w18_64 w18_60 w18_5c w18_58 w18_54 w18_50 w18_4c w18_48 w18_44 w18_40 w18_3c w18_38 w18_34 w18_30 w18_2c w18_28 w18_24 g18_12 g18_11 g18_10 g18_9 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 rb18 s18 m18 u18 c18
  -- 0x1874
  obtain ⟨n20, c20, u20⟩ := s19.block svEcW1874 E19.self svEcW1874_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m20 : n20.mem = n19.mem := u20.mem
  have s20 : St n20.mem SV n20 0x188C (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
  have rb20 : ∀ q, reg n20 q = (runBlock svEcW1874 (n19.mem, reg n19)).2 q := fun q => by rw [u20.regs]
  have fr20 : ∀ x, SvR B x → n20.mem x = n19.mem x := fun x _ => by rw [m20]
  have t20 : Steps n0 n20 := t19.trans c20
  have fR20 : ∀ x, SvR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
  have E20 : SvCode n20.mem := E19.fr F fr20
  have V20 : SvSaves B n20.mem v := V19.same m20
  have g20_2 : reg n20 sp = B + 0x21A0 := by
    rw [rb20, runBlock_reg _ _ _ sp s19.zero (by decide), g19_2]
  have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb20, runBlock_reg _ _ _ (3 : Fin 32) s19.zero (by decide), g19_3]
  have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb20, runBlock_reg _ _ _ (4 : Fin 32) s19.zero (by decide), g19_4]
  have g20_8 : reg n20 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb20, runBlock_reg _ _ _ (8 : Fin 32) s19.zero (by decide), g19_8]
  have g20_9 : reg n20 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1400 := by
    rw [rb20, runBlock_reg _ _ _ (9 : Fin 32) s19.zero (by decide), g19_9]
  have g20_18 : reg n20 (18 : Fin 32) = out := by
    rw [rb20, runBlock_reg _ _ _ (18 : Fin 32) s19.zero (by decide), g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = bp := by
    rw [rb20, runBlock_reg _ _ _ (19 : Fin 32) s19.zero (by decide), g19_19]
  have g20_20 : reg n20 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb20, runBlock_reg _ _ _ (20 : Fin 32) s19.zero (by decide), g19_20]
  have g20_21 : reg n20 (21 : Fin 32) = s5v := by
    rw [rb20, runBlock_reg _ _ _ (21 : Fin 32) s19.zero (by decide), g19_21]
  have g20_22 : reg n20 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by
    rw [rb20, runBlock_reg _ _ _ (22 : Fin 32) s19.zero (by decide), g19_22]
  have g20_23 : reg n20 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by
    rw [rb20, runBlock_reg _ _ _ (23 : Fin 32) s19.zero (by decide), g19_23]
  have g20_24 : reg n20 (24 : Fin 32) = s8v := by
    rw [rb20, runBlock_reg _ _ _ (24 : Fin 32) s19.zero (by decide), g19_24]
  have g20_25 : reg n20 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb20, runBlock_reg _ _ _ (25 : Fin 32) s19.zero (by decide), g19_25]
  have g20_26 : reg n20 (26 : Fin 32) = x26 := by
    rw [rb20, runBlock_reg _ _ _ (26 : Fin 32) s19.zero (by decide), g19_26]
  have g20_27 : reg n20 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb20, runBlock_reg _ _ _ (27 : Fin 32) s19.zero (by decide), g19_27]
  have g20_10 : reg n20 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by
    rw [rb20]; simp +decide only [runBlock, BInstr.run, svEcW1874, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g19_2, g19_3, g19_4, g19_8, g19_9, g19_18, g19_19, g19_20, g19_21, g19_22, g19_23, g19_24, g19_25, g19_26, g19_27, s19.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g20_11 : reg n20 a1 = BitVec.ofNat 32 0x101 := by
    rw [rb20]; simp +decide only [runBlock, BInstr.run, svEcW1874, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g19_2, g19_3, g19_4, g19_8, g19_9, g19_18, g19_19, g19_20, g19_21, g19_22, g19_23, g19_24, g19_25, g19_26, g19_27, s19.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g20_12 : reg n20 a2 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
    rw [rb20]; simp +decide only [runBlock, BInstr.run, svEcW1874, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g19_2, g19_3, g19_4, g19_8, g19_9, g19_18, g19_19, g19_20, g19_21, g19_22, g19_23, g19_24, g19_25, g19_26, g19_27, s19.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g20_13 : reg n20 a3 = BitVec.ofNat 32 0x20 := by
    rw [rb20]; simp +decide only [runBlock, BInstr.run, svEcW1874, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g19_2, g19_3, g19_4, g19_8, g19_9, g19_18, g19_19, g19_20, g19_21, g19_22, g19_23, g19_24, g19_25, g19_26, g19_27, s19.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g20_14 : reg n20 a4 = BitVec.ofNat 32 0x100 := by
    rw [rb20]; simp +decide only [runBlock, BInstr.run, svEcW1874, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g19_2, g19_3, g19_4, g19_8, g19_9, g19_18, g19_19, g19_20, g19_21, g19_22, g19_23, g19_24, g19_25, g19_26, g19_27, s19.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
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
  have a20_2a0 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m20]; exact a19_2a0
  have a20_2c0 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m20]; exact a19_2c0
  have a20_2e0 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m20]; exact a19_2e0
  have a20_380 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m20]; exact a19_380
  have a20_400 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m20]; exact a19_400
  have a20_13e0 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := by rw [m20]; exact a19_13e0
  have a20_1460 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := by rw [m20]; exact a19_1460
  have a20_1588 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U1 := by rw [m20]; exact a19_1588
  have p20_320 : ptF n20.mem B 0x320 = P0 := by rw [m20]; exact p19_320
  have p20_3a0 : ptF n20.mem B 0x3A0 = P1 := by rw [m20]; exact p19_3a0
  have p20_420 : ptF n20.mem B 0x420 = tbl2 P0 0 := by rw [m20]; exact p19_420
  have p20_480 : ptF n20.mem B 0x480 = tbl2 P0 1 := by rw [m20]; exact p19_480
  have p20_4e0 : ptF n20.mem B 0x4E0 = tbl2 P0 2 := by rw [m20]; exact p19_4e0
  have p20_540 : ptF n20.mem B 0x540 = tbl2 P0 3 := by rw [m20]; exact p19_540
  have p20_5a0 : ptF n20.mem B 0x5A0 = tbl2 P0 4 := by rw [m20]; exact p19_5a0
  have p20_600 : ptF n20.mem B 0x600 = tbl2 P0 5 := by rw [m20]; exact p19_600
  have p20_660 : ptF n20.mem B 0x660 = tbl2 P0 6 := by rw [m20]; exact p19_660
  have p20_6c0 : ptF n20.mem B 0x6C0 = tbl2 P0 7 := by rw [m20]; exact p19_6c0
  have p20_720 : ptF n20.mem B 0x720 = tbl2 P1 0 := by rw [m20]; exact p19_720
  have p20_780 : ptF n20.mem B 0x780 = tbl2 P1 1 := by rw [m20]; exact p19_780
  have p20_7e0 : ptF n20.mem B 0x7E0 = tbl2 P1 2 := by rw [m20]; exact p19_7e0
  have p20_840 : ptF n20.mem B 0x840 = tbl2 P1 3 := by rw [m20]; exact p19_840
  have p20_8a0 : ptF n20.mem B 0x8A0 = tbl2 P1 4 := by rw [m20]; exact p19_8a0
  have p20_900 : ptF n20.mem B 0x900 = tbl2 P1 5 := by rw [m20]; exact p19_900
  have p20_960 : ptF n20.mem B 0x960 = tbl2 P1 6 := by rw [m20]; exact p19_960
  have p20_9c0 : ptF n20.mem B 0x9C0 = tbl2 P1 7 := by rw [m20]; exact p19_9c0
  have p20_a20 : ptF n20.mem B 0xA20 = tbl2 P0 0 := by rw [m20]; exact p19_a20
  have p20_a80 : ptF n20.mem B 0xA80 = tbl2 P0 1 := by rw [m20]; exact p19_a80
  have p20_ae0 : ptF n20.mem B 0xAE0 = tbl2 P0 2 := by rw [m20]; exact p19_ae0
  have p20_b40 : ptF n20.mem B 0xB40 = tbl2 P0 3 := by rw [m20]; exact p19_b40
  have p20_ba0 : ptF n20.mem B 0xBA0 = tbl2 P0 4 := by rw [m20]; exact p19_ba0
  have p20_c00 : ptF n20.mem B 0xC00 = tbl2 P0 5 := by rw [m20]; exact p19_c00
  have p20_c60 : ptF n20.mem B 0xC60 = tbl2 P0 6 := by rw [m20]; exact p19_c60
  have p20_cc0 : ptF n20.mem B 0xCC0 = tbl2 P0 7 := by rw [m20]; exact p19_cc0
  have p20_d20 : ptF n20.mem B 0xD20 = tbl2 P1 0 := by rw [m20]; exact p19_d20
  have p20_d80 : ptF n20.mem B 0xD80 = tbl2 P1 1 := by rw [m20]; exact p19_d80
  have p20_de0 : ptF n20.mem B 0xDE0 = tbl2 P1 2 := by rw [m20]; exact p19_de0
  have p20_e40 : ptF n20.mem B 0xE40 = tbl2 P1 3 := by rw [m20]; exact p19_e40
  have p20_ea0 : ptF n20.mem B 0xEA0 = tbl2 P1 4 := by rw [m20]; exact p19_ea0
  have p20_f00 : ptF n20.mem B 0xF00 = tbl2 P1 5 := by rw [m20]; exact p19_f00
  have p20_f60 : ptF n20.mem B 0xF60 = tbl2 P1 6 := by rw [m20]; exact p19_f60
  have p20_fc0 : ptF n20.mem B 0xFC0 = tbl2 P1 7 := by rw [m20]; exact p19_fc0
  have p20_1380 : ptF n20.mem B 0x1380 = P0 := by rw [m20]; exact p19_1380
  have p20_1400 : ptF n20.mem B 0x1400 = P1 := by rw [m20]; exact p19_1400
  have mb20_1024 : memBytes n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) 0x101 = List.replicate 0x101 0 := by rw [m20]; exact mb19_1024
  have mb20_1320 : leN (memBytes n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U1 := by rw [m20]; exact mb19_1320
  have mb20_1480 : memBytes n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 0x101 = List.replicate 0x101 0 := by rw [m20]; exact mb19_1480
  clear mb19_1024 mb19_1480 mb19_1320 p19_1400 p19_1380 p19_fc0 p19_f60 p19_f00 p19_ea0 p19_e40 p19_de0 p19_d80 p19_d20 p19_cc0 p19_c60 p19_c00 p19_ba0 p19_b40 p19_ae0 p19_a80 p19_a20 p19_9c0 p19_960 p19_900 p19_8a0 p19_840 p19_7e0 p19_780 p19_720 p19_6c0 p19_660 p19_600 p19_5a0 p19_540 p19_4e0 p19_480 p19_420 p19_3a0 p19_320 a19_1588 a19_1460 a19_13e0 a19_400 a19_380 a19_2e0 a19_2c0 a19_2a0 w19_130 w19_12c w19_128 w19_124 w19_120 w19_11c w19_118 w19_114 w19_110 w19_10c w19_108 w19_104 w19_100 w19_fc w19_f8 w19_f4 w19_f0 w19_ec w19_e8 w19_e4 w19_e0 w19_dc w19_d8 w19_d4 w19_d0 w19_cc w19_c8 w19_c4 w19_c0 w19_bc w19_b8 w19_b4 w19_b0 w19_ac w19_a8 w19_a4 w19_a0 w19_9c w19_98 w19_94 w19_90 w19_8c w19_88 w19_84 w19_80 w19_7c w19_78 w19_70 w19_6c w19_68 w19_64 w19_60 w19_5c w19_58 w19_54 w19_50 w19_4c w19_48 w19_44 w19_40 w19_3c w19_38 w19_34 w19_30 w19_2c w19_28 w19_24 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_9 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 s19 X19 K19 P19
  -- 0x188C: wnaf_form
  obtain ⟨n21, P21, K21, A21, D21, H21⟩ := sv_wf (cw := 0x1024) (cc := 0x1320) F E20 (WN0.sv F fR20) s20
    sv_at_188c sv_at_1890 (by decide) (by decide) g20_2 g20_10 g20_11
    g20_12 g20_13 g20_14 (by decide) (by decide) (by decide) mb20_1320 mb20_1024
  have s21 := P21.st
  have fr21 := P21.fr
  have t21 : Steps n0 n21 := t20.trans P21.steps
  have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
  have E21 : SvCode n21.mem := E20.fr F fr21
  have V21 : SvSaves B n21.mem v := V20.keep K21 (by decide)
  have g21_2 : reg n21 sp = B + 0x21A0 := by rw [P21.regs sp (by decide), g20_2]
  have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P21.regs (3 : Fin 32) (by decide), g20_3]
  have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P21.regs (4 : Fin 32) (by decide), g20_4]
  have g21_8 : reg n21 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [P21.regs (8 : Fin 32) (by decide), g20_8]
  have g21_9 : reg n21 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1400 := by rw [P21.regs (9 : Fin 32) (by decide), g20_9]
  have g21_18 : reg n21 (18 : Fin 32) = out := by rw [P21.regs (18 : Fin 32) (by decide), g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [P21.regs (19 : Fin 32) (by decide), g20_19]
  have g21_20 : reg n21 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P21.regs (20 : Fin 32) (by decide), g20_20]
  have g21_21 : reg n21 (21 : Fin 32) = s5v := by rw [P21.regs (21 : Fin 32) (by decide), g20_21]
  have g21_22 : reg n21 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [P21.regs (22 : Fin 32) (by decide), g20_22]
  have g21_23 : reg n21 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by rw [P21.regs (23 : Fin 32) (by decide), g20_23]
  have g21_24 : reg n21 (24 : Fin 32) = s8v := by rw [P21.regs (24 : Fin 32) (by decide), g20_24]
  have g21_25 : reg n21 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P21.regs (25 : Fin 32) (by decide), g20_25]
  have g21_26 : reg n21 (26 : Fin 32) = x26 := by rw [P21.regs (26 : Fin 32) (by decide), g20_26]
  have g21_27 : reg n21 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P21.regs (27 : Fin 32) (by decide), g20_27]
  have w21_24 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K21.w32 (by decide) (by decide)).trans w20_24
  have w21_28 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K21.w32 (by decide) (by decide)).trans w20_28
  have w21_2c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K21.w32 (by decide) (by decide)).trans w20_2c
  have w21_30 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K21.w32 (by decide) (by decide)).trans w20_30
  have w21_34 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K21.w32 (by decide) (by decide)).trans w20_34
  have w21_38 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K21.w32 (by decide) (by decide)).trans w20_38
  have w21_3c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K21.w32 (by decide) (by decide)).trans w20_3c
  have w21_40 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K21.w32 (by decide) (by decide)).trans w20_40
  have w21_44 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K21.w32 (by decide) (by decide)).trans w20_44
  have w21_48 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K21.w32 (by decide) (by decide)).trans w20_48
  have w21_4c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K21.w32 (by decide) (by decide)).trans w20_4c
  have w21_50 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K21.w32 (by decide) (by decide)).trans w20_50
  have w21_54 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K21.w32 (by decide) (by decide)).trans w20_54
  have w21_58 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K21.w32 (by decide) (by decide)).trans w20_58
  have w21_5c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K21.w32 (by decide) (by decide)).trans w20_5c
  have w21_60 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K21.w32 (by decide) (by decide)).trans w20_60
  have w21_64 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K21.w32 (by decide) (by decide)).trans w20_64
  have w21_68 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K21.w32 (by decide) (by decide)).trans w20_68
  have w21_6c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K21.w32 (by decide) (by decide)).trans w20_6c
  have w21_70 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K21.w32 (by decide) (by decide)).trans w20_70
  have w21_78 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := (K21.w32 (by decide) (by decide)).trans w20_78
  have w21_7c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K21.w32 (by decide) (by decide)).trans w20_7c
  have w21_80 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K21.w32 (by decide) (by decide)).trans w20_80
  have w21_84 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K21.w32 (by decide) (by decide)).trans w20_84
  have w21_88 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K21.w32 (by decide) (by decide)).trans w20_88
  have w21_8c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K21.w32 (by decide) (by decide)).trans w20_8c
  have w21_90 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K21.w32 (by decide) (by decide)).trans w20_90
  have w21_94 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K21.w32 (by decide) (by decide)).trans w20_94
  have w21_98 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K21.w32 (by decide) (by decide)).trans w20_98
  have w21_9c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K21.w32 (by decide) (by decide)).trans w20_9c
  have w21_a0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K21.w32 (by decide) (by decide)).trans w20_a0
  have w21_a4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K21.w32 (by decide) (by decide)).trans w20_a4
  have w21_a8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K21.w32 (by decide) (by decide)).trans w20_a8
  have w21_ac : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K21.w32 (by decide) (by decide)).trans w20_ac
  have w21_b0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K21.w32 (by decide) (by decide)).trans w20_b0
  have w21_b4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K21.w32 (by decide) (by decide)).trans w20_b4
  have w21_b8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K21.w32 (by decide) (by decide)).trans w20_b8
  have w21_bc : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K21.w32 (by decide) (by decide)).trans w20_bc
  have w21_c0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K21.w32 (by decide) (by decide)).trans w20_c0
  have w21_c4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K21.w32 (by decide) (by decide)).trans w20_c4
  have w21_c8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K21.w32 (by decide) (by decide)).trans w20_c8
  have w21_cc : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K21.w32 (by decide) (by decide)).trans w20_cc
  have w21_d0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K21.w32 (by decide) (by decide)).trans w20_d0
  have w21_d4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K21.w32 (by decide) (by decide)).trans w20_d4
  have w21_d8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K21.w32 (by decide) (by decide)).trans w20_d8
  have w21_dc : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K21.w32 (by decide) (by decide)).trans w20_dc
  have w21_e0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K21.w32 (by decide) (by decide)).trans w20_e0
  have w21_e4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K21.w32 (by decide) (by decide)).trans w20_e4
  have w21_e8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K21.w32 (by decide) (by decide)).trans w20_e8
  have w21_ec : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K21.w32 (by decide) (by decide)).trans w20_ec
  have w21_f0 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K21.w32 (by decide) (by decide)).trans w20_f0
  have w21_f4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K21.w32 (by decide) (by decide)).trans w20_f4
  have w21_f8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K21.w32 (by decide) (by decide)).trans w20_f8
  have w21_fc : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K21.w32 (by decide) (by decide)).trans w20_fc
  have w21_100 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K21.w32 (by decide) (by decide)).trans w20_100
  have w21_104 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K21.w32 (by decide) (by decide)).trans w20_104
  have w21_108 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K21.w32 (by decide) (by decide)).trans w20_108
  have w21_10c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K21.w32 (by decide) (by decide)).trans w20_10c
  have w21_110 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K21.w32 (by decide) (by decide)).trans w20_110
  have w21_114 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K21.w32 (by decide) (by decide)).trans w20_114
  have w21_118 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K21.w32 (by decide) (by decide)).trans w20_118
  have w21_11c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K21.w32 (by decide) (by decide)).trans w20_11c
  have w21_120 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K21.w32 (by decide) (by decide)).trans w20_120
  have w21_124 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K21.w32 (by decide) (by decide)).trans w20_124
  have w21_128 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K21.w32 (by decide) (by decide)).trans w20_128
  have w21_12c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K21.w32 (by decide) (by decide)).trans w20_12c
  have w21_130 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K21.w32 (by decide) (by decide)).trans w20_130
  have a21_2a0 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K21.acc (by decide) (by decide)).trans a20_2a0
  have a21_2c0 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K21.acc (by decide) (by decide)).trans a20_2c0
  have a21_2e0 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K21.acc (by decide) (by decide)).trans a20_2e0
  have a21_380 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := (K21.acc (by decide) (by decide)).trans a20_380
  have a21_400 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := (K21.acc (by decide) (by decide)).trans a20_400
  have a21_13e0 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := (K21.acc (by decide) (by decide)).trans a20_13e0
  have a21_1460 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := (K21.acc (by decide) (by decide)).trans a20_1460
  have a21_1588 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U1 := (K21.acc (by decide) (by decide)).trans a20_1588
  have p21_320 : ptF n21.mem B 0x320 = P0 := (K21.pt (by decide) (by decide)).trans p20_320
  have p21_3a0 : ptF n21.mem B 0x3A0 = P1 := (K21.pt (by decide) (by decide)).trans p20_3a0
  have p21_420 : ptF n21.mem B 0x420 = tbl2 P0 0 := (K21.pt (by decide) (by decide)).trans p20_420
  have p21_480 : ptF n21.mem B 0x480 = tbl2 P0 1 := (K21.pt (by decide) (by decide)).trans p20_480
  have p21_4e0 : ptF n21.mem B 0x4E0 = tbl2 P0 2 := (K21.pt (by decide) (by decide)).trans p20_4e0
  have p21_540 : ptF n21.mem B 0x540 = tbl2 P0 3 := (K21.pt (by decide) (by decide)).trans p20_540
  have p21_5a0 : ptF n21.mem B 0x5A0 = tbl2 P0 4 := (K21.pt (by decide) (by decide)).trans p20_5a0
  have p21_600 : ptF n21.mem B 0x600 = tbl2 P0 5 := (K21.pt (by decide) (by decide)).trans p20_600
  have p21_660 : ptF n21.mem B 0x660 = tbl2 P0 6 := (K21.pt (by decide) (by decide)).trans p20_660
  have p21_6c0 : ptF n21.mem B 0x6C0 = tbl2 P0 7 := (K21.pt (by decide) (by decide)).trans p20_6c0
  have p21_720 : ptF n21.mem B 0x720 = tbl2 P1 0 := (K21.pt (by decide) (by decide)).trans p20_720
  have p21_780 : ptF n21.mem B 0x780 = tbl2 P1 1 := (K21.pt (by decide) (by decide)).trans p20_780
  have p21_7e0 : ptF n21.mem B 0x7E0 = tbl2 P1 2 := (K21.pt (by decide) (by decide)).trans p20_7e0
  have p21_840 : ptF n21.mem B 0x840 = tbl2 P1 3 := (K21.pt (by decide) (by decide)).trans p20_840
  have p21_8a0 : ptF n21.mem B 0x8A0 = tbl2 P1 4 := (K21.pt (by decide) (by decide)).trans p20_8a0
  have p21_900 : ptF n21.mem B 0x900 = tbl2 P1 5 := (K21.pt (by decide) (by decide)).trans p20_900
  have p21_960 : ptF n21.mem B 0x960 = tbl2 P1 6 := (K21.pt (by decide) (by decide)).trans p20_960
  have p21_9c0 : ptF n21.mem B 0x9C0 = tbl2 P1 7 := (K21.pt (by decide) (by decide)).trans p20_9c0
  have p21_a20 : ptF n21.mem B 0xA20 = tbl2 P0 0 := (K21.pt (by decide) (by decide)).trans p20_a20
  have p21_a80 : ptF n21.mem B 0xA80 = tbl2 P0 1 := (K21.pt (by decide) (by decide)).trans p20_a80
  have p21_ae0 : ptF n21.mem B 0xAE0 = tbl2 P0 2 := (K21.pt (by decide) (by decide)).trans p20_ae0
  have p21_b40 : ptF n21.mem B 0xB40 = tbl2 P0 3 := (K21.pt (by decide) (by decide)).trans p20_b40
  have p21_ba0 : ptF n21.mem B 0xBA0 = tbl2 P0 4 := (K21.pt (by decide) (by decide)).trans p20_ba0
  have p21_c00 : ptF n21.mem B 0xC00 = tbl2 P0 5 := (K21.pt (by decide) (by decide)).trans p20_c00
  have p21_c60 : ptF n21.mem B 0xC60 = tbl2 P0 6 := (K21.pt (by decide) (by decide)).trans p20_c60
  have p21_cc0 : ptF n21.mem B 0xCC0 = tbl2 P0 7 := (K21.pt (by decide) (by decide)).trans p20_cc0
  have p21_d20 : ptF n21.mem B 0xD20 = tbl2 P1 0 := (K21.pt (by decide) (by decide)).trans p20_d20
  have p21_d80 : ptF n21.mem B 0xD80 = tbl2 P1 1 := (K21.pt (by decide) (by decide)).trans p20_d80
  have p21_de0 : ptF n21.mem B 0xDE0 = tbl2 P1 2 := (K21.pt (by decide) (by decide)).trans p20_de0
  have p21_e40 : ptF n21.mem B 0xE40 = tbl2 P1 3 := (K21.pt (by decide) (by decide)).trans p20_e40
  have p21_ea0 : ptF n21.mem B 0xEA0 = tbl2 P1 4 := (K21.pt (by decide) (by decide)).trans p20_ea0
  have p21_f00 : ptF n21.mem B 0xF00 = tbl2 P1 5 := (K21.pt (by decide) (by decide)).trans p20_f00
  have p21_f60 : ptF n21.mem B 0xF60 = tbl2 P1 6 := (K21.pt (by decide) (by decide)).trans p20_f60
  have p21_fc0 : ptF n21.mem B 0xFC0 = tbl2 P1 7 := (K21.pt (by decide) (by decide)).trans p20_fc0
  have p21_1380 : ptF n21.mem B 0x1380 = P0 := (K21.pt (by decide) (by decide)).trans p20_1380
  have p21_1400 : ptF n21.mem B 0x1400 = P1 := (K21.pt (by decide) (by decide)).trans p20_1400
  have mb21_1320 : leN (memBytes n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U1 := by rw [K21.mb (by decide) (by decide)]; exact mb20_1320
  have mb21_1480 : memBytes n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 0x101 = List.replicate 0x101 0 := by rw [K21.mb (by decide) (by decide)]; exact mb20_1480
  have g21_10 : reg n21 a0 = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := A21
  have mb21_1024 : memBytes n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := D21
  clear mb20_1480 mb20_1320 mb20_1024 p20_1400 p20_1380 p20_fc0 p20_f60 p20_f00 p20_ea0 p20_e40 p20_de0 p20_d80 p20_d20 p20_cc0 p20_c60 p20_c00 p20_ba0 p20_b40 p20_ae0 p20_a80 p20_a20 p20_9c0 p20_960 p20_900 p20_8a0 p20_840 p20_7e0 p20_780 p20_720 p20_6c0 p20_660 p20_600 p20_5a0 p20_540 p20_4e0 p20_480 p20_420 p20_3a0 p20_320 a20_1588 a20_1460 a20_13e0 a20_400 a20_380 a20_2e0 a20_2c0 a20_2a0 w20_130 w20_12c w20_128 w20_124 w20_120 w20_11c w20_118 w20_114 w20_110 w20_10c w20_108 w20_104 w20_100 w20_fc w20_f8 w20_f4 w20_f0 w20_ec w20_e8 w20_e4 w20_e0 w20_dc w20_d8 w20_d4 w20_d0 w20_cc w20_c8 w20_c4 w20_c0 w20_bc w20_b8 w20_b4 w20_b0 w20_ac w20_a8 w20_a4 w20_a0 w20_9c w20_98 w20_94 w20_90 w20_8c w20_88 w20_84 w20_80 w20_7c w20_78 w20_70 w20_6c w20_68 w20_64 w20_60 w20_5c w20_58 w20_54 w20_50 w20_4c w20_48 w20_44 w20_40 w20_3c w20_38 w20_34 w20_30 w20_2c w20_28 w20_24 g20_14 g20_13 g20_12 g20_11 g20_10 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_9 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 rb20 s20 m20 u20 c20
  -- 0x1894: sw
  obtain ⟨n22, d22, s22, fr22, K22, W22, rg22⟩ := sv_sw F E21 s21 sv_at_1894 (off' := 0x1898) (c := 0x1020)
    (by decide) (by rw [g21_27]; sv_addr) (by decide) (by decide)
  have t22 : Steps n0 n22 := t21.trans d22
  have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
  have E22 : SvCode n22.mem := E21.fr F fr22
  have V22 : SvSaves B n22.mem v := V21.keep K22 (by decide)
  have g22_2 : reg n22 sp = B + 0x21A0 := by rw [rg22 sp, g21_2]
  have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg22 (3 : Fin 32), g21_3]
  have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg22 (4 : Fin 32), g21_4]
  have g22_8 : reg n22 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rg22 (8 : Fin 32), g21_8]
  have g22_9 : reg n22 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1400 := by rw [rg22 (9 : Fin 32), g21_9]
  have g22_10 : reg n22 a0 = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [rg22 a0, g21_10]
  have g22_18 : reg n22 (18 : Fin 32) = out := by rw [rg22 (18 : Fin 32), g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [rg22 (19 : Fin 32), g21_19]
  have g22_20 : reg n22 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg22 (20 : Fin 32), g21_20]
  have g22_21 : reg n22 (21 : Fin 32) = s5v := by rw [rg22 (21 : Fin 32), g21_21]
  have g22_22 : reg n22 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [rg22 (22 : Fin 32), g21_22]
  have g22_23 : reg n22 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by rw [rg22 (23 : Fin 32), g21_23]
  have g22_24 : reg n22 (24 : Fin 32) = s8v := by rw [rg22 (24 : Fin 32), g21_24]
  have g22_25 : reg n22 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [rg22 (25 : Fin 32), g21_25]
  have g22_26 : reg n22 (26 : Fin 32) = x26 := by rw [rg22 (26 : Fin 32), g21_26]
  have g22_27 : reg n22 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg22 (27 : Fin 32), g21_27]
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
  have w22_1020 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [W22, g21_10]
  have a22_2a0 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K22.acc (by decide) (by decide)).trans a21_2a0
  have a22_2c0 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K22.acc (by decide) (by decide)).trans a21_2c0
  have a22_2e0 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K22.acc (by decide) (by decide)).trans a21_2e0
  have a22_380 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := (K22.acc (by decide) (by decide)).trans a21_380
  have a22_400 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := (K22.acc (by decide) (by decide)).trans a21_400
  have a22_13e0 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := (K22.acc (by decide) (by decide)).trans a21_13e0
  have a22_1460 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := (K22.acc (by decide) (by decide)).trans a21_1460
  have a22_1588 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U1 := (K22.acc (by decide) (by decide)).trans a21_1588
  have p22_320 : ptF n22.mem B 0x320 = P0 := (K22.pt (by decide) (by decide)).trans p21_320
  have p22_3a0 : ptF n22.mem B 0x3A0 = P1 := (K22.pt (by decide) (by decide)).trans p21_3a0
  have p22_420 : ptF n22.mem B 0x420 = tbl2 P0 0 := (K22.pt (by decide) (by decide)).trans p21_420
  have p22_480 : ptF n22.mem B 0x480 = tbl2 P0 1 := (K22.pt (by decide) (by decide)).trans p21_480
  have p22_4e0 : ptF n22.mem B 0x4E0 = tbl2 P0 2 := (K22.pt (by decide) (by decide)).trans p21_4e0
  have p22_540 : ptF n22.mem B 0x540 = tbl2 P0 3 := (K22.pt (by decide) (by decide)).trans p21_540
  have p22_5a0 : ptF n22.mem B 0x5A0 = tbl2 P0 4 := (K22.pt (by decide) (by decide)).trans p21_5a0
  have p22_600 : ptF n22.mem B 0x600 = tbl2 P0 5 := (K22.pt (by decide) (by decide)).trans p21_600
  have p22_660 : ptF n22.mem B 0x660 = tbl2 P0 6 := (K22.pt (by decide) (by decide)).trans p21_660
  have p22_6c0 : ptF n22.mem B 0x6C0 = tbl2 P0 7 := (K22.pt (by decide) (by decide)).trans p21_6c0
  have p22_720 : ptF n22.mem B 0x720 = tbl2 P1 0 := (K22.pt (by decide) (by decide)).trans p21_720
  have p22_780 : ptF n22.mem B 0x780 = tbl2 P1 1 := (K22.pt (by decide) (by decide)).trans p21_780
  have p22_7e0 : ptF n22.mem B 0x7E0 = tbl2 P1 2 := (K22.pt (by decide) (by decide)).trans p21_7e0
  have p22_840 : ptF n22.mem B 0x840 = tbl2 P1 3 := (K22.pt (by decide) (by decide)).trans p21_840
  have p22_8a0 : ptF n22.mem B 0x8A0 = tbl2 P1 4 := (K22.pt (by decide) (by decide)).trans p21_8a0
  have p22_900 : ptF n22.mem B 0x900 = tbl2 P1 5 := (K22.pt (by decide) (by decide)).trans p21_900
  have p22_960 : ptF n22.mem B 0x960 = tbl2 P1 6 := (K22.pt (by decide) (by decide)).trans p21_960
  have p22_9c0 : ptF n22.mem B 0x9C0 = tbl2 P1 7 := (K22.pt (by decide) (by decide)).trans p21_9c0
  have p22_a20 : ptF n22.mem B 0xA20 = tbl2 P0 0 := (K22.pt (by decide) (by decide)).trans p21_a20
  have p22_a80 : ptF n22.mem B 0xA80 = tbl2 P0 1 := (K22.pt (by decide) (by decide)).trans p21_a80
  have p22_ae0 : ptF n22.mem B 0xAE0 = tbl2 P0 2 := (K22.pt (by decide) (by decide)).trans p21_ae0
  have p22_b40 : ptF n22.mem B 0xB40 = tbl2 P0 3 := (K22.pt (by decide) (by decide)).trans p21_b40
  have p22_ba0 : ptF n22.mem B 0xBA0 = tbl2 P0 4 := (K22.pt (by decide) (by decide)).trans p21_ba0
  have p22_c00 : ptF n22.mem B 0xC00 = tbl2 P0 5 := (K22.pt (by decide) (by decide)).trans p21_c00
  have p22_c60 : ptF n22.mem B 0xC60 = tbl2 P0 6 := (K22.pt (by decide) (by decide)).trans p21_c60
  have p22_cc0 : ptF n22.mem B 0xCC0 = tbl2 P0 7 := (K22.pt (by decide) (by decide)).trans p21_cc0
  have p22_d20 : ptF n22.mem B 0xD20 = tbl2 P1 0 := (K22.pt (by decide) (by decide)).trans p21_d20
  have p22_d80 : ptF n22.mem B 0xD80 = tbl2 P1 1 := (K22.pt (by decide) (by decide)).trans p21_d80
  have p22_de0 : ptF n22.mem B 0xDE0 = tbl2 P1 2 := (K22.pt (by decide) (by decide)).trans p21_de0
  have p22_e40 : ptF n22.mem B 0xE40 = tbl2 P1 3 := (K22.pt (by decide) (by decide)).trans p21_e40
  have p22_ea0 : ptF n22.mem B 0xEA0 = tbl2 P1 4 := (K22.pt (by decide) (by decide)).trans p21_ea0
  have p22_f00 : ptF n22.mem B 0xF00 = tbl2 P1 5 := (K22.pt (by decide) (by decide)).trans p21_f00
  have p22_f60 : ptF n22.mem B 0xF60 = tbl2 P1 6 := (K22.pt (by decide) (by decide)).trans p21_f60
  have p22_fc0 : ptF n22.mem B 0xFC0 = tbl2 P1 7 := (K22.pt (by decide) (by decide)).trans p21_fc0
  have p22_1380 : ptF n22.mem B 0x1380 = P0 := (K22.pt (by decide) (by decide)).trans p21_1380
  have p22_1400 : ptF n22.mem B 0x1400 = P1 := (K22.pt (by decide) (by decide)).trans p21_1400
  have mb22_1024 : memBytes n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [K22.mb (by decide) (by decide)]; exact mb21_1024
  have mb22_1320 : leN (memBytes n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U1 := by rw [K22.mb (by decide) (by decide)]; exact mb21_1320
  have mb22_1480 : memBytes n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 0x101 = List.replicate 0x101 0 := by rw [K22.mb (by decide) (by decide)]; exact mb21_1480
  clear mb21_1024 g21_10 mb21_1480 mb21_1320 p21_1400 p21_1380 p21_fc0 p21_f60 p21_f00 p21_ea0 p21_e40 p21_de0 p21_d80 p21_d20 p21_cc0 p21_c60 p21_c00 p21_ba0 p21_b40 p21_ae0 p21_a80 p21_a20 p21_9c0 p21_960 p21_900 p21_8a0 p21_840 p21_7e0 p21_780 p21_720 p21_6c0 p21_660 p21_600 p21_5a0 p21_540 p21_4e0 p21_480 p21_420 p21_3a0 p21_320 a21_1588 a21_1460 a21_13e0 a21_400 a21_380 a21_2e0 a21_2c0 a21_2a0 w21_130 w21_12c w21_128 w21_124 w21_120 w21_11c w21_118 w21_114 w21_110 w21_10c w21_108 w21_104 w21_100 w21_fc w21_f8 w21_f4 w21_f0 w21_ec w21_e8 w21_e4 w21_e0 w21_dc w21_d8 w21_d4 w21_d0 w21_cc w21_c8 w21_c4 w21_c0 w21_bc w21_b8 w21_b4 w21_b0 w21_ac w21_a8 w21_a4 w21_a0 w21_9c w21_98 w21_94 w21_90 w21_8c w21_88 w21_84 w21_80 w21_7c w21_78 w21_70 w21_6c w21_68 w21_64 w21_60 w21_5c w21_58 w21_54 w21_50 w21_4c w21_48 w21_44 w21_40 w21_3c w21_38 w21_34 w21_30 w21_2c w21_28 w21_24 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_9 g21_8 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 s21 H21 D21 A21 K21 P21
  -- 0x1898
  obtain ⟨n23, c23, u23⟩ := s22.block svEcW1898 E22.self svEcW1898_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m23 : n23.mem = n22.mem := u23.mem
  have s23 : St n23.mem SV n23 0x18AC (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
  have rb23 : ∀ q, reg n23 q = (runBlock svEcW1898 (n22.mem, reg n22)).2 q := fun q => by rw [u23.regs]
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
  have g23_8 : reg n23 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb23, runBlock_reg _ _ _ (8 : Fin 32) s22.zero (by decide), g22_8]
  have g23_9 : reg n23 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1400 := by
    rw [rb23, runBlock_reg _ _ _ (9 : Fin 32) s22.zero (by decide), g22_9]
  have g23_18 : reg n23 (18 : Fin 32) = out := by
    rw [rb23, runBlock_reg _ _ _ (18 : Fin 32) s22.zero (by decide), g22_18]
  have g23_19 : reg n23 (19 : Fin 32) = bp := by
    rw [rb23, runBlock_reg _ _ _ (19 : Fin 32) s22.zero (by decide), g22_19]
  have g23_20 : reg n23 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb23, runBlock_reg _ _ _ (20 : Fin 32) s22.zero (by decide), g22_20]
  have g23_21 : reg n23 (21 : Fin 32) = s5v := by
    rw [rb23, runBlock_reg _ _ _ (21 : Fin 32) s22.zero (by decide), g22_21]
  have g23_22 : reg n23 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by
    rw [rb23, runBlock_reg _ _ _ (22 : Fin 32) s22.zero (by decide), g22_22]
  have g23_23 : reg n23 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by
    rw [rb23, runBlock_reg _ _ _ (23 : Fin 32) s22.zero (by decide), g22_23]
  have g23_24 : reg n23 (24 : Fin 32) = s8v := by
    rw [rb23, runBlock_reg _ _ _ (24 : Fin 32) s22.zero (by decide), g22_24]
  have g23_25 : reg n23 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb23, runBlock_reg _ _ _ (25 : Fin 32) s22.zero (by decide), g22_25]
  have g23_26 : reg n23 (26 : Fin 32) = x26 := by
    rw [rb23, runBlock_reg _ _ _ (26 : Fin 32) s22.zero (by decide), g22_26]
  have g23_27 : reg n23 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb23, runBlock_reg _ _ _ (27 : Fin 32) s22.zero (by decide), g22_27]
  have g23_10 : reg n23 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by
    rw [rb23]; simp +decide only [runBlock, BInstr.run, svEcW1898, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g22_2, g22_3, g22_4, g22_8, g22_9, g22_10, g22_18, g22_19, g22_20, g22_21, g22_22, g22_23, g22_24, g22_25, g22_26, g22_27, s22.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g23_11 : reg n23 a1 = B + 0x21A0 + BitVec.ofNat 32 0x1020 := by
    rw [rb23]; simp +decide only [runBlock, BInstr.run, svEcW1898, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g22_2, g22_3, g22_4, g22_8, g22_9, g22_10, g22_18, g22_19, g22_20, g22_21, g22_22, g22_23, g22_24, g22_25, g22_26, g22_27, s22.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g23_12 : reg n23 a2 = BitVec.ofNat 32 0x108 := by
    rw [rb23]; simp +decide only [runBlock, BInstr.run, svEcW1898, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g22_2, g22_3, g22_4, g22_8, g22_9, g22_10, g22_18, g22_19, g22_20, g22_21, g22_22, g22_23, g22_24, g22_25, g22_26, g22_27, s22.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
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
  have w23_1020 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m23]; exact w22_1020
  have a23_2a0 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m23]; exact a22_2a0
  have a23_2c0 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m23]; exact a22_2c0
  have a23_2e0 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m23]; exact a22_2e0
  have a23_380 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m23]; exact a22_380
  have a23_400 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m23]; exact a22_400
  have a23_13e0 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := by rw [m23]; exact a22_13e0
  have a23_1460 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := by rw [m23]; exact a22_1460
  have a23_1588 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U1 := by rw [m23]; exact a22_1588
  have p23_320 : ptF n23.mem B 0x320 = P0 := by rw [m23]; exact p22_320
  have p23_3a0 : ptF n23.mem B 0x3A0 = P1 := by rw [m23]; exact p22_3a0
  have p23_420 : ptF n23.mem B 0x420 = tbl2 P0 0 := by rw [m23]; exact p22_420
  have p23_480 : ptF n23.mem B 0x480 = tbl2 P0 1 := by rw [m23]; exact p22_480
  have p23_4e0 : ptF n23.mem B 0x4E0 = tbl2 P0 2 := by rw [m23]; exact p22_4e0
  have p23_540 : ptF n23.mem B 0x540 = tbl2 P0 3 := by rw [m23]; exact p22_540
  have p23_5a0 : ptF n23.mem B 0x5A0 = tbl2 P0 4 := by rw [m23]; exact p22_5a0
  have p23_600 : ptF n23.mem B 0x600 = tbl2 P0 5 := by rw [m23]; exact p22_600
  have p23_660 : ptF n23.mem B 0x660 = tbl2 P0 6 := by rw [m23]; exact p22_660
  have p23_6c0 : ptF n23.mem B 0x6C0 = tbl2 P0 7 := by rw [m23]; exact p22_6c0
  have p23_720 : ptF n23.mem B 0x720 = tbl2 P1 0 := by rw [m23]; exact p22_720
  have p23_780 : ptF n23.mem B 0x780 = tbl2 P1 1 := by rw [m23]; exact p22_780
  have p23_7e0 : ptF n23.mem B 0x7E0 = tbl2 P1 2 := by rw [m23]; exact p22_7e0
  have p23_840 : ptF n23.mem B 0x840 = tbl2 P1 3 := by rw [m23]; exact p22_840
  have p23_8a0 : ptF n23.mem B 0x8A0 = tbl2 P1 4 := by rw [m23]; exact p22_8a0
  have p23_900 : ptF n23.mem B 0x900 = tbl2 P1 5 := by rw [m23]; exact p22_900
  have p23_960 : ptF n23.mem B 0x960 = tbl2 P1 6 := by rw [m23]; exact p22_960
  have p23_9c0 : ptF n23.mem B 0x9C0 = tbl2 P1 7 := by rw [m23]; exact p22_9c0
  have p23_a20 : ptF n23.mem B 0xA20 = tbl2 P0 0 := by rw [m23]; exact p22_a20
  have p23_a80 : ptF n23.mem B 0xA80 = tbl2 P0 1 := by rw [m23]; exact p22_a80
  have p23_ae0 : ptF n23.mem B 0xAE0 = tbl2 P0 2 := by rw [m23]; exact p22_ae0
  have p23_b40 : ptF n23.mem B 0xB40 = tbl2 P0 3 := by rw [m23]; exact p22_b40
  have p23_ba0 : ptF n23.mem B 0xBA0 = tbl2 P0 4 := by rw [m23]; exact p22_ba0
  have p23_c00 : ptF n23.mem B 0xC00 = tbl2 P0 5 := by rw [m23]; exact p22_c00
  have p23_c60 : ptF n23.mem B 0xC60 = tbl2 P0 6 := by rw [m23]; exact p22_c60
  have p23_cc0 : ptF n23.mem B 0xCC0 = tbl2 P0 7 := by rw [m23]; exact p22_cc0
  have p23_d20 : ptF n23.mem B 0xD20 = tbl2 P1 0 := by rw [m23]; exact p22_d20
  have p23_d80 : ptF n23.mem B 0xD80 = tbl2 P1 1 := by rw [m23]; exact p22_d80
  have p23_de0 : ptF n23.mem B 0xDE0 = tbl2 P1 2 := by rw [m23]; exact p22_de0
  have p23_e40 : ptF n23.mem B 0xE40 = tbl2 P1 3 := by rw [m23]; exact p22_e40
  have p23_ea0 : ptF n23.mem B 0xEA0 = tbl2 P1 4 := by rw [m23]; exact p22_ea0
  have p23_f00 : ptF n23.mem B 0xF00 = tbl2 P1 5 := by rw [m23]; exact p22_f00
  have p23_f60 : ptF n23.mem B 0xF60 = tbl2 P1 6 := by rw [m23]; exact p22_f60
  have p23_fc0 : ptF n23.mem B 0xFC0 = tbl2 P1 7 := by rw [m23]; exact p22_fc0
  have p23_1380 : ptF n23.mem B 0x1380 = P0 := by rw [m23]; exact p22_1380
  have p23_1400 : ptF n23.mem B 0x1400 = P1 := by rw [m23]; exact p22_1400
  have mb23_1024 : memBytes n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m23]; exact mb22_1024
  have mb23_1320 : leN (memBytes n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U1 := by rw [m23]; exact mb22_1320
  have mb23_1480 : memBytes n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 0x101 = List.replicate 0x101 0 := by rw [m23]; exact mb22_1480
  clear mb22_1480 mb22_1320 mb22_1024 p22_1400 p22_1380 p22_fc0 p22_f60 p22_f00 p22_ea0 p22_e40 p22_de0 p22_d80 p22_d20 p22_cc0 p22_c60 p22_c00 p22_ba0 p22_b40 p22_ae0 p22_a80 p22_a20 p22_9c0 p22_960 p22_900 p22_8a0 p22_840 p22_7e0 p22_780 p22_720 p22_6c0 p22_660 p22_600 p22_5a0 p22_540 p22_4e0 p22_480 p22_420 p22_3a0 p22_320 a22_1588 a22_1460 a22_13e0 a22_400 a22_380 a22_2e0 a22_2c0 a22_2a0 w22_1020 w22_130 w22_12c w22_128 w22_124 w22_120 w22_11c w22_118 w22_114 w22_110 w22_10c w22_108 w22_104 w22_100 w22_fc w22_f8 w22_f4 w22_f0 w22_ec w22_e8 w22_e4 w22_e0 w22_dc w22_d8 w22_d4 w22_d0 w22_cc w22_c8 w22_c4 w22_c0 w22_bc w22_b8 w22_b4 w22_b0 w22_ac w22_a8 w22_a4 w22_a0 w22_9c w22_98 w22_94 w22_90 w22_8c w22_88 w22_84 w22_80 w22_7c w22_78 w22_70 w22_6c w22_68 w22_64 w22_60 w22_5c w22_58 w22_54 w22_50 w22_4c w22_48 w22_44 w22_40 w22_3c w22_38 w22_34 w22_30 w22_2c w22_28 w22_24 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_10 g22_9 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 rg22 W22 K22 fr22 s22 d22
  -- 0x18AC: memcpy
  obtain ⟨n24, P24, K24, X24⟩ := sv_mc (c := 0x1480) (d := 0x1020) (N := 0x108) F E23 s23 sv_at_18ac sv_at_18b0
    (by decide) (by decide) g23_2 g23_10 g23_11 g23_12
    (by decide) (by decide) (by decide)
  have s24 := P24.st
  have fr24 := P24.fr
  have t24 : Steps n0 n24 := t23.trans P24.steps
  have fR24 : ∀ x, SvR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
  have E24 : SvCode n24.mem := E23.fr F fr24
  have V24 : SvSaves B n24.mem v := V23.keep K24 (by decide)
  have g24_2 : reg n24 sp = B + 0x21A0 := by rw [P24.regs sp (by decide), g23_2]
  have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P24.regs (3 : Fin 32) (by decide), g23_3]
  have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P24.regs (4 : Fin 32) (by decide), g23_4]
  have g24_8 : reg n24 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [P24.regs (8 : Fin 32) (by decide), g23_8]
  have g24_9 : reg n24 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1400 := by rw [P24.regs (9 : Fin 32) (by decide), g23_9]
  have g24_18 : reg n24 (18 : Fin 32) = out := by rw [P24.regs (18 : Fin 32) (by decide), g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = bp := by rw [P24.regs (19 : Fin 32) (by decide), g23_19]
  have g24_20 : reg n24 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P24.regs (20 : Fin 32) (by decide), g23_20]
  have g24_21 : reg n24 (21 : Fin 32) = s5v := by rw [P24.regs (21 : Fin 32) (by decide), g23_21]
  have g24_22 : reg n24 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [P24.regs (22 : Fin 32) (by decide), g23_22]
  have g24_23 : reg n24 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by rw [P24.regs (23 : Fin 32) (by decide), g23_23]
  have g24_24 : reg n24 (24 : Fin 32) = s8v := by rw [P24.regs (24 : Fin 32) (by decide), g23_24]
  have g24_25 : reg n24 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P24.regs (25 : Fin 32) (by decide), g23_25]
  have g24_26 : reg n24 (26 : Fin 32) = x26 := by rw [P24.regs (26 : Fin 32) (by decide), g23_26]
  have g24_27 : reg n24 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P24.regs (27 : Fin 32) (by decide), g23_27]
  have w24_24 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K24.w32 (by decide) (by decide)).trans w23_24
  have w24_28 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K24.w32 (by decide) (by decide)).trans w23_28
  have w24_2c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K24.w32 (by decide) (by decide)).trans w23_2c
  have w24_30 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K24.w32 (by decide) (by decide)).trans w23_30
  have w24_34 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K24.w32 (by decide) (by decide)).trans w23_34
  have w24_38 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K24.w32 (by decide) (by decide)).trans w23_38
  have w24_3c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K24.w32 (by decide) (by decide)).trans w23_3c
  have w24_40 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K24.w32 (by decide) (by decide)).trans w23_40
  have w24_44 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K24.w32 (by decide) (by decide)).trans w23_44
  have w24_48 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K24.w32 (by decide) (by decide)).trans w23_48
  have w24_4c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K24.w32 (by decide) (by decide)).trans w23_4c
  have w24_50 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K24.w32 (by decide) (by decide)).trans w23_50
  have w24_54 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K24.w32 (by decide) (by decide)).trans w23_54
  have w24_58 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K24.w32 (by decide) (by decide)).trans w23_58
  have w24_5c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K24.w32 (by decide) (by decide)).trans w23_5c
  have w24_60 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K24.w32 (by decide) (by decide)).trans w23_60
  have w24_64 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K24.w32 (by decide) (by decide)).trans w23_64
  have w24_68 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K24.w32 (by decide) (by decide)).trans w23_68
  have w24_6c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K24.w32 (by decide) (by decide)).trans w23_6c
  have w24_70 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K24.w32 (by decide) (by decide)).trans w23_70
  have w24_78 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := (K24.w32 (by decide) (by decide)).trans w23_78
  have w24_7c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K24.w32 (by decide) (by decide)).trans w23_7c
  have w24_80 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K24.w32 (by decide) (by decide)).trans w23_80
  have w24_84 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K24.w32 (by decide) (by decide)).trans w23_84
  have w24_88 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K24.w32 (by decide) (by decide)).trans w23_88
  have w24_8c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K24.w32 (by decide) (by decide)).trans w23_8c
  have w24_90 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K24.w32 (by decide) (by decide)).trans w23_90
  have w24_94 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K24.w32 (by decide) (by decide)).trans w23_94
  have w24_98 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K24.w32 (by decide) (by decide)).trans w23_98
  have w24_9c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K24.w32 (by decide) (by decide)).trans w23_9c
  have w24_a0 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K24.w32 (by decide) (by decide)).trans w23_a0
  have w24_a4 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K24.w32 (by decide) (by decide)).trans w23_a4
  have w24_a8 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K24.w32 (by decide) (by decide)).trans w23_a8
  have w24_ac : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K24.w32 (by decide) (by decide)).trans w23_ac
  have w24_b0 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K24.w32 (by decide) (by decide)).trans w23_b0
  have w24_b4 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K24.w32 (by decide) (by decide)).trans w23_b4
  have w24_b8 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K24.w32 (by decide) (by decide)).trans w23_b8
  have w24_bc : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K24.w32 (by decide) (by decide)).trans w23_bc
  have w24_c0 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K24.w32 (by decide) (by decide)).trans w23_c0
  have w24_c4 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K24.w32 (by decide) (by decide)).trans w23_c4
  have w24_c8 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K24.w32 (by decide) (by decide)).trans w23_c8
  have w24_cc : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K24.w32 (by decide) (by decide)).trans w23_cc
  have w24_d0 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K24.w32 (by decide) (by decide)).trans w23_d0
  have w24_d4 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K24.w32 (by decide) (by decide)).trans w23_d4
  have w24_d8 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K24.w32 (by decide) (by decide)).trans w23_d8
  have w24_dc : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K24.w32 (by decide) (by decide)).trans w23_dc
  have w24_e0 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K24.w32 (by decide) (by decide)).trans w23_e0
  have w24_e4 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K24.w32 (by decide) (by decide)).trans w23_e4
  have w24_e8 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K24.w32 (by decide) (by decide)).trans w23_e8
  have w24_ec : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K24.w32 (by decide) (by decide)).trans w23_ec
  have w24_f0 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K24.w32 (by decide) (by decide)).trans w23_f0
  have w24_f4 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K24.w32 (by decide) (by decide)).trans w23_f4
  have w24_f8 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K24.w32 (by decide) (by decide)).trans w23_f8
  have w24_fc : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K24.w32 (by decide) (by decide)).trans w23_fc
  have w24_100 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K24.w32 (by decide) (by decide)).trans w23_100
  have w24_104 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K24.w32 (by decide) (by decide)).trans w23_104
  have w24_108 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K24.w32 (by decide) (by decide)).trans w23_108
  have w24_10c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K24.w32 (by decide) (by decide)).trans w23_10c
  have w24_110 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K24.w32 (by decide) (by decide)).trans w23_110
  have w24_114 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K24.w32 (by decide) (by decide)).trans w23_114
  have w24_118 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K24.w32 (by decide) (by decide)).trans w23_118
  have w24_11c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K24.w32 (by decide) (by decide)).trans w23_11c
  have w24_120 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K24.w32 (by decide) (by decide)).trans w23_120
  have w24_124 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K24.w32 (by decide) (by decide)).trans w23_124
  have w24_128 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K24.w32 (by decide) (by decide)).trans w23_128
  have w24_12c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K24.w32 (by decide) (by decide)).trans w23_12c
  have w24_130 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K24.w32 (by decide) (by decide)).trans w23_130
  have w24_1020 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := (K24.w32 (by decide) (by decide)).trans w23_1020
  have w24_1480 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by
    rw [← w23_1020]
    exact ld_cp fun q hq => by
      have := X24 (0x0 + q) (by omega)
      rwa [show 0x1480 + (0x0 + q) = 0x1480 + q by omega,
        show 0x1020 + (0x0 + q) = 0x1020 + q by omega] at this
  have a24_2a0 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K24.acc (by decide) (by decide)).trans a23_2a0
  have a24_2c0 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K24.acc (by decide) (by decide)).trans a23_2c0
  have a24_2e0 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K24.acc (by decide) (by decide)).trans a23_2e0
  have a24_380 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := (K24.acc (by decide) (by decide)).trans a23_380
  have a24_400 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := (K24.acc (by decide) (by decide)).trans a23_400
  have a24_13e0 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := (K24.acc (by decide) (by decide)).trans a23_13e0
  have a24_1460 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := (K24.acc (by decide) (by decide)).trans a23_1460
  have a24_1588 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U1 := (K24.acc (by decide) (by decide)).trans a23_1588
  have p24_320 : ptF n24.mem B 0x320 = P0 := (K24.pt (by decide) (by decide)).trans p23_320
  have p24_3a0 : ptF n24.mem B 0x3A0 = P1 := (K24.pt (by decide) (by decide)).trans p23_3a0
  have p24_420 : ptF n24.mem B 0x420 = tbl2 P0 0 := (K24.pt (by decide) (by decide)).trans p23_420
  have p24_480 : ptF n24.mem B 0x480 = tbl2 P0 1 := (K24.pt (by decide) (by decide)).trans p23_480
  have p24_4e0 : ptF n24.mem B 0x4E0 = tbl2 P0 2 := (K24.pt (by decide) (by decide)).trans p23_4e0
  have p24_540 : ptF n24.mem B 0x540 = tbl2 P0 3 := (K24.pt (by decide) (by decide)).trans p23_540
  have p24_5a0 : ptF n24.mem B 0x5A0 = tbl2 P0 4 := (K24.pt (by decide) (by decide)).trans p23_5a0
  have p24_600 : ptF n24.mem B 0x600 = tbl2 P0 5 := (K24.pt (by decide) (by decide)).trans p23_600
  have p24_660 : ptF n24.mem B 0x660 = tbl2 P0 6 := (K24.pt (by decide) (by decide)).trans p23_660
  have p24_6c0 : ptF n24.mem B 0x6C0 = tbl2 P0 7 := (K24.pt (by decide) (by decide)).trans p23_6c0
  have p24_720 : ptF n24.mem B 0x720 = tbl2 P1 0 := (K24.pt (by decide) (by decide)).trans p23_720
  have p24_780 : ptF n24.mem B 0x780 = tbl2 P1 1 := (K24.pt (by decide) (by decide)).trans p23_780
  have p24_7e0 : ptF n24.mem B 0x7E0 = tbl2 P1 2 := (K24.pt (by decide) (by decide)).trans p23_7e0
  have p24_840 : ptF n24.mem B 0x840 = tbl2 P1 3 := (K24.pt (by decide) (by decide)).trans p23_840
  have p24_8a0 : ptF n24.mem B 0x8A0 = tbl2 P1 4 := (K24.pt (by decide) (by decide)).trans p23_8a0
  have p24_900 : ptF n24.mem B 0x900 = tbl2 P1 5 := (K24.pt (by decide) (by decide)).trans p23_900
  have p24_960 : ptF n24.mem B 0x960 = tbl2 P1 6 := (K24.pt (by decide) (by decide)).trans p23_960
  have p24_9c0 : ptF n24.mem B 0x9C0 = tbl2 P1 7 := (K24.pt (by decide) (by decide)).trans p23_9c0
  have p24_a20 : ptF n24.mem B 0xA20 = tbl2 P0 0 := (K24.pt (by decide) (by decide)).trans p23_a20
  have p24_a80 : ptF n24.mem B 0xA80 = tbl2 P0 1 := (K24.pt (by decide) (by decide)).trans p23_a80
  have p24_ae0 : ptF n24.mem B 0xAE0 = tbl2 P0 2 := (K24.pt (by decide) (by decide)).trans p23_ae0
  have p24_b40 : ptF n24.mem B 0xB40 = tbl2 P0 3 := (K24.pt (by decide) (by decide)).trans p23_b40
  have p24_ba0 : ptF n24.mem B 0xBA0 = tbl2 P0 4 := (K24.pt (by decide) (by decide)).trans p23_ba0
  have p24_c00 : ptF n24.mem B 0xC00 = tbl2 P0 5 := (K24.pt (by decide) (by decide)).trans p23_c00
  have p24_c60 : ptF n24.mem B 0xC60 = tbl2 P0 6 := (K24.pt (by decide) (by decide)).trans p23_c60
  have p24_cc0 : ptF n24.mem B 0xCC0 = tbl2 P0 7 := (K24.pt (by decide) (by decide)).trans p23_cc0
  have p24_d20 : ptF n24.mem B 0xD20 = tbl2 P1 0 := (K24.pt (by decide) (by decide)).trans p23_d20
  have p24_d80 : ptF n24.mem B 0xD80 = tbl2 P1 1 := (K24.pt (by decide) (by decide)).trans p23_d80
  have p24_de0 : ptF n24.mem B 0xDE0 = tbl2 P1 2 := (K24.pt (by decide) (by decide)).trans p23_de0
  have p24_e40 : ptF n24.mem B 0xE40 = tbl2 P1 3 := (K24.pt (by decide) (by decide)).trans p23_e40
  have p24_ea0 : ptF n24.mem B 0xEA0 = tbl2 P1 4 := (K24.pt (by decide) (by decide)).trans p23_ea0
  have p24_f00 : ptF n24.mem B 0xF00 = tbl2 P1 5 := (K24.pt (by decide) (by decide)).trans p23_f00
  have p24_f60 : ptF n24.mem B 0xF60 = tbl2 P1 6 := (K24.pt (by decide) (by decide)).trans p23_f60
  have p24_fc0 : ptF n24.mem B 0xFC0 = tbl2 P1 7 := (K24.pt (by decide) (by decide)).trans p23_fc0
  have p24_1380 : ptF n24.mem B 0x1380 = P0 := (K24.pt (by decide) (by decide)).trans p23_1380
  have p24_1400 : ptF n24.mem B 0x1400 = P1 := (K24.pt (by decide) (by decide)).trans p23_1400
  have mb24_1024 : memBytes n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [K24.mb (by decide) (by decide)]; exact mb23_1024
  have mb24_1320 : leN (memBytes n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U1 := by rw [K24.mb (by decide) (by decide)]; exact mb23_1320
  have mb24_1484 : memBytes n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by
    rw [memBytes_cp (S := B + 0x21A0) (c := 0x1484) (d := 0x1024) (N := 0x101) fun q hq => by
      rw [show 0x1484 + q = 0x1480 + (0x4 + q) by omega, X24 (0x4 + q) (by omega),
        show 0x1020 + (0x4 + q) = 0x1024 + q by omega]]; exact mb23_1024
  clear mb23_1480 mb23_1320 mb23_1024 p23_1400 p23_1380 p23_fc0 p23_f60 p23_f00 p23_ea0 p23_e40 p23_de0 p23_d80 p23_d20 p23_cc0 p23_c60 p23_c00 p23_ba0 p23_b40 p23_ae0 p23_a80 p23_a20 p23_9c0 p23_960 p23_900 p23_8a0 p23_840 p23_7e0 p23_780 p23_720 p23_6c0 p23_660 p23_600 p23_5a0 p23_540 p23_4e0 p23_480 p23_420 p23_3a0 p23_320 a23_1588 a23_1460 a23_13e0 a23_400 a23_380 a23_2e0 a23_2c0 a23_2a0 w23_1020 w23_130 w23_12c w23_128 w23_124 w23_120 w23_11c w23_118 w23_114 w23_110 w23_10c w23_108 w23_104 w23_100 w23_fc w23_f8 w23_f4 w23_f0 w23_ec w23_e8 w23_e4 w23_e0 w23_dc w23_d8 w23_d4 w23_d0 w23_cc w23_c8 w23_c4 w23_c0 w23_bc w23_b8 w23_b4 w23_b0 w23_ac w23_a8 w23_a4 w23_a0 w23_9c w23_98 w23_94 w23_90 w23_8c w23_88 w23_84 w23_80 w23_7c w23_78 w23_70 w23_6c w23_68 w23_64 w23_60 w23_5c w23_58 w23_54 w23_50 w23_4c w23_48 w23_44 w23_40 w23_3c w23_38 w23_34 w23_30 w23_2c w23_28 w23_24 g23_12 g23_11 g23_10 g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_9 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 rb23 s23 m23 u23 c23
  -- 0x18B4
  obtain ⟨n25, c25, u25⟩ := s24.block svEcW18b4 E24.self svEcW18b4_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m25 : n25.mem = n24.mem := u25.mem
  have s25 : St n25.mem SV n25 0x18C6 (reg n25) := ⟨u25.pc, rfl, fun _ => rfl⟩
  have rb25 : ∀ q, reg n25 q = (runBlock svEcW18b4 (n24.mem, reg n24)).2 q := fun q => by rw [u25.regs]
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
  have g25_8 : reg n25 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb25, runBlock_reg _ _ _ (8 : Fin 32) s24.zero (by decide), g24_8]
  have g25_9 : reg n25 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1400 := by
    rw [rb25, runBlock_reg _ _ _ (9 : Fin 32) s24.zero (by decide), g24_9]
  have g25_18 : reg n25 (18 : Fin 32) = out := by
    rw [rb25, runBlock_reg _ _ _ (18 : Fin 32) s24.zero (by decide), g24_18]
  have g25_19 : reg n25 (19 : Fin 32) = bp := by
    rw [rb25, runBlock_reg _ _ _ (19 : Fin 32) s24.zero (by decide), g24_19]
  have g25_20 : reg n25 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb25, runBlock_reg _ _ _ (20 : Fin 32) s24.zero (by decide), g24_20]
  have g25_21 : reg n25 (21 : Fin 32) = s5v := by
    rw [rb25, runBlock_reg _ _ _ (21 : Fin 32) s24.zero (by decide), g24_21]
  have g25_22 : reg n25 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by
    rw [rb25, runBlock_reg _ _ _ (22 : Fin 32) s24.zero (by decide), g24_22]
  have g25_23 : reg n25 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by
    rw [rb25, runBlock_reg _ _ _ (23 : Fin 32) s24.zero (by decide), g24_23]
  have g25_24 : reg n25 (24 : Fin 32) = s8v := by
    rw [rb25, runBlock_reg _ _ _ (24 : Fin 32) s24.zero (by decide), g24_24]
  have g25_25 : reg n25 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb25, runBlock_reg _ _ _ (25 : Fin 32) s24.zero (by decide), g24_25]
  have g25_26 : reg n25 (26 : Fin 32) = x26 := by
    rw [rb25, runBlock_reg _ _ _ (26 : Fin 32) s24.zero (by decide), g24_26]
  have g25_27 : reg n25 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb25, runBlock_reg _ _ _ (27 : Fin 32) s24.zero (by decide), g24_27]
  have g25_10 : reg n25 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb25]; simp +decide only [runBlock, BInstr.run, svEcW18b4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_9, g24_18, g24_19, g24_20, g24_21, g24_22, g24_23, g24_24, g24_25, g24_26, g24_27, s24.zero])
    all_goals (try simp only [BitVec.reduceMul, BitVec.zero_add])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g25_11 : reg n25 a1 = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by
    rw [rb25]; simp +decide only [runBlock, BInstr.run, svEcW18b4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_9, g24_18, g24_19, g24_20, g24_21, g24_22, g24_23, g24_24, g24_25, g24_26, g24_27, s24.zero])
    all_goals (try simp only [BitVec.reduceMul, BitVec.zero_add])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g25_12 : reg n25 a2 = BitVec.ofNat 32 0x108 := by
    rw [rb25]; simp +decide only [runBlock, BInstr.run, svEcW18b4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_9, g24_18, g24_19, g24_20, g24_21, g24_22, g24_23, g24_24, g24_25, g24_26, g24_27, s24.zero])
    all_goals (try simp only [BitVec.reduceMul, BitVec.zero_add])
    all_goals first | with_reducible rfl | sv_addr | decide
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
  have w25_1020 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m25]; exact w24_1020
  have w25_1480 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m25]; exact w24_1480
  have a25_2a0 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m25]; exact a24_2a0
  have a25_2c0 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m25]; exact a24_2c0
  have a25_2e0 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m25]; exact a24_2e0
  have a25_380 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m25]; exact a24_380
  have a25_400 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m25]; exact a24_400
  have a25_13e0 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := by rw [m25]; exact a24_13e0
  have a25_1460 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := by rw [m25]; exact a24_1460
  have a25_1588 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U1 := by rw [m25]; exact a24_1588
  have p25_320 : ptF n25.mem B 0x320 = P0 := by rw [m25]; exact p24_320
  have p25_3a0 : ptF n25.mem B 0x3A0 = P1 := by rw [m25]; exact p24_3a0
  have p25_420 : ptF n25.mem B 0x420 = tbl2 P0 0 := by rw [m25]; exact p24_420
  have p25_480 : ptF n25.mem B 0x480 = tbl2 P0 1 := by rw [m25]; exact p24_480
  have p25_4e0 : ptF n25.mem B 0x4E0 = tbl2 P0 2 := by rw [m25]; exact p24_4e0
  have p25_540 : ptF n25.mem B 0x540 = tbl2 P0 3 := by rw [m25]; exact p24_540
  have p25_5a0 : ptF n25.mem B 0x5A0 = tbl2 P0 4 := by rw [m25]; exact p24_5a0
  have p25_600 : ptF n25.mem B 0x600 = tbl2 P0 5 := by rw [m25]; exact p24_600
  have p25_660 : ptF n25.mem B 0x660 = tbl2 P0 6 := by rw [m25]; exact p24_660
  have p25_6c0 : ptF n25.mem B 0x6C0 = tbl2 P0 7 := by rw [m25]; exact p24_6c0
  have p25_720 : ptF n25.mem B 0x720 = tbl2 P1 0 := by rw [m25]; exact p24_720
  have p25_780 : ptF n25.mem B 0x780 = tbl2 P1 1 := by rw [m25]; exact p24_780
  have p25_7e0 : ptF n25.mem B 0x7E0 = tbl2 P1 2 := by rw [m25]; exact p24_7e0
  have p25_840 : ptF n25.mem B 0x840 = tbl2 P1 3 := by rw [m25]; exact p24_840
  have p25_8a0 : ptF n25.mem B 0x8A0 = tbl2 P1 4 := by rw [m25]; exact p24_8a0
  have p25_900 : ptF n25.mem B 0x900 = tbl2 P1 5 := by rw [m25]; exact p24_900
  have p25_960 : ptF n25.mem B 0x960 = tbl2 P1 6 := by rw [m25]; exact p24_960
  have p25_9c0 : ptF n25.mem B 0x9C0 = tbl2 P1 7 := by rw [m25]; exact p24_9c0
  have p25_a20 : ptF n25.mem B 0xA20 = tbl2 P0 0 := by rw [m25]; exact p24_a20
  have p25_a80 : ptF n25.mem B 0xA80 = tbl2 P0 1 := by rw [m25]; exact p24_a80
  have p25_ae0 : ptF n25.mem B 0xAE0 = tbl2 P0 2 := by rw [m25]; exact p24_ae0
  have p25_b40 : ptF n25.mem B 0xB40 = tbl2 P0 3 := by rw [m25]; exact p24_b40
  have p25_ba0 : ptF n25.mem B 0xBA0 = tbl2 P0 4 := by rw [m25]; exact p24_ba0
  have p25_c00 : ptF n25.mem B 0xC00 = tbl2 P0 5 := by rw [m25]; exact p24_c00
  have p25_c60 : ptF n25.mem B 0xC60 = tbl2 P0 6 := by rw [m25]; exact p24_c60
  have p25_cc0 : ptF n25.mem B 0xCC0 = tbl2 P0 7 := by rw [m25]; exact p24_cc0
  have p25_d20 : ptF n25.mem B 0xD20 = tbl2 P1 0 := by rw [m25]; exact p24_d20
  have p25_d80 : ptF n25.mem B 0xD80 = tbl2 P1 1 := by rw [m25]; exact p24_d80
  have p25_de0 : ptF n25.mem B 0xDE0 = tbl2 P1 2 := by rw [m25]; exact p24_de0
  have p25_e40 : ptF n25.mem B 0xE40 = tbl2 P1 3 := by rw [m25]; exact p24_e40
  have p25_ea0 : ptF n25.mem B 0xEA0 = tbl2 P1 4 := by rw [m25]; exact p24_ea0
  have p25_f00 : ptF n25.mem B 0xF00 = tbl2 P1 5 := by rw [m25]; exact p24_f00
  have p25_f60 : ptF n25.mem B 0xF60 = tbl2 P1 6 := by rw [m25]; exact p24_f60
  have p25_fc0 : ptF n25.mem B 0xFC0 = tbl2 P1 7 := by rw [m25]; exact p24_fc0
  have p25_1380 : ptF n25.mem B 0x1380 = P0 := by rw [m25]; exact p24_1380
  have p25_1400 : ptF n25.mem B 0x1400 = P1 := by rw [m25]; exact p24_1400
  have mb25_1024 : memBytes n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m25]; exact mb24_1024
  have mb25_1320 : leN (memBytes n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U1 := by rw [m25]; exact mb24_1320
  have mb25_1484 : memBytes n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m25]; exact mb24_1484
  clear mb24_1484 mb24_1320 mb24_1024 p24_1400 p24_1380 p24_fc0 p24_f60 p24_f00 p24_ea0 p24_e40 p24_de0 p24_d80 p24_d20 p24_cc0 p24_c60 p24_c00 p24_ba0 p24_b40 p24_ae0 p24_a80 p24_a20 p24_9c0 p24_960 p24_900 p24_8a0 p24_840 p24_7e0 p24_780 p24_720 p24_6c0 p24_660 p24_600 p24_5a0 p24_540 p24_4e0 p24_480 p24_420 p24_3a0 p24_320 a24_1588 a24_1460 a24_13e0 a24_400 a24_380 a24_2e0 a24_2c0 a24_2a0 w24_1480 w24_1020 w24_130 w24_12c w24_128 w24_124 w24_120 w24_11c w24_118 w24_114 w24_110 w24_10c w24_108 w24_104 w24_100 w24_fc w24_f8 w24_f4 w24_f0 w24_ec w24_e8 w24_e4 w24_e0 w24_dc w24_d8 w24_d4 w24_d0 w24_cc w24_c8 w24_c4 w24_c0 w24_bc w24_b8 w24_b4 w24_b0 w24_ac w24_a8 w24_a4 w24_a0 w24_9c w24_98 w24_94 w24_90 w24_8c w24_88 w24_84 w24_80 w24_7c w24_78 w24_70 w24_6c w24_68 w24_64 w24_60 w24_5c w24_58 w24_54 w24_50 w24_4c w24_48 w24_44 w24_40 w24_3c w24_38 w24_34 w24_30 w24_2c w24_28 w24_24 g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 s24 X24 K24 P24
  -- 0x18C6: memcpy
  obtain ⟨n26, P26, K26, X26⟩ := sv_mc (c := 0xA20) (d := 0x1480) (N := 0x108) F E25 s25 sv_at_18c6 sv_at_18ca
    (by decide) (by decide) g25_2 g25_10 g25_11 g25_12
    (by decide) (by decide) (by decide)
  have s26 := P26.st
  have fr26 := P26.fr
  have t26 : Steps n0 n26 := t25.trans P26.steps
  have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
  have E26 : SvCode n26.mem := E25.fr F fr26
  have V26 : SvSaves B n26.mem v := V25.keep K26 (by decide)
  have g26_2 : reg n26 sp = B + 0x21A0 := by rw [P26.regs sp (by decide), g25_2]
  have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P26.regs (3 : Fin 32) (by decide), g25_3]
  have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P26.regs (4 : Fin 32) (by decide), g25_4]
  have g26_8 : reg n26 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [P26.regs (8 : Fin 32) (by decide), g25_8]
  have g26_9 : reg n26 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1400 := by rw [P26.regs (9 : Fin 32) (by decide), g25_9]
  have g26_18 : reg n26 (18 : Fin 32) = out := by rw [P26.regs (18 : Fin 32) (by decide), g25_18]
  have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [P26.regs (19 : Fin 32) (by decide), g25_19]
  have g26_20 : reg n26 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P26.regs (20 : Fin 32) (by decide), g25_20]
  have g26_21 : reg n26 (21 : Fin 32) = s5v := by rw [P26.regs (21 : Fin 32) (by decide), g25_21]
  have g26_22 : reg n26 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [P26.regs (22 : Fin 32) (by decide), g25_22]
  have g26_23 : reg n26 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by rw [P26.regs (23 : Fin 32) (by decide), g25_23]
  have g26_24 : reg n26 (24 : Fin 32) = s8v := by rw [P26.regs (24 : Fin 32) (by decide), g25_24]
  have g26_25 : reg n26 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P26.regs (25 : Fin 32) (by decide), g25_25]
  have g26_26 : reg n26 (26 : Fin 32) = x26 := by rw [P26.regs (26 : Fin 32) (by decide), g25_26]
  have g26_27 : reg n26 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P26.regs (27 : Fin 32) (by decide), g25_27]
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
  have w26_1020 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := (K26.w32 (by decide) (by decide)).trans w25_1020
  have w26_1480 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := (K26.w32 (by decide) (by decide)).trans w25_1480
  have w26_a20 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by
    rw [← w25_1480]
    exact ld_cp fun q hq => by
      have := X26 (0x0 + q) (by omega)
      rwa [show 0xA20 + (0x0 + q) = 0xA20 + q by omega,
        show 0x1480 + (0x0 + q) = 0x1480 + q by omega] at this
  have a26_2a0 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K26.acc (by decide) (by decide)).trans a25_2a0
  have a26_2c0 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K26.acc (by decide) (by decide)).trans a25_2c0
  have a26_2e0 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K26.acc (by decide) (by decide)).trans a25_2e0
  have a26_380 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := (K26.acc (by decide) (by decide)).trans a25_380
  have a26_400 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := (K26.acc (by decide) (by decide)).trans a25_400
  have a26_13e0 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := (K26.acc (by decide) (by decide)).trans a25_13e0
  have a26_1460 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := (K26.acc (by decide) (by decide)).trans a25_1460
  have a26_1588 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U1 := (K26.acc (by decide) (by decide)).trans a25_1588
  have p26_320 : ptF n26.mem B 0x320 = P0 := (K26.pt (by decide) (by decide)).trans p25_320
  have p26_3a0 : ptF n26.mem B 0x3A0 = P1 := (K26.pt (by decide) (by decide)).trans p25_3a0
  have p26_420 : ptF n26.mem B 0x420 = tbl2 P0 0 := (K26.pt (by decide) (by decide)).trans p25_420
  have p26_480 : ptF n26.mem B 0x480 = tbl2 P0 1 := (K26.pt (by decide) (by decide)).trans p25_480
  have p26_4e0 : ptF n26.mem B 0x4E0 = tbl2 P0 2 := (K26.pt (by decide) (by decide)).trans p25_4e0
  have p26_540 : ptF n26.mem B 0x540 = tbl2 P0 3 := (K26.pt (by decide) (by decide)).trans p25_540
  have p26_5a0 : ptF n26.mem B 0x5A0 = tbl2 P0 4 := (K26.pt (by decide) (by decide)).trans p25_5a0
  have p26_600 : ptF n26.mem B 0x600 = tbl2 P0 5 := (K26.pt (by decide) (by decide)).trans p25_600
  have p26_660 : ptF n26.mem B 0x660 = tbl2 P0 6 := (K26.pt (by decide) (by decide)).trans p25_660
  have p26_6c0 : ptF n26.mem B 0x6C0 = tbl2 P0 7 := (K26.pt (by decide) (by decide)).trans p25_6c0
  have p26_720 : ptF n26.mem B 0x720 = tbl2 P1 0 := (K26.pt (by decide) (by decide)).trans p25_720
  have p26_780 : ptF n26.mem B 0x780 = tbl2 P1 1 := (K26.pt (by decide) (by decide)).trans p25_780
  have p26_7e0 : ptF n26.mem B 0x7E0 = tbl2 P1 2 := (K26.pt (by decide) (by decide)).trans p25_7e0
  have p26_840 : ptF n26.mem B 0x840 = tbl2 P1 3 := (K26.pt (by decide) (by decide)).trans p25_840
  have p26_8a0 : ptF n26.mem B 0x8A0 = tbl2 P1 4 := (K26.pt (by decide) (by decide)).trans p25_8a0
  have p26_900 : ptF n26.mem B 0x900 = tbl2 P1 5 := (K26.pt (by decide) (by decide)).trans p25_900
  have p26_960 : ptF n26.mem B 0x960 = tbl2 P1 6 := (K26.pt (by decide) (by decide)).trans p25_960
  have p26_9c0 : ptF n26.mem B 0x9C0 = tbl2 P1 7 := (K26.pt (by decide) (by decide)).trans p25_9c0
  have p26_b40 : ptF n26.mem B 0xB40 = tbl2 P0 3 := (K26.pt (by decide) (by decide)).trans p25_b40
  have p26_ba0 : ptF n26.mem B 0xBA0 = tbl2 P0 4 := (K26.pt (by decide) (by decide)).trans p25_ba0
  have p26_c00 : ptF n26.mem B 0xC00 = tbl2 P0 5 := (K26.pt (by decide) (by decide)).trans p25_c00
  have p26_c60 : ptF n26.mem B 0xC60 = tbl2 P0 6 := (K26.pt (by decide) (by decide)).trans p25_c60
  have p26_cc0 : ptF n26.mem B 0xCC0 = tbl2 P0 7 := (K26.pt (by decide) (by decide)).trans p25_cc0
  have p26_d20 : ptF n26.mem B 0xD20 = tbl2 P1 0 := (K26.pt (by decide) (by decide)).trans p25_d20
  have p26_d80 : ptF n26.mem B 0xD80 = tbl2 P1 1 := (K26.pt (by decide) (by decide)).trans p25_d80
  have p26_de0 : ptF n26.mem B 0xDE0 = tbl2 P1 2 := (K26.pt (by decide) (by decide)).trans p25_de0
  have p26_e40 : ptF n26.mem B 0xE40 = tbl2 P1 3 := (K26.pt (by decide) (by decide)).trans p25_e40
  have p26_ea0 : ptF n26.mem B 0xEA0 = tbl2 P1 4 := (K26.pt (by decide) (by decide)).trans p25_ea0
  have p26_f00 : ptF n26.mem B 0xF00 = tbl2 P1 5 := (K26.pt (by decide) (by decide)).trans p25_f00
  have p26_f60 : ptF n26.mem B 0xF60 = tbl2 P1 6 := (K26.pt (by decide) (by decide)).trans p25_f60
  have p26_fc0 : ptF n26.mem B 0xFC0 = tbl2 P1 7 := (K26.pt (by decide) (by decide)).trans p25_fc0
  have p26_1380 : ptF n26.mem B 0x1380 = P0 := (K26.pt (by decide) (by decide)).trans p25_1380
  have p26_1400 : ptF n26.mem B 0x1400 = P1 := (K26.pt (by decide) (by decide)).trans p25_1400
  have mb26_1024 : memBytes n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [K26.mb (by decide) (by decide)]; exact mb25_1024
  have mb26_1320 : leN (memBytes n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U1 := by rw [K26.mb (by decide) (by decide)]; exact mb25_1320
  have mb26_1484 : memBytes n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [K26.mb (by decide) (by decide)]; exact mb25_1484
  have mb26_a24 : memBytes n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by
    rw [memBytes_cp (S := B + 0x21A0) (c := 0xA24) (d := 0x1484) (N := 0x101) fun q hq => by
      rw [show 0xA24 + q = 0xA20 + (0x4 + q) by omega, X26 (0x4 + q) (by omega),
        show 0x1480 + (0x4 + q) = 0x1484 + q by omega]]; exact mb25_1484
  clear mb25_1484 mb25_1320 mb25_1024 p25_1400 p25_1380 p25_fc0 p25_f60 p25_f00 p25_ea0 p25_e40 p25_de0 p25_d80 p25_d20 p25_cc0 p25_c60 p25_c00 p25_ba0 p25_b40 p25_ae0 p25_a80 p25_a20 p25_9c0 p25_960 p25_900 p25_8a0 p25_840 p25_7e0 p25_780 p25_720 p25_6c0 p25_660 p25_600 p25_5a0 p25_540 p25_4e0 p25_480 p25_420 p25_3a0 p25_320 a25_1588 a25_1460 a25_13e0 a25_400 a25_380 a25_2e0 a25_2c0 a25_2a0 w25_1480 w25_1020 w25_130 w25_12c w25_128 w25_124 w25_120 w25_11c w25_118 w25_114 w25_110 w25_10c w25_108 w25_104 w25_100 w25_fc w25_f8 w25_f4 w25_f0 w25_ec w25_e8 w25_e4 w25_e0 w25_dc w25_d8 w25_d4 w25_d0 w25_cc w25_c8 w25_c4 w25_c0 w25_bc w25_b8 w25_b4 w25_b0 w25_ac w25_a8 w25_a4 w25_a0 w25_9c w25_98 w25_94 w25_90 w25_8c w25_88 w25_84 w25_80 w25_7c w25_78 w25_70 w25_6c w25_68 w25_64 w25_60 w25_5c w25_58 w25_54 w25_50 w25_4c w25_48 w25_44 w25_40 w25_3c w25_38 w25_34 w25_30 w25_2c w25_28 w25_24 g25_12 g25_11 g25_10 g25_27 g25_26 g25_25 g25_24 g25_23 g25_22 g25_21 g25_20 g25_19 g25_18 g25_9 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 fr25 rb25 s25 m25 u25 c25
  -- 0x18CE
  obtain ⟨n27, c27, u27⟩ := s26.block svEcW18ce E26.self svEcW18ce_end
    ⟨trivial, trivial⟩
  have m27 : n27.mem = n26.mem := u27.mem
  have s27 : St n27.mem SV n27 0x18D0 (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
  have rb27 : ∀ q, reg n27 q = (runBlock svEcW18ce (n26.mem, reg n26)).2 q := fun q => by rw [u27.regs]
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
  have g27_9 : reg n27 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1400 := by
    rw [rb27, runBlock_reg _ _ _ (9 : Fin 32) s26.zero (by decide), g26_9]
  have g27_18 : reg n27 (18 : Fin 32) = out := by
    rw [rb27, runBlock_reg _ _ _ (18 : Fin 32) s26.zero (by decide), g26_18]
  have g27_19 : reg n27 (19 : Fin 32) = bp := by
    rw [rb27, runBlock_reg _ _ _ (19 : Fin 32) s26.zero (by decide), g26_19]
  have g27_20 : reg n27 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb27, runBlock_reg _ _ _ (20 : Fin 32) s26.zero (by decide), g26_20]
  have g27_21 : reg n27 (21 : Fin 32) = s5v := by
    rw [rb27, runBlock_reg _ _ _ (21 : Fin 32) s26.zero (by decide), g26_21]
  have g27_22 : reg n27 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by
    rw [rb27, runBlock_reg _ _ _ (22 : Fin 32) s26.zero (by decide), g26_22]
  have g27_23 : reg n27 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by
    rw [rb27, runBlock_reg _ _ _ (23 : Fin 32) s26.zero (by decide), g26_23]
  have g27_24 : reg n27 (24 : Fin 32) = s8v := by
    rw [rb27, runBlock_reg _ _ _ (24 : Fin 32) s26.zero (by decide), g26_24]
  have g27_25 : reg n27 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb27, runBlock_reg _ _ _ (25 : Fin 32) s26.zero (by decide), g26_25]
  have g27_26 : reg n27 (26 : Fin 32) = x26 := by
    rw [rb27, runBlock_reg _ _ _ (26 : Fin 32) s26.zero (by decide), g26_26]
  have g27_27 : reg n27 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb27, runBlock_reg _ _ _ (27 : Fin 32) s26.zero (by decide), g26_27]
  have g27_8 : reg n27 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb27]; simp +decide only [runBlock, BInstr.run, svEcW18ce, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g26_2, g26_3, g26_4, g26_8, g26_9, g26_18, g26_19, g26_20, g26_21, g26_22, g26_23, g26_24, g26_25, g26_26, g26_27, s26.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
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
  have w27_a20 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m27]; exact w26_a20
  have w27_1020 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m27]; exact w26_1020
  have w27_1480 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m27]; exact w26_1480
  have a27_2a0 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m27]; exact a26_2a0
  have a27_2c0 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m27]; exact a26_2c0
  have a27_2e0 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m27]; exact a26_2e0
  have a27_380 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m27]; exact a26_380
  have a27_400 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m27]; exact a26_400
  have a27_13e0 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := by rw [m27]; exact a26_13e0
  have a27_1460 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := by rw [m27]; exact a26_1460
  have a27_1588 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U1 := by rw [m27]; exact a26_1588
  have p27_320 : ptF n27.mem B 0x320 = P0 := by rw [m27]; exact p26_320
  have p27_3a0 : ptF n27.mem B 0x3A0 = P1 := by rw [m27]; exact p26_3a0
  have p27_420 : ptF n27.mem B 0x420 = tbl2 P0 0 := by rw [m27]; exact p26_420
  have p27_480 : ptF n27.mem B 0x480 = tbl2 P0 1 := by rw [m27]; exact p26_480
  have p27_4e0 : ptF n27.mem B 0x4E0 = tbl2 P0 2 := by rw [m27]; exact p26_4e0
  have p27_540 : ptF n27.mem B 0x540 = tbl2 P0 3 := by rw [m27]; exact p26_540
  have p27_5a0 : ptF n27.mem B 0x5A0 = tbl2 P0 4 := by rw [m27]; exact p26_5a0
  have p27_600 : ptF n27.mem B 0x600 = tbl2 P0 5 := by rw [m27]; exact p26_600
  have p27_660 : ptF n27.mem B 0x660 = tbl2 P0 6 := by rw [m27]; exact p26_660
  have p27_6c0 : ptF n27.mem B 0x6C0 = tbl2 P0 7 := by rw [m27]; exact p26_6c0
  have p27_720 : ptF n27.mem B 0x720 = tbl2 P1 0 := by rw [m27]; exact p26_720
  have p27_780 : ptF n27.mem B 0x780 = tbl2 P1 1 := by rw [m27]; exact p26_780
  have p27_7e0 : ptF n27.mem B 0x7E0 = tbl2 P1 2 := by rw [m27]; exact p26_7e0
  have p27_840 : ptF n27.mem B 0x840 = tbl2 P1 3 := by rw [m27]; exact p26_840
  have p27_8a0 : ptF n27.mem B 0x8A0 = tbl2 P1 4 := by rw [m27]; exact p26_8a0
  have p27_900 : ptF n27.mem B 0x900 = tbl2 P1 5 := by rw [m27]; exact p26_900
  have p27_960 : ptF n27.mem B 0x960 = tbl2 P1 6 := by rw [m27]; exact p26_960
  have p27_9c0 : ptF n27.mem B 0x9C0 = tbl2 P1 7 := by rw [m27]; exact p26_9c0
  have p27_b40 : ptF n27.mem B 0xB40 = tbl2 P0 3 := by rw [m27]; exact p26_b40
  have p27_ba0 : ptF n27.mem B 0xBA0 = tbl2 P0 4 := by rw [m27]; exact p26_ba0
  have p27_c00 : ptF n27.mem B 0xC00 = tbl2 P0 5 := by rw [m27]; exact p26_c00
  have p27_c60 : ptF n27.mem B 0xC60 = tbl2 P0 6 := by rw [m27]; exact p26_c60
  have p27_cc0 : ptF n27.mem B 0xCC0 = tbl2 P0 7 := by rw [m27]; exact p26_cc0
  have p27_d20 : ptF n27.mem B 0xD20 = tbl2 P1 0 := by rw [m27]; exact p26_d20
  have p27_d80 : ptF n27.mem B 0xD80 = tbl2 P1 1 := by rw [m27]; exact p26_d80
  have p27_de0 : ptF n27.mem B 0xDE0 = tbl2 P1 2 := by rw [m27]; exact p26_de0
  have p27_e40 : ptF n27.mem B 0xE40 = tbl2 P1 3 := by rw [m27]; exact p26_e40
  have p27_ea0 : ptF n27.mem B 0xEA0 = tbl2 P1 4 := by rw [m27]; exact p26_ea0
  have p27_f00 : ptF n27.mem B 0xF00 = tbl2 P1 5 := by rw [m27]; exact p26_f00
  have p27_f60 : ptF n27.mem B 0xF60 = tbl2 P1 6 := by rw [m27]; exact p26_f60
  have p27_fc0 : ptF n27.mem B 0xFC0 = tbl2 P1 7 := by rw [m27]; exact p26_fc0
  have p27_1380 : ptF n27.mem B 0x1380 = P0 := by rw [m27]; exact p26_1380
  have p27_1400 : ptF n27.mem B 0x1400 = P1 := by rw [m27]; exact p26_1400
  have mb27_a24 : memBytes n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m27]; exact mb26_a24
  have mb27_1024 : memBytes n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m27]; exact mb26_1024
  have mb27_1320 : leN (memBytes n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U1 := by rw [m27]; exact mb26_1320
  have mb27_1484 : memBytes n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m27]; exact mb26_1484
  clear mb26_a24 mb26_1484 mb26_1320 mb26_1024 p26_1400 p26_1380 p26_fc0 p26_f60 p26_f00 p26_ea0 p26_e40 p26_de0 p26_d80 p26_d20 p26_cc0 p26_c60 p26_c00 p26_ba0 p26_b40 p26_9c0 p26_960 p26_900 p26_8a0 p26_840 p26_7e0 p26_780 p26_720 p26_6c0 p26_660 p26_600 p26_5a0 p26_540 p26_4e0 p26_480 p26_420 p26_3a0 p26_320 a26_1588 a26_1460 a26_13e0 a26_400 a26_380 a26_2e0 a26_2c0 a26_2a0 w26_a20 w26_1480 w26_1020 w26_130 w26_12c w26_128 w26_124 w26_120 w26_11c w26_118 w26_114 w26_110 w26_10c w26_108 w26_104 w26_100 w26_fc w26_f8 w26_f4 w26_f0 w26_ec w26_e8 w26_e4 w26_e0 w26_dc w26_d8 w26_d4 w26_d0 w26_cc w26_c8 w26_c4 w26_c0 w26_bc w26_b8 w26_b4 w26_b0 w26_ac w26_a8 w26_a4 w26_a0 w26_9c w26_98 w26_94 w26_90 w26_8c w26_88 w26_84 w26_80 w26_7c w26_78 w26_70 w26_6c w26_68 w26_64 w26_60 w26_5c w26_58 w26_54 w26_50 w26_4c w26_48 w26_44 w26_40 w26_3c w26_38 w26_34 w26_30 w26_2c w26_28 w26_24 g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 s26 X26 K26 P26
  -- 0x18D0: branch, taken
  obtain ⟨n28, d28, u28⟩ := s27.taken E27.self 0x17E0 sv_at_18d0
    (by decide) (by rw [g27_8, g27_25]; decide)
  have s28 : St n28.mem SV n28 0x17E0 (reg n28) := ⟨u28.pc, rfl, fun _ => rfl⟩
  have m28 : n28.mem = n27.mem := u28.mem
  have fr28 : ∀ x, SvR B x → n28.mem x = n27.mem x := fun x _ => by rw [m28]
  have t28 : Steps n0 n28 := t27.trans (.single d28)
  have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
  have E28 : SvCode n28.mem := E27.fr F fr28
  have V28 : SvSaves B n28.mem v := V27.same m28
  have g28_2 : reg n28 sp = B + 0x21A0 := by rw [u28.regs, g27_2]
  have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u28.regs, g27_3]
  have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u28.regs, g27_4]
  have g28_8 : reg n28 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u28.regs, g27_8]
  have g28_9 : reg n28 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1400 := by rw [u28.regs, g27_9]
  have g28_18 : reg n28 (18 : Fin 32) = out := by rw [u28.regs, g27_18]
  have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [u28.regs, g27_19]
  have g28_20 : reg n28 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u28.regs, g27_20]
  have g28_21 : reg n28 (21 : Fin 32) = s5v := by rw [u28.regs, g27_21]
  have g28_22 : reg n28 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [u28.regs, g27_22]
  have g28_23 : reg n28 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by rw [u28.regs, g27_23]
  have g28_24 : reg n28 (24 : Fin 32) = s8v := by rw [u28.regs, g27_24]
  have g28_25 : reg n28 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u28.regs, g27_25]
  have g28_26 : reg n28 (26 : Fin 32) = x26 := by rw [u28.regs, g27_26]
  have g28_27 : reg n28 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u28.regs, g27_27]
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
  have w28_a20 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m28]; exact w27_a20
  have w28_1020 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m28]; exact w27_1020
  have w28_1480 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m28]; exact w27_1480
  have a28_2a0 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m28]; exact a27_2a0
  have a28_2c0 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m28]; exact a27_2c0
  have a28_2e0 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m28]; exact a27_2e0
  have a28_380 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m28]; exact a27_380
  have a28_400 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m28]; exact a27_400
  have a28_13e0 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := by rw [m28]; exact a27_13e0
  have a28_1460 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := by rw [m28]; exact a27_1460
  have a28_1588 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U1 := by rw [m28]; exact a27_1588
  have p28_320 : ptF n28.mem B 0x320 = P0 := by rw [m28]; exact p27_320
  have p28_3a0 : ptF n28.mem B 0x3A0 = P1 := by rw [m28]; exact p27_3a0
  have p28_420 : ptF n28.mem B 0x420 = tbl2 P0 0 := by rw [m28]; exact p27_420
  have p28_480 : ptF n28.mem B 0x480 = tbl2 P0 1 := by rw [m28]; exact p27_480
  have p28_4e0 : ptF n28.mem B 0x4E0 = tbl2 P0 2 := by rw [m28]; exact p27_4e0
  have p28_540 : ptF n28.mem B 0x540 = tbl2 P0 3 := by rw [m28]; exact p27_540
  have p28_5a0 : ptF n28.mem B 0x5A0 = tbl2 P0 4 := by rw [m28]; exact p27_5a0
  have p28_600 : ptF n28.mem B 0x600 = tbl2 P0 5 := by rw [m28]; exact p27_600
  have p28_660 : ptF n28.mem B 0x660 = tbl2 P0 6 := by rw [m28]; exact p27_660
  have p28_6c0 : ptF n28.mem B 0x6C0 = tbl2 P0 7 := by rw [m28]; exact p27_6c0
  have p28_720 : ptF n28.mem B 0x720 = tbl2 P1 0 := by rw [m28]; exact p27_720
  have p28_780 : ptF n28.mem B 0x780 = tbl2 P1 1 := by rw [m28]; exact p27_780
  have p28_7e0 : ptF n28.mem B 0x7E0 = tbl2 P1 2 := by rw [m28]; exact p27_7e0
  have p28_840 : ptF n28.mem B 0x840 = tbl2 P1 3 := by rw [m28]; exact p27_840
  have p28_8a0 : ptF n28.mem B 0x8A0 = tbl2 P1 4 := by rw [m28]; exact p27_8a0
  have p28_900 : ptF n28.mem B 0x900 = tbl2 P1 5 := by rw [m28]; exact p27_900
  have p28_960 : ptF n28.mem B 0x960 = tbl2 P1 6 := by rw [m28]; exact p27_960
  have p28_9c0 : ptF n28.mem B 0x9C0 = tbl2 P1 7 := by rw [m28]; exact p27_9c0
  have p28_b40 : ptF n28.mem B 0xB40 = tbl2 P0 3 := by rw [m28]; exact p27_b40
  have p28_ba0 : ptF n28.mem B 0xBA0 = tbl2 P0 4 := by rw [m28]; exact p27_ba0
  have p28_c00 : ptF n28.mem B 0xC00 = tbl2 P0 5 := by rw [m28]; exact p27_c00
  have p28_c60 : ptF n28.mem B 0xC60 = tbl2 P0 6 := by rw [m28]; exact p27_c60
  have p28_cc0 : ptF n28.mem B 0xCC0 = tbl2 P0 7 := by rw [m28]; exact p27_cc0
  have p28_d20 : ptF n28.mem B 0xD20 = tbl2 P1 0 := by rw [m28]; exact p27_d20
  have p28_d80 : ptF n28.mem B 0xD80 = tbl2 P1 1 := by rw [m28]; exact p27_d80
  have p28_de0 : ptF n28.mem B 0xDE0 = tbl2 P1 2 := by rw [m28]; exact p27_de0
  have p28_e40 : ptF n28.mem B 0xE40 = tbl2 P1 3 := by rw [m28]; exact p27_e40
  have p28_ea0 : ptF n28.mem B 0xEA0 = tbl2 P1 4 := by rw [m28]; exact p27_ea0
  have p28_f00 : ptF n28.mem B 0xF00 = tbl2 P1 5 := by rw [m28]; exact p27_f00
  have p28_f60 : ptF n28.mem B 0xF60 = tbl2 P1 6 := by rw [m28]; exact p27_f60
  have p28_fc0 : ptF n28.mem B 0xFC0 = tbl2 P1 7 := by rw [m28]; exact p27_fc0
  have p28_1380 : ptF n28.mem B 0x1380 = P0 := by rw [m28]; exact p27_1380
  have p28_1400 : ptF n28.mem B 0x1400 = P1 := by rw [m28]; exact p27_1400
  have mb28_a24 : memBytes n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m28]; exact mb27_a24
  have mb28_1024 : memBytes n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m28]; exact mb27_1024
  have mb28_1320 : leN (memBytes n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U1 := by rw [m28]; exact mb27_1320
  have mb28_1484 : memBytes n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m28]; exact mb27_1484
  clear mb27_1484 mb27_1320 mb27_1024 mb27_a24 p27_1400 p27_1380 p27_fc0 p27_f60 p27_f00 p27_ea0 p27_e40 p27_de0 p27_d80 p27_d20 p27_cc0 p27_c60 p27_c00 p27_ba0 p27_b40 p27_9c0 p27_960 p27_900 p27_8a0 p27_840 p27_7e0 p27_780 p27_720 p27_6c0 p27_660 p27_600 p27_5a0 p27_540 p27_4e0 p27_480 p27_420 p27_3a0 p27_320 a27_1588 a27_1460 a27_13e0 a27_400 a27_380 a27_2e0 a27_2c0 a27_2a0 w27_1480 w27_1020 w27_a20 w27_130 w27_12c w27_128 w27_124 w27_120 w27_11c w27_118 w27_114 w27_110 w27_10c w27_108 w27_104 w27_100 w27_fc w27_f8 w27_f4 w27_f0 w27_ec w27_e8 w27_e4 w27_e0 w27_dc w27_d8 w27_d4 w27_d0 w27_cc w27_c8 w27_c4 w27_c0 w27_bc w27_b8 w27_b4 w27_b0 w27_ac w27_a8 w27_a4 w27_a0 w27_9c w27_98 w27_94 w27_90 w27_8c w27_88 w27_84 w27_80 w27_7c w27_78 w27_70 w27_6c w27_68 w27_64 w27_60 w27_5c w27_58 w27_54 w27_50 w27_4c w27_48 w27_44 w27_40 w27_3c w27_38 w27_34 w27_30 w27_2c w27_28 w27_24 g27_8 g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_9 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 rb27 s27 m27 u27 c27
  -- 0x17E0
  obtain ⟨n29, c29, u29⟩ := s28.block svEcW17e0 E28.self svEcW17e0_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m29 : n29.mem = n28.mem := u29.mem
  have s29 : St n29.mem SV n29 0x17F0 (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
  have rb29 : ∀ q, reg n29 q = (runBlock svEcW17e0 (n28.mem, reg n28)).2 q := fun q => by rw [u29.regs]
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
  have g29_8 : reg n29 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb29, runBlock_reg _ _ _ (8 : Fin 32) s28.zero (by decide), g28_8]
  have g29_9 : reg n29 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1400 := by
    rw [rb29, runBlock_reg _ _ _ (9 : Fin 32) s28.zero (by decide), g28_9]
  have g29_18 : reg n29 (18 : Fin 32) = out := by
    rw [rb29, runBlock_reg _ _ _ (18 : Fin 32) s28.zero (by decide), g28_18]
  have g29_19 : reg n29 (19 : Fin 32) = bp := by
    rw [rb29, runBlock_reg _ _ _ (19 : Fin 32) s28.zero (by decide), g28_19]
  have g29_20 : reg n29 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb29, runBlock_reg _ _ _ (20 : Fin 32) s28.zero (by decide), g28_20]
  have g29_21 : reg n29 (21 : Fin 32) = s5v := by
    rw [rb29, runBlock_reg _ _ _ (21 : Fin 32) s28.zero (by decide), g28_21]
  have g29_22 : reg n29 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by
    rw [rb29, runBlock_reg _ _ _ (22 : Fin 32) s28.zero (by decide), g28_22]
  have g29_23 : reg n29 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by
    rw [rb29, runBlock_reg _ _ _ (23 : Fin 32) s28.zero (by decide), g28_23]
  have g29_24 : reg n29 (24 : Fin 32) = s8v := by
    rw [rb29, runBlock_reg _ _ _ (24 : Fin 32) s28.zero (by decide), g28_24]
  have g29_25 : reg n29 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb29, runBlock_reg _ _ _ (25 : Fin 32) s28.zero (by decide), g28_25]
  have g29_26 : reg n29 (26 : Fin 32) = x26 := by
    rw [rb29, runBlock_reg _ _ _ (26 : Fin 32) s28.zero (by decide), g28_26]
  have g29_27 : reg n29 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb29, runBlock_reg _ _ _ (27 : Fin 32) s28.zero (by decide), g28_27]
  have g29_10 : reg n29 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1588 := by
    rw [rb29]; simp +decide only [runBlock, BInstr.run, svEcW17e0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g28_2, g28_3, g28_4, g28_8, g28_9, g28_18, g28_19, g28_20, g28_21, g28_22, g28_23, g28_24, g28_25, g28_26, g28_27, s28.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g29_11 : reg n29 a1 = B + 0x21A0 + BitVec.ofNat 32 0x1460 := by
    rw [rb29]; simp +decide only [runBlock, BInstr.run, svEcW17e0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g28_2, g28_3, g28_4, g28_8, g28_9, g28_18, g28_19, g28_20, g28_21, g28_22, g28_23, g28_24, g28_25, g28_26, g28_27, s28.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g29_12 : reg n29 a2 = BitVec.ofNat 32 0x20 := by
    rw [rb29]; simp +decide only [runBlock, BInstr.run, svEcW17e0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g28_2, g28_3, g28_4, g28_8, g28_9, g28_18, g28_19, g28_20, g28_21, g28_22, g28_23, g28_24, g28_25, g28_26, g28_27, s28.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
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
  have w29_a20 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m29]; exact w28_a20
  have w29_1020 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m29]; exact w28_1020
  have w29_1480 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m29]; exact w28_1480
  have a29_2a0 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m29]; exact a28_2a0
  have a29_2c0 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m29]; exact a28_2c0
  have a29_2e0 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m29]; exact a28_2e0
  have a29_380 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m29]; exact a28_380
  have a29_400 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m29]; exact a28_400
  have a29_13e0 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := by rw [m29]; exact a28_13e0
  have a29_1460 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := by rw [m29]; exact a28_1460
  have a29_1588 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U1 := by rw [m29]; exact a28_1588
  have p29_320 : ptF n29.mem B 0x320 = P0 := by rw [m29]; exact p28_320
  have p29_3a0 : ptF n29.mem B 0x3A0 = P1 := by rw [m29]; exact p28_3a0
  have p29_420 : ptF n29.mem B 0x420 = tbl2 P0 0 := by rw [m29]; exact p28_420
  have p29_480 : ptF n29.mem B 0x480 = tbl2 P0 1 := by rw [m29]; exact p28_480
  have p29_4e0 : ptF n29.mem B 0x4E0 = tbl2 P0 2 := by rw [m29]; exact p28_4e0
  have p29_540 : ptF n29.mem B 0x540 = tbl2 P0 3 := by rw [m29]; exact p28_540
  have p29_5a0 : ptF n29.mem B 0x5A0 = tbl2 P0 4 := by rw [m29]; exact p28_5a0
  have p29_600 : ptF n29.mem B 0x600 = tbl2 P0 5 := by rw [m29]; exact p28_600
  have p29_660 : ptF n29.mem B 0x660 = tbl2 P0 6 := by rw [m29]; exact p28_660
  have p29_6c0 : ptF n29.mem B 0x6C0 = tbl2 P0 7 := by rw [m29]; exact p28_6c0
  have p29_720 : ptF n29.mem B 0x720 = tbl2 P1 0 := by rw [m29]; exact p28_720
  have p29_780 : ptF n29.mem B 0x780 = tbl2 P1 1 := by rw [m29]; exact p28_780
  have p29_7e0 : ptF n29.mem B 0x7E0 = tbl2 P1 2 := by rw [m29]; exact p28_7e0
  have p29_840 : ptF n29.mem B 0x840 = tbl2 P1 3 := by rw [m29]; exact p28_840
  have p29_8a0 : ptF n29.mem B 0x8A0 = tbl2 P1 4 := by rw [m29]; exact p28_8a0
  have p29_900 : ptF n29.mem B 0x900 = tbl2 P1 5 := by rw [m29]; exact p28_900
  have p29_960 : ptF n29.mem B 0x960 = tbl2 P1 6 := by rw [m29]; exact p28_960
  have p29_9c0 : ptF n29.mem B 0x9C0 = tbl2 P1 7 := by rw [m29]; exact p28_9c0
  have p29_b40 : ptF n29.mem B 0xB40 = tbl2 P0 3 := by rw [m29]; exact p28_b40
  have p29_ba0 : ptF n29.mem B 0xBA0 = tbl2 P0 4 := by rw [m29]; exact p28_ba0
  have p29_c00 : ptF n29.mem B 0xC00 = tbl2 P0 5 := by rw [m29]; exact p28_c00
  have p29_c60 : ptF n29.mem B 0xC60 = tbl2 P0 6 := by rw [m29]; exact p28_c60
  have p29_cc0 : ptF n29.mem B 0xCC0 = tbl2 P0 7 := by rw [m29]; exact p28_cc0
  have p29_d20 : ptF n29.mem B 0xD20 = tbl2 P1 0 := by rw [m29]; exact p28_d20
  have p29_d80 : ptF n29.mem B 0xD80 = tbl2 P1 1 := by rw [m29]; exact p28_d80
  have p29_de0 : ptF n29.mem B 0xDE0 = tbl2 P1 2 := by rw [m29]; exact p28_de0
  have p29_e40 : ptF n29.mem B 0xE40 = tbl2 P1 3 := by rw [m29]; exact p28_e40
  have p29_ea0 : ptF n29.mem B 0xEA0 = tbl2 P1 4 := by rw [m29]; exact p28_ea0
  have p29_f00 : ptF n29.mem B 0xF00 = tbl2 P1 5 := by rw [m29]; exact p28_f00
  have p29_f60 : ptF n29.mem B 0xF60 = tbl2 P1 6 := by rw [m29]; exact p28_f60
  have p29_fc0 : ptF n29.mem B 0xFC0 = tbl2 P1 7 := by rw [m29]; exact p28_fc0
  have p29_1380 : ptF n29.mem B 0x1380 = P0 := by rw [m29]; exact p28_1380
  have p29_1400 : ptF n29.mem B 0x1400 = P1 := by rw [m29]; exact p28_1400
  have mb29_a24 : memBytes n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m29]; exact mb28_a24
  have mb29_1024 : memBytes n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m29]; exact mb28_1024
  have mb29_1320 : leN (memBytes n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U1 := by rw [m29]; exact mb28_1320
  have mb29_1484 : memBytes n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m29]; exact mb28_1484
  clear mb28_1484 mb28_1320 mb28_1024 mb28_a24 p28_1400 p28_1380 p28_fc0 p28_f60 p28_f00 p28_ea0 p28_e40 p28_de0 p28_d80 p28_d20 p28_cc0 p28_c60 p28_c00 p28_ba0 p28_b40 p28_9c0 p28_960 p28_900 p28_8a0 p28_840 p28_7e0 p28_780 p28_720 p28_6c0 p28_660 p28_600 p28_5a0 p28_540 p28_4e0 p28_480 p28_420 p28_3a0 p28_320 a28_1588 a28_1460 a28_13e0 a28_400 a28_380 a28_2e0 a28_2c0 a28_2a0 w28_1480 w28_1020 w28_a20 w28_130 w28_12c w28_128 w28_124 w28_120 w28_11c w28_118 w28_114 w28_110 w28_10c w28_108 w28_104 w28_100 w28_fc w28_f8 w28_f4 w28_f0 w28_ec w28_e8 w28_e4 w28_e0 w28_dc w28_d8 w28_d4 w28_d0 w28_cc w28_c8 w28_c4 w28_c0 w28_bc w28_b8 w28_b4 w28_b0 w28_ac w28_a8 w28_a4 w28_a0 w28_9c w28_98 w28_94 w28_90 w28_8c w28_88 w28_84 w28_80 w28_7c w28_78 w28_70 w28_6c w28_68 w28_64 w28_60 w28_5c w28_58 w28_54 w28_50 w28_4c w28_48 w28_44 w28_40 w28_3c w28_38 w28_34 w28_30 w28_2c w28_28 w28_24 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 m28 s28 u28 d28
  -- 0x17F0: memcpy
  obtain ⟨n30, P30, K30, X30⟩ := sv_mc (c := 0x1588) (d := 0x1460) (N := 0x20) F E29 s29 sv_at_17f0 sv_at_17f4
    (by decide) (by decide) g29_2 g29_10 g29_11 g29_12
    (by decide) (by decide) (by decide)
  have s30 := P30.st
  have fr30 := P30.fr
  have t30 : Steps n0 n30 := t29.trans P30.steps
  have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
  have E30 : SvCode n30.mem := E29.fr F fr30
  have V30 : SvSaves B n30.mem v := V29.keep K30 (by decide)
  have g30_2 : reg n30 sp = B + 0x21A0 := by rw [P30.regs sp (by decide), g29_2]
  have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P30.regs (3 : Fin 32) (by decide), g29_3]
  have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P30.regs (4 : Fin 32) (by decide), g29_4]
  have g30_8 : reg n30 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P30.regs (8 : Fin 32) (by decide), g29_8]
  have g30_9 : reg n30 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1400 := by rw [P30.regs (9 : Fin 32) (by decide), g29_9]
  have g30_18 : reg n30 (18 : Fin 32) = out := by rw [P30.regs (18 : Fin 32) (by decide), g29_18]
  have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [P30.regs (19 : Fin 32) (by decide), g29_19]
  have g30_20 : reg n30 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P30.regs (20 : Fin 32) (by decide), g29_20]
  have g30_21 : reg n30 (21 : Fin 32) = s5v := by rw [P30.regs (21 : Fin 32) (by decide), g29_21]
  have g30_22 : reg n30 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [P30.regs (22 : Fin 32) (by decide), g29_22]
  have g30_23 : reg n30 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by rw [P30.regs (23 : Fin 32) (by decide), g29_23]
  have g30_24 : reg n30 (24 : Fin 32) = s8v := by rw [P30.regs (24 : Fin 32) (by decide), g29_24]
  have g30_25 : reg n30 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P30.regs (25 : Fin 32) (by decide), g29_25]
  have g30_26 : reg n30 (26 : Fin 32) = x26 := by rw [P30.regs (26 : Fin 32) (by decide), g29_26]
  have g30_27 : reg n30 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P30.regs (27 : Fin 32) (by decide), g29_27]
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
  have w30_a20 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := (K30.w32 (by decide) (by decide)).trans w29_a20
  have w30_1020 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := (K30.w32 (by decide) (by decide)).trans w29_1020
  have w30_1480 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := (K30.w32 (by decide) (by decide)).trans w29_1480
  have a30_2a0 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K30.acc (by decide) (by decide)).trans a29_2a0
  have a30_2c0 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K30.acc (by decide) (by decide)).trans a29_2c0
  have a30_2e0 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K30.acc (by decide) (by decide)).trans a29_2e0
  have a30_380 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := (K30.acc (by decide) (by decide)).trans a29_380
  have a30_400 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := (K30.acc (by decide) (by decide)).trans a29_400
  have a30_13e0 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := (K30.acc (by decide) (by decide)).trans a29_13e0
  have a30_1460 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := (K30.acc (by decide) (by decide)).trans a29_1460
  have p30_320 : ptF n30.mem B 0x320 = P0 := (K30.pt (by decide) (by decide)).trans p29_320
  have p30_3a0 : ptF n30.mem B 0x3A0 = P1 := (K30.pt (by decide) (by decide)).trans p29_3a0
  have p30_420 : ptF n30.mem B 0x420 = tbl2 P0 0 := (K30.pt (by decide) (by decide)).trans p29_420
  have p30_480 : ptF n30.mem B 0x480 = tbl2 P0 1 := (K30.pt (by decide) (by decide)).trans p29_480
  have p30_4e0 : ptF n30.mem B 0x4E0 = tbl2 P0 2 := (K30.pt (by decide) (by decide)).trans p29_4e0
  have p30_540 : ptF n30.mem B 0x540 = tbl2 P0 3 := (K30.pt (by decide) (by decide)).trans p29_540
  have p30_5a0 : ptF n30.mem B 0x5A0 = tbl2 P0 4 := (K30.pt (by decide) (by decide)).trans p29_5a0
  have p30_600 : ptF n30.mem B 0x600 = tbl2 P0 5 := (K30.pt (by decide) (by decide)).trans p29_600
  have p30_660 : ptF n30.mem B 0x660 = tbl2 P0 6 := (K30.pt (by decide) (by decide)).trans p29_660
  have p30_6c0 : ptF n30.mem B 0x6C0 = tbl2 P0 7 := (K30.pt (by decide) (by decide)).trans p29_6c0
  have p30_720 : ptF n30.mem B 0x720 = tbl2 P1 0 := (K30.pt (by decide) (by decide)).trans p29_720
  have p30_780 : ptF n30.mem B 0x780 = tbl2 P1 1 := (K30.pt (by decide) (by decide)).trans p29_780
  have p30_7e0 : ptF n30.mem B 0x7E0 = tbl2 P1 2 := (K30.pt (by decide) (by decide)).trans p29_7e0
  have p30_840 : ptF n30.mem B 0x840 = tbl2 P1 3 := (K30.pt (by decide) (by decide)).trans p29_840
  have p30_8a0 : ptF n30.mem B 0x8A0 = tbl2 P1 4 := (K30.pt (by decide) (by decide)).trans p29_8a0
  have p30_900 : ptF n30.mem B 0x900 = tbl2 P1 5 := (K30.pt (by decide) (by decide)).trans p29_900
  have p30_960 : ptF n30.mem B 0x960 = tbl2 P1 6 := (K30.pt (by decide) (by decide)).trans p29_960
  have p30_9c0 : ptF n30.mem B 0x9C0 = tbl2 P1 7 := (K30.pt (by decide) (by decide)).trans p29_9c0
  have p30_b40 : ptF n30.mem B 0xB40 = tbl2 P0 3 := (K30.pt (by decide) (by decide)).trans p29_b40
  have p30_ba0 : ptF n30.mem B 0xBA0 = tbl2 P0 4 := (K30.pt (by decide) (by decide)).trans p29_ba0
  have p30_c00 : ptF n30.mem B 0xC00 = tbl2 P0 5 := (K30.pt (by decide) (by decide)).trans p29_c00
  have p30_c60 : ptF n30.mem B 0xC60 = tbl2 P0 6 := (K30.pt (by decide) (by decide)).trans p29_c60
  have p30_cc0 : ptF n30.mem B 0xCC0 = tbl2 P0 7 := (K30.pt (by decide) (by decide)).trans p29_cc0
  have p30_d20 : ptF n30.mem B 0xD20 = tbl2 P1 0 := (K30.pt (by decide) (by decide)).trans p29_d20
  have p30_d80 : ptF n30.mem B 0xD80 = tbl2 P1 1 := (K30.pt (by decide) (by decide)).trans p29_d80
  have p30_de0 : ptF n30.mem B 0xDE0 = tbl2 P1 2 := (K30.pt (by decide) (by decide)).trans p29_de0
  have p30_e40 : ptF n30.mem B 0xE40 = tbl2 P1 3 := (K30.pt (by decide) (by decide)).trans p29_e40
  have p30_ea0 : ptF n30.mem B 0xEA0 = tbl2 P1 4 := (K30.pt (by decide) (by decide)).trans p29_ea0
  have p30_f00 : ptF n30.mem B 0xF00 = tbl2 P1 5 := (K30.pt (by decide) (by decide)).trans p29_f00
  have p30_f60 : ptF n30.mem B 0xF60 = tbl2 P1 6 := (K30.pt (by decide) (by decide)).trans p29_f60
  have p30_fc0 : ptF n30.mem B 0xFC0 = tbl2 P1 7 := (K30.pt (by decide) (by decide)).trans p29_fc0
  have p30_1380 : ptF n30.mem B 0x1380 = P0 := (K30.pt (by decide) (by decide)).trans p29_1380
  have p30_1400 : ptF n30.mem B 0x1400 = P1 := (K30.pt (by decide) (by decide)).trans p29_1400
  have mb30_a24 : memBytes n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [K30.mb (by decide) (by decide)]; exact mb29_a24
  have mb30_1024 : memBytes n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [K30.mb (by decide) (by decide)]; exact mb29_1024
  have mb30_1320 : leN (memBytes n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U1 := by rw [K30.mb (by decide) (by decide)]; exact mb29_1320
  have mb30_1484 : memBytes n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [K30.mb (by decide) (by decide)]; exact mb29_1484
  have a30_1588 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U2 := (accV_S 8 fun q hq => by
    rw [show 0x1588 + q = 0x1588 + (0x0 + q) by omega, X30 (0x0 + q) (by omega),
      show 0x1460 + (0x0 + q) = 0x1460 + q by omega]).trans a29_1460
  clear mb29_1484 mb29_1320 mb29_1024 mb29_a24 p29_1400 p29_1380 p29_fc0 p29_f60 p29_f00 p29_ea0 p29_e40 p29_de0 p29_d80 p29_d20 p29_cc0 p29_c60 p29_c00 p29_ba0 p29_b40 p29_9c0 p29_960 p29_900 p29_8a0 p29_840 p29_7e0 p29_780 p29_720 p29_6c0 p29_660 p29_600 p29_5a0 p29_540 p29_4e0 p29_480 p29_420 p29_3a0 p29_320 a29_1588 a29_1460 a29_13e0 a29_400 a29_380 a29_2e0 a29_2c0 a29_2a0 w29_1480 w29_1020 w29_a20 w29_130 w29_12c w29_128 w29_124 w29_120 w29_11c w29_118 w29_114 w29_110 w29_10c w29_108 w29_104 w29_100 w29_fc w29_f8 w29_f4 w29_f0 w29_ec w29_e8 w29_e4 w29_e0 w29_dc w29_d8 w29_d4 w29_d0 w29_cc w29_c8 w29_c4 w29_c0 w29_bc w29_b8 w29_b4 w29_b0 w29_ac w29_a8 w29_a4 w29_a0 w29_9c w29_98 w29_94 w29_90 w29_8c w29_88 w29_84 w29_80 w29_7c w29_78 w29_70 w29_6c w29_68 w29_64 w29_60 w29_5c w29_58 w29_54 w29_50 w29_4c w29_48 w29_44 w29_40 w29_3c w29_38 w29_34 w29_30 w29_2c w29_28 w29_24 g29_12 g29_11 g29_10 g29_27 g29_26 g29_25 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_9 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 rb29 s29 m29 u29 c29
  -- 0x17F8
  obtain ⟨n31, c31, u31⟩ := s30.block svEcW17f8 E30.self svEcW17f8_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m31 : n31.mem = n30.mem := u31.mem
  have s31 : St n31.mem SV n31 0x1808 (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
  have rb31 : ∀ q, reg n31 q = (runBlock svEcW17f8 (n30.mem, reg n30)).2 q := fun q => by rw [u31.regs]
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
  have g31_8 : reg n31 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb31, runBlock_reg _ _ _ (8 : Fin 32) s30.zero (by decide), g30_8]
  have g31_9 : reg n31 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1400 := by
    rw [rb31, runBlock_reg _ _ _ (9 : Fin 32) s30.zero (by decide), g30_9]
  have g31_18 : reg n31 (18 : Fin 32) = out := by
    rw [rb31, runBlock_reg _ _ _ (18 : Fin 32) s30.zero (by decide), g30_18]
  have g31_19 : reg n31 (19 : Fin 32) = bp := by
    rw [rb31, runBlock_reg _ _ _ (19 : Fin 32) s30.zero (by decide), g30_19]
  have g31_20 : reg n31 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb31, runBlock_reg _ _ _ (20 : Fin 32) s30.zero (by decide), g30_20]
  have g31_21 : reg n31 (21 : Fin 32) = s5v := by
    rw [rb31, runBlock_reg _ _ _ (21 : Fin 32) s30.zero (by decide), g30_21]
  have g31_22 : reg n31 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by
    rw [rb31, runBlock_reg _ _ _ (22 : Fin 32) s30.zero (by decide), g30_22]
  have g31_23 : reg n31 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by
    rw [rb31, runBlock_reg _ _ _ (23 : Fin 32) s30.zero (by decide), g30_23]
  have g31_24 : reg n31 (24 : Fin 32) = s8v := by
    rw [rb31, runBlock_reg _ _ _ (24 : Fin 32) s30.zero (by decide), g30_24]
  have g31_25 : reg n31 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb31, runBlock_reg _ _ _ (25 : Fin 32) s30.zero (by decide), g30_25]
  have g31_26 : reg n31 (26 : Fin 32) = x26 := by
    rw [rb31, runBlock_reg _ _ _ (26 : Fin 32) s30.zero (by decide), g30_26]
  have g31_27 : reg n31 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb31, runBlock_reg _ _ _ (27 : Fin 32) s30.zero (by decide), g30_27]
  have g31_10 : reg n31 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by
    rw [rb31]; simp +decide only [runBlock, BInstr.run, svEcW17f8, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g30_2, g30_3, g30_4, g30_8, g30_9, g30_18, g30_19, g30_20, g30_21, g30_22, g30_23, g30_24, g30_25, g30_26, g30_27, s30.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g31_11 : reg n31 a1 = B + 0x21A0 + BitVec.ofNat 32 0x1588 := by
    rw [rb31]; simp +decide only [runBlock, BInstr.run, svEcW17f8, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g30_2, g30_3, g30_4, g30_8, g30_9, g30_18, g30_19, g30_20, g30_21, g30_22, g30_23, g30_24, g30_25, g30_26, g30_27, s30.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
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
  have w31_a20 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m31]; exact w30_a20
  have w31_1020 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m31]; exact w30_1020
  have w31_1480 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m31]; exact w30_1480
  have a31_2a0 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m31]; exact a30_2a0
  have a31_2c0 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m31]; exact a30_2c0
  have a31_2e0 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m31]; exact a30_2e0
  have a31_380 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m31]; exact a30_380
  have a31_400 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m31]; exact a30_400
  have a31_13e0 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := by rw [m31]; exact a30_13e0
  have a31_1460 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := by rw [m31]; exact a30_1460
  have a31_1588 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U2 := by rw [m31]; exact a30_1588
  have p31_320 : ptF n31.mem B 0x320 = P0 := by rw [m31]; exact p30_320
  have p31_3a0 : ptF n31.mem B 0x3A0 = P1 := by rw [m31]; exact p30_3a0
  have p31_420 : ptF n31.mem B 0x420 = tbl2 P0 0 := by rw [m31]; exact p30_420
  have p31_480 : ptF n31.mem B 0x480 = tbl2 P0 1 := by rw [m31]; exact p30_480
  have p31_4e0 : ptF n31.mem B 0x4E0 = tbl2 P0 2 := by rw [m31]; exact p30_4e0
  have p31_540 : ptF n31.mem B 0x540 = tbl2 P0 3 := by rw [m31]; exact p30_540
  have p31_5a0 : ptF n31.mem B 0x5A0 = tbl2 P0 4 := by rw [m31]; exact p30_5a0
  have p31_600 : ptF n31.mem B 0x600 = tbl2 P0 5 := by rw [m31]; exact p30_600
  have p31_660 : ptF n31.mem B 0x660 = tbl2 P0 6 := by rw [m31]; exact p30_660
  have p31_6c0 : ptF n31.mem B 0x6C0 = tbl2 P0 7 := by rw [m31]; exact p30_6c0
  have p31_720 : ptF n31.mem B 0x720 = tbl2 P1 0 := by rw [m31]; exact p30_720
  have p31_780 : ptF n31.mem B 0x780 = tbl2 P1 1 := by rw [m31]; exact p30_780
  have p31_7e0 : ptF n31.mem B 0x7E0 = tbl2 P1 2 := by rw [m31]; exact p30_7e0
  have p31_840 : ptF n31.mem B 0x840 = tbl2 P1 3 := by rw [m31]; exact p30_840
  have p31_8a0 : ptF n31.mem B 0x8A0 = tbl2 P1 4 := by rw [m31]; exact p30_8a0
  have p31_900 : ptF n31.mem B 0x900 = tbl2 P1 5 := by rw [m31]; exact p30_900
  have p31_960 : ptF n31.mem B 0x960 = tbl2 P1 6 := by rw [m31]; exact p30_960
  have p31_9c0 : ptF n31.mem B 0x9C0 = tbl2 P1 7 := by rw [m31]; exact p30_9c0
  have p31_b40 : ptF n31.mem B 0xB40 = tbl2 P0 3 := by rw [m31]; exact p30_b40
  have p31_ba0 : ptF n31.mem B 0xBA0 = tbl2 P0 4 := by rw [m31]; exact p30_ba0
  have p31_c00 : ptF n31.mem B 0xC00 = tbl2 P0 5 := by rw [m31]; exact p30_c00
  have p31_c60 : ptF n31.mem B 0xC60 = tbl2 P0 6 := by rw [m31]; exact p30_c60
  have p31_cc0 : ptF n31.mem B 0xCC0 = tbl2 P0 7 := by rw [m31]; exact p30_cc0
  have p31_d20 : ptF n31.mem B 0xD20 = tbl2 P1 0 := by rw [m31]; exact p30_d20
  have p31_d80 : ptF n31.mem B 0xD80 = tbl2 P1 1 := by rw [m31]; exact p30_d80
  have p31_de0 : ptF n31.mem B 0xDE0 = tbl2 P1 2 := by rw [m31]; exact p30_de0
  have p31_e40 : ptF n31.mem B 0xE40 = tbl2 P1 3 := by rw [m31]; exact p30_e40
  have p31_ea0 : ptF n31.mem B 0xEA0 = tbl2 P1 4 := by rw [m31]; exact p30_ea0
  have p31_f00 : ptF n31.mem B 0xF00 = tbl2 P1 5 := by rw [m31]; exact p30_f00
  have p31_f60 : ptF n31.mem B 0xF60 = tbl2 P1 6 := by rw [m31]; exact p30_f60
  have p31_fc0 : ptF n31.mem B 0xFC0 = tbl2 P1 7 := by rw [m31]; exact p30_fc0
  have p31_1380 : ptF n31.mem B 0x1380 = P0 := by rw [m31]; exact p30_1380
  have p31_1400 : ptF n31.mem B 0x1400 = P1 := by rw [m31]; exact p30_1400
  have mb31_a24 : memBytes n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m31]; exact mb30_a24
  have mb31_1024 : memBytes n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m31]; exact mb30_1024
  have mb31_1320 : leN (memBytes n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U1 := by rw [m31]; exact mb30_1320
  have mb31_1484 : memBytes n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m31]; exact mb30_1484
  clear a30_1588 mb30_1484 mb30_1320 mb30_1024 mb30_a24 p30_1400 p30_1380 p30_fc0 p30_f60 p30_f00 p30_ea0 p30_e40 p30_de0 p30_d80 p30_d20 p30_cc0 p30_c60 p30_c00 p30_ba0 p30_b40 p30_9c0 p30_960 p30_900 p30_8a0 p30_840 p30_7e0 p30_780 p30_720 p30_6c0 p30_660 p30_600 p30_5a0 p30_540 p30_4e0 p30_480 p30_420 p30_3a0 p30_320 a30_1460 a30_13e0 a30_400 a30_380 a30_2e0 a30_2c0 a30_2a0 w30_1480 w30_1020 w30_a20 w30_130 w30_12c w30_128 w30_124 w30_120 w30_11c w30_118 w30_114 w30_110 w30_10c w30_108 w30_104 w30_100 w30_fc w30_f8 w30_f4 w30_f0 w30_ec w30_e8 w30_e4 w30_e0 w30_dc w30_d8 w30_d4 w30_d0 w30_cc w30_c8 w30_c4 w30_c0 w30_bc w30_b8 w30_b4 w30_b0 w30_ac w30_a8 w30_a4 w30_a0 w30_9c w30_98 w30_94 w30_90 w30_8c w30_88 w30_84 w30_80 w30_7c w30_78 w30_70 w30_6c w30_68 w30_64 w30_60 w30_5c w30_58 w30_54 w30_50 w30_4c w30_48 w30_44 w30_40 w30_3c w30_38 w30_34 w30_30 w30_2c w30_28 w30_24 g30_27 g30_26 g30_25 g30_24 g30_23 g30_22 g30_21 g30_20 g30_19 g30_18 g30_9 g30_8 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 s30 X30 K30 P30
  -- 0x1808: to_be_byte_array
  obtain ⟨n32, P32, K32, L32⟩ := sv_tbb8 (co := 0x1480) (cx := 0x1588) F E31 (WN0.sv F fR31) s31
    sv_at_1808 sv_at_180c (by decide) (by decide) g31_2 g31_10 g31_11
    (by decide) (by decide) (by decide)
  rw [a31_1588] at L32
  have s32 := P32.st
  have fr32 := P32.fr
  have t32 : Steps n0 n32 := t31.trans P32.steps
  have fR32 : ∀ x, SvR B x → n32.mem x = M0 x := fun x hx => (fr32 x hx).trans (fR31 x hx)
  have E32 : SvCode n32.mem := E31.fr F fr32
  have V32 : SvSaves B n32.mem v := V31.keep K32 (by decide)
  have g32_2 : reg n32 sp = B + 0x21A0 := by rw [P32.regs sp (by decide), g31_2]
  have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P32.regs (3 : Fin 32) (by decide), g31_3]
  have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P32.regs (4 : Fin 32) (by decide), g31_4]
  have g32_8 : reg n32 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P32.regs (8 : Fin 32) (by decide), g31_8]
  have g32_9 : reg n32 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1400 := by rw [P32.regs (9 : Fin 32) (by decide), g31_9]
  have g32_18 : reg n32 (18 : Fin 32) = out := by rw [P32.regs (18 : Fin 32) (by decide), g31_18]
  have g32_19 : reg n32 (19 : Fin 32) = bp := by rw [P32.regs (19 : Fin 32) (by decide), g31_19]
  have g32_20 : reg n32 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P32.regs (20 : Fin 32) (by decide), g31_20]
  have g32_21 : reg n32 (21 : Fin 32) = s5v := by rw [P32.regs (21 : Fin 32) (by decide), g31_21]
  have g32_22 : reg n32 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [P32.regs (22 : Fin 32) (by decide), g31_22]
  have g32_23 : reg n32 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by rw [P32.regs (23 : Fin 32) (by decide), g31_23]
  have g32_24 : reg n32 (24 : Fin 32) = s8v := by rw [P32.regs (24 : Fin 32) (by decide), g31_24]
  have g32_25 : reg n32 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P32.regs (25 : Fin 32) (by decide), g31_25]
  have g32_26 : reg n32 (26 : Fin 32) = x26 := by rw [P32.regs (26 : Fin 32) (by decide), g31_26]
  have g32_27 : reg n32 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P32.regs (27 : Fin 32) (by decide), g31_27]
  have w32_24 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K32.w32 (by decide) (by decide)).trans w31_24
  have w32_28 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K32.w32 (by decide) (by decide)).trans w31_28
  have w32_2c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K32.w32 (by decide) (by decide)).trans w31_2c
  have w32_30 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K32.w32 (by decide) (by decide)).trans w31_30
  have w32_34 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K32.w32 (by decide) (by decide)).trans w31_34
  have w32_38 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K32.w32 (by decide) (by decide)).trans w31_38
  have w32_3c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K32.w32 (by decide) (by decide)).trans w31_3c
  have w32_40 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K32.w32 (by decide) (by decide)).trans w31_40
  have w32_44 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K32.w32 (by decide) (by decide)).trans w31_44
  have w32_48 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K32.w32 (by decide) (by decide)).trans w31_48
  have w32_4c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K32.w32 (by decide) (by decide)).trans w31_4c
  have w32_50 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K32.w32 (by decide) (by decide)).trans w31_50
  have w32_54 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K32.w32 (by decide) (by decide)).trans w31_54
  have w32_58 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K32.w32 (by decide) (by decide)).trans w31_58
  have w32_5c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K32.w32 (by decide) (by decide)).trans w31_5c
  have w32_60 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K32.w32 (by decide) (by decide)).trans w31_60
  have w32_64 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K32.w32 (by decide) (by decide)).trans w31_64
  have w32_68 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K32.w32 (by decide) (by decide)).trans w31_68
  have w32_6c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K32.w32 (by decide) (by decide)).trans w31_6c
  have w32_70 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K32.w32 (by decide) (by decide)).trans w31_70
  have w32_78 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := (K32.w32 (by decide) (by decide)).trans w31_78
  have w32_7c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K32.w32 (by decide) (by decide)).trans w31_7c
  have w32_80 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K32.w32 (by decide) (by decide)).trans w31_80
  have w32_84 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K32.w32 (by decide) (by decide)).trans w31_84
  have w32_88 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K32.w32 (by decide) (by decide)).trans w31_88
  have w32_8c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K32.w32 (by decide) (by decide)).trans w31_8c
  have w32_90 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K32.w32 (by decide) (by decide)).trans w31_90
  have w32_94 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K32.w32 (by decide) (by decide)).trans w31_94
  have w32_98 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K32.w32 (by decide) (by decide)).trans w31_98
  have w32_9c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K32.w32 (by decide) (by decide)).trans w31_9c
  have w32_a0 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K32.w32 (by decide) (by decide)).trans w31_a0
  have w32_a4 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K32.w32 (by decide) (by decide)).trans w31_a4
  have w32_a8 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K32.w32 (by decide) (by decide)).trans w31_a8
  have w32_ac : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K32.w32 (by decide) (by decide)).trans w31_ac
  have w32_b0 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K32.w32 (by decide) (by decide)).trans w31_b0
  have w32_b4 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K32.w32 (by decide) (by decide)).trans w31_b4
  have w32_b8 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K32.w32 (by decide) (by decide)).trans w31_b8
  have w32_bc : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K32.w32 (by decide) (by decide)).trans w31_bc
  have w32_c0 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K32.w32 (by decide) (by decide)).trans w31_c0
  have w32_c4 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K32.w32 (by decide) (by decide)).trans w31_c4
  have w32_c8 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K32.w32 (by decide) (by decide)).trans w31_c8
  have w32_cc : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K32.w32 (by decide) (by decide)).trans w31_cc
  have w32_d0 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K32.w32 (by decide) (by decide)).trans w31_d0
  have w32_d4 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K32.w32 (by decide) (by decide)).trans w31_d4
  have w32_d8 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K32.w32 (by decide) (by decide)).trans w31_d8
  have w32_dc : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K32.w32 (by decide) (by decide)).trans w31_dc
  have w32_e0 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K32.w32 (by decide) (by decide)).trans w31_e0
  have w32_e4 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K32.w32 (by decide) (by decide)).trans w31_e4
  have w32_e8 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K32.w32 (by decide) (by decide)).trans w31_e8
  have w32_ec : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K32.w32 (by decide) (by decide)).trans w31_ec
  have w32_f0 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K32.w32 (by decide) (by decide)).trans w31_f0
  have w32_f4 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K32.w32 (by decide) (by decide)).trans w31_f4
  have w32_f8 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K32.w32 (by decide) (by decide)).trans w31_f8
  have w32_fc : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K32.w32 (by decide) (by decide)).trans w31_fc
  have w32_100 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K32.w32 (by decide) (by decide)).trans w31_100
  have w32_104 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K32.w32 (by decide) (by decide)).trans w31_104
  have w32_108 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K32.w32 (by decide) (by decide)).trans w31_108
  have w32_10c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K32.w32 (by decide) (by decide)).trans w31_10c
  have w32_110 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K32.w32 (by decide) (by decide)).trans w31_110
  have w32_114 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K32.w32 (by decide) (by decide)).trans w31_114
  have w32_118 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K32.w32 (by decide) (by decide)).trans w31_118
  have w32_11c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K32.w32 (by decide) (by decide)).trans w31_11c
  have w32_120 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K32.w32 (by decide) (by decide)).trans w31_120
  have w32_124 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K32.w32 (by decide) (by decide)).trans w31_124
  have w32_128 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K32.w32 (by decide) (by decide)).trans w31_128
  have w32_12c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K32.w32 (by decide) (by decide)).trans w31_12c
  have w32_130 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K32.w32 (by decide) (by decide)).trans w31_130
  have w32_a20 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := (K32.w32 (by decide) (by decide)).trans w31_a20
  have w32_1020 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := (K32.w32 (by decide) (by decide)).trans w31_1020
  have a32_2a0 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K32.acc (by decide) (by decide)).trans a31_2a0
  have a32_2c0 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K32.acc (by decide) (by decide)).trans a31_2c0
  have a32_2e0 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K32.acc (by decide) (by decide)).trans a31_2e0
  have a32_380 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := (K32.acc (by decide) (by decide)).trans a31_380
  have a32_400 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := (K32.acc (by decide) (by decide)).trans a31_400
  have a32_13e0 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := (K32.acc (by decide) (by decide)).trans a31_13e0
  have a32_1460 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := (K32.acc (by decide) (by decide)).trans a31_1460
  have a32_1588 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U2 := (K32.acc (by decide) (by decide)).trans a31_1588
  have p32_320 : ptF n32.mem B 0x320 = P0 := (K32.pt (by decide) (by decide)).trans p31_320
  have p32_3a0 : ptF n32.mem B 0x3A0 = P1 := (K32.pt (by decide) (by decide)).trans p31_3a0
  have p32_420 : ptF n32.mem B 0x420 = tbl2 P0 0 := (K32.pt (by decide) (by decide)).trans p31_420
  have p32_480 : ptF n32.mem B 0x480 = tbl2 P0 1 := (K32.pt (by decide) (by decide)).trans p31_480
  have p32_4e0 : ptF n32.mem B 0x4E0 = tbl2 P0 2 := (K32.pt (by decide) (by decide)).trans p31_4e0
  have p32_540 : ptF n32.mem B 0x540 = tbl2 P0 3 := (K32.pt (by decide) (by decide)).trans p31_540
  have p32_5a0 : ptF n32.mem B 0x5A0 = tbl2 P0 4 := (K32.pt (by decide) (by decide)).trans p31_5a0
  have p32_600 : ptF n32.mem B 0x600 = tbl2 P0 5 := (K32.pt (by decide) (by decide)).trans p31_600
  have p32_660 : ptF n32.mem B 0x660 = tbl2 P0 6 := (K32.pt (by decide) (by decide)).trans p31_660
  have p32_6c0 : ptF n32.mem B 0x6C0 = tbl2 P0 7 := (K32.pt (by decide) (by decide)).trans p31_6c0
  have p32_720 : ptF n32.mem B 0x720 = tbl2 P1 0 := (K32.pt (by decide) (by decide)).trans p31_720
  have p32_780 : ptF n32.mem B 0x780 = tbl2 P1 1 := (K32.pt (by decide) (by decide)).trans p31_780
  have p32_7e0 : ptF n32.mem B 0x7E0 = tbl2 P1 2 := (K32.pt (by decide) (by decide)).trans p31_7e0
  have p32_840 : ptF n32.mem B 0x840 = tbl2 P1 3 := (K32.pt (by decide) (by decide)).trans p31_840
  have p32_8a0 : ptF n32.mem B 0x8A0 = tbl2 P1 4 := (K32.pt (by decide) (by decide)).trans p31_8a0
  have p32_900 : ptF n32.mem B 0x900 = tbl2 P1 5 := (K32.pt (by decide) (by decide)).trans p31_900
  have p32_960 : ptF n32.mem B 0x960 = tbl2 P1 6 := (K32.pt (by decide) (by decide)).trans p31_960
  have p32_9c0 : ptF n32.mem B 0x9C0 = tbl2 P1 7 := (K32.pt (by decide) (by decide)).trans p31_9c0
  have p32_b40 : ptF n32.mem B 0xB40 = tbl2 P0 3 := (K32.pt (by decide) (by decide)).trans p31_b40
  have p32_ba0 : ptF n32.mem B 0xBA0 = tbl2 P0 4 := (K32.pt (by decide) (by decide)).trans p31_ba0
  have p32_c00 : ptF n32.mem B 0xC00 = tbl2 P0 5 := (K32.pt (by decide) (by decide)).trans p31_c00
  have p32_c60 : ptF n32.mem B 0xC60 = tbl2 P0 6 := (K32.pt (by decide) (by decide)).trans p31_c60
  have p32_cc0 : ptF n32.mem B 0xCC0 = tbl2 P0 7 := (K32.pt (by decide) (by decide)).trans p31_cc0
  have p32_d20 : ptF n32.mem B 0xD20 = tbl2 P1 0 := (K32.pt (by decide) (by decide)).trans p31_d20
  have p32_d80 : ptF n32.mem B 0xD80 = tbl2 P1 1 := (K32.pt (by decide) (by decide)).trans p31_d80
  have p32_de0 : ptF n32.mem B 0xDE0 = tbl2 P1 2 := (K32.pt (by decide) (by decide)).trans p31_de0
  have p32_e40 : ptF n32.mem B 0xE40 = tbl2 P1 3 := (K32.pt (by decide) (by decide)).trans p31_e40
  have p32_ea0 : ptF n32.mem B 0xEA0 = tbl2 P1 4 := (K32.pt (by decide) (by decide)).trans p31_ea0
  have p32_f00 : ptF n32.mem B 0xF00 = tbl2 P1 5 := (K32.pt (by decide) (by decide)).trans p31_f00
  have p32_f60 : ptF n32.mem B 0xF60 = tbl2 P1 6 := (K32.pt (by decide) (by decide)).trans p31_f60
  have p32_fc0 : ptF n32.mem B 0xFC0 = tbl2 P1 7 := (K32.pt (by decide) (by decide)).trans p31_fc0
  have p32_1380 : ptF n32.mem B 0x1380 = P0 := (K32.pt (by decide) (by decide)).trans p31_1380
  have p32_1400 : ptF n32.mem B 0x1400 = P1 := (K32.pt (by decide) (by decide)).trans p31_1400
  have mb32_a24 : memBytes n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [K32.mb (by decide) (by decide)]; exact mb31_a24
  have mb32_1024 : memBytes n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [K32.mb (by decide) (by decide)]; exact mb31_1024
  have mb32_1320 : leN (memBytes n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U1 := by rw [K32.mb (by decide) (by decide)]; exact mb31_1320
  have mb32_1480 : leN (memBytes n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 0x20).reverse = U2 := L32
  clear mb31_1484 mb31_1320 mb31_1024 mb31_a24 p31_1400 p31_1380 p31_fc0 p31_f60 p31_f00 p31_ea0 p31_e40 p31_de0 p31_d80 p31_d20 p31_cc0 p31_c60 p31_c00 p31_ba0 p31_b40 p31_9c0 p31_960 p31_900 p31_8a0 p31_840 p31_7e0 p31_780 p31_720 p31_6c0 p31_660 p31_600 p31_5a0 p31_540 p31_4e0 p31_480 p31_420 p31_3a0 p31_320 a31_1588 a31_1460 a31_13e0 a31_400 a31_380 a31_2e0 a31_2c0 a31_2a0 w31_1480 w31_1020 w31_a20 w31_130 w31_12c w31_128 w31_124 w31_120 w31_11c w31_118 w31_114 w31_110 w31_10c w31_108 w31_104 w31_100 w31_fc w31_f8 w31_f4 w31_f0 w31_ec w31_e8 w31_e4 w31_e0 w31_dc w31_d8 w31_d4 w31_d0 w31_cc w31_c8 w31_c4 w31_c0 w31_bc w31_b8 w31_b4 w31_b0 w31_ac w31_a8 w31_a4 w31_a0 w31_9c w31_98 w31_94 w31_90 w31_8c w31_88 w31_84 w31_80 w31_7c w31_78 w31_70 w31_6c w31_68 w31_64 w31_60 w31_5c w31_58 w31_54 w31_50 w31_4c w31_48 w31_44 w31_40 w31_3c w31_38 w31_34 w31_30 w31_2c w31_28 w31_24 g31_11 g31_10 g31_27 g31_26 g31_25 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_9 g31_8 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 rb31 s31 m31 u31 c31
  -- 0x1810
  obtain ⟨n33, c33, u33⟩ := s32.block svEcW1810 E32.self svEcW1810_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m33 : n33.mem = n32.mem := u33.mem
  have s33 : St n33.mem SV n33 0x181C (reg n33) := ⟨u33.pc, rfl, fun _ => rfl⟩
  have rb33 : ∀ q, reg n33 q = (runBlock svEcW1810 (n32.mem, reg n32)).2 q := fun q => by rw [u33.regs]
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
  have g33_8 : reg n33 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb33, runBlock_reg _ _ _ (8 : Fin 32) s32.zero (by decide), g32_8]
  have g33_9 : reg n33 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1400 := by
    rw [rb33, runBlock_reg _ _ _ (9 : Fin 32) s32.zero (by decide), g32_9]
  have g33_18 : reg n33 (18 : Fin 32) = out := by
    rw [rb33, runBlock_reg _ _ _ (18 : Fin 32) s32.zero (by decide), g32_18]
  have g33_19 : reg n33 (19 : Fin 32) = bp := by
    rw [rb33, runBlock_reg _ _ _ (19 : Fin 32) s32.zero (by decide), g32_19]
  have g33_20 : reg n33 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb33, runBlock_reg _ _ _ (20 : Fin 32) s32.zero (by decide), g32_20]
  have g33_21 : reg n33 (21 : Fin 32) = s5v := by
    rw [rb33, runBlock_reg _ _ _ (21 : Fin 32) s32.zero (by decide), g32_21]
  have g33_22 : reg n33 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by
    rw [rb33, runBlock_reg _ _ _ (22 : Fin 32) s32.zero (by decide), g32_22]
  have g33_23 : reg n33 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by
    rw [rb33, runBlock_reg _ _ _ (23 : Fin 32) s32.zero (by decide), g32_23]
  have g33_24 : reg n33 (24 : Fin 32) = s8v := by
    rw [rb33, runBlock_reg _ _ _ (24 : Fin 32) s32.zero (by decide), g32_24]
  have g33_25 : reg n33 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb33, runBlock_reg _ _ _ (25 : Fin 32) s32.zero (by decide), g32_25]
  have g33_26 : reg n33 (26 : Fin 32) = x26 := by
    rw [rb33, runBlock_reg _ _ _ (26 : Fin 32) s32.zero (by decide), g32_26]
  have g33_27 : reg n33 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb33, runBlock_reg _ _ _ (27 : Fin 32) s32.zero (by decide), g32_27]
  have g33_10 : reg n33 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by
    rw [rb33]; simp +decide only [runBlock, BInstr.run, svEcW1810, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g32_2, g32_3, g32_4, g32_8, g32_9, g32_18, g32_19, g32_20, g32_21, g32_22, g32_23, g32_24, g32_25, g32_26, g32_27, s32.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g33_11 : reg n33 a1 = BitVec.ofNat 32 0x20 := by
    rw [rb33]; simp +decide only [runBlock, BInstr.run, svEcW1810, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g32_2, g32_3, g32_4, g32_8, g32_9, g32_18, g32_19, g32_20, g32_21, g32_22, g32_23, g32_24, g32_25, g32_26, g32_27, s32.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
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
  have w33_a20 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m33]; exact w32_a20
  have w33_1020 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m33]; exact w32_1020
  have a33_2a0 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m33]; exact a32_2a0
  have a33_2c0 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m33]; exact a32_2c0
  have a33_2e0 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m33]; exact a32_2e0
  have a33_380 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m33]; exact a32_380
  have a33_400 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m33]; exact a32_400
  have a33_13e0 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := by rw [m33]; exact a32_13e0
  have a33_1460 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := by rw [m33]; exact a32_1460
  have a33_1588 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U2 := by rw [m33]; exact a32_1588
  have p33_320 : ptF n33.mem B 0x320 = P0 := by rw [m33]; exact p32_320
  have p33_3a0 : ptF n33.mem B 0x3A0 = P1 := by rw [m33]; exact p32_3a0
  have p33_420 : ptF n33.mem B 0x420 = tbl2 P0 0 := by rw [m33]; exact p32_420
  have p33_480 : ptF n33.mem B 0x480 = tbl2 P0 1 := by rw [m33]; exact p32_480
  have p33_4e0 : ptF n33.mem B 0x4E0 = tbl2 P0 2 := by rw [m33]; exact p32_4e0
  have p33_540 : ptF n33.mem B 0x540 = tbl2 P0 3 := by rw [m33]; exact p32_540
  have p33_5a0 : ptF n33.mem B 0x5A0 = tbl2 P0 4 := by rw [m33]; exact p32_5a0
  have p33_600 : ptF n33.mem B 0x600 = tbl2 P0 5 := by rw [m33]; exact p32_600
  have p33_660 : ptF n33.mem B 0x660 = tbl2 P0 6 := by rw [m33]; exact p32_660
  have p33_6c0 : ptF n33.mem B 0x6C0 = tbl2 P0 7 := by rw [m33]; exact p32_6c0
  have p33_720 : ptF n33.mem B 0x720 = tbl2 P1 0 := by rw [m33]; exact p32_720
  have p33_780 : ptF n33.mem B 0x780 = tbl2 P1 1 := by rw [m33]; exact p32_780
  have p33_7e0 : ptF n33.mem B 0x7E0 = tbl2 P1 2 := by rw [m33]; exact p32_7e0
  have p33_840 : ptF n33.mem B 0x840 = tbl2 P1 3 := by rw [m33]; exact p32_840
  have p33_8a0 : ptF n33.mem B 0x8A0 = tbl2 P1 4 := by rw [m33]; exact p32_8a0
  have p33_900 : ptF n33.mem B 0x900 = tbl2 P1 5 := by rw [m33]; exact p32_900
  have p33_960 : ptF n33.mem B 0x960 = tbl2 P1 6 := by rw [m33]; exact p32_960
  have p33_9c0 : ptF n33.mem B 0x9C0 = tbl2 P1 7 := by rw [m33]; exact p32_9c0
  have p33_b40 : ptF n33.mem B 0xB40 = tbl2 P0 3 := by rw [m33]; exact p32_b40
  have p33_ba0 : ptF n33.mem B 0xBA0 = tbl2 P0 4 := by rw [m33]; exact p32_ba0
  have p33_c00 : ptF n33.mem B 0xC00 = tbl2 P0 5 := by rw [m33]; exact p32_c00
  have p33_c60 : ptF n33.mem B 0xC60 = tbl2 P0 6 := by rw [m33]; exact p32_c60
  have p33_cc0 : ptF n33.mem B 0xCC0 = tbl2 P0 7 := by rw [m33]; exact p32_cc0
  have p33_d20 : ptF n33.mem B 0xD20 = tbl2 P1 0 := by rw [m33]; exact p32_d20
  have p33_d80 : ptF n33.mem B 0xD80 = tbl2 P1 1 := by rw [m33]; exact p32_d80
  have p33_de0 : ptF n33.mem B 0xDE0 = tbl2 P1 2 := by rw [m33]; exact p32_de0
  have p33_e40 : ptF n33.mem B 0xE40 = tbl2 P1 3 := by rw [m33]; exact p32_e40
  have p33_ea0 : ptF n33.mem B 0xEA0 = tbl2 P1 4 := by rw [m33]; exact p32_ea0
  have p33_f00 : ptF n33.mem B 0xF00 = tbl2 P1 5 := by rw [m33]; exact p32_f00
  have p33_f60 : ptF n33.mem B 0xF60 = tbl2 P1 6 := by rw [m33]; exact p32_f60
  have p33_fc0 : ptF n33.mem B 0xFC0 = tbl2 P1 7 := by rw [m33]; exact p32_fc0
  have p33_1380 : ptF n33.mem B 0x1380 = P0 := by rw [m33]; exact p32_1380
  have p33_1400 : ptF n33.mem B 0x1400 = P1 := by rw [m33]; exact p32_1400
  have mb33_a24 : memBytes n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m33]; exact mb32_a24
  have mb33_1024 : memBytes n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m33]; exact mb32_1024
  have mb33_1320 : leN (memBytes n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U1 := by rw [m33]; exact mb32_1320
  have mb33_1480 : leN (memBytes n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 0x20).reverse = U2 := by rw [m33]; exact mb32_1480
  clear mb32_1480 mb32_1320 mb32_1024 mb32_a24 p32_1400 p32_1380 p32_fc0 p32_f60 p32_f00 p32_ea0 p32_e40 p32_de0 p32_d80 p32_d20 p32_cc0 p32_c60 p32_c00 p32_ba0 p32_b40 p32_9c0 p32_960 p32_900 p32_8a0 p32_840 p32_7e0 p32_780 p32_720 p32_6c0 p32_660 p32_600 p32_5a0 p32_540 p32_4e0 p32_480 p32_420 p32_3a0 p32_320 a32_1588 a32_1460 a32_13e0 a32_400 a32_380 a32_2e0 a32_2c0 a32_2a0 w32_1020 w32_a20 w32_130 w32_12c w32_128 w32_124 w32_120 w32_11c w32_118 w32_114 w32_110 w32_10c w32_108 w32_104 w32_100 w32_fc w32_f8 w32_f4 w32_f0 w32_ec w32_e8 w32_e4 w32_e0 w32_dc w32_d8 w32_d4 w32_d0 w32_cc w32_c8 w32_c4 w32_c0 w32_bc w32_b8 w32_b4 w32_b0 w32_ac w32_a8 w32_a4 w32_a0 w32_9c w32_98 w32_94 w32_90 w32_8c w32_88 w32_84 w32_80 w32_7c w32_78 w32_70 w32_6c w32_68 w32_64 w32_60 w32_5c w32_58 w32_54 w32_50 w32_4c w32_48 w32_44 w32_40 w32_3c w32_38 w32_34 w32_30 w32_2c w32_28 w32_24 g32_27 g32_26 g32_25 g32_24 g32_23 g32_22 g32_21 g32_20 g32_19 g32_18 g32_9 g32_8 g32_4 g32_3 g32_2 V32 E32 fR32 t32 fr32 s32 L32 K32 P32
  -- 0x181C: reverse
  obtain ⟨n34, P34, K34, R34⟩ := sv_rev (c := 0x1480) (N := 0x20) F E33 (WN0.sv F fR33) s33
    sv_at_181c sv_at_1820 (by decide) (by decide) g33_10 g33_11 (by decide)
  have mbr34 := mb33_1480
  have s34 := P34.st
  have fr34 := P34.fr
  have t34 : Steps n0 n34 := t33.trans P34.steps
  have fR34 : ∀ x, SvR B x → n34.mem x = M0 x := fun x hx => (fr34 x hx).trans (fR33 x hx)
  have E34 : SvCode n34.mem := E33.fr F fr34
  have V34 : SvSaves B n34.mem v := V33.keep K34 (by decide)
  have g34_2 : reg n34 sp = B + 0x21A0 := by rw [P34.regs sp (by decide), g33_2]
  have g34_3 : reg n34 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P34.regs (3 : Fin 32) (by decide), g33_3]
  have g34_4 : reg n34 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P34.regs (4 : Fin 32) (by decide), g33_4]
  have g34_8 : reg n34 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P34.regs (8 : Fin 32) (by decide), g33_8]
  have g34_9 : reg n34 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1400 := by rw [P34.regs (9 : Fin 32) (by decide), g33_9]
  have g34_18 : reg n34 (18 : Fin 32) = out := by rw [P34.regs (18 : Fin 32) (by decide), g33_18]
  have g34_19 : reg n34 (19 : Fin 32) = bp := by rw [P34.regs (19 : Fin 32) (by decide), g33_19]
  have g34_20 : reg n34 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P34.regs (20 : Fin 32) (by decide), g33_20]
  have g34_21 : reg n34 (21 : Fin 32) = s5v := by rw [P34.regs (21 : Fin 32) (by decide), g33_21]
  have g34_22 : reg n34 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [P34.regs (22 : Fin 32) (by decide), g33_22]
  have g34_23 : reg n34 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by rw [P34.regs (23 : Fin 32) (by decide), g33_23]
  have g34_24 : reg n34 (24 : Fin 32) = s8v := by rw [P34.regs (24 : Fin 32) (by decide), g33_24]
  have g34_25 : reg n34 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P34.regs (25 : Fin 32) (by decide), g33_25]
  have g34_26 : reg n34 (26 : Fin 32) = x26 := by rw [P34.regs (26 : Fin 32) (by decide), g33_26]
  have g34_27 : reg n34 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P34.regs (27 : Fin 32) (by decide), g33_27]
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
  have w34_a20 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := (K34.w32 (by decide) (by decide)).trans w33_a20
  have w34_1020 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := (K34.w32 (by decide) (by decide)).trans w33_1020
  have a34_2a0 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K34.acc (by decide) (by decide)).trans a33_2a0
  have a34_2c0 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K34.acc (by decide) (by decide)).trans a33_2c0
  have a34_2e0 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K34.acc (by decide) (by decide)).trans a33_2e0
  have a34_380 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := (K34.acc (by decide) (by decide)).trans a33_380
  have a34_400 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := (K34.acc (by decide) (by decide)).trans a33_400
  have a34_13e0 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := (K34.acc (by decide) (by decide)).trans a33_13e0
  have a34_1460 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := (K34.acc (by decide) (by decide)).trans a33_1460
  have a34_1588 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U2 := (K34.acc (by decide) (by decide)).trans a33_1588
  have p34_320 : ptF n34.mem B 0x320 = P0 := (K34.pt (by decide) (by decide)).trans p33_320
  have p34_3a0 : ptF n34.mem B 0x3A0 = P1 := (K34.pt (by decide) (by decide)).trans p33_3a0
  have p34_420 : ptF n34.mem B 0x420 = tbl2 P0 0 := (K34.pt (by decide) (by decide)).trans p33_420
  have p34_480 : ptF n34.mem B 0x480 = tbl2 P0 1 := (K34.pt (by decide) (by decide)).trans p33_480
  have p34_4e0 : ptF n34.mem B 0x4E0 = tbl2 P0 2 := (K34.pt (by decide) (by decide)).trans p33_4e0
  have p34_540 : ptF n34.mem B 0x540 = tbl2 P0 3 := (K34.pt (by decide) (by decide)).trans p33_540
  have p34_5a0 : ptF n34.mem B 0x5A0 = tbl2 P0 4 := (K34.pt (by decide) (by decide)).trans p33_5a0
  have p34_600 : ptF n34.mem B 0x600 = tbl2 P0 5 := (K34.pt (by decide) (by decide)).trans p33_600
  have p34_660 : ptF n34.mem B 0x660 = tbl2 P0 6 := (K34.pt (by decide) (by decide)).trans p33_660
  have p34_6c0 : ptF n34.mem B 0x6C0 = tbl2 P0 7 := (K34.pt (by decide) (by decide)).trans p33_6c0
  have p34_720 : ptF n34.mem B 0x720 = tbl2 P1 0 := (K34.pt (by decide) (by decide)).trans p33_720
  have p34_780 : ptF n34.mem B 0x780 = tbl2 P1 1 := (K34.pt (by decide) (by decide)).trans p33_780
  have p34_7e0 : ptF n34.mem B 0x7E0 = tbl2 P1 2 := (K34.pt (by decide) (by decide)).trans p33_7e0
  have p34_840 : ptF n34.mem B 0x840 = tbl2 P1 3 := (K34.pt (by decide) (by decide)).trans p33_840
  have p34_8a0 : ptF n34.mem B 0x8A0 = tbl2 P1 4 := (K34.pt (by decide) (by decide)).trans p33_8a0
  have p34_900 : ptF n34.mem B 0x900 = tbl2 P1 5 := (K34.pt (by decide) (by decide)).trans p33_900
  have p34_960 : ptF n34.mem B 0x960 = tbl2 P1 6 := (K34.pt (by decide) (by decide)).trans p33_960
  have p34_9c0 : ptF n34.mem B 0x9C0 = tbl2 P1 7 := (K34.pt (by decide) (by decide)).trans p33_9c0
  have p34_b40 : ptF n34.mem B 0xB40 = tbl2 P0 3 := (K34.pt (by decide) (by decide)).trans p33_b40
  have p34_ba0 : ptF n34.mem B 0xBA0 = tbl2 P0 4 := (K34.pt (by decide) (by decide)).trans p33_ba0
  have p34_c00 : ptF n34.mem B 0xC00 = tbl2 P0 5 := (K34.pt (by decide) (by decide)).trans p33_c00
  have p34_c60 : ptF n34.mem B 0xC60 = tbl2 P0 6 := (K34.pt (by decide) (by decide)).trans p33_c60
  have p34_cc0 : ptF n34.mem B 0xCC0 = tbl2 P0 7 := (K34.pt (by decide) (by decide)).trans p33_cc0
  have p34_d20 : ptF n34.mem B 0xD20 = tbl2 P1 0 := (K34.pt (by decide) (by decide)).trans p33_d20
  have p34_d80 : ptF n34.mem B 0xD80 = tbl2 P1 1 := (K34.pt (by decide) (by decide)).trans p33_d80
  have p34_de0 : ptF n34.mem B 0xDE0 = tbl2 P1 2 := (K34.pt (by decide) (by decide)).trans p33_de0
  have p34_e40 : ptF n34.mem B 0xE40 = tbl2 P1 3 := (K34.pt (by decide) (by decide)).trans p33_e40
  have p34_ea0 : ptF n34.mem B 0xEA0 = tbl2 P1 4 := (K34.pt (by decide) (by decide)).trans p33_ea0
  have p34_f00 : ptF n34.mem B 0xF00 = tbl2 P1 5 := (K34.pt (by decide) (by decide)).trans p33_f00
  have p34_f60 : ptF n34.mem B 0xF60 = tbl2 P1 6 := (K34.pt (by decide) (by decide)).trans p33_f60
  have p34_fc0 : ptF n34.mem B 0xFC0 = tbl2 P1 7 := (K34.pt (by decide) (by decide)).trans p33_fc0
  have p34_1380 : ptF n34.mem B 0x1380 = P0 := (K34.pt (by decide) (by decide)).trans p33_1380
  have p34_1400 : ptF n34.mem B 0x1400 = P1 := (K34.pt (by decide) (by decide)).trans p33_1400
  have mb34_a24 : memBytes n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [K34.mb (by decide) (by decide)]; exact mb33_a24
  have mb34_1024 : memBytes n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [K34.mb (by decide) (by decide)]; exact mb33_1024
  have mb34_1320 : leN (memBytes n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U1 := by rw [K34.mb (by decide) (by decide)]; exact mb33_1320
  have mb34_1480 : leN (memBytes n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 0x20) = U2 := by rw [R34]; exact mbr34
  clear mb33_1480 mb33_1320 mb33_1024 mb33_a24 p33_1400 p33_1380 p33_fc0 p33_f60 p33_f00 p33_ea0 p33_e40 p33_de0 p33_d80 p33_d20 p33_cc0 p33_c60 p33_c00 p33_ba0 p33_b40 p33_9c0 p33_960 p33_900 p33_8a0 p33_840 p33_7e0 p33_780 p33_720 p33_6c0 p33_660 p33_600 p33_5a0 p33_540 p33_4e0 p33_480 p33_420 p33_3a0 p33_320 a33_1588 a33_1460 a33_13e0 a33_400 a33_380 a33_2e0 a33_2c0 a33_2a0 w33_1020 w33_a20 w33_130 w33_12c w33_128 w33_124 w33_120 w33_11c w33_118 w33_114 w33_110 w33_10c w33_108 w33_104 w33_100 w33_fc w33_f8 w33_f4 w33_f0 w33_ec w33_e8 w33_e4 w33_e0 w33_dc w33_d8 w33_d4 w33_d0 w33_cc w33_c8 w33_c4 w33_c0 w33_bc w33_b8 w33_b4 w33_b0 w33_ac w33_a8 w33_a4 w33_a0 w33_9c w33_98 w33_94 w33_90 w33_8c w33_88 w33_84 w33_80 w33_7c w33_78 w33_70 w33_6c w33_68 w33_64 w33_60 w33_5c w33_58 w33_54 w33_50 w33_4c w33_48 w33_44 w33_40 w33_3c w33_38 w33_34 w33_30 w33_2c w33_28 w33_24 g33_11 g33_10 g33_27 g33_26 g33_25 g33_24 g33_23 g33_22 g33_21 g33_20 g33_19 g33_18 g33_9 g33_8 g33_4 g33_3 g33_2 V33 E33 fR33 t33 fr33 rb33 s33 m33 u33 c33
  -- 0x1824
  obtain ⟨n35, c35, u35⟩ := s34.block svEcW1824 E34.self svEcW1824_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m35 : n35.mem = n34.mem := u35.mem
  have s35 : St n35.mem SV n35 0x1838 (reg n35) := ⟨u35.pc, rfl, fun _ => rfl⟩
  have rb35 : ∀ q, reg n35 q = (runBlock svEcW1824 (n34.mem, reg n34)).2 q := fun q => by rw [u35.regs]
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
  have g35_8 : reg n35 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb35, runBlock_reg _ _ _ (8 : Fin 32) s34.zero (by decide), g34_8]
  have g35_9 : reg n35 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1400 := by
    rw [rb35, runBlock_reg _ _ _ (9 : Fin 32) s34.zero (by decide), g34_9]
  have g35_18 : reg n35 (18 : Fin 32) = out := by
    rw [rb35, runBlock_reg _ _ _ (18 : Fin 32) s34.zero (by decide), g34_18]
  have g35_19 : reg n35 (19 : Fin 32) = bp := by
    rw [rb35, runBlock_reg _ _ _ (19 : Fin 32) s34.zero (by decide), g34_19]
  have g35_20 : reg n35 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb35, runBlock_reg _ _ _ (20 : Fin 32) s34.zero (by decide), g34_20]
  have g35_21 : reg n35 (21 : Fin 32) = s5v := by
    rw [rb35, runBlock_reg _ _ _ (21 : Fin 32) s34.zero (by decide), g34_21]
  have g35_22 : reg n35 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by
    rw [rb35, runBlock_reg _ _ _ (22 : Fin 32) s34.zero (by decide), g34_22]
  have g35_23 : reg n35 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by
    rw [rb35, runBlock_reg _ _ _ (23 : Fin 32) s34.zero (by decide), g34_23]
  have g35_24 : reg n35 (24 : Fin 32) = s8v := by
    rw [rb35, runBlock_reg _ _ _ (24 : Fin 32) s34.zero (by decide), g34_24]
  have g35_25 : reg n35 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb35, runBlock_reg _ _ _ (25 : Fin 32) s34.zero (by decide), g34_25]
  have g35_26 : reg n35 (26 : Fin 32) = x26 := by
    rw [rb35, runBlock_reg _ _ _ (26 : Fin 32) s34.zero (by decide), g34_26]
  have g35_27 : reg n35 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb35, runBlock_reg _ _ _ (27 : Fin 32) s34.zero (by decide), g34_27]
  have g35_10 : reg n35 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
    rw [rb35]; simp +decide only [runBlock, BInstr.run, svEcW1824, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g34_2, g34_3, g34_4, g34_8, g34_9, g34_18, g34_19, g34_20, g34_21, g34_22, g34_23, g34_24, g34_25, g34_26, g34_27, s34.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g35_11 : reg n35 a1 = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by
    rw [rb35]; simp +decide only [runBlock, BInstr.run, svEcW1824, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g34_2, g34_3, g34_4, g34_8, g34_9, g34_18, g34_19, g34_20, g34_21, g34_22, g34_23, g34_24, g34_25, g34_26, g34_27, s34.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g35_12 : reg n35 a2 = BitVec.ofNat 32 0x20 := by
    rw [rb35]; simp +decide only [runBlock, BInstr.run, svEcW1824, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g34_2, g34_3, g34_4, g34_8, g34_9, g34_18, g34_19, g34_20, g34_21, g34_22, g34_23, g34_24, g34_25, g34_26, g34_27, s34.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
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
  have w35_a20 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m35]; exact w34_a20
  have w35_1020 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m35]; exact w34_1020
  have a35_2a0 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m35]; exact a34_2a0
  have a35_2c0 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m35]; exact a34_2c0
  have a35_2e0 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m35]; exact a34_2e0
  have a35_380 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m35]; exact a34_380
  have a35_400 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m35]; exact a34_400
  have a35_13e0 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := by rw [m35]; exact a34_13e0
  have a35_1460 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := by rw [m35]; exact a34_1460
  have a35_1588 : accV n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U2 := by rw [m35]; exact a34_1588
  have p35_320 : ptF n35.mem B 0x320 = P0 := by rw [m35]; exact p34_320
  have p35_3a0 : ptF n35.mem B 0x3A0 = P1 := by rw [m35]; exact p34_3a0
  have p35_420 : ptF n35.mem B 0x420 = tbl2 P0 0 := by rw [m35]; exact p34_420
  have p35_480 : ptF n35.mem B 0x480 = tbl2 P0 1 := by rw [m35]; exact p34_480
  have p35_4e0 : ptF n35.mem B 0x4E0 = tbl2 P0 2 := by rw [m35]; exact p34_4e0
  have p35_540 : ptF n35.mem B 0x540 = tbl2 P0 3 := by rw [m35]; exact p34_540
  have p35_5a0 : ptF n35.mem B 0x5A0 = tbl2 P0 4 := by rw [m35]; exact p34_5a0
  have p35_600 : ptF n35.mem B 0x600 = tbl2 P0 5 := by rw [m35]; exact p34_600
  have p35_660 : ptF n35.mem B 0x660 = tbl2 P0 6 := by rw [m35]; exact p34_660
  have p35_6c0 : ptF n35.mem B 0x6C0 = tbl2 P0 7 := by rw [m35]; exact p34_6c0
  have p35_720 : ptF n35.mem B 0x720 = tbl2 P1 0 := by rw [m35]; exact p34_720
  have p35_780 : ptF n35.mem B 0x780 = tbl2 P1 1 := by rw [m35]; exact p34_780
  have p35_7e0 : ptF n35.mem B 0x7E0 = tbl2 P1 2 := by rw [m35]; exact p34_7e0
  have p35_840 : ptF n35.mem B 0x840 = tbl2 P1 3 := by rw [m35]; exact p34_840
  have p35_8a0 : ptF n35.mem B 0x8A0 = tbl2 P1 4 := by rw [m35]; exact p34_8a0
  have p35_900 : ptF n35.mem B 0x900 = tbl2 P1 5 := by rw [m35]; exact p34_900
  have p35_960 : ptF n35.mem B 0x960 = tbl2 P1 6 := by rw [m35]; exact p34_960
  have p35_9c0 : ptF n35.mem B 0x9C0 = tbl2 P1 7 := by rw [m35]; exact p34_9c0
  have p35_b40 : ptF n35.mem B 0xB40 = tbl2 P0 3 := by rw [m35]; exact p34_b40
  have p35_ba0 : ptF n35.mem B 0xBA0 = tbl2 P0 4 := by rw [m35]; exact p34_ba0
  have p35_c00 : ptF n35.mem B 0xC00 = tbl2 P0 5 := by rw [m35]; exact p34_c00
  have p35_c60 : ptF n35.mem B 0xC60 = tbl2 P0 6 := by rw [m35]; exact p34_c60
  have p35_cc0 : ptF n35.mem B 0xCC0 = tbl2 P0 7 := by rw [m35]; exact p34_cc0
  have p35_d20 : ptF n35.mem B 0xD20 = tbl2 P1 0 := by rw [m35]; exact p34_d20
  have p35_d80 : ptF n35.mem B 0xD80 = tbl2 P1 1 := by rw [m35]; exact p34_d80
  have p35_de0 : ptF n35.mem B 0xDE0 = tbl2 P1 2 := by rw [m35]; exact p34_de0
  have p35_e40 : ptF n35.mem B 0xE40 = tbl2 P1 3 := by rw [m35]; exact p34_e40
  have p35_ea0 : ptF n35.mem B 0xEA0 = tbl2 P1 4 := by rw [m35]; exact p34_ea0
  have p35_f00 : ptF n35.mem B 0xF00 = tbl2 P1 5 := by rw [m35]; exact p34_f00
  have p35_f60 : ptF n35.mem B 0xF60 = tbl2 P1 6 := by rw [m35]; exact p34_f60
  have p35_fc0 : ptF n35.mem B 0xFC0 = tbl2 P1 7 := by rw [m35]; exact p34_fc0
  have p35_1380 : ptF n35.mem B 0x1380 = P0 := by rw [m35]; exact p34_1380
  have p35_1400 : ptF n35.mem B 0x1400 = P1 := by rw [m35]; exact p34_1400
  have mb35_a24 : memBytes n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m35]; exact mb34_a24
  have mb35_1024 : memBytes n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m35]; exact mb34_1024
  have mb35_1320 : leN (memBytes n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U1 := by rw [m35]; exact mb34_1320
  have mb35_1480 : leN (memBytes n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 0x20) = U2 := by rw [m35]; exact mb34_1480
  clear mb34_1480 mb34_1320 mb34_1024 mb34_a24 p34_1400 p34_1380 p34_fc0 p34_f60 p34_f00 p34_ea0 p34_e40 p34_de0 p34_d80 p34_d20 p34_cc0 p34_c60 p34_c00 p34_ba0 p34_b40 p34_9c0 p34_960 p34_900 p34_8a0 p34_840 p34_7e0 p34_780 p34_720 p34_6c0 p34_660 p34_600 p34_5a0 p34_540 p34_4e0 p34_480 p34_420 p34_3a0 p34_320 a34_1588 a34_1460 a34_13e0 a34_400 a34_380 a34_2e0 a34_2c0 a34_2a0 w34_1020 w34_a20 w34_130 w34_12c w34_128 w34_124 w34_120 w34_11c w34_118 w34_114 w34_110 w34_10c w34_108 w34_104 w34_100 w34_fc w34_f8 w34_f4 w34_f0 w34_ec w34_e8 w34_e4 w34_e0 w34_dc w34_d8 w34_d4 w34_d0 w34_cc w34_c8 w34_c4 w34_c0 w34_bc w34_b8 w34_b4 w34_b0 w34_ac w34_a8 w34_a4 w34_a0 w34_9c w34_98 w34_94 w34_90 w34_8c w34_88 w34_84 w34_80 w34_7c w34_78 w34_70 w34_6c w34_68 w34_64 w34_60 w34_5c w34_58 w34_54 w34_50 w34_4c w34_48 w34_44 w34_40 w34_3c w34_38 w34_34 w34_30 w34_2c w34_28 w34_24 g34_27 g34_26 g34_25 g34_24 g34_23 g34_22 g34_21 g34_20 g34_19 g34_18 g34_9 g34_8 g34_4 g34_3 g34_2 V34 E34 fR34 t34 fr34 s34 mbr34 R34 K34 P34
  -- 0x1838: memcpy
  obtain ⟨n36, P36, K36, X36⟩ := sv_mc (c := 0x1320) (d := 0x1480) (N := 0x20) F E35 s35 sv_at_1838 sv_at_183c
    (by decide) (by decide) g35_2 g35_10 g35_11 g35_12
    (by decide) (by decide) (by decide)
  have s36 := P36.st
  have fr36 := P36.fr
  have t36 : Steps n0 n36 := t35.trans P36.steps
  have fR36 : ∀ x, SvR B x → n36.mem x = M0 x := fun x hx => (fr36 x hx).trans (fR35 x hx)
  have E36 : SvCode n36.mem := E35.fr F fr36
  have V36 : SvSaves B n36.mem v := V35.keep K36 (by decide)
  have g36_2 : reg n36 sp = B + 0x21A0 := by rw [P36.regs sp (by decide), g35_2]
  have g36_3 : reg n36 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P36.regs (3 : Fin 32) (by decide), g35_3]
  have g36_4 : reg n36 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P36.regs (4 : Fin 32) (by decide), g35_4]
  have g36_8 : reg n36 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P36.regs (8 : Fin 32) (by decide), g35_8]
  have g36_9 : reg n36 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1400 := by rw [P36.regs (9 : Fin 32) (by decide), g35_9]
  have g36_18 : reg n36 (18 : Fin 32) = out := by rw [P36.regs (18 : Fin 32) (by decide), g35_18]
  have g36_19 : reg n36 (19 : Fin 32) = bp := by rw [P36.regs (19 : Fin 32) (by decide), g35_19]
  have g36_20 : reg n36 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P36.regs (20 : Fin 32) (by decide), g35_20]
  have g36_21 : reg n36 (21 : Fin 32) = s5v := by rw [P36.regs (21 : Fin 32) (by decide), g35_21]
  have g36_22 : reg n36 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [P36.regs (22 : Fin 32) (by decide), g35_22]
  have g36_23 : reg n36 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by rw [P36.regs (23 : Fin 32) (by decide), g35_23]
  have g36_24 : reg n36 (24 : Fin 32) = s8v := by rw [P36.regs (24 : Fin 32) (by decide), g35_24]
  have g36_25 : reg n36 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P36.regs (25 : Fin 32) (by decide), g35_25]
  have g36_26 : reg n36 (26 : Fin 32) = x26 := by rw [P36.regs (26 : Fin 32) (by decide), g35_26]
  have g36_27 : reg n36 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P36.regs (27 : Fin 32) (by decide), g35_27]
  have w36_24 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K36.w32 (by decide) (by decide)).trans w35_24
  have w36_28 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K36.w32 (by decide) (by decide)).trans w35_28
  have w36_2c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K36.w32 (by decide) (by decide)).trans w35_2c
  have w36_30 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K36.w32 (by decide) (by decide)).trans w35_30
  have w36_34 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K36.w32 (by decide) (by decide)).trans w35_34
  have w36_38 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K36.w32 (by decide) (by decide)).trans w35_38
  have w36_3c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K36.w32 (by decide) (by decide)).trans w35_3c
  have w36_40 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K36.w32 (by decide) (by decide)).trans w35_40
  have w36_44 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K36.w32 (by decide) (by decide)).trans w35_44
  have w36_48 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K36.w32 (by decide) (by decide)).trans w35_48
  have w36_4c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K36.w32 (by decide) (by decide)).trans w35_4c
  have w36_50 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K36.w32 (by decide) (by decide)).trans w35_50
  have w36_54 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K36.w32 (by decide) (by decide)).trans w35_54
  have w36_58 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K36.w32 (by decide) (by decide)).trans w35_58
  have w36_5c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K36.w32 (by decide) (by decide)).trans w35_5c
  have w36_60 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K36.w32 (by decide) (by decide)).trans w35_60
  have w36_64 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K36.w32 (by decide) (by decide)).trans w35_64
  have w36_68 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K36.w32 (by decide) (by decide)).trans w35_68
  have w36_6c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K36.w32 (by decide) (by decide)).trans w35_6c
  have w36_70 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K36.w32 (by decide) (by decide)).trans w35_70
  have w36_78 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := (K36.w32 (by decide) (by decide)).trans w35_78
  have w36_7c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K36.w32 (by decide) (by decide)).trans w35_7c
  have w36_80 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K36.w32 (by decide) (by decide)).trans w35_80
  have w36_84 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K36.w32 (by decide) (by decide)).trans w35_84
  have w36_88 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K36.w32 (by decide) (by decide)).trans w35_88
  have w36_8c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K36.w32 (by decide) (by decide)).trans w35_8c
  have w36_90 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K36.w32 (by decide) (by decide)).trans w35_90
  have w36_94 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K36.w32 (by decide) (by decide)).trans w35_94
  have w36_98 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K36.w32 (by decide) (by decide)).trans w35_98
  have w36_9c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K36.w32 (by decide) (by decide)).trans w35_9c
  have w36_a0 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K36.w32 (by decide) (by decide)).trans w35_a0
  have w36_a4 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K36.w32 (by decide) (by decide)).trans w35_a4
  have w36_a8 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K36.w32 (by decide) (by decide)).trans w35_a8
  have w36_ac : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K36.w32 (by decide) (by decide)).trans w35_ac
  have w36_b0 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K36.w32 (by decide) (by decide)).trans w35_b0
  have w36_b4 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K36.w32 (by decide) (by decide)).trans w35_b4
  have w36_b8 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K36.w32 (by decide) (by decide)).trans w35_b8
  have w36_bc : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K36.w32 (by decide) (by decide)).trans w35_bc
  have w36_c0 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K36.w32 (by decide) (by decide)).trans w35_c0
  have w36_c4 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K36.w32 (by decide) (by decide)).trans w35_c4
  have w36_c8 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K36.w32 (by decide) (by decide)).trans w35_c8
  have w36_cc : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K36.w32 (by decide) (by decide)).trans w35_cc
  have w36_d0 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K36.w32 (by decide) (by decide)).trans w35_d0
  have w36_d4 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K36.w32 (by decide) (by decide)).trans w35_d4
  have w36_d8 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K36.w32 (by decide) (by decide)).trans w35_d8
  have w36_dc : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K36.w32 (by decide) (by decide)).trans w35_dc
  have w36_e0 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K36.w32 (by decide) (by decide)).trans w35_e0
  have w36_e4 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K36.w32 (by decide) (by decide)).trans w35_e4
  have w36_e8 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K36.w32 (by decide) (by decide)).trans w35_e8
  have w36_ec : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K36.w32 (by decide) (by decide)).trans w35_ec
  have w36_f0 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K36.w32 (by decide) (by decide)).trans w35_f0
  have w36_f4 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K36.w32 (by decide) (by decide)).trans w35_f4
  have w36_f8 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K36.w32 (by decide) (by decide)).trans w35_f8
  have w36_fc : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K36.w32 (by decide) (by decide)).trans w35_fc
  have w36_100 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K36.w32 (by decide) (by decide)).trans w35_100
  have w36_104 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K36.w32 (by decide) (by decide)).trans w35_104
  have w36_108 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K36.w32 (by decide) (by decide)).trans w35_108
  have w36_10c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K36.w32 (by decide) (by decide)).trans w35_10c
  have w36_110 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K36.w32 (by decide) (by decide)).trans w35_110
  have w36_114 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K36.w32 (by decide) (by decide)).trans w35_114
  have w36_118 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K36.w32 (by decide) (by decide)).trans w35_118
  have w36_11c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K36.w32 (by decide) (by decide)).trans w35_11c
  have w36_120 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K36.w32 (by decide) (by decide)).trans w35_120
  have w36_124 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K36.w32 (by decide) (by decide)).trans w35_124
  have w36_128 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K36.w32 (by decide) (by decide)).trans w35_128
  have w36_12c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K36.w32 (by decide) (by decide)).trans w35_12c
  have w36_130 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K36.w32 (by decide) (by decide)).trans w35_130
  have w36_a20 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := (K36.w32 (by decide) (by decide)).trans w35_a20
  have w36_1020 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := (K36.w32 (by decide) (by decide)).trans w35_1020
  have a36_2a0 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K36.acc (by decide) (by decide)).trans a35_2a0
  have a36_2c0 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K36.acc (by decide) (by decide)).trans a35_2c0
  have a36_2e0 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K36.acc (by decide) (by decide)).trans a35_2e0
  have a36_380 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := (K36.acc (by decide) (by decide)).trans a35_380
  have a36_400 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := (K36.acc (by decide) (by decide)).trans a35_400
  have a36_13e0 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := (K36.acc (by decide) (by decide)).trans a35_13e0
  have a36_1460 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := (K36.acc (by decide) (by decide)).trans a35_1460
  have a36_1588 : accV n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U2 := (K36.acc (by decide) (by decide)).trans a35_1588
  have p36_320 : ptF n36.mem B 0x320 = P0 := (K36.pt (by decide) (by decide)).trans p35_320
  have p36_3a0 : ptF n36.mem B 0x3A0 = P1 := (K36.pt (by decide) (by decide)).trans p35_3a0
  have p36_420 : ptF n36.mem B 0x420 = tbl2 P0 0 := (K36.pt (by decide) (by decide)).trans p35_420
  have p36_480 : ptF n36.mem B 0x480 = tbl2 P0 1 := (K36.pt (by decide) (by decide)).trans p35_480
  have p36_4e0 : ptF n36.mem B 0x4E0 = tbl2 P0 2 := (K36.pt (by decide) (by decide)).trans p35_4e0
  have p36_540 : ptF n36.mem B 0x540 = tbl2 P0 3 := (K36.pt (by decide) (by decide)).trans p35_540
  have p36_5a0 : ptF n36.mem B 0x5A0 = tbl2 P0 4 := (K36.pt (by decide) (by decide)).trans p35_5a0
  have p36_600 : ptF n36.mem B 0x600 = tbl2 P0 5 := (K36.pt (by decide) (by decide)).trans p35_600
  have p36_660 : ptF n36.mem B 0x660 = tbl2 P0 6 := (K36.pt (by decide) (by decide)).trans p35_660
  have p36_6c0 : ptF n36.mem B 0x6C0 = tbl2 P0 7 := (K36.pt (by decide) (by decide)).trans p35_6c0
  have p36_720 : ptF n36.mem B 0x720 = tbl2 P1 0 := (K36.pt (by decide) (by decide)).trans p35_720
  have p36_780 : ptF n36.mem B 0x780 = tbl2 P1 1 := (K36.pt (by decide) (by decide)).trans p35_780
  have p36_7e0 : ptF n36.mem B 0x7E0 = tbl2 P1 2 := (K36.pt (by decide) (by decide)).trans p35_7e0
  have p36_840 : ptF n36.mem B 0x840 = tbl2 P1 3 := (K36.pt (by decide) (by decide)).trans p35_840
  have p36_8a0 : ptF n36.mem B 0x8A0 = tbl2 P1 4 := (K36.pt (by decide) (by decide)).trans p35_8a0
  have p36_900 : ptF n36.mem B 0x900 = tbl2 P1 5 := (K36.pt (by decide) (by decide)).trans p35_900
  have p36_960 : ptF n36.mem B 0x960 = tbl2 P1 6 := (K36.pt (by decide) (by decide)).trans p35_960
  have p36_9c0 : ptF n36.mem B 0x9C0 = tbl2 P1 7 := (K36.pt (by decide) (by decide)).trans p35_9c0
  have p36_b40 : ptF n36.mem B 0xB40 = tbl2 P0 3 := (K36.pt (by decide) (by decide)).trans p35_b40
  have p36_ba0 : ptF n36.mem B 0xBA0 = tbl2 P0 4 := (K36.pt (by decide) (by decide)).trans p35_ba0
  have p36_c00 : ptF n36.mem B 0xC00 = tbl2 P0 5 := (K36.pt (by decide) (by decide)).trans p35_c00
  have p36_c60 : ptF n36.mem B 0xC60 = tbl2 P0 6 := (K36.pt (by decide) (by decide)).trans p35_c60
  have p36_cc0 : ptF n36.mem B 0xCC0 = tbl2 P0 7 := (K36.pt (by decide) (by decide)).trans p35_cc0
  have p36_d20 : ptF n36.mem B 0xD20 = tbl2 P1 0 := (K36.pt (by decide) (by decide)).trans p35_d20
  have p36_d80 : ptF n36.mem B 0xD80 = tbl2 P1 1 := (K36.pt (by decide) (by decide)).trans p35_d80
  have p36_de0 : ptF n36.mem B 0xDE0 = tbl2 P1 2 := (K36.pt (by decide) (by decide)).trans p35_de0
  have p36_e40 : ptF n36.mem B 0xE40 = tbl2 P1 3 := (K36.pt (by decide) (by decide)).trans p35_e40
  have p36_ea0 : ptF n36.mem B 0xEA0 = tbl2 P1 4 := (K36.pt (by decide) (by decide)).trans p35_ea0
  have p36_f00 : ptF n36.mem B 0xF00 = tbl2 P1 5 := (K36.pt (by decide) (by decide)).trans p35_f00
  have p36_f60 : ptF n36.mem B 0xF60 = tbl2 P1 6 := (K36.pt (by decide) (by decide)).trans p35_f60
  have p36_fc0 : ptF n36.mem B 0xFC0 = tbl2 P1 7 := (K36.pt (by decide) (by decide)).trans p35_fc0
  have p36_1380 : ptF n36.mem B 0x1380 = P0 := (K36.pt (by decide) (by decide)).trans p35_1380
  have p36_1400 : ptF n36.mem B 0x1400 = P1 := (K36.pt (by decide) (by decide)).trans p35_1400
  have mb36_a24 : memBytes n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [K36.mb (by decide) (by decide)]; exact mb35_a24
  have mb36_1024 : memBytes n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [K36.mb (by decide) (by decide)]; exact mb35_1024
  have mb36_1480 : leN (memBytes n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 0x20) = U2 := by rw [K36.mb (by decide) (by decide)]; exact mb35_1480
  have mb36_1320 : leN (memBytes n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U2 := by
    rw [memBytes_cp (S := B + 0x21A0) (c := 0x1320) (d := 0x1480) (N := 0x20) fun q hq => by
      rw [show 0x1320 + q = 0x1320 + (0x0 + q) by omega, X36 (0x0 + q) (by omega),
        show 0x1480 + (0x0 + q) = 0x1480 + q by omega]]; exact mb35_1480
  clear mb35_1480 mb35_1320 mb35_1024 mb35_a24 p35_1400 p35_1380 p35_fc0 p35_f60 p35_f00 p35_ea0 p35_e40 p35_de0 p35_d80 p35_d20 p35_cc0 p35_c60 p35_c00 p35_ba0 p35_b40 p35_9c0 p35_960 p35_900 p35_8a0 p35_840 p35_7e0 p35_780 p35_720 p35_6c0 p35_660 p35_600 p35_5a0 p35_540 p35_4e0 p35_480 p35_420 p35_3a0 p35_320 a35_1588 a35_1460 a35_13e0 a35_400 a35_380 a35_2e0 a35_2c0 a35_2a0 w35_1020 w35_a20 w35_130 w35_12c w35_128 w35_124 w35_120 w35_11c w35_118 w35_114 w35_110 w35_10c w35_108 w35_104 w35_100 w35_fc w35_f8 w35_f4 w35_f0 w35_ec w35_e8 w35_e4 w35_e0 w35_dc w35_d8 w35_d4 w35_d0 w35_cc w35_c8 w35_c4 w35_c0 w35_bc w35_b8 w35_b4 w35_b0 w35_ac w35_a8 w35_a4 w35_a0 w35_9c w35_98 w35_94 w35_90 w35_8c w35_88 w35_84 w35_80 w35_7c w35_78 w35_70 w35_6c w35_68 w35_64 w35_60 w35_5c w35_58 w35_54 w35_50 w35_4c w35_48 w35_44 w35_40 w35_3c w35_38 w35_34 w35_30 w35_2c w35_28 w35_24 g35_12 g35_11 g35_10 g35_27 g35_26 g35_25 g35_24 g35_23 g35_22 g35_21 g35_20 g35_19 g35_18 g35_9 g35_8 g35_4 g35_3 g35_2 V35 E35 fR35 t35 fr35 rb35 s35 m35 u35 c35
  -- 0x1840
  obtain ⟨n37, c37, u37⟩ := s36.block svEcW1840 E36.self svEcW1840_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m37 : n37.mem = n36.mem := u37.mem
  have s37 : St n37.mem SV n37 0x184C (reg n37) := ⟨u37.pc, rfl, fun _ => rfl⟩
  have rb37 : ∀ q, reg n37 q = (runBlock svEcW1840 (n36.mem, reg n36)).2 q := fun q => by rw [u37.regs]
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
  have g37_8 : reg n37 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb37, runBlock_reg _ _ _ (8 : Fin 32) s36.zero (by decide), g36_8]
  have g37_9 : reg n37 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1400 := by
    rw [rb37, runBlock_reg _ _ _ (9 : Fin 32) s36.zero (by decide), g36_9]
  have g37_18 : reg n37 (18 : Fin 32) = out := by
    rw [rb37, runBlock_reg _ _ _ (18 : Fin 32) s36.zero (by decide), g36_18]
  have g37_19 : reg n37 (19 : Fin 32) = bp := by
    rw [rb37, runBlock_reg _ _ _ (19 : Fin 32) s36.zero (by decide), g36_19]
  have g37_20 : reg n37 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb37, runBlock_reg _ _ _ (20 : Fin 32) s36.zero (by decide), g36_20]
  have g37_21 : reg n37 (21 : Fin 32) = s5v := by
    rw [rb37, runBlock_reg _ _ _ (21 : Fin 32) s36.zero (by decide), g36_21]
  have g37_22 : reg n37 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by
    rw [rb37, runBlock_reg _ _ _ (22 : Fin 32) s36.zero (by decide), g36_22]
  have g37_23 : reg n37 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by
    rw [rb37, runBlock_reg _ _ _ (23 : Fin 32) s36.zero (by decide), g36_23]
  have g37_24 : reg n37 (24 : Fin 32) = s8v := by
    rw [rb37, runBlock_reg _ _ _ (24 : Fin 32) s36.zero (by decide), g36_24]
  have g37_25 : reg n37 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb37, runBlock_reg _ _ _ (25 : Fin 32) s36.zero (by decide), g36_25]
  have g37_26 : reg n37 (26 : Fin 32) = x26 := by
    rw [rb37, runBlock_reg _ _ _ (26 : Fin 32) s36.zero (by decide), g36_26]
  have g37_27 : reg n37 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb37, runBlock_reg _ _ _ (27 : Fin 32) s36.zero (by decide), g36_27]
  have g37_10 : reg n37 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by
    rw [rb37]; simp +decide only [runBlock, BInstr.run, svEcW1840, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g36_2, g36_3, g36_4, g36_8, g36_9, g36_18, g36_19, g36_20, g36_21, g36_22, g36_23, g36_24, g36_25, g36_26, g36_27, s36.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g37_11 : reg n37 a1 = BitVec.ofNat 32 0x101 := by
    rw [rb37]; simp +decide only [runBlock, BInstr.run, svEcW1840, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g36_2, g36_3, g36_4, g36_8, g36_9, g36_18, g36_19, g36_20, g36_21, g36_22, g36_23, g36_24, g36_25, g36_26, g36_27, s36.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
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
  have w37_a20 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m37]; exact w36_a20
  have w37_1020 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m37]; exact w36_1020
  have a37_2a0 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m37]; exact a36_2a0
  have a37_2c0 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m37]; exact a36_2c0
  have a37_2e0 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m37]; exact a36_2e0
  have a37_380 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m37]; exact a36_380
  have a37_400 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m37]; exact a36_400
  have a37_13e0 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := by rw [m37]; exact a36_13e0
  have a37_1460 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := by rw [m37]; exact a36_1460
  have a37_1588 : accV n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U2 := by rw [m37]; exact a36_1588
  have p37_320 : ptF n37.mem B 0x320 = P0 := by rw [m37]; exact p36_320
  have p37_3a0 : ptF n37.mem B 0x3A0 = P1 := by rw [m37]; exact p36_3a0
  have p37_420 : ptF n37.mem B 0x420 = tbl2 P0 0 := by rw [m37]; exact p36_420
  have p37_480 : ptF n37.mem B 0x480 = tbl2 P0 1 := by rw [m37]; exact p36_480
  have p37_4e0 : ptF n37.mem B 0x4E0 = tbl2 P0 2 := by rw [m37]; exact p36_4e0
  have p37_540 : ptF n37.mem B 0x540 = tbl2 P0 3 := by rw [m37]; exact p36_540
  have p37_5a0 : ptF n37.mem B 0x5A0 = tbl2 P0 4 := by rw [m37]; exact p36_5a0
  have p37_600 : ptF n37.mem B 0x600 = tbl2 P0 5 := by rw [m37]; exact p36_600
  have p37_660 : ptF n37.mem B 0x660 = tbl2 P0 6 := by rw [m37]; exact p36_660
  have p37_6c0 : ptF n37.mem B 0x6C0 = tbl2 P0 7 := by rw [m37]; exact p36_6c0
  have p37_720 : ptF n37.mem B 0x720 = tbl2 P1 0 := by rw [m37]; exact p36_720
  have p37_780 : ptF n37.mem B 0x780 = tbl2 P1 1 := by rw [m37]; exact p36_780
  have p37_7e0 : ptF n37.mem B 0x7E0 = tbl2 P1 2 := by rw [m37]; exact p36_7e0
  have p37_840 : ptF n37.mem B 0x840 = tbl2 P1 3 := by rw [m37]; exact p36_840
  have p37_8a0 : ptF n37.mem B 0x8A0 = tbl2 P1 4 := by rw [m37]; exact p36_8a0
  have p37_900 : ptF n37.mem B 0x900 = tbl2 P1 5 := by rw [m37]; exact p36_900
  have p37_960 : ptF n37.mem B 0x960 = tbl2 P1 6 := by rw [m37]; exact p36_960
  have p37_9c0 : ptF n37.mem B 0x9C0 = tbl2 P1 7 := by rw [m37]; exact p36_9c0
  have p37_b40 : ptF n37.mem B 0xB40 = tbl2 P0 3 := by rw [m37]; exact p36_b40
  have p37_ba0 : ptF n37.mem B 0xBA0 = tbl2 P0 4 := by rw [m37]; exact p36_ba0
  have p37_c00 : ptF n37.mem B 0xC00 = tbl2 P0 5 := by rw [m37]; exact p36_c00
  have p37_c60 : ptF n37.mem B 0xC60 = tbl2 P0 6 := by rw [m37]; exact p36_c60
  have p37_cc0 : ptF n37.mem B 0xCC0 = tbl2 P0 7 := by rw [m37]; exact p36_cc0
  have p37_d20 : ptF n37.mem B 0xD20 = tbl2 P1 0 := by rw [m37]; exact p36_d20
  have p37_d80 : ptF n37.mem B 0xD80 = tbl2 P1 1 := by rw [m37]; exact p36_d80
  have p37_de0 : ptF n37.mem B 0xDE0 = tbl2 P1 2 := by rw [m37]; exact p36_de0
  have p37_e40 : ptF n37.mem B 0xE40 = tbl2 P1 3 := by rw [m37]; exact p36_e40
  have p37_ea0 : ptF n37.mem B 0xEA0 = tbl2 P1 4 := by rw [m37]; exact p36_ea0
  have p37_f00 : ptF n37.mem B 0xF00 = tbl2 P1 5 := by rw [m37]; exact p36_f00
  have p37_f60 : ptF n37.mem B 0xF60 = tbl2 P1 6 := by rw [m37]; exact p36_f60
  have p37_fc0 : ptF n37.mem B 0xFC0 = tbl2 P1 7 := by rw [m37]; exact p36_fc0
  have p37_1380 : ptF n37.mem B 0x1380 = P0 := by rw [m37]; exact p36_1380
  have p37_1400 : ptF n37.mem B 0x1400 = P1 := by rw [m37]; exact p36_1400
  have mb37_a24 : memBytes n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m37]; exact mb36_a24
  have mb37_1024 : memBytes n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m37]; exact mb36_1024
  have mb37_1320 : leN (memBytes n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U2 := by rw [m37]; exact mb36_1320
  have mb37_1480 : leN (memBytes n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 0x20) = U2 := by rw [m37]; exact mb36_1480
  clear mb36_1320 mb36_1480 mb36_1024 mb36_a24 p36_1400 p36_1380 p36_fc0 p36_f60 p36_f00 p36_ea0 p36_e40 p36_de0 p36_d80 p36_d20 p36_cc0 p36_c60 p36_c00 p36_ba0 p36_b40 p36_9c0 p36_960 p36_900 p36_8a0 p36_840 p36_7e0 p36_780 p36_720 p36_6c0 p36_660 p36_600 p36_5a0 p36_540 p36_4e0 p36_480 p36_420 p36_3a0 p36_320 a36_1588 a36_1460 a36_13e0 a36_400 a36_380 a36_2e0 a36_2c0 a36_2a0 w36_1020 w36_a20 w36_130 w36_12c w36_128 w36_124 w36_120 w36_11c w36_118 w36_114 w36_110 w36_10c w36_108 w36_104 w36_100 w36_fc w36_f8 w36_f4 w36_f0 w36_ec w36_e8 w36_e4 w36_e0 w36_dc w36_d8 w36_d4 w36_d0 w36_cc w36_c8 w36_c4 w36_c0 w36_bc w36_b8 w36_b4 w36_b0 w36_ac w36_a8 w36_a4 w36_a0 w36_9c w36_98 w36_94 w36_90 w36_8c w36_88 w36_84 w36_80 w36_7c w36_78 w36_70 w36_6c w36_68 w36_64 w36_60 w36_5c w36_58 w36_54 w36_50 w36_4c w36_48 w36_44 w36_40 w36_3c w36_38 w36_34 w36_30 w36_2c w36_28 w36_24 g36_27 g36_26 g36_25 g36_24 g36_23 g36_22 g36_21 g36_20 g36_19 g36_18 g36_9 g36_8 g36_4 g36_3 g36_2 V36 E36 fR36 t36 fr36 s36 X36 K36 P36
  -- 0x184C: branch, not taken
  obtain ⟨n38, d38, u38⟩ := s37.notTaken E37.self 0x184E sv_at_184c
    (by decide) (by rw [g37_11, s37.zero]; decide)
  have s38 : St n38.mem SV n38 0x184E (reg n38) := ⟨u38.pc, rfl, fun _ => rfl⟩
  have m38 : n38.mem = n37.mem := u38.mem
  have fr38 : ∀ x, SvR B x → n38.mem x = n37.mem x := fun x _ => by rw [m38]
  have t38 : Steps n0 n38 := t37.trans (.single d38)
  have fR38 : ∀ x, SvR B x → n38.mem x = M0 x := fun x hx => (fr38 x hx).trans (fR37 x hx)
  have E38 : SvCode n38.mem := E37.fr F fr38
  have V38 : SvSaves B n38.mem v := V37.same m38
  have g38_2 : reg n38 sp = B + 0x21A0 := by rw [u38.regs, g37_2]
  have g38_3 : reg n38 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u38.regs, g37_3]
  have g38_4 : reg n38 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u38.regs, g37_4]
  have g38_8 : reg n38 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u38.regs, g37_8]
  have g38_9 : reg n38 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1400 := by rw [u38.regs, g37_9]
  have g38_10 : reg n38 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by rw [u38.regs, g37_10]
  have g38_11 : reg n38 a1 = BitVec.ofNat 32 0x101 := by rw [u38.regs, g37_11]
  have g38_18 : reg n38 (18 : Fin 32) = out := by rw [u38.regs, g37_18]
  have g38_19 : reg n38 (19 : Fin 32) = bp := by rw [u38.regs, g37_19]
  have g38_20 : reg n38 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u38.regs, g37_20]
  have g38_21 : reg n38 (21 : Fin 32) = s5v := by rw [u38.regs, g37_21]
  have g38_22 : reg n38 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [u38.regs, g37_22]
  have g38_23 : reg n38 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by rw [u38.regs, g37_23]
  have g38_24 : reg n38 (24 : Fin 32) = s8v := by rw [u38.regs, g37_24]
  have g38_25 : reg n38 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u38.regs, g37_25]
  have g38_26 : reg n38 (26 : Fin 32) = x26 := by rw [u38.regs, g37_26]
  have g38_27 : reg n38 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u38.regs, g37_27]
  have w38_24 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m38]; exact w37_24
  have w38_28 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m38]; exact w37_28
  have w38_2c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m38]; exact w37_2c
  have w38_30 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m38]; exact w37_30
  have w38_34 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m38]; exact w37_34
  have w38_38 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m38]; exact w37_38
  have w38_3c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m38]; exact w37_3c
  have w38_40 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m38]; exact w37_40
  have w38_44 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m38]; exact w37_44
  have w38_48 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m38]; exact w37_48
  have w38_4c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m38]; exact w37_4c
  have w38_50 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m38]; exact w37_50
  have w38_54 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m38]; exact w37_54
  have w38_58 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m38]; exact w37_58
  have w38_5c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m38]; exact w37_5c
  have w38_60 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m38]; exact w37_60
  have w38_64 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m38]; exact w37_64
  have w38_68 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m38]; exact w37_68
  have w38_6c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m38]; exact w37_6c
  have w38_70 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m38]; exact w37_70
  have w38_78 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m38]; exact w37_78
  have w38_7c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m38]; exact w37_7c
  have w38_80 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m38]; exact w37_80
  have w38_84 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m38]; exact w37_84
  have w38_88 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m38]; exact w37_88
  have w38_8c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m38]; exact w37_8c
  have w38_90 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m38]; exact w37_90
  have w38_94 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m38]; exact w37_94
  have w38_98 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m38]; exact w37_98
  have w38_9c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m38]; exact w37_9c
  have w38_a0 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m38]; exact w37_a0
  have w38_a4 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m38]; exact w37_a4
  have w38_a8 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m38]; exact w37_a8
  have w38_ac : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m38]; exact w37_ac
  have w38_b0 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m38]; exact w37_b0
  have w38_b4 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m38]; exact w37_b4
  have w38_b8 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m38]; exact w37_b8
  have w38_bc : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m38]; exact w37_bc
  have w38_c0 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m38]; exact w37_c0
  have w38_c4 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m38]; exact w37_c4
  have w38_c8 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m38]; exact w37_c8
  have w38_cc : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m38]; exact w37_cc
  have w38_d0 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m38]; exact w37_d0
  have w38_d4 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m38]; exact w37_d4
  have w38_d8 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m38]; exact w37_d8
  have w38_dc : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m38]; exact w37_dc
  have w38_e0 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m38]; exact w37_e0
  have w38_e4 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m38]; exact w37_e4
  have w38_e8 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m38]; exact w37_e8
  have w38_ec : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m38]; exact w37_ec
  have w38_f0 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m38]; exact w37_f0
  have w38_f4 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m38]; exact w37_f4
  have w38_f8 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m38]; exact w37_f8
  have w38_fc : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m38]; exact w37_fc
  have w38_100 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m38]; exact w37_100
  have w38_104 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m38]; exact w37_104
  have w38_108 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m38]; exact w37_108
  have w38_10c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m38]; exact w37_10c
  have w38_110 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m38]; exact w37_110
  have w38_114 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m38]; exact w37_114
  have w38_118 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m38]; exact w37_118
  have w38_11c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m38]; exact w37_11c
  have w38_120 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m38]; exact w37_120
  have w38_124 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m38]; exact w37_124
  have w38_128 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m38]; exact w37_128
  have w38_12c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m38]; exact w37_12c
  have w38_130 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m38]; exact w37_130
  have w38_a20 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m38]; exact w37_a20
  have w38_1020 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m38]; exact w37_1020
  have a38_2a0 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m38]; exact a37_2a0
  have a38_2c0 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m38]; exact a37_2c0
  have a38_2e0 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m38]; exact a37_2e0
  have a38_380 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m38]; exact a37_380
  have a38_400 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m38]; exact a37_400
  have a38_13e0 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := by rw [m38]; exact a37_13e0
  have a38_1460 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := by rw [m38]; exact a37_1460
  have a38_1588 : accV n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U2 := by rw [m38]; exact a37_1588
  have p38_320 : ptF n38.mem B 0x320 = P0 := by rw [m38]; exact p37_320
  have p38_3a0 : ptF n38.mem B 0x3A0 = P1 := by rw [m38]; exact p37_3a0
  have p38_420 : ptF n38.mem B 0x420 = tbl2 P0 0 := by rw [m38]; exact p37_420
  have p38_480 : ptF n38.mem B 0x480 = tbl2 P0 1 := by rw [m38]; exact p37_480
  have p38_4e0 : ptF n38.mem B 0x4E0 = tbl2 P0 2 := by rw [m38]; exact p37_4e0
  have p38_540 : ptF n38.mem B 0x540 = tbl2 P0 3 := by rw [m38]; exact p37_540
  have p38_5a0 : ptF n38.mem B 0x5A0 = tbl2 P0 4 := by rw [m38]; exact p37_5a0
  have p38_600 : ptF n38.mem B 0x600 = tbl2 P0 5 := by rw [m38]; exact p37_600
  have p38_660 : ptF n38.mem B 0x660 = tbl2 P0 6 := by rw [m38]; exact p37_660
  have p38_6c0 : ptF n38.mem B 0x6C0 = tbl2 P0 7 := by rw [m38]; exact p37_6c0
  have p38_720 : ptF n38.mem B 0x720 = tbl2 P1 0 := by rw [m38]; exact p37_720
  have p38_780 : ptF n38.mem B 0x780 = tbl2 P1 1 := by rw [m38]; exact p37_780
  have p38_7e0 : ptF n38.mem B 0x7E0 = tbl2 P1 2 := by rw [m38]; exact p37_7e0
  have p38_840 : ptF n38.mem B 0x840 = tbl2 P1 3 := by rw [m38]; exact p37_840
  have p38_8a0 : ptF n38.mem B 0x8A0 = tbl2 P1 4 := by rw [m38]; exact p37_8a0
  have p38_900 : ptF n38.mem B 0x900 = tbl2 P1 5 := by rw [m38]; exact p37_900
  have p38_960 : ptF n38.mem B 0x960 = tbl2 P1 6 := by rw [m38]; exact p37_960
  have p38_9c0 : ptF n38.mem B 0x9C0 = tbl2 P1 7 := by rw [m38]; exact p37_9c0
  have p38_b40 : ptF n38.mem B 0xB40 = tbl2 P0 3 := by rw [m38]; exact p37_b40
  have p38_ba0 : ptF n38.mem B 0xBA0 = tbl2 P0 4 := by rw [m38]; exact p37_ba0
  have p38_c00 : ptF n38.mem B 0xC00 = tbl2 P0 5 := by rw [m38]; exact p37_c00
  have p38_c60 : ptF n38.mem B 0xC60 = tbl2 P0 6 := by rw [m38]; exact p37_c60
  have p38_cc0 : ptF n38.mem B 0xCC0 = tbl2 P0 7 := by rw [m38]; exact p37_cc0
  have p38_d20 : ptF n38.mem B 0xD20 = tbl2 P1 0 := by rw [m38]; exact p37_d20
  have p38_d80 : ptF n38.mem B 0xD80 = tbl2 P1 1 := by rw [m38]; exact p37_d80
  have p38_de0 : ptF n38.mem B 0xDE0 = tbl2 P1 2 := by rw [m38]; exact p37_de0
  have p38_e40 : ptF n38.mem B 0xE40 = tbl2 P1 3 := by rw [m38]; exact p37_e40
  have p38_ea0 : ptF n38.mem B 0xEA0 = tbl2 P1 4 := by rw [m38]; exact p37_ea0
  have p38_f00 : ptF n38.mem B 0xF00 = tbl2 P1 5 := by rw [m38]; exact p37_f00
  have p38_f60 : ptF n38.mem B 0xF60 = tbl2 P1 6 := by rw [m38]; exact p37_f60
  have p38_fc0 : ptF n38.mem B 0xFC0 = tbl2 P1 7 := by rw [m38]; exact p37_fc0
  have p38_1380 : ptF n38.mem B 0x1380 = P0 := by rw [m38]; exact p37_1380
  have p38_1400 : ptF n38.mem B 0x1400 = P1 := by rw [m38]; exact p37_1400
  have mb38_a24 : memBytes n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m38]; exact mb37_a24
  have mb38_1024 : memBytes n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m38]; exact mb37_1024
  have mb38_1320 : leN (memBytes n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U2 := by rw [m38]; exact mb37_1320
  have mb38_1480 : leN (memBytes n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 0x20) = U2 := by rw [m38]; exact mb37_1480
  clear mb37_1480 mb37_1320 mb37_1024 mb37_a24 p37_1400 p37_1380 p37_fc0 p37_f60 p37_f00 p37_ea0 p37_e40 p37_de0 p37_d80 p37_d20 p37_cc0 p37_c60 p37_c00 p37_ba0 p37_b40 p37_9c0 p37_960 p37_900 p37_8a0 p37_840 p37_7e0 p37_780 p37_720 p37_6c0 p37_660 p37_600 p37_5a0 p37_540 p37_4e0 p37_480 p37_420 p37_3a0 p37_320 a37_1588 a37_1460 a37_13e0 a37_400 a37_380 a37_2e0 a37_2c0 a37_2a0 w37_1020 w37_a20 w37_130 w37_12c w37_128 w37_124 w37_120 w37_11c w37_118 w37_114 w37_110 w37_10c w37_108 w37_104 w37_100 w37_fc w37_f8 w37_f4 w37_f0 w37_ec w37_e8 w37_e4 w37_e0 w37_dc w37_d8 w37_d4 w37_d0 w37_cc w37_c8 w37_c4 w37_c0 w37_bc w37_b8 w37_b4 w37_b0 w37_ac w37_a8 w37_a4 w37_a0 w37_9c w37_98 w37_94 w37_90 w37_8c w37_88 w37_84 w37_80 w37_7c w37_78 w37_70 w37_6c w37_68 w37_64 w37_60 w37_5c w37_58 w37_54 w37_50 w37_4c w37_48 w37_44 w37_40 w37_3c w37_38 w37_34 w37_30 w37_2c w37_28 w37_24 g37_11 g37_10 g37_27 g37_26 g37_25 g37_24 g37_23 g37_22 g37_21 g37_20 g37_19 g37_18 g37_9 g37_8 g37_4 g37_3 g37_2 V37 E37 fR37 t37 fr37 rb37 s37 m37 u37 c37
  -- 0x184E: clear 0x101 bytes
  obtain ⟨n39, Z39, c39, s39', C39, rk39, z39, fz39⟩ := ec_zloop F (c := 0x1480) (N := 0x101) (by decide)
    0x101 0 (by decide) (by decide) E38.self s38 (by rw [g38_10]; try rfl) g38_11
  have s39 : St n39.mem SV n39 0x1858 (reg n39) := ⟨s39'.pc, rfl, fun _ => rfl⟩
  have fr39 : ∀ x, SvR B x → n39.mem x = n38.mem x := fun x hx => by
    rw [s39'.mem]; exact fz39 x (svR_hi (c := 0x1480 + 0) hx (by decide))
  have K39 : SvKeep B n38.mem n39.mem 0x1480 0x101 := fun e he hh => by
    rw [s39'.mem]; exact fz39 _ (sepS (B + 0x21A0) (c := 0x1480 + 0) (n := 0x101) (d := e) (k := 1) (by omega) (by omega) (by omega))
  have t39 : Steps n0 n39 := t38.trans c39
  have fR39 : ∀ x, SvR B x → n39.mem x = M0 x := fun x hx => (fr39 x hx).trans (fR38 x hx)
  have E39 : SvCode n39.mem := E38.fr F fr39
  have V39 : SvSaves B n39.mem v := V38.keep K39 (by decide)
  have g39_2 : reg n39 sp = B + 0x21A0 := by rw [rk39 sp (by decide) (by decide), g38_2]
  have g39_3 : reg n39 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk39 (3 : Fin 32) (by decide) (by decide), g38_3]
  have g39_4 : reg n39 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk39 (4 : Fin 32) (by decide) (by decide), g38_4]
  have g39_8 : reg n39 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rk39 (8 : Fin 32) (by decide) (by decide), g38_8]
  have g39_9 : reg n39 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1400 := by rw [rk39 (9 : Fin 32) (by decide) (by decide), g38_9]
  have g39_18 : reg n39 (18 : Fin 32) = out := by rw [rk39 (18 : Fin 32) (by decide) (by decide), g38_18]
  have g39_19 : reg n39 (19 : Fin 32) = bp := by rw [rk39 (19 : Fin 32) (by decide) (by decide), g38_19]
  have g39_20 : reg n39 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk39 (20 : Fin 32) (by decide) (by decide), g38_20]
  have g39_21 : reg n39 (21 : Fin 32) = s5v := by rw [rk39 (21 : Fin 32) (by decide) (by decide), g38_21]
  have g39_22 : reg n39 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [rk39 (22 : Fin 32) (by decide) (by decide), g38_22]
  have g39_23 : reg n39 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by rw [rk39 (23 : Fin 32) (by decide) (by decide), g38_23]
  have g39_24 : reg n39 (24 : Fin 32) = s8v := by rw [rk39 (24 : Fin 32) (by decide) (by decide), g38_24]
  have g39_25 : reg n39 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [rk39 (25 : Fin 32) (by decide) (by decide), g38_25]
  have g39_26 : reg n39 (26 : Fin 32) = x26 := by rw [rk39 (26 : Fin 32) (by decide) (by decide), g38_26]
  have g39_27 : reg n39 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk39 (27 : Fin 32) (by decide) (by decide), g38_27]
  have w39_24 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K39.w32 (by decide) (by decide)).trans w38_24
  have w39_28 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K39.w32 (by decide) (by decide)).trans w38_28
  have w39_2c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K39.w32 (by decide) (by decide)).trans w38_2c
  have w39_30 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K39.w32 (by decide) (by decide)).trans w38_30
  have w39_34 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K39.w32 (by decide) (by decide)).trans w38_34
  have w39_38 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K39.w32 (by decide) (by decide)).trans w38_38
  have w39_3c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K39.w32 (by decide) (by decide)).trans w38_3c
  have w39_40 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K39.w32 (by decide) (by decide)).trans w38_40
  have w39_44 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K39.w32 (by decide) (by decide)).trans w38_44
  have w39_48 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K39.w32 (by decide) (by decide)).trans w38_48
  have w39_4c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K39.w32 (by decide) (by decide)).trans w38_4c
  have w39_50 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K39.w32 (by decide) (by decide)).trans w38_50
  have w39_54 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K39.w32 (by decide) (by decide)).trans w38_54
  have w39_58 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K39.w32 (by decide) (by decide)).trans w38_58
  have w39_5c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K39.w32 (by decide) (by decide)).trans w38_5c
  have w39_60 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K39.w32 (by decide) (by decide)).trans w38_60
  have w39_64 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K39.w32 (by decide) (by decide)).trans w38_64
  have w39_68 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K39.w32 (by decide) (by decide)).trans w38_68
  have w39_6c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K39.w32 (by decide) (by decide)).trans w38_6c
  have w39_70 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K39.w32 (by decide) (by decide)).trans w38_70
  have w39_78 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := (K39.w32 (by decide) (by decide)).trans w38_78
  have w39_7c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K39.w32 (by decide) (by decide)).trans w38_7c
  have w39_80 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K39.w32 (by decide) (by decide)).trans w38_80
  have w39_84 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K39.w32 (by decide) (by decide)).trans w38_84
  have w39_88 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K39.w32 (by decide) (by decide)).trans w38_88
  have w39_8c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K39.w32 (by decide) (by decide)).trans w38_8c
  have w39_90 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K39.w32 (by decide) (by decide)).trans w38_90
  have w39_94 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K39.w32 (by decide) (by decide)).trans w38_94
  have w39_98 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K39.w32 (by decide) (by decide)).trans w38_98
  have w39_9c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K39.w32 (by decide) (by decide)).trans w38_9c
  have w39_a0 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K39.w32 (by decide) (by decide)).trans w38_a0
  have w39_a4 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K39.w32 (by decide) (by decide)).trans w38_a4
  have w39_a8 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K39.w32 (by decide) (by decide)).trans w38_a8
  have w39_ac : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K39.w32 (by decide) (by decide)).trans w38_ac
  have w39_b0 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K39.w32 (by decide) (by decide)).trans w38_b0
  have w39_b4 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K39.w32 (by decide) (by decide)).trans w38_b4
  have w39_b8 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K39.w32 (by decide) (by decide)).trans w38_b8
  have w39_bc : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K39.w32 (by decide) (by decide)).trans w38_bc
  have w39_c0 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K39.w32 (by decide) (by decide)).trans w38_c0
  have w39_c4 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K39.w32 (by decide) (by decide)).trans w38_c4
  have w39_c8 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K39.w32 (by decide) (by decide)).trans w38_c8
  have w39_cc : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K39.w32 (by decide) (by decide)).trans w38_cc
  have w39_d0 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K39.w32 (by decide) (by decide)).trans w38_d0
  have w39_d4 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K39.w32 (by decide) (by decide)).trans w38_d4
  have w39_d8 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K39.w32 (by decide) (by decide)).trans w38_d8
  have w39_dc : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K39.w32 (by decide) (by decide)).trans w38_dc
  have w39_e0 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K39.w32 (by decide) (by decide)).trans w38_e0
  have w39_e4 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K39.w32 (by decide) (by decide)).trans w38_e4
  have w39_e8 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K39.w32 (by decide) (by decide)).trans w38_e8
  have w39_ec : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K39.w32 (by decide) (by decide)).trans w38_ec
  have w39_f0 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K39.w32 (by decide) (by decide)).trans w38_f0
  have w39_f4 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K39.w32 (by decide) (by decide)).trans w38_f4
  have w39_f8 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K39.w32 (by decide) (by decide)).trans w38_f8
  have w39_fc : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K39.w32 (by decide) (by decide)).trans w38_fc
  have w39_100 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K39.w32 (by decide) (by decide)).trans w38_100
  have w39_104 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K39.w32 (by decide) (by decide)).trans w38_104
  have w39_108 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K39.w32 (by decide) (by decide)).trans w38_108
  have w39_10c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K39.w32 (by decide) (by decide)).trans w38_10c
  have w39_110 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K39.w32 (by decide) (by decide)).trans w38_110
  have w39_114 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K39.w32 (by decide) (by decide)).trans w38_114
  have w39_118 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K39.w32 (by decide) (by decide)).trans w38_118
  have w39_11c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K39.w32 (by decide) (by decide)).trans w38_11c
  have w39_120 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K39.w32 (by decide) (by decide)).trans w38_120
  have w39_124 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K39.w32 (by decide) (by decide)).trans w38_124
  have w39_128 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K39.w32 (by decide) (by decide)).trans w38_128
  have w39_12c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K39.w32 (by decide) (by decide)).trans w38_12c
  have w39_130 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K39.w32 (by decide) (by decide)).trans w38_130
  have w39_a20 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := (K39.w32 (by decide) (by decide)).trans w38_a20
  have w39_1020 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := (K39.w32 (by decide) (by decide)).trans w38_1020
  have a39_2a0 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K39.acc (by decide) (by decide)).trans a38_2a0
  have a39_2c0 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K39.acc (by decide) (by decide)).trans a38_2c0
  have a39_2e0 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K39.acc (by decide) (by decide)).trans a38_2e0
  have a39_380 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := (K39.acc (by decide) (by decide)).trans a38_380
  have a39_400 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := (K39.acc (by decide) (by decide)).trans a38_400
  have a39_13e0 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := (K39.acc (by decide) (by decide)).trans a38_13e0
  have a39_1460 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := (K39.acc (by decide) (by decide)).trans a38_1460
  have a39_1588 : accV n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U2 := (K39.acc (by decide) (by decide)).trans a38_1588
  have p39_320 : ptF n39.mem B 0x320 = P0 := (K39.pt (by decide) (by decide)).trans p38_320
  have p39_3a0 : ptF n39.mem B 0x3A0 = P1 := (K39.pt (by decide) (by decide)).trans p38_3a0
  have p39_420 : ptF n39.mem B 0x420 = tbl2 P0 0 := (K39.pt (by decide) (by decide)).trans p38_420
  have p39_480 : ptF n39.mem B 0x480 = tbl2 P0 1 := (K39.pt (by decide) (by decide)).trans p38_480
  have p39_4e0 : ptF n39.mem B 0x4E0 = tbl2 P0 2 := (K39.pt (by decide) (by decide)).trans p38_4e0
  have p39_540 : ptF n39.mem B 0x540 = tbl2 P0 3 := (K39.pt (by decide) (by decide)).trans p38_540
  have p39_5a0 : ptF n39.mem B 0x5A0 = tbl2 P0 4 := (K39.pt (by decide) (by decide)).trans p38_5a0
  have p39_600 : ptF n39.mem B 0x600 = tbl2 P0 5 := (K39.pt (by decide) (by decide)).trans p38_600
  have p39_660 : ptF n39.mem B 0x660 = tbl2 P0 6 := (K39.pt (by decide) (by decide)).trans p38_660
  have p39_6c0 : ptF n39.mem B 0x6C0 = tbl2 P0 7 := (K39.pt (by decide) (by decide)).trans p38_6c0
  have p39_720 : ptF n39.mem B 0x720 = tbl2 P1 0 := (K39.pt (by decide) (by decide)).trans p38_720
  have p39_780 : ptF n39.mem B 0x780 = tbl2 P1 1 := (K39.pt (by decide) (by decide)).trans p38_780
  have p39_7e0 : ptF n39.mem B 0x7E0 = tbl2 P1 2 := (K39.pt (by decide) (by decide)).trans p38_7e0
  have p39_840 : ptF n39.mem B 0x840 = tbl2 P1 3 := (K39.pt (by decide) (by decide)).trans p38_840
  have p39_8a0 : ptF n39.mem B 0x8A0 = tbl2 P1 4 := (K39.pt (by decide) (by decide)).trans p38_8a0
  have p39_900 : ptF n39.mem B 0x900 = tbl2 P1 5 := (K39.pt (by decide) (by decide)).trans p38_900
  have p39_960 : ptF n39.mem B 0x960 = tbl2 P1 6 := (K39.pt (by decide) (by decide)).trans p38_960
  have p39_9c0 : ptF n39.mem B 0x9C0 = tbl2 P1 7 := (K39.pt (by decide) (by decide)).trans p38_9c0
  have p39_b40 : ptF n39.mem B 0xB40 = tbl2 P0 3 := (K39.pt (by decide) (by decide)).trans p38_b40
  have p39_ba0 : ptF n39.mem B 0xBA0 = tbl2 P0 4 := (K39.pt (by decide) (by decide)).trans p38_ba0
  have p39_c00 : ptF n39.mem B 0xC00 = tbl2 P0 5 := (K39.pt (by decide) (by decide)).trans p38_c00
  have p39_c60 : ptF n39.mem B 0xC60 = tbl2 P0 6 := (K39.pt (by decide) (by decide)).trans p38_c60
  have p39_cc0 : ptF n39.mem B 0xCC0 = tbl2 P0 7 := (K39.pt (by decide) (by decide)).trans p38_cc0
  have p39_d20 : ptF n39.mem B 0xD20 = tbl2 P1 0 := (K39.pt (by decide) (by decide)).trans p38_d20
  have p39_d80 : ptF n39.mem B 0xD80 = tbl2 P1 1 := (K39.pt (by decide) (by decide)).trans p38_d80
  have p39_de0 : ptF n39.mem B 0xDE0 = tbl2 P1 2 := (K39.pt (by decide) (by decide)).trans p38_de0
  have p39_e40 : ptF n39.mem B 0xE40 = tbl2 P1 3 := (K39.pt (by decide) (by decide)).trans p38_e40
  have p39_ea0 : ptF n39.mem B 0xEA0 = tbl2 P1 4 := (K39.pt (by decide) (by decide)).trans p38_ea0
  have p39_f00 : ptF n39.mem B 0xF00 = tbl2 P1 5 := (K39.pt (by decide) (by decide)).trans p38_f00
  have p39_f60 : ptF n39.mem B 0xF60 = tbl2 P1 6 := (K39.pt (by decide) (by decide)).trans p38_f60
  have p39_fc0 : ptF n39.mem B 0xFC0 = tbl2 P1 7 := (K39.pt (by decide) (by decide)).trans p38_fc0
  have p39_1380 : ptF n39.mem B 0x1380 = P0 := (K39.pt (by decide) (by decide)).trans p38_1380
  have p39_1400 : ptF n39.mem B 0x1400 = P1 := (K39.pt (by decide) (by decide)).trans p38_1400
  have mb39_a24 : memBytes n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [K39.mb (by decide) (by decide)]; exact mb38_a24
  have mb39_1024 : memBytes n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [K39.mb (by decide) (by decide)]; exact mb38_1024
  have mb39_1320 : leN (memBytes n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U2 := by rw [K39.mb (by decide) (by decide)]; exact mb38_1320
  have mb39_1480 : memBytes n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 0x101 = List.replicate 0x101 0 :=
    Pv.memBytes_zero fun j hj => by rw [s39'.mem]; have := z39 j hj; rwa [Nat.add_zero] at this
  clear mb38_1480 mb38_1320 mb38_1024 mb38_a24 p38_1400 p38_1380 p38_fc0 p38_f60 p38_f00 p38_ea0 p38_e40 p38_de0 p38_d80 p38_d20 p38_cc0 p38_c60 p38_c00 p38_ba0 p38_b40 p38_9c0 p38_960 p38_900 p38_8a0 p38_840 p38_7e0 p38_780 p38_720 p38_6c0 p38_660 p38_600 p38_5a0 p38_540 p38_4e0 p38_480 p38_420 p38_3a0 p38_320 a38_1588 a38_1460 a38_13e0 a38_400 a38_380 a38_2e0 a38_2c0 a38_2a0 w38_1020 w38_a20 w38_130 w38_12c w38_128 w38_124 w38_120 w38_11c w38_118 w38_114 w38_110 w38_10c w38_108 w38_104 w38_100 w38_fc w38_f8 w38_f4 w38_f0 w38_ec w38_e8 w38_e4 w38_e0 w38_dc w38_d8 w38_d4 w38_d0 w38_cc w38_c8 w38_c4 w38_c0 w38_bc w38_b8 w38_b4 w38_b0 w38_ac w38_a8 w38_a4 w38_a0 w38_9c w38_98 w38_94 w38_90 w38_8c w38_88 w38_84 w38_80 w38_7c w38_78 w38_70 w38_6c w38_68 w38_64 w38_60 w38_5c w38_58 w38_54 w38_50 w38_4c w38_48 w38_44 w38_40 w38_3c w38_38 w38_34 w38_30 w38_2c w38_28 w38_24 g38_27 g38_26 g38_25 g38_24 g38_23 g38_22 g38_21 g38_20 g38_19 g38_18 g38_11 g38_10 g38_9 g38_8 g38_4 g38_3 g38_2 V38 E38 fR38 t38 fr38 m38 s38 u38 d38
  -- 0x1858
  obtain ⟨n40, c40, u40⟩ := s39.block svEcW1858 E39.self svEcW1858_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m40 : n40.mem = n39.mem := u40.mem
  have s40 : St n40.mem SV n40 0x186C (reg n40) := ⟨u40.pc, rfl, fun _ => rfl⟩
  have rb40 : ∀ q, reg n40 q = (runBlock svEcW1858 (n39.mem, reg n39)).2 q := fun q => by rw [u40.regs]
  have fr40 : ∀ x, SvR B x → n40.mem x = n39.mem x := fun x _ => by rw [m40]
  have t40 : Steps n0 n40 := t39.trans c40
  have fR40 : ∀ x, SvR B x → n40.mem x = M0 x := fun x hx => (fr40 x hx).trans (fR39 x hx)
  have E40 : SvCode n40.mem := E39.fr F fr40
  have V40 : SvSaves B n40.mem v := V39.same m40
  have g40_2 : reg n40 sp = B + 0x21A0 := by
    rw [rb40, runBlock_reg _ _ _ sp s39.zero (by decide), g39_2]
  have g40_3 : reg n40 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb40, runBlock_reg _ _ _ (3 : Fin 32) s39.zero (by decide), g39_3]
  have g40_4 : reg n40 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb40, runBlock_reg _ _ _ (4 : Fin 32) s39.zero (by decide), g39_4]
  have g40_8 : reg n40 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb40, runBlock_reg _ _ _ (8 : Fin 32) s39.zero (by decide), g39_8]
  have g40_18 : reg n40 (18 : Fin 32) = out := by
    rw [rb40, runBlock_reg _ _ _ (18 : Fin 32) s39.zero (by decide), g39_18]
  have g40_19 : reg n40 (19 : Fin 32) = bp := by
    rw [rb40, runBlock_reg _ _ _ (19 : Fin 32) s39.zero (by decide), g39_19]
  have g40_20 : reg n40 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb40, runBlock_reg _ _ _ (20 : Fin 32) s39.zero (by decide), g39_20]
  have g40_21 : reg n40 (21 : Fin 32) = s5v := by
    rw [rb40, runBlock_reg _ _ _ (21 : Fin 32) s39.zero (by decide), g39_21]
  have g40_22 : reg n40 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by
    rw [rb40, runBlock_reg _ _ _ (22 : Fin 32) s39.zero (by decide), g39_22]
  have g40_23 : reg n40 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by
    rw [rb40, runBlock_reg _ _ _ (23 : Fin 32) s39.zero (by decide), g39_23]
  have g40_24 : reg n40 (24 : Fin 32) = s8v := by
    rw [rb40, runBlock_reg _ _ _ (24 : Fin 32) s39.zero (by decide), g39_24]
  have g40_25 : reg n40 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb40, runBlock_reg _ _ _ (25 : Fin 32) s39.zero (by decide), g39_25]
  have g40_26 : reg n40 (26 : Fin 32) = x26 := by
    rw [rb40, runBlock_reg _ _ _ (26 : Fin 32) s39.zero (by decide), g39_26]
  have g40_27 : reg n40 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb40, runBlock_reg _ _ _ (27 : Fin 32) s39.zero (by decide), g39_27]
  have g40_9 : reg n40 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by
    rw [rb40]; simp +decide only [runBlock, BInstr.run, svEcW1858, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g39_2, g39_3, g39_4, g39_8, g39_9, g39_18, g39_19, g39_20, g39_21, g39_22, g39_23, g39_24, g39_25, g39_26, g39_27, s39.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g40_10 : reg n40 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by
    rw [rb40]; simp +decide only [runBlock, BInstr.run, svEcW1858, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g39_2, g39_3, g39_4, g39_8, g39_9, g39_18, g39_19, g39_20, g39_21, g39_22, g39_23, g39_24, g39_25, g39_26, g39_27, s39.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g40_11 : reg n40 a1 = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by
    rw [rb40]; simp +decide only [runBlock, BInstr.run, svEcW1858, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g39_2, g39_3, g39_4, g39_8, g39_9, g39_18, g39_19, g39_20, g39_21, g39_22, g39_23, g39_24, g39_25, g39_26, g39_27, s39.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g40_12 : reg n40 a2 = BitVec.ofNat 32 0x101 := by
    rw [rb40]; simp +decide only [runBlock, BInstr.run, svEcW1858, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g39_2, g39_3, g39_4, g39_8, g39_9, g39_18, g39_19, g39_20, g39_21, g39_22, g39_23, g39_24, g39_25, g39_26, g39_27, s39.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w40_24 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m40]; exact w39_24
  have w40_28 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m40]; exact w39_28
  have w40_2c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m40]; exact w39_2c
  have w40_30 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m40]; exact w39_30
  have w40_34 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m40]; exact w39_34
  have w40_38 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m40]; exact w39_38
  have w40_3c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m40]; exact w39_3c
  have w40_40 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m40]; exact w39_40
  have w40_44 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m40]; exact w39_44
  have w40_48 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m40]; exact w39_48
  have w40_4c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m40]; exact w39_4c
  have w40_50 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m40]; exact w39_50
  have w40_54 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m40]; exact w39_54
  have w40_58 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m40]; exact w39_58
  have w40_5c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m40]; exact w39_5c
  have w40_60 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m40]; exact w39_60
  have w40_64 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m40]; exact w39_64
  have w40_68 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m40]; exact w39_68
  have w40_6c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m40]; exact w39_6c
  have w40_70 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m40]; exact w39_70
  have w40_78 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m40]; exact w39_78
  have w40_7c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m40]; exact w39_7c
  have w40_80 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m40]; exact w39_80
  have w40_84 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m40]; exact w39_84
  have w40_88 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m40]; exact w39_88
  have w40_8c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m40]; exact w39_8c
  have w40_90 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m40]; exact w39_90
  have w40_94 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m40]; exact w39_94
  have w40_98 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m40]; exact w39_98
  have w40_9c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m40]; exact w39_9c
  have w40_a0 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m40]; exact w39_a0
  have w40_a4 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m40]; exact w39_a4
  have w40_a8 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m40]; exact w39_a8
  have w40_ac : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m40]; exact w39_ac
  have w40_b0 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m40]; exact w39_b0
  have w40_b4 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m40]; exact w39_b4
  have w40_b8 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m40]; exact w39_b8
  have w40_bc : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m40]; exact w39_bc
  have w40_c0 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m40]; exact w39_c0
  have w40_c4 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m40]; exact w39_c4
  have w40_c8 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m40]; exact w39_c8
  have w40_cc : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m40]; exact w39_cc
  have w40_d0 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m40]; exact w39_d0
  have w40_d4 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m40]; exact w39_d4
  have w40_d8 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m40]; exact w39_d8
  have w40_dc : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m40]; exact w39_dc
  have w40_e0 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m40]; exact w39_e0
  have w40_e4 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m40]; exact w39_e4
  have w40_e8 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m40]; exact w39_e8
  have w40_ec : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m40]; exact w39_ec
  have w40_f0 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m40]; exact w39_f0
  have w40_f4 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m40]; exact w39_f4
  have w40_f8 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m40]; exact w39_f8
  have w40_fc : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m40]; exact w39_fc
  have w40_100 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m40]; exact w39_100
  have w40_104 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m40]; exact w39_104
  have w40_108 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m40]; exact w39_108
  have w40_10c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m40]; exact w39_10c
  have w40_110 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m40]; exact w39_110
  have w40_114 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m40]; exact w39_114
  have w40_118 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m40]; exact w39_118
  have w40_11c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m40]; exact w39_11c
  have w40_120 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m40]; exact w39_120
  have w40_124 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m40]; exact w39_124
  have w40_128 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m40]; exact w39_128
  have w40_12c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m40]; exact w39_12c
  have w40_130 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m40]; exact w39_130
  have w40_a20 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m40]; exact w39_a20
  have w40_1020 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m40]; exact w39_1020
  have a40_2a0 : accV n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m40]; exact a39_2a0
  have a40_2c0 : accV n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m40]; exact a39_2c0
  have a40_2e0 : accV n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m40]; exact a39_2e0
  have a40_380 : accV n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m40]; exact a39_380
  have a40_400 : accV n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m40]; exact a39_400
  have a40_13e0 : accV n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := by rw [m40]; exact a39_13e0
  have a40_1460 : accV n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := by rw [m40]; exact a39_1460
  have a40_1588 : accV n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U2 := by rw [m40]; exact a39_1588
  have p40_320 : ptF n40.mem B 0x320 = P0 := by rw [m40]; exact p39_320
  have p40_3a0 : ptF n40.mem B 0x3A0 = P1 := by rw [m40]; exact p39_3a0
  have p40_420 : ptF n40.mem B 0x420 = tbl2 P0 0 := by rw [m40]; exact p39_420
  have p40_480 : ptF n40.mem B 0x480 = tbl2 P0 1 := by rw [m40]; exact p39_480
  have p40_4e0 : ptF n40.mem B 0x4E0 = tbl2 P0 2 := by rw [m40]; exact p39_4e0
  have p40_540 : ptF n40.mem B 0x540 = tbl2 P0 3 := by rw [m40]; exact p39_540
  have p40_5a0 : ptF n40.mem B 0x5A0 = tbl2 P0 4 := by rw [m40]; exact p39_5a0
  have p40_600 : ptF n40.mem B 0x600 = tbl2 P0 5 := by rw [m40]; exact p39_600
  have p40_660 : ptF n40.mem B 0x660 = tbl2 P0 6 := by rw [m40]; exact p39_660
  have p40_6c0 : ptF n40.mem B 0x6C0 = tbl2 P0 7 := by rw [m40]; exact p39_6c0
  have p40_720 : ptF n40.mem B 0x720 = tbl2 P1 0 := by rw [m40]; exact p39_720
  have p40_780 : ptF n40.mem B 0x780 = tbl2 P1 1 := by rw [m40]; exact p39_780
  have p40_7e0 : ptF n40.mem B 0x7E0 = tbl2 P1 2 := by rw [m40]; exact p39_7e0
  have p40_840 : ptF n40.mem B 0x840 = tbl2 P1 3 := by rw [m40]; exact p39_840
  have p40_8a0 : ptF n40.mem B 0x8A0 = tbl2 P1 4 := by rw [m40]; exact p39_8a0
  have p40_900 : ptF n40.mem B 0x900 = tbl2 P1 5 := by rw [m40]; exact p39_900
  have p40_960 : ptF n40.mem B 0x960 = tbl2 P1 6 := by rw [m40]; exact p39_960
  have p40_9c0 : ptF n40.mem B 0x9C0 = tbl2 P1 7 := by rw [m40]; exact p39_9c0
  have p40_b40 : ptF n40.mem B 0xB40 = tbl2 P0 3 := by rw [m40]; exact p39_b40
  have p40_ba0 : ptF n40.mem B 0xBA0 = tbl2 P0 4 := by rw [m40]; exact p39_ba0
  have p40_c00 : ptF n40.mem B 0xC00 = tbl2 P0 5 := by rw [m40]; exact p39_c00
  have p40_c60 : ptF n40.mem B 0xC60 = tbl2 P0 6 := by rw [m40]; exact p39_c60
  have p40_cc0 : ptF n40.mem B 0xCC0 = tbl2 P0 7 := by rw [m40]; exact p39_cc0
  have p40_d20 : ptF n40.mem B 0xD20 = tbl2 P1 0 := by rw [m40]; exact p39_d20
  have p40_d80 : ptF n40.mem B 0xD80 = tbl2 P1 1 := by rw [m40]; exact p39_d80
  have p40_de0 : ptF n40.mem B 0xDE0 = tbl2 P1 2 := by rw [m40]; exact p39_de0
  have p40_e40 : ptF n40.mem B 0xE40 = tbl2 P1 3 := by rw [m40]; exact p39_e40
  have p40_ea0 : ptF n40.mem B 0xEA0 = tbl2 P1 4 := by rw [m40]; exact p39_ea0
  have p40_f00 : ptF n40.mem B 0xF00 = tbl2 P1 5 := by rw [m40]; exact p39_f00
  have p40_f60 : ptF n40.mem B 0xF60 = tbl2 P1 6 := by rw [m40]; exact p39_f60
  have p40_fc0 : ptF n40.mem B 0xFC0 = tbl2 P1 7 := by rw [m40]; exact p39_fc0
  have p40_1380 : ptF n40.mem B 0x1380 = P0 := by rw [m40]; exact p39_1380
  have p40_1400 : ptF n40.mem B 0x1400 = P1 := by rw [m40]; exact p39_1400
  have mb40_a24 : memBytes n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m40]; exact mb39_a24
  have mb40_1024 : memBytes n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m40]; exact mb39_1024
  have mb40_1320 : leN (memBytes n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U2 := by rw [m40]; exact mb39_1320
  have mb40_1480 : memBytes n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 0x101 = List.replicate 0x101 0 := by rw [m40]; exact mb39_1480
  clear mb39_1480 mb39_1320 mb39_1024 mb39_a24 p39_1400 p39_1380 p39_fc0 p39_f60 p39_f00 p39_ea0 p39_e40 p39_de0 p39_d80 p39_d20 p39_cc0 p39_c60 p39_c00 p39_ba0 p39_b40 p39_9c0 p39_960 p39_900 p39_8a0 p39_840 p39_7e0 p39_780 p39_720 p39_6c0 p39_660 p39_600 p39_5a0 p39_540 p39_4e0 p39_480 p39_420 p39_3a0 p39_320 a39_1588 a39_1460 a39_13e0 a39_400 a39_380 a39_2e0 a39_2c0 a39_2a0 w39_1020 w39_a20 w39_130 w39_12c w39_128 w39_124 w39_120 w39_11c w39_118 w39_114 w39_110 w39_10c w39_108 w39_104 w39_100 w39_fc w39_f8 w39_f4 w39_f0 w39_ec w39_e8 w39_e4 w39_e0 w39_dc w39_d8 w39_d4 w39_d0 w39_cc w39_c8 w39_c4 w39_c0 w39_bc w39_b8 w39_b4 w39_b0 w39_ac w39_a8 w39_a4 w39_a0 w39_9c w39_98 w39_94 w39_90 w39_8c w39_88 w39_84 w39_80 w39_7c w39_78 w39_70 w39_6c w39_68 w39_64 w39_60 w39_5c w39_58 w39_54 w39_50 w39_4c w39_48 w39_44 w39_40 w39_3c w39_38 w39_34 w39_30 w39_2c w39_28 w39_24 g39_27 g39_26 g39_25 g39_24 g39_23 g39_22 g39_21 g39_20 g39_19 g39_18 g39_9 g39_8 g39_4 g39_3 g39_2 V39 E39 fR39 t39 K39 fr39 s39 fz39 z39 rk39 C39 s39' c39 Z39
  -- 0x186C: memcpy
  obtain ⟨n41, P41, K41, X41⟩ := sv_mc (c := 0x1024) (d := 0x1480) (N := 0x101) F E40 s40 sv_at_186c sv_at_1870
    (by decide) (by decide) g40_2 g40_10 g40_11 g40_12
    (by decide) (by decide) (by decide)
  have s41 := P41.st
  have fr41 := P41.fr
  have t41 : Steps n0 n41 := t40.trans P41.steps
  have fR41 : ∀ x, SvR B x → n41.mem x = M0 x := fun x hx => (fr41 x hx).trans (fR40 x hx)
  have E41 : SvCode n41.mem := E40.fr F fr41
  have V41 : SvSaves B n41.mem v := V40.keep K41 (by decide)
  have g41_2 : reg n41 sp = B + 0x21A0 := by rw [P41.regs sp (by decide), g40_2]
  have g41_3 : reg n41 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P41.regs (3 : Fin 32) (by decide), g40_3]
  have g41_4 : reg n41 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P41.regs (4 : Fin 32) (by decide), g40_4]
  have g41_8 : reg n41 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P41.regs (8 : Fin 32) (by decide), g40_8]
  have g41_9 : reg n41 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by rw [P41.regs (9 : Fin 32) (by decide), g40_9]
  have g41_18 : reg n41 (18 : Fin 32) = out := by rw [P41.regs (18 : Fin 32) (by decide), g40_18]
  have g41_19 : reg n41 (19 : Fin 32) = bp := by rw [P41.regs (19 : Fin 32) (by decide), g40_19]
  have g41_20 : reg n41 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P41.regs (20 : Fin 32) (by decide), g40_20]
  have g41_21 : reg n41 (21 : Fin 32) = s5v := by rw [P41.regs (21 : Fin 32) (by decide), g40_21]
  have g41_22 : reg n41 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [P41.regs (22 : Fin 32) (by decide), g40_22]
  have g41_23 : reg n41 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by rw [P41.regs (23 : Fin 32) (by decide), g40_23]
  have g41_24 : reg n41 (24 : Fin 32) = s8v := by rw [P41.regs (24 : Fin 32) (by decide), g40_24]
  have g41_25 : reg n41 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P41.regs (25 : Fin 32) (by decide), g40_25]
  have g41_26 : reg n41 (26 : Fin 32) = x26 := by rw [P41.regs (26 : Fin 32) (by decide), g40_26]
  have g41_27 : reg n41 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P41.regs (27 : Fin 32) (by decide), g40_27]
  have w41_24 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K41.w32 (by decide) (by decide)).trans w40_24
  have w41_28 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K41.w32 (by decide) (by decide)).trans w40_28
  have w41_2c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K41.w32 (by decide) (by decide)).trans w40_2c
  have w41_30 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K41.w32 (by decide) (by decide)).trans w40_30
  have w41_34 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K41.w32 (by decide) (by decide)).trans w40_34
  have w41_38 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K41.w32 (by decide) (by decide)).trans w40_38
  have w41_3c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K41.w32 (by decide) (by decide)).trans w40_3c
  have w41_40 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K41.w32 (by decide) (by decide)).trans w40_40
  have w41_44 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K41.w32 (by decide) (by decide)).trans w40_44
  have w41_48 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K41.w32 (by decide) (by decide)).trans w40_48
  have w41_4c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K41.w32 (by decide) (by decide)).trans w40_4c
  have w41_50 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K41.w32 (by decide) (by decide)).trans w40_50
  have w41_54 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K41.w32 (by decide) (by decide)).trans w40_54
  have w41_58 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K41.w32 (by decide) (by decide)).trans w40_58
  have w41_5c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K41.w32 (by decide) (by decide)).trans w40_5c
  have w41_60 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K41.w32 (by decide) (by decide)).trans w40_60
  have w41_64 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K41.w32 (by decide) (by decide)).trans w40_64
  have w41_68 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K41.w32 (by decide) (by decide)).trans w40_68
  have w41_6c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K41.w32 (by decide) (by decide)).trans w40_6c
  have w41_70 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K41.w32 (by decide) (by decide)).trans w40_70
  have w41_78 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := (K41.w32 (by decide) (by decide)).trans w40_78
  have w41_7c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K41.w32 (by decide) (by decide)).trans w40_7c
  have w41_80 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K41.w32 (by decide) (by decide)).trans w40_80
  have w41_84 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K41.w32 (by decide) (by decide)).trans w40_84
  have w41_88 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K41.w32 (by decide) (by decide)).trans w40_88
  have w41_8c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K41.w32 (by decide) (by decide)).trans w40_8c
  have w41_90 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K41.w32 (by decide) (by decide)).trans w40_90
  have w41_94 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K41.w32 (by decide) (by decide)).trans w40_94
  have w41_98 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K41.w32 (by decide) (by decide)).trans w40_98
  have w41_9c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K41.w32 (by decide) (by decide)).trans w40_9c
  have w41_a0 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K41.w32 (by decide) (by decide)).trans w40_a0
  have w41_a4 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K41.w32 (by decide) (by decide)).trans w40_a4
  have w41_a8 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K41.w32 (by decide) (by decide)).trans w40_a8
  have w41_ac : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K41.w32 (by decide) (by decide)).trans w40_ac
  have w41_b0 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K41.w32 (by decide) (by decide)).trans w40_b0
  have w41_b4 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K41.w32 (by decide) (by decide)).trans w40_b4
  have w41_b8 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K41.w32 (by decide) (by decide)).trans w40_b8
  have w41_bc : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K41.w32 (by decide) (by decide)).trans w40_bc
  have w41_c0 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K41.w32 (by decide) (by decide)).trans w40_c0
  have w41_c4 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K41.w32 (by decide) (by decide)).trans w40_c4
  have w41_c8 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K41.w32 (by decide) (by decide)).trans w40_c8
  have w41_cc : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K41.w32 (by decide) (by decide)).trans w40_cc
  have w41_d0 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K41.w32 (by decide) (by decide)).trans w40_d0
  have w41_d4 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K41.w32 (by decide) (by decide)).trans w40_d4
  have w41_d8 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K41.w32 (by decide) (by decide)).trans w40_d8
  have w41_dc : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K41.w32 (by decide) (by decide)).trans w40_dc
  have w41_e0 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K41.w32 (by decide) (by decide)).trans w40_e0
  have w41_e4 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K41.w32 (by decide) (by decide)).trans w40_e4
  have w41_e8 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K41.w32 (by decide) (by decide)).trans w40_e8
  have w41_ec : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K41.w32 (by decide) (by decide)).trans w40_ec
  have w41_f0 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K41.w32 (by decide) (by decide)).trans w40_f0
  have w41_f4 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K41.w32 (by decide) (by decide)).trans w40_f4
  have w41_f8 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K41.w32 (by decide) (by decide)).trans w40_f8
  have w41_fc : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K41.w32 (by decide) (by decide)).trans w40_fc
  have w41_100 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K41.w32 (by decide) (by decide)).trans w40_100
  have w41_104 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K41.w32 (by decide) (by decide)).trans w40_104
  have w41_108 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K41.w32 (by decide) (by decide)).trans w40_108
  have w41_10c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K41.w32 (by decide) (by decide)).trans w40_10c
  have w41_110 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K41.w32 (by decide) (by decide)).trans w40_110
  have w41_114 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K41.w32 (by decide) (by decide)).trans w40_114
  have w41_118 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K41.w32 (by decide) (by decide)).trans w40_118
  have w41_11c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K41.w32 (by decide) (by decide)).trans w40_11c
  have w41_120 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K41.w32 (by decide) (by decide)).trans w40_120
  have w41_124 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K41.w32 (by decide) (by decide)).trans w40_124
  have w41_128 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K41.w32 (by decide) (by decide)).trans w40_128
  have w41_12c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K41.w32 (by decide) (by decide)).trans w40_12c
  have w41_130 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K41.w32 (by decide) (by decide)).trans w40_130
  have w41_a20 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := (K41.w32 (by decide) (by decide)).trans w40_a20
  have w41_1020 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := (K41.w32 (by decide) (by decide)).trans w40_1020
  have a41_2a0 : accV n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K41.acc (by decide) (by decide)).trans a40_2a0
  have a41_2c0 : accV n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K41.acc (by decide) (by decide)).trans a40_2c0
  have a41_2e0 : accV n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K41.acc (by decide) (by decide)).trans a40_2e0
  have a41_380 : accV n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := (K41.acc (by decide) (by decide)).trans a40_380
  have a41_400 : accV n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := (K41.acc (by decide) (by decide)).trans a40_400
  have a41_13e0 : accV n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := (K41.acc (by decide) (by decide)).trans a40_13e0
  have a41_1460 : accV n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := (K41.acc (by decide) (by decide)).trans a40_1460
  have a41_1588 : accV n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U2 := (K41.acc (by decide) (by decide)).trans a40_1588
  have p41_320 : ptF n41.mem B 0x320 = P0 := (K41.pt (by decide) (by decide)).trans p40_320
  have p41_3a0 : ptF n41.mem B 0x3A0 = P1 := (K41.pt (by decide) (by decide)).trans p40_3a0
  have p41_420 : ptF n41.mem B 0x420 = tbl2 P0 0 := (K41.pt (by decide) (by decide)).trans p40_420
  have p41_480 : ptF n41.mem B 0x480 = tbl2 P0 1 := (K41.pt (by decide) (by decide)).trans p40_480
  have p41_4e0 : ptF n41.mem B 0x4E0 = tbl2 P0 2 := (K41.pt (by decide) (by decide)).trans p40_4e0
  have p41_540 : ptF n41.mem B 0x540 = tbl2 P0 3 := (K41.pt (by decide) (by decide)).trans p40_540
  have p41_5a0 : ptF n41.mem B 0x5A0 = tbl2 P0 4 := (K41.pt (by decide) (by decide)).trans p40_5a0
  have p41_600 : ptF n41.mem B 0x600 = tbl2 P0 5 := (K41.pt (by decide) (by decide)).trans p40_600
  have p41_660 : ptF n41.mem B 0x660 = tbl2 P0 6 := (K41.pt (by decide) (by decide)).trans p40_660
  have p41_6c0 : ptF n41.mem B 0x6C0 = tbl2 P0 7 := (K41.pt (by decide) (by decide)).trans p40_6c0
  have p41_720 : ptF n41.mem B 0x720 = tbl2 P1 0 := (K41.pt (by decide) (by decide)).trans p40_720
  have p41_780 : ptF n41.mem B 0x780 = tbl2 P1 1 := (K41.pt (by decide) (by decide)).trans p40_780
  have p41_7e0 : ptF n41.mem B 0x7E0 = tbl2 P1 2 := (K41.pt (by decide) (by decide)).trans p40_7e0
  have p41_840 : ptF n41.mem B 0x840 = tbl2 P1 3 := (K41.pt (by decide) (by decide)).trans p40_840
  have p41_8a0 : ptF n41.mem B 0x8A0 = tbl2 P1 4 := (K41.pt (by decide) (by decide)).trans p40_8a0
  have p41_900 : ptF n41.mem B 0x900 = tbl2 P1 5 := (K41.pt (by decide) (by decide)).trans p40_900
  have p41_960 : ptF n41.mem B 0x960 = tbl2 P1 6 := (K41.pt (by decide) (by decide)).trans p40_960
  have p41_9c0 : ptF n41.mem B 0x9C0 = tbl2 P1 7 := (K41.pt (by decide) (by decide)).trans p40_9c0
  have p41_b40 : ptF n41.mem B 0xB40 = tbl2 P0 3 := (K41.pt (by decide) (by decide)).trans p40_b40
  have p41_ba0 : ptF n41.mem B 0xBA0 = tbl2 P0 4 := (K41.pt (by decide) (by decide)).trans p40_ba0
  have p41_c00 : ptF n41.mem B 0xC00 = tbl2 P0 5 := (K41.pt (by decide) (by decide)).trans p40_c00
  have p41_c60 : ptF n41.mem B 0xC60 = tbl2 P0 6 := (K41.pt (by decide) (by decide)).trans p40_c60
  have p41_cc0 : ptF n41.mem B 0xCC0 = tbl2 P0 7 := (K41.pt (by decide) (by decide)).trans p40_cc0
  have p41_d20 : ptF n41.mem B 0xD20 = tbl2 P1 0 := (K41.pt (by decide) (by decide)).trans p40_d20
  have p41_d80 : ptF n41.mem B 0xD80 = tbl2 P1 1 := (K41.pt (by decide) (by decide)).trans p40_d80
  have p41_de0 : ptF n41.mem B 0xDE0 = tbl2 P1 2 := (K41.pt (by decide) (by decide)).trans p40_de0
  have p41_e40 : ptF n41.mem B 0xE40 = tbl2 P1 3 := (K41.pt (by decide) (by decide)).trans p40_e40
  have p41_ea0 : ptF n41.mem B 0xEA0 = tbl2 P1 4 := (K41.pt (by decide) (by decide)).trans p40_ea0
  have p41_f00 : ptF n41.mem B 0xF00 = tbl2 P1 5 := (K41.pt (by decide) (by decide)).trans p40_f00
  have p41_f60 : ptF n41.mem B 0xF60 = tbl2 P1 6 := (K41.pt (by decide) (by decide)).trans p40_f60
  have p41_fc0 : ptF n41.mem B 0xFC0 = tbl2 P1 7 := (K41.pt (by decide) (by decide)).trans p40_fc0
  have p41_1380 : ptF n41.mem B 0x1380 = P0 := (K41.pt (by decide) (by decide)).trans p40_1380
  have p41_1400 : ptF n41.mem B 0x1400 = P1 := (K41.pt (by decide) (by decide)).trans p40_1400
  have mb41_a24 : memBytes n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [K41.mb (by decide) (by decide)]; exact mb40_a24
  have mb41_1320 : leN (memBytes n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U2 := by rw [K41.mb (by decide) (by decide)]; exact mb40_1320
  have mb41_1480 : memBytes n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 0x101 = List.replicate 0x101 0 := by rw [K41.mb (by decide) (by decide)]; exact mb40_1480
  have mb41_1024 : memBytes n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) 0x101 = List.replicate 0x101 0 := by
    rw [memBytes_cp (S := B + 0x21A0) (c := 0x1024) (d := 0x1480) (N := 0x101) fun q hq => by
      rw [show 0x1024 + q = 0x1024 + (0x0 + q) by omega, X41 (0x0 + q) (by omega),
        show 0x1480 + (0x0 + q) = 0x1480 + q by omega]]; exact mb40_1480
  clear mb40_1480 mb40_1320 mb40_1024 mb40_a24 p40_1400 p40_1380 p40_fc0 p40_f60 p40_f00 p40_ea0 p40_e40 p40_de0 p40_d80 p40_d20 p40_cc0 p40_c60 p40_c00 p40_ba0 p40_b40 p40_9c0 p40_960 p40_900 p40_8a0 p40_840 p40_7e0 p40_780 p40_720 p40_6c0 p40_660 p40_600 p40_5a0 p40_540 p40_4e0 p40_480 p40_420 p40_3a0 p40_320 a40_1588 a40_1460 a40_13e0 a40_400 a40_380 a40_2e0 a40_2c0 a40_2a0 w40_1020 w40_a20 w40_130 w40_12c w40_128 w40_124 w40_120 w40_11c w40_118 w40_114 w40_110 w40_10c w40_108 w40_104 w40_100 w40_fc w40_f8 w40_f4 w40_f0 w40_ec w40_e8 w40_e4 w40_e0 w40_dc w40_d8 w40_d4 w40_d0 w40_cc w40_c8 w40_c4 w40_c0 w40_bc w40_b8 w40_b4 w40_b0 w40_ac w40_a8 w40_a4 w40_a0 w40_9c w40_98 w40_94 w40_90 w40_8c w40_88 w40_84 w40_80 w40_7c w40_78 w40_70 w40_6c w40_68 w40_64 w40_60 w40_5c w40_58 w40_54 w40_50 w40_4c w40_48 w40_44 w40_40 w40_3c w40_38 w40_34 w40_30 w40_2c w40_28 w40_24 g40_12 g40_11 g40_10 g40_9 g40_27 g40_26 g40_25 g40_24 g40_23 g40_22 g40_21 g40_20 g40_19 g40_18 g40_8 g40_4 g40_3 g40_2 V40 E40 fR40 t40 fr40 rb40 s40 m40 u40 c40
  -- 0x1874
  obtain ⟨n42, c42, u42⟩ := s41.block svEcW1874 E41.self svEcW1874_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m42 : n42.mem = n41.mem := u42.mem
  have s42 : St n42.mem SV n42 0x188C (reg n42) := ⟨u42.pc, rfl, fun _ => rfl⟩
  have rb42 : ∀ q, reg n42 q = (runBlock svEcW1874 (n41.mem, reg n41)).2 q := fun q => by rw [u42.regs]
  have fr42 : ∀ x, SvR B x → n42.mem x = n41.mem x := fun x _ => by rw [m42]
  have t42 : Steps n0 n42 := t41.trans c42
  have fR42 : ∀ x, SvR B x → n42.mem x = M0 x := fun x hx => (fr42 x hx).trans (fR41 x hx)
  have E42 : SvCode n42.mem := E41.fr F fr42
  have V42 : SvSaves B n42.mem v := V41.same m42
  have g42_2 : reg n42 sp = B + 0x21A0 := by
    rw [rb42, runBlock_reg _ _ _ sp s41.zero (by decide), g41_2]
  have g42_3 : reg n42 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb42, runBlock_reg _ _ _ (3 : Fin 32) s41.zero (by decide), g41_3]
  have g42_4 : reg n42 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb42, runBlock_reg _ _ _ (4 : Fin 32) s41.zero (by decide), g41_4]
  have g42_8 : reg n42 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb42, runBlock_reg _ _ _ (8 : Fin 32) s41.zero (by decide), g41_8]
  have g42_9 : reg n42 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by
    rw [rb42, runBlock_reg _ _ _ (9 : Fin 32) s41.zero (by decide), g41_9]
  have g42_18 : reg n42 (18 : Fin 32) = out := by
    rw [rb42, runBlock_reg _ _ _ (18 : Fin 32) s41.zero (by decide), g41_18]
  have g42_19 : reg n42 (19 : Fin 32) = bp := by
    rw [rb42, runBlock_reg _ _ _ (19 : Fin 32) s41.zero (by decide), g41_19]
  have g42_20 : reg n42 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb42, runBlock_reg _ _ _ (20 : Fin 32) s41.zero (by decide), g41_20]
  have g42_21 : reg n42 (21 : Fin 32) = s5v := by
    rw [rb42, runBlock_reg _ _ _ (21 : Fin 32) s41.zero (by decide), g41_21]
  have g42_22 : reg n42 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by
    rw [rb42, runBlock_reg _ _ _ (22 : Fin 32) s41.zero (by decide), g41_22]
  have g42_23 : reg n42 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by
    rw [rb42, runBlock_reg _ _ _ (23 : Fin 32) s41.zero (by decide), g41_23]
  have g42_24 : reg n42 (24 : Fin 32) = s8v := by
    rw [rb42, runBlock_reg _ _ _ (24 : Fin 32) s41.zero (by decide), g41_24]
  have g42_25 : reg n42 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb42, runBlock_reg _ _ _ (25 : Fin 32) s41.zero (by decide), g41_25]
  have g42_26 : reg n42 (26 : Fin 32) = x26 := by
    rw [rb42, runBlock_reg _ _ _ (26 : Fin 32) s41.zero (by decide), g41_26]
  have g42_27 : reg n42 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb42, runBlock_reg _ _ _ (27 : Fin 32) s41.zero (by decide), g41_27]
  have g42_10 : reg n42 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by
    rw [rb42]; simp +decide only [runBlock, BInstr.run, svEcW1874, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g41_2, g41_3, g41_4, g41_8, g41_9, g41_18, g41_19, g41_20, g41_21, g41_22, g41_23, g41_24, g41_25, g41_26, g41_27, s41.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g42_11 : reg n42 a1 = BitVec.ofNat 32 0x101 := by
    rw [rb42]; simp +decide only [runBlock, BInstr.run, svEcW1874, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g41_2, g41_3, g41_4, g41_8, g41_9, g41_18, g41_19, g41_20, g41_21, g41_22, g41_23, g41_24, g41_25, g41_26, g41_27, s41.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g42_12 : reg n42 a2 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
    rw [rb42]; simp +decide only [runBlock, BInstr.run, svEcW1874, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g41_2, g41_3, g41_4, g41_8, g41_9, g41_18, g41_19, g41_20, g41_21, g41_22, g41_23, g41_24, g41_25, g41_26, g41_27, s41.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g42_13 : reg n42 a3 = BitVec.ofNat 32 0x20 := by
    rw [rb42]; simp +decide only [runBlock, BInstr.run, svEcW1874, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g41_2, g41_3, g41_4, g41_8, g41_9, g41_18, g41_19, g41_20, g41_21, g41_22, g41_23, g41_24, g41_25, g41_26, g41_27, s41.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g42_14 : reg n42 a4 = BitVec.ofNat 32 0x100 := by
    rw [rb42]; simp +decide only [runBlock, BInstr.run, svEcW1874, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g41_2, g41_3, g41_4, g41_8, g41_9, g41_18, g41_19, g41_20, g41_21, g41_22, g41_23, g41_24, g41_25, g41_26, g41_27, s41.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w42_24 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m42]; exact w41_24
  have w42_28 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m42]; exact w41_28
  have w42_2c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m42]; exact w41_2c
  have w42_30 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m42]; exact w41_30
  have w42_34 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m42]; exact w41_34
  have w42_38 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m42]; exact w41_38
  have w42_3c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m42]; exact w41_3c
  have w42_40 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m42]; exact w41_40
  have w42_44 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m42]; exact w41_44
  have w42_48 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m42]; exact w41_48
  have w42_4c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m42]; exact w41_4c
  have w42_50 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m42]; exact w41_50
  have w42_54 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m42]; exact w41_54
  have w42_58 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m42]; exact w41_58
  have w42_5c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m42]; exact w41_5c
  have w42_60 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m42]; exact w41_60
  have w42_64 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m42]; exact w41_64
  have w42_68 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m42]; exact w41_68
  have w42_6c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m42]; exact w41_6c
  have w42_70 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m42]; exact w41_70
  have w42_78 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m42]; exact w41_78
  have w42_7c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m42]; exact w41_7c
  have w42_80 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m42]; exact w41_80
  have w42_84 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m42]; exact w41_84
  have w42_88 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m42]; exact w41_88
  have w42_8c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m42]; exact w41_8c
  have w42_90 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m42]; exact w41_90
  have w42_94 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m42]; exact w41_94
  have w42_98 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m42]; exact w41_98
  have w42_9c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m42]; exact w41_9c
  have w42_a0 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m42]; exact w41_a0
  have w42_a4 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m42]; exact w41_a4
  have w42_a8 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m42]; exact w41_a8
  have w42_ac : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m42]; exact w41_ac
  have w42_b0 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m42]; exact w41_b0
  have w42_b4 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m42]; exact w41_b4
  have w42_b8 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m42]; exact w41_b8
  have w42_bc : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m42]; exact w41_bc
  have w42_c0 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m42]; exact w41_c0
  have w42_c4 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m42]; exact w41_c4
  have w42_c8 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m42]; exact w41_c8
  have w42_cc : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m42]; exact w41_cc
  have w42_d0 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m42]; exact w41_d0
  have w42_d4 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m42]; exact w41_d4
  have w42_d8 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m42]; exact w41_d8
  have w42_dc : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m42]; exact w41_dc
  have w42_e0 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m42]; exact w41_e0
  have w42_e4 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m42]; exact w41_e4
  have w42_e8 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m42]; exact w41_e8
  have w42_ec : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m42]; exact w41_ec
  have w42_f0 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m42]; exact w41_f0
  have w42_f4 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m42]; exact w41_f4
  have w42_f8 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m42]; exact w41_f8
  have w42_fc : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m42]; exact w41_fc
  have w42_100 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m42]; exact w41_100
  have w42_104 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m42]; exact w41_104
  have w42_108 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m42]; exact w41_108
  have w42_10c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m42]; exact w41_10c
  have w42_110 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m42]; exact w41_110
  have w42_114 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m42]; exact w41_114
  have w42_118 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m42]; exact w41_118
  have w42_11c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m42]; exact w41_11c
  have w42_120 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m42]; exact w41_120
  have w42_124 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m42]; exact w41_124
  have w42_128 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m42]; exact w41_128
  have w42_12c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m42]; exact w41_12c
  have w42_130 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m42]; exact w41_130
  have w42_a20 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m42]; exact w41_a20
  have w42_1020 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m42]; exact w41_1020
  have a42_2a0 : accV n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m42]; exact a41_2a0
  have a42_2c0 : accV n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m42]; exact a41_2c0
  have a42_2e0 : accV n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m42]; exact a41_2e0
  have a42_380 : accV n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m42]; exact a41_380
  have a42_400 : accV n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m42]; exact a41_400
  have a42_13e0 : accV n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := by rw [m42]; exact a41_13e0
  have a42_1460 : accV n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := by rw [m42]; exact a41_1460
  have a42_1588 : accV n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U2 := by rw [m42]; exact a41_1588
  have p42_320 : ptF n42.mem B 0x320 = P0 := by rw [m42]; exact p41_320
  have p42_3a0 : ptF n42.mem B 0x3A0 = P1 := by rw [m42]; exact p41_3a0
  have p42_420 : ptF n42.mem B 0x420 = tbl2 P0 0 := by rw [m42]; exact p41_420
  have p42_480 : ptF n42.mem B 0x480 = tbl2 P0 1 := by rw [m42]; exact p41_480
  have p42_4e0 : ptF n42.mem B 0x4E0 = tbl2 P0 2 := by rw [m42]; exact p41_4e0
  have p42_540 : ptF n42.mem B 0x540 = tbl2 P0 3 := by rw [m42]; exact p41_540
  have p42_5a0 : ptF n42.mem B 0x5A0 = tbl2 P0 4 := by rw [m42]; exact p41_5a0
  have p42_600 : ptF n42.mem B 0x600 = tbl2 P0 5 := by rw [m42]; exact p41_600
  have p42_660 : ptF n42.mem B 0x660 = tbl2 P0 6 := by rw [m42]; exact p41_660
  have p42_6c0 : ptF n42.mem B 0x6C0 = tbl2 P0 7 := by rw [m42]; exact p41_6c0
  have p42_720 : ptF n42.mem B 0x720 = tbl2 P1 0 := by rw [m42]; exact p41_720
  have p42_780 : ptF n42.mem B 0x780 = tbl2 P1 1 := by rw [m42]; exact p41_780
  have p42_7e0 : ptF n42.mem B 0x7E0 = tbl2 P1 2 := by rw [m42]; exact p41_7e0
  have p42_840 : ptF n42.mem B 0x840 = tbl2 P1 3 := by rw [m42]; exact p41_840
  have p42_8a0 : ptF n42.mem B 0x8A0 = tbl2 P1 4 := by rw [m42]; exact p41_8a0
  have p42_900 : ptF n42.mem B 0x900 = tbl2 P1 5 := by rw [m42]; exact p41_900
  have p42_960 : ptF n42.mem B 0x960 = tbl2 P1 6 := by rw [m42]; exact p41_960
  have p42_9c0 : ptF n42.mem B 0x9C0 = tbl2 P1 7 := by rw [m42]; exact p41_9c0
  have p42_b40 : ptF n42.mem B 0xB40 = tbl2 P0 3 := by rw [m42]; exact p41_b40
  have p42_ba0 : ptF n42.mem B 0xBA0 = tbl2 P0 4 := by rw [m42]; exact p41_ba0
  have p42_c00 : ptF n42.mem B 0xC00 = tbl2 P0 5 := by rw [m42]; exact p41_c00
  have p42_c60 : ptF n42.mem B 0xC60 = tbl2 P0 6 := by rw [m42]; exact p41_c60
  have p42_cc0 : ptF n42.mem B 0xCC0 = tbl2 P0 7 := by rw [m42]; exact p41_cc0
  have p42_d20 : ptF n42.mem B 0xD20 = tbl2 P1 0 := by rw [m42]; exact p41_d20
  have p42_d80 : ptF n42.mem B 0xD80 = tbl2 P1 1 := by rw [m42]; exact p41_d80
  have p42_de0 : ptF n42.mem B 0xDE0 = tbl2 P1 2 := by rw [m42]; exact p41_de0
  have p42_e40 : ptF n42.mem B 0xE40 = tbl2 P1 3 := by rw [m42]; exact p41_e40
  have p42_ea0 : ptF n42.mem B 0xEA0 = tbl2 P1 4 := by rw [m42]; exact p41_ea0
  have p42_f00 : ptF n42.mem B 0xF00 = tbl2 P1 5 := by rw [m42]; exact p41_f00
  have p42_f60 : ptF n42.mem B 0xF60 = tbl2 P1 6 := by rw [m42]; exact p41_f60
  have p42_fc0 : ptF n42.mem B 0xFC0 = tbl2 P1 7 := by rw [m42]; exact p41_fc0
  have p42_1380 : ptF n42.mem B 0x1380 = P0 := by rw [m42]; exact p41_1380
  have p42_1400 : ptF n42.mem B 0x1400 = P1 := by rw [m42]; exact p41_1400
  have mb42_a24 : memBytes n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m42]; exact mb41_a24
  have mb42_1024 : memBytes n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) 0x101 = List.replicate 0x101 0 := by rw [m42]; exact mb41_1024
  have mb42_1320 : leN (memBytes n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U2 := by rw [m42]; exact mb41_1320
  have mb42_1480 : memBytes n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 0x101 = List.replicate 0x101 0 := by rw [m42]; exact mb41_1480
  clear mb41_1024 mb41_1480 mb41_1320 mb41_a24 p41_1400 p41_1380 p41_fc0 p41_f60 p41_f00 p41_ea0 p41_e40 p41_de0 p41_d80 p41_d20 p41_cc0 p41_c60 p41_c00 p41_ba0 p41_b40 p41_9c0 p41_960 p41_900 p41_8a0 p41_840 p41_7e0 p41_780 p41_720 p41_6c0 p41_660 p41_600 p41_5a0 p41_540 p41_4e0 p41_480 p41_420 p41_3a0 p41_320 a41_1588 a41_1460 a41_13e0 a41_400 a41_380 a41_2e0 a41_2c0 a41_2a0 w41_1020 w41_a20 w41_130 w41_12c w41_128 w41_124 w41_120 w41_11c w41_118 w41_114 w41_110 w41_10c w41_108 w41_104 w41_100 w41_fc w41_f8 w41_f4 w41_f0 w41_ec w41_e8 w41_e4 w41_e0 w41_dc w41_d8 w41_d4 w41_d0 w41_cc w41_c8 w41_c4 w41_c0 w41_bc w41_b8 w41_b4 w41_b0 w41_ac w41_a8 w41_a4 w41_a0 w41_9c w41_98 w41_94 w41_90 w41_8c w41_88 w41_84 w41_80 w41_7c w41_78 w41_70 w41_6c w41_68 w41_64 w41_60 w41_5c w41_58 w41_54 w41_50 w41_4c w41_48 w41_44 w41_40 w41_3c w41_38 w41_34 w41_30 w41_2c w41_28 w41_24 g41_27 g41_26 g41_25 g41_24 g41_23 g41_22 g41_21 g41_20 g41_19 g41_18 g41_9 g41_8 g41_4 g41_3 g41_2 V41 E41 fR41 t41 fr41 s41 X41 K41 P41
  -- 0x188C: wnaf_form
  obtain ⟨n43, P43, K43, A43, D43, H43⟩ := sv_wf (cw := 0x1024) (cc := 0x1320) F E42 (WN0.sv F fR42) s42
    sv_at_188c sv_at_1890 (by decide) (by decide) g42_2 g42_10 g42_11
    g42_12 g42_13 g42_14 (by decide) (by decide) (by decide) mb42_1320 mb42_1024
  have s43 := P43.st
  have fr43 := P43.fr
  have t43 : Steps n0 n43 := t42.trans P43.steps
  have fR43 : ∀ x, SvR B x → n43.mem x = M0 x := fun x hx => (fr43 x hx).trans (fR42 x hx)
  have E43 : SvCode n43.mem := E42.fr F fr43
  have V43 : SvSaves B n43.mem v := V42.keep K43 (by decide)
  have g43_2 : reg n43 sp = B + 0x21A0 := by rw [P43.regs sp (by decide), g42_2]
  have g43_3 : reg n43 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P43.regs (3 : Fin 32) (by decide), g42_3]
  have g43_4 : reg n43 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P43.regs (4 : Fin 32) (by decide), g42_4]
  have g43_8 : reg n43 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P43.regs (8 : Fin 32) (by decide), g42_8]
  have g43_9 : reg n43 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by rw [P43.regs (9 : Fin 32) (by decide), g42_9]
  have g43_18 : reg n43 (18 : Fin 32) = out := by rw [P43.regs (18 : Fin 32) (by decide), g42_18]
  have g43_19 : reg n43 (19 : Fin 32) = bp := by rw [P43.regs (19 : Fin 32) (by decide), g42_19]
  have g43_20 : reg n43 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P43.regs (20 : Fin 32) (by decide), g42_20]
  have g43_21 : reg n43 (21 : Fin 32) = s5v := by rw [P43.regs (21 : Fin 32) (by decide), g42_21]
  have g43_22 : reg n43 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [P43.regs (22 : Fin 32) (by decide), g42_22]
  have g43_23 : reg n43 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by rw [P43.regs (23 : Fin 32) (by decide), g42_23]
  have g43_24 : reg n43 (24 : Fin 32) = s8v := by rw [P43.regs (24 : Fin 32) (by decide), g42_24]
  have g43_25 : reg n43 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P43.regs (25 : Fin 32) (by decide), g42_25]
  have g43_26 : reg n43 (26 : Fin 32) = x26 := by rw [P43.regs (26 : Fin 32) (by decide), g42_26]
  have g43_27 : reg n43 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P43.regs (27 : Fin 32) (by decide), g42_27]
  have w43_24 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K43.w32 (by decide) (by decide)).trans w42_24
  have w43_28 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K43.w32 (by decide) (by decide)).trans w42_28
  have w43_2c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K43.w32 (by decide) (by decide)).trans w42_2c
  have w43_30 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K43.w32 (by decide) (by decide)).trans w42_30
  have w43_34 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K43.w32 (by decide) (by decide)).trans w42_34
  have w43_38 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K43.w32 (by decide) (by decide)).trans w42_38
  have w43_3c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K43.w32 (by decide) (by decide)).trans w42_3c
  have w43_40 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K43.w32 (by decide) (by decide)).trans w42_40
  have w43_44 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K43.w32 (by decide) (by decide)).trans w42_44
  have w43_48 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K43.w32 (by decide) (by decide)).trans w42_48
  have w43_4c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K43.w32 (by decide) (by decide)).trans w42_4c
  have w43_50 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K43.w32 (by decide) (by decide)).trans w42_50
  have w43_54 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K43.w32 (by decide) (by decide)).trans w42_54
  have w43_58 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K43.w32 (by decide) (by decide)).trans w42_58
  have w43_5c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K43.w32 (by decide) (by decide)).trans w42_5c
  have w43_60 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K43.w32 (by decide) (by decide)).trans w42_60
  have w43_64 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K43.w32 (by decide) (by decide)).trans w42_64
  have w43_68 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K43.w32 (by decide) (by decide)).trans w42_68
  have w43_6c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K43.w32 (by decide) (by decide)).trans w42_6c
  have w43_70 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K43.w32 (by decide) (by decide)).trans w42_70
  have w43_78 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := (K43.w32 (by decide) (by decide)).trans w42_78
  have w43_7c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K43.w32 (by decide) (by decide)).trans w42_7c
  have w43_80 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K43.w32 (by decide) (by decide)).trans w42_80
  have w43_84 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K43.w32 (by decide) (by decide)).trans w42_84
  have w43_88 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K43.w32 (by decide) (by decide)).trans w42_88
  have w43_8c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K43.w32 (by decide) (by decide)).trans w42_8c
  have w43_90 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K43.w32 (by decide) (by decide)).trans w42_90
  have w43_94 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K43.w32 (by decide) (by decide)).trans w42_94
  have w43_98 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K43.w32 (by decide) (by decide)).trans w42_98
  have w43_9c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K43.w32 (by decide) (by decide)).trans w42_9c
  have w43_a0 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K43.w32 (by decide) (by decide)).trans w42_a0
  have w43_a4 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K43.w32 (by decide) (by decide)).trans w42_a4
  have w43_a8 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K43.w32 (by decide) (by decide)).trans w42_a8
  have w43_ac : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K43.w32 (by decide) (by decide)).trans w42_ac
  have w43_b0 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K43.w32 (by decide) (by decide)).trans w42_b0
  have w43_b4 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K43.w32 (by decide) (by decide)).trans w42_b4
  have w43_b8 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K43.w32 (by decide) (by decide)).trans w42_b8
  have w43_bc : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K43.w32 (by decide) (by decide)).trans w42_bc
  have w43_c0 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K43.w32 (by decide) (by decide)).trans w42_c0
  have w43_c4 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K43.w32 (by decide) (by decide)).trans w42_c4
  have w43_c8 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K43.w32 (by decide) (by decide)).trans w42_c8
  have w43_cc : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K43.w32 (by decide) (by decide)).trans w42_cc
  have w43_d0 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K43.w32 (by decide) (by decide)).trans w42_d0
  have w43_d4 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K43.w32 (by decide) (by decide)).trans w42_d4
  have w43_d8 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K43.w32 (by decide) (by decide)).trans w42_d8
  have w43_dc : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K43.w32 (by decide) (by decide)).trans w42_dc
  have w43_e0 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K43.w32 (by decide) (by decide)).trans w42_e0
  have w43_e4 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K43.w32 (by decide) (by decide)).trans w42_e4
  have w43_e8 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K43.w32 (by decide) (by decide)).trans w42_e8
  have w43_ec : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K43.w32 (by decide) (by decide)).trans w42_ec
  have w43_f0 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K43.w32 (by decide) (by decide)).trans w42_f0
  have w43_f4 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K43.w32 (by decide) (by decide)).trans w42_f4
  have w43_f8 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K43.w32 (by decide) (by decide)).trans w42_f8
  have w43_fc : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K43.w32 (by decide) (by decide)).trans w42_fc
  have w43_100 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K43.w32 (by decide) (by decide)).trans w42_100
  have w43_104 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K43.w32 (by decide) (by decide)).trans w42_104
  have w43_108 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K43.w32 (by decide) (by decide)).trans w42_108
  have w43_10c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K43.w32 (by decide) (by decide)).trans w42_10c
  have w43_110 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K43.w32 (by decide) (by decide)).trans w42_110
  have w43_114 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K43.w32 (by decide) (by decide)).trans w42_114
  have w43_118 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K43.w32 (by decide) (by decide)).trans w42_118
  have w43_11c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K43.w32 (by decide) (by decide)).trans w42_11c
  have w43_120 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K43.w32 (by decide) (by decide)).trans w42_120
  have w43_124 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K43.w32 (by decide) (by decide)).trans w42_124
  have w43_128 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K43.w32 (by decide) (by decide)).trans w42_128
  have w43_12c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K43.w32 (by decide) (by decide)).trans w42_12c
  have w43_130 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K43.w32 (by decide) (by decide)).trans w42_130
  have w43_a20 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := (K43.w32 (by decide) (by decide)).trans w42_a20
  have w43_1020 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := (K43.w32 (by decide) (by decide)).trans w42_1020
  have a43_2a0 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K43.acc (by decide) (by decide)).trans a42_2a0
  have a43_2c0 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K43.acc (by decide) (by decide)).trans a42_2c0
  have a43_2e0 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K43.acc (by decide) (by decide)).trans a42_2e0
  have a43_380 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := (K43.acc (by decide) (by decide)).trans a42_380
  have a43_400 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := (K43.acc (by decide) (by decide)).trans a42_400
  have a43_13e0 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := (K43.acc (by decide) (by decide)).trans a42_13e0
  have a43_1460 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := (K43.acc (by decide) (by decide)).trans a42_1460
  have a43_1588 : accV n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U2 := (K43.acc (by decide) (by decide)).trans a42_1588
  have p43_320 : ptF n43.mem B 0x320 = P0 := (K43.pt (by decide) (by decide)).trans p42_320
  have p43_3a0 : ptF n43.mem B 0x3A0 = P1 := (K43.pt (by decide) (by decide)).trans p42_3a0
  have p43_420 : ptF n43.mem B 0x420 = tbl2 P0 0 := (K43.pt (by decide) (by decide)).trans p42_420
  have p43_480 : ptF n43.mem B 0x480 = tbl2 P0 1 := (K43.pt (by decide) (by decide)).trans p42_480
  have p43_4e0 : ptF n43.mem B 0x4E0 = tbl2 P0 2 := (K43.pt (by decide) (by decide)).trans p42_4e0
  have p43_540 : ptF n43.mem B 0x540 = tbl2 P0 3 := (K43.pt (by decide) (by decide)).trans p42_540
  have p43_5a0 : ptF n43.mem B 0x5A0 = tbl2 P0 4 := (K43.pt (by decide) (by decide)).trans p42_5a0
  have p43_600 : ptF n43.mem B 0x600 = tbl2 P0 5 := (K43.pt (by decide) (by decide)).trans p42_600
  have p43_660 : ptF n43.mem B 0x660 = tbl2 P0 6 := (K43.pt (by decide) (by decide)).trans p42_660
  have p43_6c0 : ptF n43.mem B 0x6C0 = tbl2 P0 7 := (K43.pt (by decide) (by decide)).trans p42_6c0
  have p43_720 : ptF n43.mem B 0x720 = tbl2 P1 0 := (K43.pt (by decide) (by decide)).trans p42_720
  have p43_780 : ptF n43.mem B 0x780 = tbl2 P1 1 := (K43.pt (by decide) (by decide)).trans p42_780
  have p43_7e0 : ptF n43.mem B 0x7E0 = tbl2 P1 2 := (K43.pt (by decide) (by decide)).trans p42_7e0
  have p43_840 : ptF n43.mem B 0x840 = tbl2 P1 3 := (K43.pt (by decide) (by decide)).trans p42_840
  have p43_8a0 : ptF n43.mem B 0x8A0 = tbl2 P1 4 := (K43.pt (by decide) (by decide)).trans p42_8a0
  have p43_900 : ptF n43.mem B 0x900 = tbl2 P1 5 := (K43.pt (by decide) (by decide)).trans p42_900
  have p43_960 : ptF n43.mem B 0x960 = tbl2 P1 6 := (K43.pt (by decide) (by decide)).trans p42_960
  have p43_9c0 : ptF n43.mem B 0x9C0 = tbl2 P1 7 := (K43.pt (by decide) (by decide)).trans p42_9c0
  have p43_b40 : ptF n43.mem B 0xB40 = tbl2 P0 3 := (K43.pt (by decide) (by decide)).trans p42_b40
  have p43_ba0 : ptF n43.mem B 0xBA0 = tbl2 P0 4 := (K43.pt (by decide) (by decide)).trans p42_ba0
  have p43_c00 : ptF n43.mem B 0xC00 = tbl2 P0 5 := (K43.pt (by decide) (by decide)).trans p42_c00
  have p43_c60 : ptF n43.mem B 0xC60 = tbl2 P0 6 := (K43.pt (by decide) (by decide)).trans p42_c60
  have p43_cc0 : ptF n43.mem B 0xCC0 = tbl2 P0 7 := (K43.pt (by decide) (by decide)).trans p42_cc0
  have p43_d20 : ptF n43.mem B 0xD20 = tbl2 P1 0 := (K43.pt (by decide) (by decide)).trans p42_d20
  have p43_d80 : ptF n43.mem B 0xD80 = tbl2 P1 1 := (K43.pt (by decide) (by decide)).trans p42_d80
  have p43_de0 : ptF n43.mem B 0xDE0 = tbl2 P1 2 := (K43.pt (by decide) (by decide)).trans p42_de0
  have p43_e40 : ptF n43.mem B 0xE40 = tbl2 P1 3 := (K43.pt (by decide) (by decide)).trans p42_e40
  have p43_ea0 : ptF n43.mem B 0xEA0 = tbl2 P1 4 := (K43.pt (by decide) (by decide)).trans p42_ea0
  have p43_f00 : ptF n43.mem B 0xF00 = tbl2 P1 5 := (K43.pt (by decide) (by decide)).trans p42_f00
  have p43_f60 : ptF n43.mem B 0xF60 = tbl2 P1 6 := (K43.pt (by decide) (by decide)).trans p42_f60
  have p43_fc0 : ptF n43.mem B 0xFC0 = tbl2 P1 7 := (K43.pt (by decide) (by decide)).trans p42_fc0
  have p43_1380 : ptF n43.mem B 0x1380 = P0 := (K43.pt (by decide) (by decide)).trans p42_1380
  have p43_1400 : ptF n43.mem B 0x1400 = P1 := (K43.pt (by decide) (by decide)).trans p42_1400
  have mb43_a24 : memBytes n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [K43.mb (by decide) (by decide)]; exact mb42_a24
  have mb43_1320 : leN (memBytes n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U2 := by rw [K43.mb (by decide) (by decide)]; exact mb42_1320
  have mb43_1480 : memBytes n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 0x101 = List.replicate 0x101 0 := by rw [K43.mb (by decide) (by decide)]; exact mb42_1480
  have g43_10 : reg n43 a0 = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := A43
  have mb43_1024 : memBytes n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := D43
  clear mb42_1480 mb42_1320 mb42_1024 mb42_a24 p42_1400 p42_1380 p42_fc0 p42_f60 p42_f00 p42_ea0 p42_e40 p42_de0 p42_d80 p42_d20 p42_cc0 p42_c60 p42_c00 p42_ba0 p42_b40 p42_9c0 p42_960 p42_900 p42_8a0 p42_840 p42_7e0 p42_780 p42_720 p42_6c0 p42_660 p42_600 p42_5a0 p42_540 p42_4e0 p42_480 p42_420 p42_3a0 p42_320 a42_1588 a42_1460 a42_13e0 a42_400 a42_380 a42_2e0 a42_2c0 a42_2a0 w42_1020 w42_a20 w42_130 w42_12c w42_128 w42_124 w42_120 w42_11c w42_118 w42_114 w42_110 w42_10c w42_108 w42_104 w42_100 w42_fc w42_f8 w42_f4 w42_f0 w42_ec w42_e8 w42_e4 w42_e0 w42_dc w42_d8 w42_d4 w42_d0 w42_cc w42_c8 w42_c4 w42_c0 w42_bc w42_b8 w42_b4 w42_b0 w42_ac w42_a8 w42_a4 w42_a0 w42_9c w42_98 w42_94 w42_90 w42_8c w42_88 w42_84 w42_80 w42_7c w42_78 w42_70 w42_6c w42_68 w42_64 w42_60 w42_5c w42_58 w42_54 w42_50 w42_4c w42_48 w42_44 w42_40 w42_3c w42_38 w42_34 w42_30 w42_2c w42_28 w42_24 g42_14 g42_13 g42_12 g42_11 g42_10 g42_27 g42_26 g42_25 g42_24 g42_23 g42_22 g42_21 g42_20 g42_19 g42_18 g42_9 g42_8 g42_4 g42_3 g42_2 V42 E42 fR42 t42 fr42 rb42 s42 m42 u42 c42
  -- 0x1894: sw
  obtain ⟨n44, d44, s44, fr44, K44, W44, rg44⟩ := sv_sw F E43 s43 sv_at_1894 (off' := 0x1898) (c := 0x1020)
    (by decide) (by rw [g43_27]; sv_addr) (by decide) (by decide)
  have t44 : Steps n0 n44 := t43.trans d44
  have fR44 : ∀ x, SvR B x → n44.mem x = M0 x := fun x hx => (fr44 x hx).trans (fR43 x hx)
  have E44 : SvCode n44.mem := E43.fr F fr44
  have V44 : SvSaves B n44.mem v := V43.keep K44 (by decide)
  have g44_2 : reg n44 sp = B + 0x21A0 := by rw [rg44 sp, g43_2]
  have g44_3 : reg n44 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg44 (3 : Fin 32), g43_3]
  have g44_4 : reg n44 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg44 (4 : Fin 32), g43_4]
  have g44_8 : reg n44 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rg44 (8 : Fin 32), g43_8]
  have g44_9 : reg n44 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by rw [rg44 (9 : Fin 32), g43_9]
  have g44_10 : reg n44 a0 = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by rw [rg44 a0, g43_10]
  have g44_18 : reg n44 (18 : Fin 32) = out := by rw [rg44 (18 : Fin 32), g43_18]
  have g44_19 : reg n44 (19 : Fin 32) = bp := by rw [rg44 (19 : Fin 32), g43_19]
  have g44_20 : reg n44 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg44 (20 : Fin 32), g43_20]
  have g44_21 : reg n44 (21 : Fin 32) = s5v := by rw [rg44 (21 : Fin 32), g43_21]
  have g44_22 : reg n44 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [rg44 (22 : Fin 32), g43_22]
  have g44_23 : reg n44 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by rw [rg44 (23 : Fin 32), g43_23]
  have g44_24 : reg n44 (24 : Fin 32) = s8v := by rw [rg44 (24 : Fin 32), g43_24]
  have g44_25 : reg n44 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [rg44 (25 : Fin 32), g43_25]
  have g44_26 : reg n44 (26 : Fin 32) = x26 := by rw [rg44 (26 : Fin 32), g43_26]
  have g44_27 : reg n44 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg44 (27 : Fin 32), g43_27]
  have w44_24 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K44.w32 (by decide) (by decide)).trans w43_24
  have w44_28 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K44.w32 (by decide) (by decide)).trans w43_28
  have w44_2c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K44.w32 (by decide) (by decide)).trans w43_2c
  have w44_30 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K44.w32 (by decide) (by decide)).trans w43_30
  have w44_34 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K44.w32 (by decide) (by decide)).trans w43_34
  have w44_38 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K44.w32 (by decide) (by decide)).trans w43_38
  have w44_3c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K44.w32 (by decide) (by decide)).trans w43_3c
  have w44_40 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K44.w32 (by decide) (by decide)).trans w43_40
  have w44_44 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K44.w32 (by decide) (by decide)).trans w43_44
  have w44_48 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K44.w32 (by decide) (by decide)).trans w43_48
  have w44_4c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K44.w32 (by decide) (by decide)).trans w43_4c
  have w44_50 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K44.w32 (by decide) (by decide)).trans w43_50
  have w44_54 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K44.w32 (by decide) (by decide)).trans w43_54
  have w44_58 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K44.w32 (by decide) (by decide)).trans w43_58
  have w44_5c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K44.w32 (by decide) (by decide)).trans w43_5c
  have w44_60 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K44.w32 (by decide) (by decide)).trans w43_60
  have w44_64 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K44.w32 (by decide) (by decide)).trans w43_64
  have w44_68 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K44.w32 (by decide) (by decide)).trans w43_68
  have w44_6c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K44.w32 (by decide) (by decide)).trans w43_6c
  have w44_70 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K44.w32 (by decide) (by decide)).trans w43_70
  have w44_78 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := (K44.w32 (by decide) (by decide)).trans w43_78
  have w44_7c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K44.w32 (by decide) (by decide)).trans w43_7c
  have w44_80 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K44.w32 (by decide) (by decide)).trans w43_80
  have w44_84 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K44.w32 (by decide) (by decide)).trans w43_84
  have w44_88 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K44.w32 (by decide) (by decide)).trans w43_88
  have w44_8c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K44.w32 (by decide) (by decide)).trans w43_8c
  have w44_90 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K44.w32 (by decide) (by decide)).trans w43_90
  have w44_94 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K44.w32 (by decide) (by decide)).trans w43_94
  have w44_98 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K44.w32 (by decide) (by decide)).trans w43_98
  have w44_9c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K44.w32 (by decide) (by decide)).trans w43_9c
  have w44_a0 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K44.w32 (by decide) (by decide)).trans w43_a0
  have w44_a4 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K44.w32 (by decide) (by decide)).trans w43_a4
  have w44_a8 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K44.w32 (by decide) (by decide)).trans w43_a8
  have w44_ac : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K44.w32 (by decide) (by decide)).trans w43_ac
  have w44_b0 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K44.w32 (by decide) (by decide)).trans w43_b0
  have w44_b4 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K44.w32 (by decide) (by decide)).trans w43_b4
  have w44_b8 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K44.w32 (by decide) (by decide)).trans w43_b8
  have w44_bc : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K44.w32 (by decide) (by decide)).trans w43_bc
  have w44_c0 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K44.w32 (by decide) (by decide)).trans w43_c0
  have w44_c4 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K44.w32 (by decide) (by decide)).trans w43_c4
  have w44_c8 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K44.w32 (by decide) (by decide)).trans w43_c8
  have w44_cc : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K44.w32 (by decide) (by decide)).trans w43_cc
  have w44_d0 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K44.w32 (by decide) (by decide)).trans w43_d0
  have w44_d4 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K44.w32 (by decide) (by decide)).trans w43_d4
  have w44_d8 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K44.w32 (by decide) (by decide)).trans w43_d8
  have w44_dc : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K44.w32 (by decide) (by decide)).trans w43_dc
  have w44_e0 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K44.w32 (by decide) (by decide)).trans w43_e0
  have w44_e4 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K44.w32 (by decide) (by decide)).trans w43_e4
  have w44_e8 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K44.w32 (by decide) (by decide)).trans w43_e8
  have w44_ec : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K44.w32 (by decide) (by decide)).trans w43_ec
  have w44_f0 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K44.w32 (by decide) (by decide)).trans w43_f0
  have w44_f4 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K44.w32 (by decide) (by decide)).trans w43_f4
  have w44_f8 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K44.w32 (by decide) (by decide)).trans w43_f8
  have w44_fc : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K44.w32 (by decide) (by decide)).trans w43_fc
  have w44_100 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K44.w32 (by decide) (by decide)).trans w43_100
  have w44_104 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K44.w32 (by decide) (by decide)).trans w43_104
  have w44_108 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K44.w32 (by decide) (by decide)).trans w43_108
  have w44_10c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K44.w32 (by decide) (by decide)).trans w43_10c
  have w44_110 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K44.w32 (by decide) (by decide)).trans w43_110
  have w44_114 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K44.w32 (by decide) (by decide)).trans w43_114
  have w44_118 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K44.w32 (by decide) (by decide)).trans w43_118
  have w44_11c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K44.w32 (by decide) (by decide)).trans w43_11c
  have w44_120 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K44.w32 (by decide) (by decide)).trans w43_120
  have w44_124 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K44.w32 (by decide) (by decide)).trans w43_124
  have w44_128 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K44.w32 (by decide) (by decide)).trans w43_128
  have w44_12c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K44.w32 (by decide) (by decide)).trans w43_12c
  have w44_130 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K44.w32 (by decide) (by decide)).trans w43_130
  have w44_a20 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := (K44.w32 (by decide) (by decide)).trans w43_a20
  have w44_1020 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by rw [W44, g43_10]
  have a44_2a0 : accV n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K44.acc (by decide) (by decide)).trans a43_2a0
  have a44_2c0 : accV n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K44.acc (by decide) (by decide)).trans a43_2c0
  have a44_2e0 : accV n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K44.acc (by decide) (by decide)).trans a43_2e0
  have a44_380 : accV n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := (K44.acc (by decide) (by decide)).trans a43_380
  have a44_400 : accV n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := (K44.acc (by decide) (by decide)).trans a43_400
  have a44_13e0 : accV n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := (K44.acc (by decide) (by decide)).trans a43_13e0
  have a44_1460 : accV n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := (K44.acc (by decide) (by decide)).trans a43_1460
  have a44_1588 : accV n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U2 := (K44.acc (by decide) (by decide)).trans a43_1588
  have p44_320 : ptF n44.mem B 0x320 = P0 := (K44.pt (by decide) (by decide)).trans p43_320
  have p44_3a0 : ptF n44.mem B 0x3A0 = P1 := (K44.pt (by decide) (by decide)).trans p43_3a0
  have p44_420 : ptF n44.mem B 0x420 = tbl2 P0 0 := (K44.pt (by decide) (by decide)).trans p43_420
  have p44_480 : ptF n44.mem B 0x480 = tbl2 P0 1 := (K44.pt (by decide) (by decide)).trans p43_480
  have p44_4e0 : ptF n44.mem B 0x4E0 = tbl2 P0 2 := (K44.pt (by decide) (by decide)).trans p43_4e0
  have p44_540 : ptF n44.mem B 0x540 = tbl2 P0 3 := (K44.pt (by decide) (by decide)).trans p43_540
  have p44_5a0 : ptF n44.mem B 0x5A0 = tbl2 P0 4 := (K44.pt (by decide) (by decide)).trans p43_5a0
  have p44_600 : ptF n44.mem B 0x600 = tbl2 P0 5 := (K44.pt (by decide) (by decide)).trans p43_600
  have p44_660 : ptF n44.mem B 0x660 = tbl2 P0 6 := (K44.pt (by decide) (by decide)).trans p43_660
  have p44_6c0 : ptF n44.mem B 0x6C0 = tbl2 P0 7 := (K44.pt (by decide) (by decide)).trans p43_6c0
  have p44_720 : ptF n44.mem B 0x720 = tbl2 P1 0 := (K44.pt (by decide) (by decide)).trans p43_720
  have p44_780 : ptF n44.mem B 0x780 = tbl2 P1 1 := (K44.pt (by decide) (by decide)).trans p43_780
  have p44_7e0 : ptF n44.mem B 0x7E0 = tbl2 P1 2 := (K44.pt (by decide) (by decide)).trans p43_7e0
  have p44_840 : ptF n44.mem B 0x840 = tbl2 P1 3 := (K44.pt (by decide) (by decide)).trans p43_840
  have p44_8a0 : ptF n44.mem B 0x8A0 = tbl2 P1 4 := (K44.pt (by decide) (by decide)).trans p43_8a0
  have p44_900 : ptF n44.mem B 0x900 = tbl2 P1 5 := (K44.pt (by decide) (by decide)).trans p43_900
  have p44_960 : ptF n44.mem B 0x960 = tbl2 P1 6 := (K44.pt (by decide) (by decide)).trans p43_960
  have p44_9c0 : ptF n44.mem B 0x9C0 = tbl2 P1 7 := (K44.pt (by decide) (by decide)).trans p43_9c0
  have p44_b40 : ptF n44.mem B 0xB40 = tbl2 P0 3 := (K44.pt (by decide) (by decide)).trans p43_b40
  have p44_ba0 : ptF n44.mem B 0xBA0 = tbl2 P0 4 := (K44.pt (by decide) (by decide)).trans p43_ba0
  have p44_c00 : ptF n44.mem B 0xC00 = tbl2 P0 5 := (K44.pt (by decide) (by decide)).trans p43_c00
  have p44_c60 : ptF n44.mem B 0xC60 = tbl2 P0 6 := (K44.pt (by decide) (by decide)).trans p43_c60
  have p44_cc0 : ptF n44.mem B 0xCC0 = tbl2 P0 7 := (K44.pt (by decide) (by decide)).trans p43_cc0
  have p44_d20 : ptF n44.mem B 0xD20 = tbl2 P1 0 := (K44.pt (by decide) (by decide)).trans p43_d20
  have p44_d80 : ptF n44.mem B 0xD80 = tbl2 P1 1 := (K44.pt (by decide) (by decide)).trans p43_d80
  have p44_de0 : ptF n44.mem B 0xDE0 = tbl2 P1 2 := (K44.pt (by decide) (by decide)).trans p43_de0
  have p44_e40 : ptF n44.mem B 0xE40 = tbl2 P1 3 := (K44.pt (by decide) (by decide)).trans p43_e40
  have p44_ea0 : ptF n44.mem B 0xEA0 = tbl2 P1 4 := (K44.pt (by decide) (by decide)).trans p43_ea0
  have p44_f00 : ptF n44.mem B 0xF00 = tbl2 P1 5 := (K44.pt (by decide) (by decide)).trans p43_f00
  have p44_f60 : ptF n44.mem B 0xF60 = tbl2 P1 6 := (K44.pt (by decide) (by decide)).trans p43_f60
  have p44_fc0 : ptF n44.mem B 0xFC0 = tbl2 P1 7 := (K44.pt (by decide) (by decide)).trans p43_fc0
  have p44_1380 : ptF n44.mem B 0x1380 = P0 := (K44.pt (by decide) (by decide)).trans p43_1380
  have p44_1400 : ptF n44.mem B 0x1400 = P1 := (K44.pt (by decide) (by decide)).trans p43_1400
  have mb44_a24 : memBytes n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [K44.mb (by decide) (by decide)]; exact mb43_a24
  have mb44_1024 : memBytes n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [K44.mb (by decide) (by decide)]; exact mb43_1024
  have mb44_1320 : leN (memBytes n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U2 := by rw [K44.mb (by decide) (by decide)]; exact mb43_1320
  have mb44_1480 : memBytes n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 0x101 = List.replicate 0x101 0 := by rw [K44.mb (by decide) (by decide)]; exact mb43_1480
  clear mb43_1024 g43_10 mb43_1480 mb43_1320 mb43_a24 p43_1400 p43_1380 p43_fc0 p43_f60 p43_f00 p43_ea0 p43_e40 p43_de0 p43_d80 p43_d20 p43_cc0 p43_c60 p43_c00 p43_ba0 p43_b40 p43_9c0 p43_960 p43_900 p43_8a0 p43_840 p43_7e0 p43_780 p43_720 p43_6c0 p43_660 p43_600 p43_5a0 p43_540 p43_4e0 p43_480 p43_420 p43_3a0 p43_320 a43_1588 a43_1460 a43_13e0 a43_400 a43_380 a43_2e0 a43_2c0 a43_2a0 w43_1020 w43_a20 w43_130 w43_12c w43_128 w43_124 w43_120 w43_11c w43_118 w43_114 w43_110 w43_10c w43_108 w43_104 w43_100 w43_fc w43_f8 w43_f4 w43_f0 w43_ec w43_e8 w43_e4 w43_e0 w43_dc w43_d8 w43_d4 w43_d0 w43_cc w43_c8 w43_c4 w43_c0 w43_bc w43_b8 w43_b4 w43_b0 w43_ac w43_a8 w43_a4 w43_a0 w43_9c w43_98 w43_94 w43_90 w43_8c w43_88 w43_84 w43_80 w43_7c w43_78 w43_70 w43_6c w43_68 w43_64 w43_60 w43_5c w43_58 w43_54 w43_50 w43_4c w43_48 w43_44 w43_40 w43_3c w43_38 w43_34 w43_30 w43_2c w43_28 w43_24 g43_27 g43_26 g43_25 g43_24 g43_23 g43_22 g43_21 g43_20 g43_19 g43_18 g43_9 g43_8 g43_4 g43_3 g43_2 V43 E43 fR43 t43 fr43 s43 H43 D43 A43 K43 P43
  -- 0x1898
  obtain ⟨n45, c45, u45⟩ := s44.block svEcW1898 E44.self svEcW1898_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m45 : n45.mem = n44.mem := u45.mem
  have s45 : St n45.mem SV n45 0x18AC (reg n45) := ⟨u45.pc, rfl, fun _ => rfl⟩
  have rb45 : ∀ q, reg n45 q = (runBlock svEcW1898 (n44.mem, reg n44)).2 q := fun q => by rw [u45.regs]
  have fr45 : ∀ x, SvR B x → n45.mem x = n44.mem x := fun x _ => by rw [m45]
  have t45 : Steps n0 n45 := t44.trans c45
  have fR45 : ∀ x, SvR B x → n45.mem x = M0 x := fun x hx => (fr45 x hx).trans (fR44 x hx)
  have E45 : SvCode n45.mem := E44.fr F fr45
  have V45 : SvSaves B n45.mem v := V44.same m45
  have g45_2 : reg n45 sp = B + 0x21A0 := by
    rw [rb45, runBlock_reg _ _ _ sp s44.zero (by decide), g44_2]
  have g45_3 : reg n45 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb45, runBlock_reg _ _ _ (3 : Fin 32) s44.zero (by decide), g44_3]
  have g45_4 : reg n45 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb45, runBlock_reg _ _ _ (4 : Fin 32) s44.zero (by decide), g44_4]
  have g45_8 : reg n45 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb45, runBlock_reg _ _ _ (8 : Fin 32) s44.zero (by decide), g44_8]
  have g45_9 : reg n45 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by
    rw [rb45, runBlock_reg _ _ _ (9 : Fin 32) s44.zero (by decide), g44_9]
  have g45_18 : reg n45 (18 : Fin 32) = out := by
    rw [rb45, runBlock_reg _ _ _ (18 : Fin 32) s44.zero (by decide), g44_18]
  have g45_19 : reg n45 (19 : Fin 32) = bp := by
    rw [rb45, runBlock_reg _ _ _ (19 : Fin 32) s44.zero (by decide), g44_19]
  have g45_20 : reg n45 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb45, runBlock_reg _ _ _ (20 : Fin 32) s44.zero (by decide), g44_20]
  have g45_21 : reg n45 (21 : Fin 32) = s5v := by
    rw [rb45, runBlock_reg _ _ _ (21 : Fin 32) s44.zero (by decide), g44_21]
  have g45_22 : reg n45 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by
    rw [rb45, runBlock_reg _ _ _ (22 : Fin 32) s44.zero (by decide), g44_22]
  have g45_23 : reg n45 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by
    rw [rb45, runBlock_reg _ _ _ (23 : Fin 32) s44.zero (by decide), g44_23]
  have g45_24 : reg n45 (24 : Fin 32) = s8v := by
    rw [rb45, runBlock_reg _ _ _ (24 : Fin 32) s44.zero (by decide), g44_24]
  have g45_25 : reg n45 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb45, runBlock_reg _ _ _ (25 : Fin 32) s44.zero (by decide), g44_25]
  have g45_26 : reg n45 (26 : Fin 32) = x26 := by
    rw [rb45, runBlock_reg _ _ _ (26 : Fin 32) s44.zero (by decide), g44_26]
  have g45_27 : reg n45 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb45, runBlock_reg _ _ _ (27 : Fin 32) s44.zero (by decide), g44_27]
  have g45_10 : reg n45 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by
    rw [rb45]; simp +decide only [runBlock, BInstr.run, svEcW1898, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g44_2, g44_3, g44_4, g44_8, g44_9, g44_10, g44_18, g44_19, g44_20, g44_21, g44_22, g44_23, g44_24, g44_25, g44_26, g44_27, s44.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g45_11 : reg n45 a1 = B + 0x21A0 + BitVec.ofNat 32 0x1020 := by
    rw [rb45]; simp +decide only [runBlock, BInstr.run, svEcW1898, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g44_2, g44_3, g44_4, g44_8, g44_9, g44_10, g44_18, g44_19, g44_20, g44_21, g44_22, g44_23, g44_24, g44_25, g44_26, g44_27, s44.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g45_12 : reg n45 a2 = BitVec.ofNat 32 0x108 := by
    rw [rb45]; simp +decide only [runBlock, BInstr.run, svEcW1898, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g44_2, g44_3, g44_4, g44_8, g44_9, g44_10, g44_18, g44_19, g44_20, g44_21, g44_22, g44_23, g44_24, g44_25, g44_26, g44_27, s44.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w45_24 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m45]; exact w44_24
  have w45_28 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m45]; exact w44_28
  have w45_2c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m45]; exact w44_2c
  have w45_30 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m45]; exact w44_30
  have w45_34 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m45]; exact w44_34
  have w45_38 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m45]; exact w44_38
  have w45_3c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m45]; exact w44_3c
  have w45_40 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m45]; exact w44_40
  have w45_44 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m45]; exact w44_44
  have w45_48 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m45]; exact w44_48
  have w45_4c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m45]; exact w44_4c
  have w45_50 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m45]; exact w44_50
  have w45_54 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m45]; exact w44_54
  have w45_58 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m45]; exact w44_58
  have w45_5c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m45]; exact w44_5c
  have w45_60 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m45]; exact w44_60
  have w45_64 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m45]; exact w44_64
  have w45_68 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m45]; exact w44_68
  have w45_6c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m45]; exact w44_6c
  have w45_70 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m45]; exact w44_70
  have w45_78 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m45]; exact w44_78
  have w45_7c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m45]; exact w44_7c
  have w45_80 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m45]; exact w44_80
  have w45_84 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m45]; exact w44_84
  have w45_88 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m45]; exact w44_88
  have w45_8c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m45]; exact w44_8c
  have w45_90 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m45]; exact w44_90
  have w45_94 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m45]; exact w44_94
  have w45_98 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m45]; exact w44_98
  have w45_9c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m45]; exact w44_9c
  have w45_a0 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m45]; exact w44_a0
  have w45_a4 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m45]; exact w44_a4
  have w45_a8 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m45]; exact w44_a8
  have w45_ac : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m45]; exact w44_ac
  have w45_b0 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m45]; exact w44_b0
  have w45_b4 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m45]; exact w44_b4
  have w45_b8 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m45]; exact w44_b8
  have w45_bc : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m45]; exact w44_bc
  have w45_c0 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m45]; exact w44_c0
  have w45_c4 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m45]; exact w44_c4
  have w45_c8 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m45]; exact w44_c8
  have w45_cc : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m45]; exact w44_cc
  have w45_d0 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m45]; exact w44_d0
  have w45_d4 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m45]; exact w44_d4
  have w45_d8 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m45]; exact w44_d8
  have w45_dc : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m45]; exact w44_dc
  have w45_e0 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m45]; exact w44_e0
  have w45_e4 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m45]; exact w44_e4
  have w45_e8 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m45]; exact w44_e8
  have w45_ec : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m45]; exact w44_ec
  have w45_f0 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m45]; exact w44_f0
  have w45_f4 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m45]; exact w44_f4
  have w45_f8 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m45]; exact w44_f8
  have w45_fc : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m45]; exact w44_fc
  have w45_100 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m45]; exact w44_100
  have w45_104 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m45]; exact w44_104
  have w45_108 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m45]; exact w44_108
  have w45_10c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m45]; exact w44_10c
  have w45_110 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m45]; exact w44_110
  have w45_114 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m45]; exact w44_114
  have w45_118 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m45]; exact w44_118
  have w45_11c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m45]; exact w44_11c
  have w45_120 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m45]; exact w44_120
  have w45_124 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m45]; exact w44_124
  have w45_128 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m45]; exact w44_128
  have w45_12c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m45]; exact w44_12c
  have w45_130 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m45]; exact w44_130
  have w45_a20 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m45]; exact w44_a20
  have w45_1020 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by rw [m45]; exact w44_1020
  have a45_2a0 : accV n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m45]; exact a44_2a0
  have a45_2c0 : accV n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m45]; exact a44_2c0
  have a45_2e0 : accV n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m45]; exact a44_2e0
  have a45_380 : accV n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m45]; exact a44_380
  have a45_400 : accV n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m45]; exact a44_400
  have a45_13e0 : accV n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := by rw [m45]; exact a44_13e0
  have a45_1460 : accV n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := by rw [m45]; exact a44_1460
  have a45_1588 : accV n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U2 := by rw [m45]; exact a44_1588
  have p45_320 : ptF n45.mem B 0x320 = P0 := by rw [m45]; exact p44_320
  have p45_3a0 : ptF n45.mem B 0x3A0 = P1 := by rw [m45]; exact p44_3a0
  have p45_420 : ptF n45.mem B 0x420 = tbl2 P0 0 := by rw [m45]; exact p44_420
  have p45_480 : ptF n45.mem B 0x480 = tbl2 P0 1 := by rw [m45]; exact p44_480
  have p45_4e0 : ptF n45.mem B 0x4E0 = tbl2 P0 2 := by rw [m45]; exact p44_4e0
  have p45_540 : ptF n45.mem B 0x540 = tbl2 P0 3 := by rw [m45]; exact p44_540
  have p45_5a0 : ptF n45.mem B 0x5A0 = tbl2 P0 4 := by rw [m45]; exact p44_5a0
  have p45_600 : ptF n45.mem B 0x600 = tbl2 P0 5 := by rw [m45]; exact p44_600
  have p45_660 : ptF n45.mem B 0x660 = tbl2 P0 6 := by rw [m45]; exact p44_660
  have p45_6c0 : ptF n45.mem B 0x6C0 = tbl2 P0 7 := by rw [m45]; exact p44_6c0
  have p45_720 : ptF n45.mem B 0x720 = tbl2 P1 0 := by rw [m45]; exact p44_720
  have p45_780 : ptF n45.mem B 0x780 = tbl2 P1 1 := by rw [m45]; exact p44_780
  have p45_7e0 : ptF n45.mem B 0x7E0 = tbl2 P1 2 := by rw [m45]; exact p44_7e0
  have p45_840 : ptF n45.mem B 0x840 = tbl2 P1 3 := by rw [m45]; exact p44_840
  have p45_8a0 : ptF n45.mem B 0x8A0 = tbl2 P1 4 := by rw [m45]; exact p44_8a0
  have p45_900 : ptF n45.mem B 0x900 = tbl2 P1 5 := by rw [m45]; exact p44_900
  have p45_960 : ptF n45.mem B 0x960 = tbl2 P1 6 := by rw [m45]; exact p44_960
  have p45_9c0 : ptF n45.mem B 0x9C0 = tbl2 P1 7 := by rw [m45]; exact p44_9c0
  have p45_b40 : ptF n45.mem B 0xB40 = tbl2 P0 3 := by rw [m45]; exact p44_b40
  have p45_ba0 : ptF n45.mem B 0xBA0 = tbl2 P0 4 := by rw [m45]; exact p44_ba0
  have p45_c00 : ptF n45.mem B 0xC00 = tbl2 P0 5 := by rw [m45]; exact p44_c00
  have p45_c60 : ptF n45.mem B 0xC60 = tbl2 P0 6 := by rw [m45]; exact p44_c60
  have p45_cc0 : ptF n45.mem B 0xCC0 = tbl2 P0 7 := by rw [m45]; exact p44_cc0
  have p45_d20 : ptF n45.mem B 0xD20 = tbl2 P1 0 := by rw [m45]; exact p44_d20
  have p45_d80 : ptF n45.mem B 0xD80 = tbl2 P1 1 := by rw [m45]; exact p44_d80
  have p45_de0 : ptF n45.mem B 0xDE0 = tbl2 P1 2 := by rw [m45]; exact p44_de0
  have p45_e40 : ptF n45.mem B 0xE40 = tbl2 P1 3 := by rw [m45]; exact p44_e40
  have p45_ea0 : ptF n45.mem B 0xEA0 = tbl2 P1 4 := by rw [m45]; exact p44_ea0
  have p45_f00 : ptF n45.mem B 0xF00 = tbl2 P1 5 := by rw [m45]; exact p44_f00
  have p45_f60 : ptF n45.mem B 0xF60 = tbl2 P1 6 := by rw [m45]; exact p44_f60
  have p45_fc0 : ptF n45.mem B 0xFC0 = tbl2 P1 7 := by rw [m45]; exact p44_fc0
  have p45_1380 : ptF n45.mem B 0x1380 = P0 := by rw [m45]; exact p44_1380
  have p45_1400 : ptF n45.mem B 0x1400 = P1 := by rw [m45]; exact p44_1400
  have mb45_a24 : memBytes n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m45]; exact mb44_a24
  have mb45_1024 : memBytes n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [m45]; exact mb44_1024
  have mb45_1320 : leN (memBytes n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U2 := by rw [m45]; exact mb44_1320
  have mb45_1480 : memBytes n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 0x101 = List.replicate 0x101 0 := by rw [m45]; exact mb44_1480
  clear mb44_1480 mb44_1320 mb44_1024 mb44_a24 p44_1400 p44_1380 p44_fc0 p44_f60 p44_f00 p44_ea0 p44_e40 p44_de0 p44_d80 p44_d20 p44_cc0 p44_c60 p44_c00 p44_ba0 p44_b40 p44_9c0 p44_960 p44_900 p44_8a0 p44_840 p44_7e0 p44_780 p44_720 p44_6c0 p44_660 p44_600 p44_5a0 p44_540 p44_4e0 p44_480 p44_420 p44_3a0 p44_320 a44_1588 a44_1460 a44_13e0 a44_400 a44_380 a44_2e0 a44_2c0 a44_2a0 w44_1020 w44_a20 w44_130 w44_12c w44_128 w44_124 w44_120 w44_11c w44_118 w44_114 w44_110 w44_10c w44_108 w44_104 w44_100 w44_fc w44_f8 w44_f4 w44_f0 w44_ec w44_e8 w44_e4 w44_e0 w44_dc w44_d8 w44_d4 w44_d0 w44_cc w44_c8 w44_c4 w44_c0 w44_bc w44_b8 w44_b4 w44_b0 w44_ac w44_a8 w44_a4 w44_a0 w44_9c w44_98 w44_94 w44_90 w44_8c w44_88 w44_84 w44_80 w44_7c w44_78 w44_70 w44_6c w44_68 w44_64 w44_60 w44_5c w44_58 w44_54 w44_50 w44_4c w44_48 w44_44 w44_40 w44_3c w44_38 w44_34 w44_30 w44_2c w44_28 w44_24 g44_27 g44_26 g44_25 g44_24 g44_23 g44_22 g44_21 g44_20 g44_19 g44_18 g44_10 g44_9 g44_8 g44_4 g44_3 g44_2 V44 E44 fR44 t44 rg44 W44 K44 fr44 s44 d44
  -- 0x18AC: memcpy
  obtain ⟨n46, P46, K46, X46⟩ := sv_mc (c := 0x1480) (d := 0x1020) (N := 0x108) F E45 s45 sv_at_18ac sv_at_18b0
    (by decide) (by decide) g45_2 g45_10 g45_11 g45_12
    (by decide) (by decide) (by decide)
  have s46 := P46.st
  have fr46 := P46.fr
  have t46 : Steps n0 n46 := t45.trans P46.steps
  have fR46 : ∀ x, SvR B x → n46.mem x = M0 x := fun x hx => (fr46 x hx).trans (fR45 x hx)
  have E46 : SvCode n46.mem := E45.fr F fr46
  have V46 : SvSaves B n46.mem v := V45.keep K46 (by decide)
  have g46_2 : reg n46 sp = B + 0x21A0 := by rw [P46.regs sp (by decide), g45_2]
  have g46_3 : reg n46 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P46.regs (3 : Fin 32) (by decide), g45_3]
  have g46_4 : reg n46 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P46.regs (4 : Fin 32) (by decide), g45_4]
  have g46_8 : reg n46 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P46.regs (8 : Fin 32) (by decide), g45_8]
  have g46_9 : reg n46 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by rw [P46.regs (9 : Fin 32) (by decide), g45_9]
  have g46_18 : reg n46 (18 : Fin 32) = out := by rw [P46.regs (18 : Fin 32) (by decide), g45_18]
  have g46_19 : reg n46 (19 : Fin 32) = bp := by rw [P46.regs (19 : Fin 32) (by decide), g45_19]
  have g46_20 : reg n46 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P46.regs (20 : Fin 32) (by decide), g45_20]
  have g46_21 : reg n46 (21 : Fin 32) = s5v := by rw [P46.regs (21 : Fin 32) (by decide), g45_21]
  have g46_22 : reg n46 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [P46.regs (22 : Fin 32) (by decide), g45_22]
  have g46_23 : reg n46 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by rw [P46.regs (23 : Fin 32) (by decide), g45_23]
  have g46_24 : reg n46 (24 : Fin 32) = s8v := by rw [P46.regs (24 : Fin 32) (by decide), g45_24]
  have g46_25 : reg n46 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P46.regs (25 : Fin 32) (by decide), g45_25]
  have g46_26 : reg n46 (26 : Fin 32) = x26 := by rw [P46.regs (26 : Fin 32) (by decide), g45_26]
  have g46_27 : reg n46 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P46.regs (27 : Fin 32) (by decide), g45_27]
  have w46_24 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K46.w32 (by decide) (by decide)).trans w45_24
  have w46_28 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K46.w32 (by decide) (by decide)).trans w45_28
  have w46_2c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K46.w32 (by decide) (by decide)).trans w45_2c
  have w46_30 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K46.w32 (by decide) (by decide)).trans w45_30
  have w46_34 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K46.w32 (by decide) (by decide)).trans w45_34
  have w46_38 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K46.w32 (by decide) (by decide)).trans w45_38
  have w46_3c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K46.w32 (by decide) (by decide)).trans w45_3c
  have w46_40 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K46.w32 (by decide) (by decide)).trans w45_40
  have w46_44 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K46.w32 (by decide) (by decide)).trans w45_44
  have w46_48 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K46.w32 (by decide) (by decide)).trans w45_48
  have w46_4c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K46.w32 (by decide) (by decide)).trans w45_4c
  have w46_50 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K46.w32 (by decide) (by decide)).trans w45_50
  have w46_54 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K46.w32 (by decide) (by decide)).trans w45_54
  have w46_58 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K46.w32 (by decide) (by decide)).trans w45_58
  have w46_5c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K46.w32 (by decide) (by decide)).trans w45_5c
  have w46_60 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K46.w32 (by decide) (by decide)).trans w45_60
  have w46_64 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K46.w32 (by decide) (by decide)).trans w45_64
  have w46_68 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K46.w32 (by decide) (by decide)).trans w45_68
  have w46_6c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K46.w32 (by decide) (by decide)).trans w45_6c
  have w46_70 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K46.w32 (by decide) (by decide)).trans w45_70
  have w46_78 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := (K46.w32 (by decide) (by decide)).trans w45_78
  have w46_7c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K46.w32 (by decide) (by decide)).trans w45_7c
  have w46_80 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K46.w32 (by decide) (by decide)).trans w45_80
  have w46_84 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K46.w32 (by decide) (by decide)).trans w45_84
  have w46_88 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K46.w32 (by decide) (by decide)).trans w45_88
  have w46_8c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K46.w32 (by decide) (by decide)).trans w45_8c
  have w46_90 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K46.w32 (by decide) (by decide)).trans w45_90
  have w46_94 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K46.w32 (by decide) (by decide)).trans w45_94
  have w46_98 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K46.w32 (by decide) (by decide)).trans w45_98
  have w46_9c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K46.w32 (by decide) (by decide)).trans w45_9c
  have w46_a0 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K46.w32 (by decide) (by decide)).trans w45_a0
  have w46_a4 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K46.w32 (by decide) (by decide)).trans w45_a4
  have w46_a8 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K46.w32 (by decide) (by decide)).trans w45_a8
  have w46_ac : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K46.w32 (by decide) (by decide)).trans w45_ac
  have w46_b0 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K46.w32 (by decide) (by decide)).trans w45_b0
  have w46_b4 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K46.w32 (by decide) (by decide)).trans w45_b4
  have w46_b8 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K46.w32 (by decide) (by decide)).trans w45_b8
  have w46_bc : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K46.w32 (by decide) (by decide)).trans w45_bc
  have w46_c0 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K46.w32 (by decide) (by decide)).trans w45_c0
  have w46_c4 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K46.w32 (by decide) (by decide)).trans w45_c4
  have w46_c8 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K46.w32 (by decide) (by decide)).trans w45_c8
  have w46_cc : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K46.w32 (by decide) (by decide)).trans w45_cc
  have w46_d0 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K46.w32 (by decide) (by decide)).trans w45_d0
  have w46_d4 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K46.w32 (by decide) (by decide)).trans w45_d4
  have w46_d8 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K46.w32 (by decide) (by decide)).trans w45_d8
  have w46_dc : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K46.w32 (by decide) (by decide)).trans w45_dc
  have w46_e0 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K46.w32 (by decide) (by decide)).trans w45_e0
  have w46_e4 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K46.w32 (by decide) (by decide)).trans w45_e4
  have w46_e8 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K46.w32 (by decide) (by decide)).trans w45_e8
  have w46_ec : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K46.w32 (by decide) (by decide)).trans w45_ec
  have w46_f0 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K46.w32 (by decide) (by decide)).trans w45_f0
  have w46_f4 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K46.w32 (by decide) (by decide)).trans w45_f4
  have w46_f8 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K46.w32 (by decide) (by decide)).trans w45_f8
  have w46_fc : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K46.w32 (by decide) (by decide)).trans w45_fc
  have w46_100 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K46.w32 (by decide) (by decide)).trans w45_100
  have w46_104 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K46.w32 (by decide) (by decide)).trans w45_104
  have w46_108 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K46.w32 (by decide) (by decide)).trans w45_108
  have w46_10c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K46.w32 (by decide) (by decide)).trans w45_10c
  have w46_110 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K46.w32 (by decide) (by decide)).trans w45_110
  have w46_114 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K46.w32 (by decide) (by decide)).trans w45_114
  have w46_118 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K46.w32 (by decide) (by decide)).trans w45_118
  have w46_11c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K46.w32 (by decide) (by decide)).trans w45_11c
  have w46_120 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K46.w32 (by decide) (by decide)).trans w45_120
  have w46_124 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K46.w32 (by decide) (by decide)).trans w45_124
  have w46_128 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K46.w32 (by decide) (by decide)).trans w45_128
  have w46_12c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K46.w32 (by decide) (by decide)).trans w45_12c
  have w46_130 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K46.w32 (by decide) (by decide)).trans w45_130
  have w46_a20 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := (K46.w32 (by decide) (by decide)).trans w45_a20
  have w46_1020 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := (K46.w32 (by decide) (by decide)).trans w45_1020
  have w46_1480 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by
    rw [← w45_1020]
    exact ld_cp fun q hq => by
      have := X46 (0x0 + q) (by omega)
      rwa [show 0x1480 + (0x0 + q) = 0x1480 + q by omega,
        show 0x1020 + (0x0 + q) = 0x1020 + q by omega] at this
  have a46_2a0 : accV n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K46.acc (by decide) (by decide)).trans a45_2a0
  have a46_2c0 : accV n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K46.acc (by decide) (by decide)).trans a45_2c0
  have a46_2e0 : accV n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K46.acc (by decide) (by decide)).trans a45_2e0
  have a46_380 : accV n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := (K46.acc (by decide) (by decide)).trans a45_380
  have a46_400 : accV n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := (K46.acc (by decide) (by decide)).trans a45_400
  have a46_13e0 : accV n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := (K46.acc (by decide) (by decide)).trans a45_13e0
  have a46_1460 : accV n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := (K46.acc (by decide) (by decide)).trans a45_1460
  have a46_1588 : accV n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U2 := (K46.acc (by decide) (by decide)).trans a45_1588
  have p46_320 : ptF n46.mem B 0x320 = P0 := (K46.pt (by decide) (by decide)).trans p45_320
  have p46_3a0 : ptF n46.mem B 0x3A0 = P1 := (K46.pt (by decide) (by decide)).trans p45_3a0
  have p46_420 : ptF n46.mem B 0x420 = tbl2 P0 0 := (K46.pt (by decide) (by decide)).trans p45_420
  have p46_480 : ptF n46.mem B 0x480 = tbl2 P0 1 := (K46.pt (by decide) (by decide)).trans p45_480
  have p46_4e0 : ptF n46.mem B 0x4E0 = tbl2 P0 2 := (K46.pt (by decide) (by decide)).trans p45_4e0
  have p46_540 : ptF n46.mem B 0x540 = tbl2 P0 3 := (K46.pt (by decide) (by decide)).trans p45_540
  have p46_5a0 : ptF n46.mem B 0x5A0 = tbl2 P0 4 := (K46.pt (by decide) (by decide)).trans p45_5a0
  have p46_600 : ptF n46.mem B 0x600 = tbl2 P0 5 := (K46.pt (by decide) (by decide)).trans p45_600
  have p46_660 : ptF n46.mem B 0x660 = tbl2 P0 6 := (K46.pt (by decide) (by decide)).trans p45_660
  have p46_6c0 : ptF n46.mem B 0x6C0 = tbl2 P0 7 := (K46.pt (by decide) (by decide)).trans p45_6c0
  have p46_720 : ptF n46.mem B 0x720 = tbl2 P1 0 := (K46.pt (by decide) (by decide)).trans p45_720
  have p46_780 : ptF n46.mem B 0x780 = tbl2 P1 1 := (K46.pt (by decide) (by decide)).trans p45_780
  have p46_7e0 : ptF n46.mem B 0x7E0 = tbl2 P1 2 := (K46.pt (by decide) (by decide)).trans p45_7e0
  have p46_840 : ptF n46.mem B 0x840 = tbl2 P1 3 := (K46.pt (by decide) (by decide)).trans p45_840
  have p46_8a0 : ptF n46.mem B 0x8A0 = tbl2 P1 4 := (K46.pt (by decide) (by decide)).trans p45_8a0
  have p46_900 : ptF n46.mem B 0x900 = tbl2 P1 5 := (K46.pt (by decide) (by decide)).trans p45_900
  have p46_960 : ptF n46.mem B 0x960 = tbl2 P1 6 := (K46.pt (by decide) (by decide)).trans p45_960
  have p46_9c0 : ptF n46.mem B 0x9C0 = tbl2 P1 7 := (K46.pt (by decide) (by decide)).trans p45_9c0
  have p46_b40 : ptF n46.mem B 0xB40 = tbl2 P0 3 := (K46.pt (by decide) (by decide)).trans p45_b40
  have p46_ba0 : ptF n46.mem B 0xBA0 = tbl2 P0 4 := (K46.pt (by decide) (by decide)).trans p45_ba0
  have p46_c00 : ptF n46.mem B 0xC00 = tbl2 P0 5 := (K46.pt (by decide) (by decide)).trans p45_c00
  have p46_c60 : ptF n46.mem B 0xC60 = tbl2 P0 6 := (K46.pt (by decide) (by decide)).trans p45_c60
  have p46_cc0 : ptF n46.mem B 0xCC0 = tbl2 P0 7 := (K46.pt (by decide) (by decide)).trans p45_cc0
  have p46_d20 : ptF n46.mem B 0xD20 = tbl2 P1 0 := (K46.pt (by decide) (by decide)).trans p45_d20
  have p46_d80 : ptF n46.mem B 0xD80 = tbl2 P1 1 := (K46.pt (by decide) (by decide)).trans p45_d80
  have p46_de0 : ptF n46.mem B 0xDE0 = tbl2 P1 2 := (K46.pt (by decide) (by decide)).trans p45_de0
  have p46_e40 : ptF n46.mem B 0xE40 = tbl2 P1 3 := (K46.pt (by decide) (by decide)).trans p45_e40
  have p46_ea0 : ptF n46.mem B 0xEA0 = tbl2 P1 4 := (K46.pt (by decide) (by decide)).trans p45_ea0
  have p46_f00 : ptF n46.mem B 0xF00 = tbl2 P1 5 := (K46.pt (by decide) (by decide)).trans p45_f00
  have p46_f60 : ptF n46.mem B 0xF60 = tbl2 P1 6 := (K46.pt (by decide) (by decide)).trans p45_f60
  have p46_fc0 : ptF n46.mem B 0xFC0 = tbl2 P1 7 := (K46.pt (by decide) (by decide)).trans p45_fc0
  have p46_1380 : ptF n46.mem B 0x1380 = P0 := (K46.pt (by decide) (by decide)).trans p45_1380
  have p46_1400 : ptF n46.mem B 0x1400 = P1 := (K46.pt (by decide) (by decide)).trans p45_1400
  have mb46_a24 : memBytes n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [K46.mb (by decide) (by decide)]; exact mb45_a24
  have mb46_1024 : memBytes n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [K46.mb (by decide) (by decide)]; exact mb45_1024
  have mb46_1320 : leN (memBytes n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U2 := by rw [K46.mb (by decide) (by decide)]; exact mb45_1320
  have mb46_1484 : memBytes n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by
    rw [memBytes_cp (S := B + 0x21A0) (c := 0x1484) (d := 0x1024) (N := 0x101) fun q hq => by
      rw [show 0x1484 + q = 0x1480 + (0x4 + q) by omega, X46 (0x4 + q) (by omega),
        show 0x1020 + (0x4 + q) = 0x1024 + q by omega]]; exact mb45_1024
  clear mb45_1480 mb45_1320 mb45_1024 mb45_a24 p45_1400 p45_1380 p45_fc0 p45_f60 p45_f00 p45_ea0 p45_e40 p45_de0 p45_d80 p45_d20 p45_cc0 p45_c60 p45_c00 p45_ba0 p45_b40 p45_9c0 p45_960 p45_900 p45_8a0 p45_840 p45_7e0 p45_780 p45_720 p45_6c0 p45_660 p45_600 p45_5a0 p45_540 p45_4e0 p45_480 p45_420 p45_3a0 p45_320 a45_1588 a45_1460 a45_13e0 a45_400 a45_380 a45_2e0 a45_2c0 a45_2a0 w45_1020 w45_a20 w45_130 w45_12c w45_128 w45_124 w45_120 w45_11c w45_118 w45_114 w45_110 w45_10c w45_108 w45_104 w45_100 w45_fc w45_f8 w45_f4 w45_f0 w45_ec w45_e8 w45_e4 w45_e0 w45_dc w45_d8 w45_d4 w45_d0 w45_cc w45_c8 w45_c4 w45_c0 w45_bc w45_b8 w45_b4 w45_b0 w45_ac w45_a8 w45_a4 w45_a0 w45_9c w45_98 w45_94 w45_90 w45_8c w45_88 w45_84 w45_80 w45_7c w45_78 w45_70 w45_6c w45_68 w45_64 w45_60 w45_5c w45_58 w45_54 w45_50 w45_4c w45_48 w45_44 w45_40 w45_3c w45_38 w45_34 w45_30 w45_2c w45_28 w45_24 g45_12 g45_11 g45_10 g45_27 g45_26 g45_25 g45_24 g45_23 g45_22 g45_21 g45_20 g45_19 g45_18 g45_9 g45_8 g45_4 g45_3 g45_2 V45 E45 fR45 t45 fr45 rb45 s45 m45 u45 c45
  -- 0x18B4
  obtain ⟨n47, c47, u47⟩ := s46.block svEcW18b4 E46.self svEcW18b4_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m47 : n47.mem = n46.mem := u47.mem
  have s47 : St n47.mem SV n47 0x18C6 (reg n47) := ⟨u47.pc, rfl, fun _ => rfl⟩
  have rb47 : ∀ q, reg n47 q = (runBlock svEcW18b4 (n46.mem, reg n46)).2 q := fun q => by rw [u47.regs]
  have fr47 : ∀ x, SvR B x → n47.mem x = n46.mem x := fun x _ => by rw [m47]
  have t47 : Steps n0 n47 := t46.trans c47
  have fR47 : ∀ x, SvR B x → n47.mem x = M0 x := fun x hx => (fr47 x hx).trans (fR46 x hx)
  have E47 : SvCode n47.mem := E46.fr F fr47
  have V47 : SvSaves B n47.mem v := V46.same m47
  have g47_2 : reg n47 sp = B + 0x21A0 := by
    rw [rb47, runBlock_reg _ _ _ sp s46.zero (by decide), g46_2]
  have g47_3 : reg n47 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb47, runBlock_reg _ _ _ (3 : Fin 32) s46.zero (by decide), g46_3]
  have g47_4 : reg n47 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb47, runBlock_reg _ _ _ (4 : Fin 32) s46.zero (by decide), g46_4]
  have g47_8 : reg n47 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb47, runBlock_reg _ _ _ (8 : Fin 32) s46.zero (by decide), g46_8]
  have g47_9 : reg n47 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by
    rw [rb47, runBlock_reg _ _ _ (9 : Fin 32) s46.zero (by decide), g46_9]
  have g47_18 : reg n47 (18 : Fin 32) = out := by
    rw [rb47, runBlock_reg _ _ _ (18 : Fin 32) s46.zero (by decide), g46_18]
  have g47_19 : reg n47 (19 : Fin 32) = bp := by
    rw [rb47, runBlock_reg _ _ _ (19 : Fin 32) s46.zero (by decide), g46_19]
  have g47_20 : reg n47 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb47, runBlock_reg _ _ _ (20 : Fin 32) s46.zero (by decide), g46_20]
  have g47_21 : reg n47 (21 : Fin 32) = s5v := by
    rw [rb47, runBlock_reg _ _ _ (21 : Fin 32) s46.zero (by decide), g46_21]
  have g47_22 : reg n47 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by
    rw [rb47, runBlock_reg _ _ _ (22 : Fin 32) s46.zero (by decide), g46_22]
  have g47_23 : reg n47 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by
    rw [rb47, runBlock_reg _ _ _ (23 : Fin 32) s46.zero (by decide), g46_23]
  have g47_24 : reg n47 (24 : Fin 32) = s8v := by
    rw [rb47, runBlock_reg _ _ _ (24 : Fin 32) s46.zero (by decide), g46_24]
  have g47_25 : reg n47 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb47, runBlock_reg _ _ _ (25 : Fin 32) s46.zero (by decide), g46_25]
  have g47_26 : reg n47 (26 : Fin 32) = x26 := by
    rw [rb47, runBlock_reg _ _ _ (26 : Fin 32) s46.zero (by decide), g46_26]
  have g47_27 : reg n47 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb47, runBlock_reg _ _ _ (27 : Fin 32) s46.zero (by decide), g46_27]
  have g47_10 : reg n47 a0 = B + 0x21A0 + BitVec.ofNat 32 0xB28 := by
    rw [rb47]; simp +decide only [runBlock, BInstr.run, svEcW18b4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g46_2, g46_3, g46_4, g46_8, g46_9, g46_18, g46_19, g46_20, g46_21, g46_22, g46_23, g46_24, g46_25, g46_26, g46_27, s46.zero])
    all_goals (try simp only [BitVec.reduceMul, BitVec.zero_add])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g47_11 : reg n47 a1 = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by
    rw [rb47]; simp +decide only [runBlock, BInstr.run, svEcW18b4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g46_2, g46_3, g46_4, g46_8, g46_9, g46_18, g46_19, g46_20, g46_21, g46_22, g46_23, g46_24, g46_25, g46_26, g46_27, s46.zero])
    all_goals (try simp only [BitVec.reduceMul, BitVec.zero_add])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g47_12 : reg n47 a2 = BitVec.ofNat 32 0x108 := by
    rw [rb47]; simp +decide only [runBlock, BInstr.run, svEcW18b4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g46_2, g46_3, g46_4, g46_8, g46_9, g46_18, g46_19, g46_20, g46_21, g46_22, g46_23, g46_24, g46_25, g46_26, g46_27, s46.zero])
    all_goals (try simp only [BitVec.reduceMul, BitVec.zero_add])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w47_24 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m47]; exact w46_24
  have w47_28 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m47]; exact w46_28
  have w47_2c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m47]; exact w46_2c
  have w47_30 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m47]; exact w46_30
  have w47_34 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m47]; exact w46_34
  have w47_38 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m47]; exact w46_38
  have w47_3c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m47]; exact w46_3c
  have w47_40 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m47]; exact w46_40
  have w47_44 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m47]; exact w46_44
  have w47_48 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m47]; exact w46_48
  have w47_4c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m47]; exact w46_4c
  have w47_50 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m47]; exact w46_50
  have w47_54 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m47]; exact w46_54
  have w47_58 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m47]; exact w46_58
  have w47_5c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m47]; exact w46_5c
  have w47_60 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m47]; exact w46_60
  have w47_64 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m47]; exact w46_64
  have w47_68 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m47]; exact w46_68
  have w47_6c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m47]; exact w46_6c
  have w47_70 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m47]; exact w46_70
  have w47_78 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m47]; exact w46_78
  have w47_7c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m47]; exact w46_7c
  have w47_80 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m47]; exact w46_80
  have w47_84 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m47]; exact w46_84
  have w47_88 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m47]; exact w46_88
  have w47_8c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m47]; exact w46_8c
  have w47_90 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m47]; exact w46_90
  have w47_94 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m47]; exact w46_94
  have w47_98 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m47]; exact w46_98
  have w47_9c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m47]; exact w46_9c
  have w47_a0 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m47]; exact w46_a0
  have w47_a4 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m47]; exact w46_a4
  have w47_a8 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m47]; exact w46_a8
  have w47_ac : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m47]; exact w46_ac
  have w47_b0 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m47]; exact w46_b0
  have w47_b4 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m47]; exact w46_b4
  have w47_b8 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m47]; exact w46_b8
  have w47_bc : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m47]; exact w46_bc
  have w47_c0 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m47]; exact w46_c0
  have w47_c4 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m47]; exact w46_c4
  have w47_c8 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m47]; exact w46_c8
  have w47_cc : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m47]; exact w46_cc
  have w47_d0 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m47]; exact w46_d0
  have w47_d4 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m47]; exact w46_d4
  have w47_d8 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m47]; exact w46_d8
  have w47_dc : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m47]; exact w46_dc
  have w47_e0 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m47]; exact w46_e0
  have w47_e4 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m47]; exact w46_e4
  have w47_e8 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m47]; exact w46_e8
  have w47_ec : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m47]; exact w46_ec
  have w47_f0 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m47]; exact w46_f0
  have w47_f4 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m47]; exact w46_f4
  have w47_f8 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m47]; exact w46_f8
  have w47_fc : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m47]; exact w46_fc
  have w47_100 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m47]; exact w46_100
  have w47_104 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m47]; exact w46_104
  have w47_108 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m47]; exact w46_108
  have w47_10c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m47]; exact w46_10c
  have w47_110 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m47]; exact w46_110
  have w47_114 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m47]; exact w46_114
  have w47_118 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m47]; exact w46_118
  have w47_11c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m47]; exact w46_11c
  have w47_120 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m47]; exact w46_120
  have w47_124 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m47]; exact w46_124
  have w47_128 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m47]; exact w46_128
  have w47_12c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m47]; exact w46_12c
  have w47_130 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m47]; exact w46_130
  have w47_a20 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m47]; exact w46_a20
  have w47_1020 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by rw [m47]; exact w46_1020
  have w47_1480 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by rw [m47]; exact w46_1480
  have a47_2a0 : accV n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m47]; exact a46_2a0
  have a47_2c0 : accV n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m47]; exact a46_2c0
  have a47_2e0 : accV n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m47]; exact a46_2e0
  have a47_380 : accV n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m47]; exact a46_380
  have a47_400 : accV n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m47]; exact a46_400
  have a47_13e0 : accV n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := by rw [m47]; exact a46_13e0
  have a47_1460 : accV n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := by rw [m47]; exact a46_1460
  have a47_1588 : accV n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U2 := by rw [m47]; exact a46_1588
  have p47_320 : ptF n47.mem B 0x320 = P0 := by rw [m47]; exact p46_320
  have p47_3a0 : ptF n47.mem B 0x3A0 = P1 := by rw [m47]; exact p46_3a0
  have p47_420 : ptF n47.mem B 0x420 = tbl2 P0 0 := by rw [m47]; exact p46_420
  have p47_480 : ptF n47.mem B 0x480 = tbl2 P0 1 := by rw [m47]; exact p46_480
  have p47_4e0 : ptF n47.mem B 0x4E0 = tbl2 P0 2 := by rw [m47]; exact p46_4e0
  have p47_540 : ptF n47.mem B 0x540 = tbl2 P0 3 := by rw [m47]; exact p46_540
  have p47_5a0 : ptF n47.mem B 0x5A0 = tbl2 P0 4 := by rw [m47]; exact p46_5a0
  have p47_600 : ptF n47.mem B 0x600 = tbl2 P0 5 := by rw [m47]; exact p46_600
  have p47_660 : ptF n47.mem B 0x660 = tbl2 P0 6 := by rw [m47]; exact p46_660
  have p47_6c0 : ptF n47.mem B 0x6C0 = tbl2 P0 7 := by rw [m47]; exact p46_6c0
  have p47_720 : ptF n47.mem B 0x720 = tbl2 P1 0 := by rw [m47]; exact p46_720
  have p47_780 : ptF n47.mem B 0x780 = tbl2 P1 1 := by rw [m47]; exact p46_780
  have p47_7e0 : ptF n47.mem B 0x7E0 = tbl2 P1 2 := by rw [m47]; exact p46_7e0
  have p47_840 : ptF n47.mem B 0x840 = tbl2 P1 3 := by rw [m47]; exact p46_840
  have p47_8a0 : ptF n47.mem B 0x8A0 = tbl2 P1 4 := by rw [m47]; exact p46_8a0
  have p47_900 : ptF n47.mem B 0x900 = tbl2 P1 5 := by rw [m47]; exact p46_900
  have p47_960 : ptF n47.mem B 0x960 = tbl2 P1 6 := by rw [m47]; exact p46_960
  have p47_9c0 : ptF n47.mem B 0x9C0 = tbl2 P1 7 := by rw [m47]; exact p46_9c0
  have p47_b40 : ptF n47.mem B 0xB40 = tbl2 P0 3 := by rw [m47]; exact p46_b40
  have p47_ba0 : ptF n47.mem B 0xBA0 = tbl2 P0 4 := by rw [m47]; exact p46_ba0
  have p47_c00 : ptF n47.mem B 0xC00 = tbl2 P0 5 := by rw [m47]; exact p46_c00
  have p47_c60 : ptF n47.mem B 0xC60 = tbl2 P0 6 := by rw [m47]; exact p46_c60
  have p47_cc0 : ptF n47.mem B 0xCC0 = tbl2 P0 7 := by rw [m47]; exact p46_cc0
  have p47_d20 : ptF n47.mem B 0xD20 = tbl2 P1 0 := by rw [m47]; exact p46_d20
  have p47_d80 : ptF n47.mem B 0xD80 = tbl2 P1 1 := by rw [m47]; exact p46_d80
  have p47_de0 : ptF n47.mem B 0xDE0 = tbl2 P1 2 := by rw [m47]; exact p46_de0
  have p47_e40 : ptF n47.mem B 0xE40 = tbl2 P1 3 := by rw [m47]; exact p46_e40
  have p47_ea0 : ptF n47.mem B 0xEA0 = tbl2 P1 4 := by rw [m47]; exact p46_ea0
  have p47_f00 : ptF n47.mem B 0xF00 = tbl2 P1 5 := by rw [m47]; exact p46_f00
  have p47_f60 : ptF n47.mem B 0xF60 = tbl2 P1 6 := by rw [m47]; exact p46_f60
  have p47_fc0 : ptF n47.mem B 0xFC0 = tbl2 P1 7 := by rw [m47]; exact p46_fc0
  have p47_1380 : ptF n47.mem B 0x1380 = P0 := by rw [m47]; exact p46_1380
  have p47_1400 : ptF n47.mem B 0x1400 = P1 := by rw [m47]; exact p46_1400
  have mb47_a24 : memBytes n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m47]; exact mb46_a24
  have mb47_1024 : memBytes n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [m47]; exact mb46_1024
  have mb47_1320 : leN (memBytes n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U2 := by rw [m47]; exact mb46_1320
  have mb47_1484 : memBytes n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [m47]; exact mb46_1484
  clear mb46_1484 mb46_1320 mb46_1024 mb46_a24 p46_1400 p46_1380 p46_fc0 p46_f60 p46_f00 p46_ea0 p46_e40 p46_de0 p46_d80 p46_d20 p46_cc0 p46_c60 p46_c00 p46_ba0 p46_b40 p46_9c0 p46_960 p46_900 p46_8a0 p46_840 p46_7e0 p46_780 p46_720 p46_6c0 p46_660 p46_600 p46_5a0 p46_540 p46_4e0 p46_480 p46_420 p46_3a0 p46_320 a46_1588 a46_1460 a46_13e0 a46_400 a46_380 a46_2e0 a46_2c0 a46_2a0 w46_1480 w46_1020 w46_a20 w46_130 w46_12c w46_128 w46_124 w46_120 w46_11c w46_118 w46_114 w46_110 w46_10c w46_108 w46_104 w46_100 w46_fc w46_f8 w46_f4 w46_f0 w46_ec w46_e8 w46_e4 w46_e0 w46_dc w46_d8 w46_d4 w46_d0 w46_cc w46_c8 w46_c4 w46_c0 w46_bc w46_b8 w46_b4 w46_b0 w46_ac w46_a8 w46_a4 w46_a0 w46_9c w46_98 w46_94 w46_90 w46_8c w46_88 w46_84 w46_80 w46_7c w46_78 w46_70 w46_6c w46_68 w46_64 w46_60 w46_5c w46_58 w46_54 w46_50 w46_4c w46_48 w46_44 w46_40 w46_3c w46_38 w46_34 w46_30 w46_2c w46_28 w46_24 g46_27 g46_26 g46_25 g46_24 g46_23 g46_22 g46_21 g46_20 g46_19 g46_18 g46_9 g46_8 g46_4 g46_3 g46_2 V46 E46 fR46 t46 fr46 s46 X46 K46 P46
  -- 0x18C6: memcpy
  obtain ⟨n48, P48, K48, X48⟩ := sv_mc (c := 0xB28) (d := 0x1480) (N := 0x108) F E47 s47 sv_at_18c6 sv_at_18ca
    (by decide) (by decide) g47_2 g47_10 g47_11 g47_12
    (by decide) (by decide) (by decide)
  have s48 := P48.st
  have fr48 := P48.fr
  have t48 : Steps n0 n48 := t47.trans P48.steps
  have fR48 : ∀ x, SvR B x → n48.mem x = M0 x := fun x hx => (fr48 x hx).trans (fR47 x hx)
  have E48 : SvCode n48.mem := E47.fr F fr48
  have V48 : SvSaves B n48.mem v := V47.keep K48 (by decide)
  have g48_2 : reg n48 sp = B + 0x21A0 := by rw [P48.regs sp (by decide), g47_2]
  have g48_3 : reg n48 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P48.regs (3 : Fin 32) (by decide), g47_3]
  have g48_4 : reg n48 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P48.regs (4 : Fin 32) (by decide), g47_4]
  have g48_8 : reg n48 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [P48.regs (8 : Fin 32) (by decide), g47_8]
  have g48_9 : reg n48 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by rw [P48.regs (9 : Fin 32) (by decide), g47_9]
  have g48_18 : reg n48 (18 : Fin 32) = out := by rw [P48.regs (18 : Fin 32) (by decide), g47_18]
  have g48_19 : reg n48 (19 : Fin 32) = bp := by rw [P48.regs (19 : Fin 32) (by decide), g47_19]
  have g48_20 : reg n48 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P48.regs (20 : Fin 32) (by decide), g47_20]
  have g48_21 : reg n48 (21 : Fin 32) = s5v := by rw [P48.regs (21 : Fin 32) (by decide), g47_21]
  have g48_22 : reg n48 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [P48.regs (22 : Fin 32) (by decide), g47_22]
  have g48_23 : reg n48 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by rw [P48.regs (23 : Fin 32) (by decide), g47_23]
  have g48_24 : reg n48 (24 : Fin 32) = s8v := by rw [P48.regs (24 : Fin 32) (by decide), g47_24]
  have g48_25 : reg n48 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P48.regs (25 : Fin 32) (by decide), g47_25]
  have g48_26 : reg n48 (26 : Fin 32) = x26 := by rw [P48.regs (26 : Fin 32) (by decide), g47_26]
  have g48_27 : reg n48 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P48.regs (27 : Fin 32) (by decide), g47_27]
  have w48_24 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K48.w32 (by decide) (by decide)).trans w47_24
  have w48_28 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K48.w32 (by decide) (by decide)).trans w47_28
  have w48_2c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K48.w32 (by decide) (by decide)).trans w47_2c
  have w48_30 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K48.w32 (by decide) (by decide)).trans w47_30
  have w48_34 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K48.w32 (by decide) (by decide)).trans w47_34
  have w48_38 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K48.w32 (by decide) (by decide)).trans w47_38
  have w48_3c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K48.w32 (by decide) (by decide)).trans w47_3c
  have w48_40 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K48.w32 (by decide) (by decide)).trans w47_40
  have w48_44 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K48.w32 (by decide) (by decide)).trans w47_44
  have w48_48 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K48.w32 (by decide) (by decide)).trans w47_48
  have w48_4c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K48.w32 (by decide) (by decide)).trans w47_4c
  have w48_50 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K48.w32 (by decide) (by decide)).trans w47_50
  have w48_54 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K48.w32 (by decide) (by decide)).trans w47_54
  have w48_58 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K48.w32 (by decide) (by decide)).trans w47_58
  have w48_5c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K48.w32 (by decide) (by decide)).trans w47_5c
  have w48_60 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K48.w32 (by decide) (by decide)).trans w47_60
  have w48_64 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K48.w32 (by decide) (by decide)).trans w47_64
  have w48_68 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K48.w32 (by decide) (by decide)).trans w47_68
  have w48_6c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K48.w32 (by decide) (by decide)).trans w47_6c
  have w48_70 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K48.w32 (by decide) (by decide)).trans w47_70
  have w48_78 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := (K48.w32 (by decide) (by decide)).trans w47_78
  have w48_7c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K48.w32 (by decide) (by decide)).trans w47_7c
  have w48_80 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K48.w32 (by decide) (by decide)).trans w47_80
  have w48_84 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K48.w32 (by decide) (by decide)).trans w47_84
  have w48_88 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K48.w32 (by decide) (by decide)).trans w47_88
  have w48_8c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K48.w32 (by decide) (by decide)).trans w47_8c
  have w48_90 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K48.w32 (by decide) (by decide)).trans w47_90
  have w48_94 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K48.w32 (by decide) (by decide)).trans w47_94
  have w48_98 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K48.w32 (by decide) (by decide)).trans w47_98
  have w48_9c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K48.w32 (by decide) (by decide)).trans w47_9c
  have w48_a0 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K48.w32 (by decide) (by decide)).trans w47_a0
  have w48_a4 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K48.w32 (by decide) (by decide)).trans w47_a4
  have w48_a8 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K48.w32 (by decide) (by decide)).trans w47_a8
  have w48_ac : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K48.w32 (by decide) (by decide)).trans w47_ac
  have w48_b0 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K48.w32 (by decide) (by decide)).trans w47_b0
  have w48_b4 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K48.w32 (by decide) (by decide)).trans w47_b4
  have w48_b8 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K48.w32 (by decide) (by decide)).trans w47_b8
  have w48_bc : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K48.w32 (by decide) (by decide)).trans w47_bc
  have w48_c0 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K48.w32 (by decide) (by decide)).trans w47_c0
  have w48_c4 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K48.w32 (by decide) (by decide)).trans w47_c4
  have w48_c8 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K48.w32 (by decide) (by decide)).trans w47_c8
  have w48_cc : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K48.w32 (by decide) (by decide)).trans w47_cc
  have w48_d0 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K48.w32 (by decide) (by decide)).trans w47_d0
  have w48_d4 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K48.w32 (by decide) (by decide)).trans w47_d4
  have w48_d8 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K48.w32 (by decide) (by decide)).trans w47_d8
  have w48_dc : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K48.w32 (by decide) (by decide)).trans w47_dc
  have w48_e0 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K48.w32 (by decide) (by decide)).trans w47_e0
  have w48_e4 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K48.w32 (by decide) (by decide)).trans w47_e4
  have w48_e8 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K48.w32 (by decide) (by decide)).trans w47_e8
  have w48_ec : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K48.w32 (by decide) (by decide)).trans w47_ec
  have w48_f0 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K48.w32 (by decide) (by decide)).trans w47_f0
  have w48_f4 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K48.w32 (by decide) (by decide)).trans w47_f4
  have w48_f8 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K48.w32 (by decide) (by decide)).trans w47_f8
  have w48_fc : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K48.w32 (by decide) (by decide)).trans w47_fc
  have w48_100 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K48.w32 (by decide) (by decide)).trans w47_100
  have w48_104 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K48.w32 (by decide) (by decide)).trans w47_104
  have w48_108 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K48.w32 (by decide) (by decide)).trans w47_108
  have w48_10c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K48.w32 (by decide) (by decide)).trans w47_10c
  have w48_110 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K48.w32 (by decide) (by decide)).trans w47_110
  have w48_114 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K48.w32 (by decide) (by decide)).trans w47_114
  have w48_118 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K48.w32 (by decide) (by decide)).trans w47_118
  have w48_11c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K48.w32 (by decide) (by decide)).trans w47_11c
  have w48_120 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K48.w32 (by decide) (by decide)).trans w47_120
  have w48_124 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K48.w32 (by decide) (by decide)).trans w47_124
  have w48_128 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K48.w32 (by decide) (by decide)).trans w47_128
  have w48_12c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K48.w32 (by decide) (by decide)).trans w47_12c
  have w48_130 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K48.w32 (by decide) (by decide)).trans w47_130
  have w48_a20 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := (K48.w32 (by decide) (by decide)).trans w47_a20
  have w48_1020 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := (K48.w32 (by decide) (by decide)).trans w47_1020
  have w48_1480 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := (K48.w32 (by decide) (by decide)).trans w47_1480
  have w48_b28 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xB28) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by
    rw [← w47_1480]
    exact ld_cp fun q hq => by
      have := X48 (0x0 + q) (by omega)
      rwa [show 0xB28 + (0x0 + q) = 0xB28 + q by omega,
        show 0x1480 + (0x0 + q) = 0x1480 + q by omega] at this
  have a48_2a0 : accV n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K48.acc (by decide) (by decide)).trans a47_2a0
  have a48_2c0 : accV n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K48.acc (by decide) (by decide)).trans a47_2c0
  have a48_2e0 : accV n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K48.acc (by decide) (by decide)).trans a47_2e0
  have a48_380 : accV n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := (K48.acc (by decide) (by decide)).trans a47_380
  have a48_400 : accV n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := (K48.acc (by decide) (by decide)).trans a47_400
  have a48_13e0 : accV n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := (K48.acc (by decide) (by decide)).trans a47_13e0
  have a48_1460 : accV n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := (K48.acc (by decide) (by decide)).trans a47_1460
  have a48_1588 : accV n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U2 := (K48.acc (by decide) (by decide)).trans a47_1588
  have p48_320 : ptF n48.mem B 0x320 = P0 := (K48.pt (by decide) (by decide)).trans p47_320
  have p48_3a0 : ptF n48.mem B 0x3A0 = P1 := (K48.pt (by decide) (by decide)).trans p47_3a0
  have p48_420 : ptF n48.mem B 0x420 = tbl2 P0 0 := (K48.pt (by decide) (by decide)).trans p47_420
  have p48_480 : ptF n48.mem B 0x480 = tbl2 P0 1 := (K48.pt (by decide) (by decide)).trans p47_480
  have p48_4e0 : ptF n48.mem B 0x4E0 = tbl2 P0 2 := (K48.pt (by decide) (by decide)).trans p47_4e0
  have p48_540 : ptF n48.mem B 0x540 = tbl2 P0 3 := (K48.pt (by decide) (by decide)).trans p47_540
  have p48_5a0 : ptF n48.mem B 0x5A0 = tbl2 P0 4 := (K48.pt (by decide) (by decide)).trans p47_5a0
  have p48_600 : ptF n48.mem B 0x600 = tbl2 P0 5 := (K48.pt (by decide) (by decide)).trans p47_600
  have p48_660 : ptF n48.mem B 0x660 = tbl2 P0 6 := (K48.pt (by decide) (by decide)).trans p47_660
  have p48_6c0 : ptF n48.mem B 0x6C0 = tbl2 P0 7 := (K48.pt (by decide) (by decide)).trans p47_6c0
  have p48_720 : ptF n48.mem B 0x720 = tbl2 P1 0 := (K48.pt (by decide) (by decide)).trans p47_720
  have p48_780 : ptF n48.mem B 0x780 = tbl2 P1 1 := (K48.pt (by decide) (by decide)).trans p47_780
  have p48_7e0 : ptF n48.mem B 0x7E0 = tbl2 P1 2 := (K48.pt (by decide) (by decide)).trans p47_7e0
  have p48_840 : ptF n48.mem B 0x840 = tbl2 P1 3 := (K48.pt (by decide) (by decide)).trans p47_840
  have p48_8a0 : ptF n48.mem B 0x8A0 = tbl2 P1 4 := (K48.pt (by decide) (by decide)).trans p47_8a0
  have p48_900 : ptF n48.mem B 0x900 = tbl2 P1 5 := (K48.pt (by decide) (by decide)).trans p47_900
  have p48_960 : ptF n48.mem B 0x960 = tbl2 P1 6 := (K48.pt (by decide) (by decide)).trans p47_960
  have p48_9c0 : ptF n48.mem B 0x9C0 = tbl2 P1 7 := (K48.pt (by decide) (by decide)).trans p47_9c0
  have p48_c60 : ptF n48.mem B 0xC60 = tbl2 P0 6 := (K48.pt (by decide) (by decide)).trans p47_c60
  have p48_cc0 : ptF n48.mem B 0xCC0 = tbl2 P0 7 := (K48.pt (by decide) (by decide)).trans p47_cc0
  have p48_d20 : ptF n48.mem B 0xD20 = tbl2 P1 0 := (K48.pt (by decide) (by decide)).trans p47_d20
  have p48_d80 : ptF n48.mem B 0xD80 = tbl2 P1 1 := (K48.pt (by decide) (by decide)).trans p47_d80
  have p48_de0 : ptF n48.mem B 0xDE0 = tbl2 P1 2 := (K48.pt (by decide) (by decide)).trans p47_de0
  have p48_e40 : ptF n48.mem B 0xE40 = tbl2 P1 3 := (K48.pt (by decide) (by decide)).trans p47_e40
  have p48_ea0 : ptF n48.mem B 0xEA0 = tbl2 P1 4 := (K48.pt (by decide) (by decide)).trans p47_ea0
  have p48_f00 : ptF n48.mem B 0xF00 = tbl2 P1 5 := (K48.pt (by decide) (by decide)).trans p47_f00
  have p48_f60 : ptF n48.mem B 0xF60 = tbl2 P1 6 := (K48.pt (by decide) (by decide)).trans p47_f60
  have p48_fc0 : ptF n48.mem B 0xFC0 = tbl2 P1 7 := (K48.pt (by decide) (by decide)).trans p47_fc0
  have p48_1380 : ptF n48.mem B 0x1380 = P0 := (K48.pt (by decide) (by decide)).trans p47_1380
  have p48_1400 : ptF n48.mem B 0x1400 = P1 := (K48.pt (by decide) (by decide)).trans p47_1400
  have mb48_a24 : memBytes n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [K48.mb (by decide) (by decide)]; exact mb47_a24
  have mb48_1024 : memBytes n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [K48.mb (by decide) (by decide)]; exact mb47_1024
  have mb48_1320 : leN (memBytes n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U2 := by rw [K48.mb (by decide) (by decide)]; exact mb47_1320
  have mb48_1484 : memBytes n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [K48.mb (by decide) (by decide)]; exact mb47_1484
  have mb48_b2c : memBytes n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xB2C) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by
    rw [memBytes_cp (S := B + 0x21A0) (c := 0xB2C) (d := 0x1484) (N := 0x101) fun q hq => by
      rw [show 0xB2C + q = 0xB28 + (0x4 + q) by omega, X48 (0x4 + q) (by omega),
        show 0x1480 + (0x4 + q) = 0x1484 + q by omega]]; exact mb47_1484
  clear mb47_1484 mb47_1320 mb47_1024 mb47_a24 p47_1400 p47_1380 p47_fc0 p47_f60 p47_f00 p47_ea0 p47_e40 p47_de0 p47_d80 p47_d20 p47_cc0 p47_c60 p47_c00 p47_ba0 p47_b40 p47_9c0 p47_960 p47_900 p47_8a0 p47_840 p47_7e0 p47_780 p47_720 p47_6c0 p47_660 p47_600 p47_5a0 p47_540 p47_4e0 p47_480 p47_420 p47_3a0 p47_320 a47_1588 a47_1460 a47_13e0 a47_400 a47_380 a47_2e0 a47_2c0 a47_2a0 w47_1480 w47_1020 w47_a20 w47_130 w47_12c w47_128 w47_124 w47_120 w47_11c w47_118 w47_114 w47_110 w47_10c w47_108 w47_104 w47_100 w47_fc w47_f8 w47_f4 w47_f0 w47_ec w47_e8 w47_e4 w47_e0 w47_dc w47_d8 w47_d4 w47_d0 w47_cc w47_c8 w47_c4 w47_c0 w47_bc w47_b8 w47_b4 w47_b0 w47_ac w47_a8 w47_a4 w47_a0 w47_9c w47_98 w47_94 w47_90 w47_8c w47_88 w47_84 w47_80 w47_7c w47_78 w47_70 w47_6c w47_68 w47_64 w47_60 w47_5c w47_58 w47_54 w47_50 w47_4c w47_48 w47_44 w47_40 w47_3c w47_38 w47_34 w47_30 w47_2c w47_28 w47_24 g47_12 g47_11 g47_10 g47_27 g47_26 g47_25 g47_24 g47_23 g47_22 g47_21 g47_20 g47_19 g47_18 g47_9 g47_8 g47_4 g47_3 g47_2 V47 E47 fR47 t47 fr47 rb47 s47 m47 u47 c47
  -- 0x18CE
  obtain ⟨n49, c49, u49⟩ := s48.block svEcW18ce E48.self svEcW18ce_end
    ⟨trivial, trivial⟩
  have m49 : n49.mem = n48.mem := u49.mem
  have s49 : St n49.mem SV n49 0x18D0 (reg n49) := ⟨u49.pc, rfl, fun _ => rfl⟩
  have rb49 : ∀ q, reg n49 q = (runBlock svEcW18ce (n48.mem, reg n48)).2 q := fun q => by rw [u49.regs]
  have fr49 : ∀ x, SvR B x → n49.mem x = n48.mem x := fun x _ => by rw [m49]
  have t49 : Steps n0 n49 := t48.trans c49
  have fR49 : ∀ x, SvR B x → n49.mem x = M0 x := fun x hx => (fr49 x hx).trans (fR48 x hx)
  have E49 : SvCode n49.mem := E48.fr F fr49
  have V49 : SvSaves B n49.mem v := V48.same m49
  have g49_2 : reg n49 sp = B + 0x21A0 := by
    rw [rb49, runBlock_reg _ _ _ sp s48.zero (by decide), g48_2]
  have g49_3 : reg n49 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb49, runBlock_reg _ _ _ (3 : Fin 32) s48.zero (by decide), g48_3]
  have g49_4 : reg n49 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb49, runBlock_reg _ _ _ (4 : Fin 32) s48.zero (by decide), g48_4]
  have g49_9 : reg n49 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by
    rw [rb49, runBlock_reg _ _ _ (9 : Fin 32) s48.zero (by decide), g48_9]
  have g49_18 : reg n49 (18 : Fin 32) = out := by
    rw [rb49, runBlock_reg _ _ _ (18 : Fin 32) s48.zero (by decide), g48_18]
  have g49_19 : reg n49 (19 : Fin 32) = bp := by
    rw [rb49, runBlock_reg _ _ _ (19 : Fin 32) s48.zero (by decide), g48_19]
  have g49_20 : reg n49 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb49, runBlock_reg _ _ _ (20 : Fin 32) s48.zero (by decide), g48_20]
  have g49_21 : reg n49 (21 : Fin 32) = s5v := by
    rw [rb49, runBlock_reg _ _ _ (21 : Fin 32) s48.zero (by decide), g48_21]
  have g49_22 : reg n49 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by
    rw [rb49, runBlock_reg _ _ _ (22 : Fin 32) s48.zero (by decide), g48_22]
  have g49_23 : reg n49 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by
    rw [rb49, runBlock_reg _ _ _ (23 : Fin 32) s48.zero (by decide), g48_23]
  have g49_24 : reg n49 (24 : Fin 32) = s8v := by
    rw [rb49, runBlock_reg _ _ _ (24 : Fin 32) s48.zero (by decide), g48_24]
  have g49_25 : reg n49 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb49, runBlock_reg _ _ _ (25 : Fin 32) s48.zero (by decide), g48_25]
  have g49_26 : reg n49 (26 : Fin 32) = x26 := by
    rw [rb49, runBlock_reg _ _ _ (26 : Fin 32) s48.zero (by decide), g48_26]
  have g49_27 : reg n49 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb49, runBlock_reg _ _ _ (27 : Fin 32) s48.zero (by decide), g48_27]
  have g49_8 : reg n49 (8 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb49]; simp +decide only [runBlock, BInstr.run, svEcW18ce, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g48_2, g48_3, g48_4, g48_8, g48_9, g48_18, g48_19, g48_20, g48_21, g48_22, g48_23, g48_24, g48_25, g48_26, g48_27, s48.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w49_24 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m49]; exact w48_24
  have w49_28 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m49]; exact w48_28
  have w49_2c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m49]; exact w48_2c
  have w49_30 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m49]; exact w48_30
  have w49_34 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m49]; exact w48_34
  have w49_38 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m49]; exact w48_38
  have w49_3c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m49]; exact w48_3c
  have w49_40 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m49]; exact w48_40
  have w49_44 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m49]; exact w48_44
  have w49_48 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m49]; exact w48_48
  have w49_4c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m49]; exact w48_4c
  have w49_50 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m49]; exact w48_50
  have w49_54 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m49]; exact w48_54
  have w49_58 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m49]; exact w48_58
  have w49_5c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m49]; exact w48_5c
  have w49_60 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m49]; exact w48_60
  have w49_64 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m49]; exact w48_64
  have w49_68 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m49]; exact w48_68
  have w49_6c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m49]; exact w48_6c
  have w49_70 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m49]; exact w48_70
  have w49_78 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m49]; exact w48_78
  have w49_7c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m49]; exact w48_7c
  have w49_80 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m49]; exact w48_80
  have w49_84 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m49]; exact w48_84
  have w49_88 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m49]; exact w48_88
  have w49_8c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m49]; exact w48_8c
  have w49_90 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m49]; exact w48_90
  have w49_94 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m49]; exact w48_94
  have w49_98 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m49]; exact w48_98
  have w49_9c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m49]; exact w48_9c
  have w49_a0 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m49]; exact w48_a0
  have w49_a4 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m49]; exact w48_a4
  have w49_a8 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m49]; exact w48_a8
  have w49_ac : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m49]; exact w48_ac
  have w49_b0 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m49]; exact w48_b0
  have w49_b4 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m49]; exact w48_b4
  have w49_b8 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m49]; exact w48_b8
  have w49_bc : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m49]; exact w48_bc
  have w49_c0 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m49]; exact w48_c0
  have w49_c4 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m49]; exact w48_c4
  have w49_c8 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m49]; exact w48_c8
  have w49_cc : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m49]; exact w48_cc
  have w49_d0 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m49]; exact w48_d0
  have w49_d4 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m49]; exact w48_d4
  have w49_d8 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m49]; exact w48_d8
  have w49_dc : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m49]; exact w48_dc
  have w49_e0 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m49]; exact w48_e0
  have w49_e4 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m49]; exact w48_e4
  have w49_e8 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m49]; exact w48_e8
  have w49_ec : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m49]; exact w48_ec
  have w49_f0 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m49]; exact w48_f0
  have w49_f4 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m49]; exact w48_f4
  have w49_f8 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m49]; exact w48_f8
  have w49_fc : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m49]; exact w48_fc
  have w49_100 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m49]; exact w48_100
  have w49_104 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m49]; exact w48_104
  have w49_108 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m49]; exact w48_108
  have w49_10c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m49]; exact w48_10c
  have w49_110 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m49]; exact w48_110
  have w49_114 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m49]; exact w48_114
  have w49_118 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m49]; exact w48_118
  have w49_11c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m49]; exact w48_11c
  have w49_120 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m49]; exact w48_120
  have w49_124 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m49]; exact w48_124
  have w49_128 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m49]; exact w48_128
  have w49_12c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m49]; exact w48_12c
  have w49_130 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m49]; exact w48_130
  have w49_a20 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m49]; exact w48_a20
  have w49_b28 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xB28) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by rw [m49]; exact w48_b28
  have w49_1020 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by rw [m49]; exact w48_1020
  have w49_1480 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by rw [m49]; exact w48_1480
  have a49_2a0 : accV n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m49]; exact a48_2a0
  have a49_2c0 : accV n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m49]; exact a48_2c0
  have a49_2e0 : accV n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m49]; exact a48_2e0
  have a49_380 : accV n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m49]; exact a48_380
  have a49_400 : accV n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m49]; exact a48_400
  have a49_13e0 : accV n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := by rw [m49]; exact a48_13e0
  have a49_1460 : accV n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := by rw [m49]; exact a48_1460
  have a49_1588 : accV n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U2 := by rw [m49]; exact a48_1588
  have p49_320 : ptF n49.mem B 0x320 = P0 := by rw [m49]; exact p48_320
  have p49_3a0 : ptF n49.mem B 0x3A0 = P1 := by rw [m49]; exact p48_3a0
  have p49_420 : ptF n49.mem B 0x420 = tbl2 P0 0 := by rw [m49]; exact p48_420
  have p49_480 : ptF n49.mem B 0x480 = tbl2 P0 1 := by rw [m49]; exact p48_480
  have p49_4e0 : ptF n49.mem B 0x4E0 = tbl2 P0 2 := by rw [m49]; exact p48_4e0
  have p49_540 : ptF n49.mem B 0x540 = tbl2 P0 3 := by rw [m49]; exact p48_540
  have p49_5a0 : ptF n49.mem B 0x5A0 = tbl2 P0 4 := by rw [m49]; exact p48_5a0
  have p49_600 : ptF n49.mem B 0x600 = tbl2 P0 5 := by rw [m49]; exact p48_600
  have p49_660 : ptF n49.mem B 0x660 = tbl2 P0 6 := by rw [m49]; exact p48_660
  have p49_6c0 : ptF n49.mem B 0x6C0 = tbl2 P0 7 := by rw [m49]; exact p48_6c0
  have p49_720 : ptF n49.mem B 0x720 = tbl2 P1 0 := by rw [m49]; exact p48_720
  have p49_780 : ptF n49.mem B 0x780 = tbl2 P1 1 := by rw [m49]; exact p48_780
  have p49_7e0 : ptF n49.mem B 0x7E0 = tbl2 P1 2 := by rw [m49]; exact p48_7e0
  have p49_840 : ptF n49.mem B 0x840 = tbl2 P1 3 := by rw [m49]; exact p48_840
  have p49_8a0 : ptF n49.mem B 0x8A0 = tbl2 P1 4 := by rw [m49]; exact p48_8a0
  have p49_900 : ptF n49.mem B 0x900 = tbl2 P1 5 := by rw [m49]; exact p48_900
  have p49_960 : ptF n49.mem B 0x960 = tbl2 P1 6 := by rw [m49]; exact p48_960
  have p49_9c0 : ptF n49.mem B 0x9C0 = tbl2 P1 7 := by rw [m49]; exact p48_9c0
  have p49_c60 : ptF n49.mem B 0xC60 = tbl2 P0 6 := by rw [m49]; exact p48_c60
  have p49_cc0 : ptF n49.mem B 0xCC0 = tbl2 P0 7 := by rw [m49]; exact p48_cc0
  have p49_d20 : ptF n49.mem B 0xD20 = tbl2 P1 0 := by rw [m49]; exact p48_d20
  have p49_d80 : ptF n49.mem B 0xD80 = tbl2 P1 1 := by rw [m49]; exact p48_d80
  have p49_de0 : ptF n49.mem B 0xDE0 = tbl2 P1 2 := by rw [m49]; exact p48_de0
  have p49_e40 : ptF n49.mem B 0xE40 = tbl2 P1 3 := by rw [m49]; exact p48_e40
  have p49_ea0 : ptF n49.mem B 0xEA0 = tbl2 P1 4 := by rw [m49]; exact p48_ea0
  have p49_f00 : ptF n49.mem B 0xF00 = tbl2 P1 5 := by rw [m49]; exact p48_f00
  have p49_f60 : ptF n49.mem B 0xF60 = tbl2 P1 6 := by rw [m49]; exact p48_f60
  have p49_fc0 : ptF n49.mem B 0xFC0 = tbl2 P1 7 := by rw [m49]; exact p48_fc0
  have p49_1380 : ptF n49.mem B 0x1380 = P0 := by rw [m49]; exact p48_1380
  have p49_1400 : ptF n49.mem B 0x1400 = P1 := by rw [m49]; exact p48_1400
  have mb49_a24 : memBytes n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m49]; exact mb48_a24
  have mb49_b2c : memBytes n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xB2C) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [m49]; exact mb48_b2c
  have mb49_1024 : memBytes n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [m49]; exact mb48_1024
  have mb49_1320 : leN (memBytes n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U2 := by rw [m49]; exact mb48_1320
  have mb49_1484 : memBytes n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [m49]; exact mb48_1484
  clear mb48_b2c mb48_1484 mb48_1320 mb48_1024 mb48_a24 p48_1400 p48_1380 p48_fc0 p48_f60 p48_f00 p48_ea0 p48_e40 p48_de0 p48_d80 p48_d20 p48_cc0 p48_c60 p48_9c0 p48_960 p48_900 p48_8a0 p48_840 p48_7e0 p48_780 p48_720 p48_6c0 p48_660 p48_600 p48_5a0 p48_540 p48_4e0 p48_480 p48_420 p48_3a0 p48_320 a48_1588 a48_1460 a48_13e0 a48_400 a48_380 a48_2e0 a48_2c0 a48_2a0 w48_b28 w48_1480 w48_1020 w48_a20 w48_130 w48_12c w48_128 w48_124 w48_120 w48_11c w48_118 w48_114 w48_110 w48_10c w48_108 w48_104 w48_100 w48_fc w48_f8 w48_f4 w48_f0 w48_ec w48_e8 w48_e4 w48_e0 w48_dc w48_d8 w48_d4 w48_d0 w48_cc w48_c8 w48_c4 w48_c0 w48_bc w48_b8 w48_b4 w48_b0 w48_ac w48_a8 w48_a4 w48_a0 w48_9c w48_98 w48_94 w48_90 w48_8c w48_88 w48_84 w48_80 w48_7c w48_78 w48_70 w48_6c w48_68 w48_64 w48_60 w48_5c w48_58 w48_54 w48_50 w48_4c w48_48 w48_44 w48_40 w48_3c w48_38 w48_34 w48_30 w48_2c w48_28 w48_24 g48_27 g48_26 g48_25 g48_24 g48_23 g48_22 g48_21 g48_20 g48_19 g48_18 g48_9 g48_8 g48_4 g48_3 g48_2 V48 E48 fR48 t48 fr48 s48 X48 K48 P48
  -- 0x18D0: branch, not taken
  obtain ⟨n50, d50, u50⟩ := s49.notTaken E49.self 0x18D4 sv_at_18d0
    (by decide) (by rw [g49_8, g49_25]; decide)
  have s50 : St n50.mem SV n50 0x18D4 (reg n50) := ⟨u50.pc, rfl, fun _ => rfl⟩
  have m50 : n50.mem = n49.mem := u50.mem
  have fr50 : ∀ x, SvR B x → n50.mem x = n49.mem x := fun x _ => by rw [m50]
  have t50 : Steps n0 n50 := t49.trans (.single d50)
  have fR50 : ∀ x, SvR B x → n50.mem x = M0 x := fun x hx => (fr50 x hx).trans (fR49 x hx)
  have E50 : SvCode n50.mem := E49.fr F fr50
  have V50 : SvSaves B n50.mem v := V49.same m50
  have g50_2 : reg n50 sp = B + 0x21A0 := by rw [u50.regs, g49_2]
  have g50_3 : reg n50 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u50.regs, g49_3]
  have g50_4 : reg n50 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u50.regs, g49_4]
  have g50_8 : reg n50 (8 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u50.regs, g49_8]
  have g50_9 : reg n50 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by rw [u50.regs, g49_9]
  have g50_18 : reg n50 (18 : Fin 32) = out := by rw [u50.regs, g49_18]
  have g50_19 : reg n50 (19 : Fin 32) = bp := by rw [u50.regs, g49_19]
  have g50_20 : reg n50 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u50.regs, g49_20]
  have g50_21 : reg n50 (21 : Fin 32) = s5v := by rw [u50.regs, g49_21]
  have g50_22 : reg n50 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [u50.regs, g49_22]
  have g50_23 : reg n50 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by rw [u50.regs, g49_23]
  have g50_24 : reg n50 (24 : Fin 32) = s8v := by rw [u50.regs, g49_24]
  have g50_25 : reg n50 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u50.regs, g49_25]
  have g50_26 : reg n50 (26 : Fin 32) = x26 := by rw [u50.regs, g49_26]
  have g50_27 : reg n50 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u50.regs, g49_27]
  have w50_24 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m50]; exact w49_24
  have w50_28 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m50]; exact w49_28
  have w50_2c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m50]; exact w49_2c
  have w50_30 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m50]; exact w49_30
  have w50_34 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m50]; exact w49_34
  have w50_38 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m50]; exact w49_38
  have w50_3c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m50]; exact w49_3c
  have w50_40 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m50]; exact w49_40
  have w50_44 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m50]; exact w49_44
  have w50_48 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m50]; exact w49_48
  have w50_4c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m50]; exact w49_4c
  have w50_50 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m50]; exact w49_50
  have w50_54 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m50]; exact w49_54
  have w50_58 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m50]; exact w49_58
  have w50_5c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m50]; exact w49_5c
  have w50_60 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m50]; exact w49_60
  have w50_64 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m50]; exact w49_64
  have w50_68 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m50]; exact w49_68
  have w50_6c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m50]; exact w49_6c
  have w50_70 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m50]; exact w49_70
  have w50_78 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m50]; exact w49_78
  have w50_7c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m50]; exact w49_7c
  have w50_80 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m50]; exact w49_80
  have w50_84 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m50]; exact w49_84
  have w50_88 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m50]; exact w49_88
  have w50_8c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m50]; exact w49_8c
  have w50_90 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m50]; exact w49_90
  have w50_94 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m50]; exact w49_94
  have w50_98 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m50]; exact w49_98
  have w50_9c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m50]; exact w49_9c
  have w50_a0 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m50]; exact w49_a0
  have w50_a4 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m50]; exact w49_a4
  have w50_a8 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m50]; exact w49_a8
  have w50_ac : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m50]; exact w49_ac
  have w50_b0 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m50]; exact w49_b0
  have w50_b4 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m50]; exact w49_b4
  have w50_b8 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m50]; exact w49_b8
  have w50_bc : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m50]; exact w49_bc
  have w50_c0 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m50]; exact w49_c0
  have w50_c4 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m50]; exact w49_c4
  have w50_c8 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m50]; exact w49_c8
  have w50_cc : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m50]; exact w49_cc
  have w50_d0 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m50]; exact w49_d0
  have w50_d4 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m50]; exact w49_d4
  have w50_d8 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m50]; exact w49_d8
  have w50_dc : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m50]; exact w49_dc
  have w50_e0 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m50]; exact w49_e0
  have w50_e4 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m50]; exact w49_e4
  have w50_e8 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m50]; exact w49_e8
  have w50_ec : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m50]; exact w49_ec
  have w50_f0 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m50]; exact w49_f0
  have w50_f4 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m50]; exact w49_f4
  have w50_f8 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m50]; exact w49_f8
  have w50_fc : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m50]; exact w49_fc
  have w50_100 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m50]; exact w49_100
  have w50_104 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m50]; exact w49_104
  have w50_108 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m50]; exact w49_108
  have w50_10c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m50]; exact w49_10c
  have w50_110 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m50]; exact w49_110
  have w50_114 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m50]; exact w49_114
  have w50_118 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m50]; exact w49_118
  have w50_11c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m50]; exact w49_11c
  have w50_120 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m50]; exact w49_120
  have w50_124 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m50]; exact w49_124
  have w50_128 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m50]; exact w49_128
  have w50_12c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m50]; exact w49_12c
  have w50_130 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m50]; exact w49_130
  have w50_a20 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m50]; exact w49_a20
  have w50_b28 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xB28) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by rw [m50]; exact w49_b28
  have w50_1020 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by rw [m50]; exact w49_1020
  have w50_1480 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by rw [m50]; exact w49_1480
  have a50_2a0 : accV n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m50]; exact a49_2a0
  have a50_2c0 : accV n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m50]; exact a49_2c0
  have a50_2e0 : accV n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m50]; exact a49_2e0
  have a50_380 : accV n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m50]; exact a49_380
  have a50_400 : accV n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m50]; exact a49_400
  have a50_13e0 : accV n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := by rw [m50]; exact a49_13e0
  have a50_1460 : accV n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := by rw [m50]; exact a49_1460
  have a50_1588 : accV n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U2 := by rw [m50]; exact a49_1588
  have p50_320 : ptF n50.mem B 0x320 = P0 := by rw [m50]; exact p49_320
  have p50_3a0 : ptF n50.mem B 0x3A0 = P1 := by rw [m50]; exact p49_3a0
  have p50_420 : ptF n50.mem B 0x420 = tbl2 P0 0 := by rw [m50]; exact p49_420
  have p50_480 : ptF n50.mem B 0x480 = tbl2 P0 1 := by rw [m50]; exact p49_480
  have p50_4e0 : ptF n50.mem B 0x4E0 = tbl2 P0 2 := by rw [m50]; exact p49_4e0
  have p50_540 : ptF n50.mem B 0x540 = tbl2 P0 3 := by rw [m50]; exact p49_540
  have p50_5a0 : ptF n50.mem B 0x5A0 = tbl2 P0 4 := by rw [m50]; exact p49_5a0
  have p50_600 : ptF n50.mem B 0x600 = tbl2 P0 5 := by rw [m50]; exact p49_600
  have p50_660 : ptF n50.mem B 0x660 = tbl2 P0 6 := by rw [m50]; exact p49_660
  have p50_6c0 : ptF n50.mem B 0x6C0 = tbl2 P0 7 := by rw [m50]; exact p49_6c0
  have p50_720 : ptF n50.mem B 0x720 = tbl2 P1 0 := by rw [m50]; exact p49_720
  have p50_780 : ptF n50.mem B 0x780 = tbl2 P1 1 := by rw [m50]; exact p49_780
  have p50_7e0 : ptF n50.mem B 0x7E0 = tbl2 P1 2 := by rw [m50]; exact p49_7e0
  have p50_840 : ptF n50.mem B 0x840 = tbl2 P1 3 := by rw [m50]; exact p49_840
  have p50_8a0 : ptF n50.mem B 0x8A0 = tbl2 P1 4 := by rw [m50]; exact p49_8a0
  have p50_900 : ptF n50.mem B 0x900 = tbl2 P1 5 := by rw [m50]; exact p49_900
  have p50_960 : ptF n50.mem B 0x960 = tbl2 P1 6 := by rw [m50]; exact p49_960
  have p50_9c0 : ptF n50.mem B 0x9C0 = tbl2 P1 7 := by rw [m50]; exact p49_9c0
  have p50_c60 : ptF n50.mem B 0xC60 = tbl2 P0 6 := by rw [m50]; exact p49_c60
  have p50_cc0 : ptF n50.mem B 0xCC0 = tbl2 P0 7 := by rw [m50]; exact p49_cc0
  have p50_d20 : ptF n50.mem B 0xD20 = tbl2 P1 0 := by rw [m50]; exact p49_d20
  have p50_d80 : ptF n50.mem B 0xD80 = tbl2 P1 1 := by rw [m50]; exact p49_d80
  have p50_de0 : ptF n50.mem B 0xDE0 = tbl2 P1 2 := by rw [m50]; exact p49_de0
  have p50_e40 : ptF n50.mem B 0xE40 = tbl2 P1 3 := by rw [m50]; exact p49_e40
  have p50_ea0 : ptF n50.mem B 0xEA0 = tbl2 P1 4 := by rw [m50]; exact p49_ea0
  have p50_f00 : ptF n50.mem B 0xF00 = tbl2 P1 5 := by rw [m50]; exact p49_f00
  have p50_f60 : ptF n50.mem B 0xF60 = tbl2 P1 6 := by rw [m50]; exact p49_f60
  have p50_fc0 : ptF n50.mem B 0xFC0 = tbl2 P1 7 := by rw [m50]; exact p49_fc0
  have p50_1380 : ptF n50.mem B 0x1380 = P0 := by rw [m50]; exact p49_1380
  have p50_1400 : ptF n50.mem B 0x1400 = P1 := by rw [m50]; exact p49_1400
  have mb50_a24 : memBytes n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m50]; exact mb49_a24
  have mb50_b2c : memBytes n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xB2C) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [m50]; exact mb49_b2c
  have mb50_1024 : memBytes n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [m50]; exact mb49_1024
  have mb50_1320 : leN (memBytes n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U2 := by rw [m50]; exact mb49_1320
  have mb50_1484 : memBytes n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [m50]; exact mb49_1484
  clear mb49_1484 mb49_1320 mb49_1024 mb49_b2c mb49_a24 p49_1400 p49_1380 p49_fc0 p49_f60 p49_f00 p49_ea0 p49_e40 p49_de0 p49_d80 p49_d20 p49_cc0 p49_c60 p49_9c0 p49_960 p49_900 p49_8a0 p49_840 p49_7e0 p49_780 p49_720 p49_6c0 p49_660 p49_600 p49_5a0 p49_540 p49_4e0 p49_480 p49_420 p49_3a0 p49_320 a49_1588 a49_1460 a49_13e0 a49_400 a49_380 a49_2e0 a49_2c0 a49_2a0 w49_1480 w49_1020 w49_b28 w49_a20 w49_130 w49_12c w49_128 w49_124 w49_120 w49_11c w49_118 w49_114 w49_110 w49_10c w49_108 w49_104 w49_100 w49_fc w49_f8 w49_f4 w49_f0 w49_ec w49_e8 w49_e4 w49_e0 w49_dc w49_d8 w49_d4 w49_d0 w49_cc w49_c8 w49_c4 w49_c0 w49_bc w49_b8 w49_b4 w49_b0 w49_ac w49_a8 w49_a4 w49_a0 w49_9c w49_98 w49_94 w49_90 w49_8c w49_88 w49_84 w49_80 w49_7c w49_78 w49_70 w49_6c w49_68 w49_64 w49_60 w49_5c w49_58 w49_54 w49_50 w49_4c w49_48 w49_44 w49_40 w49_3c w49_38 w49_34 w49_30 w49_2c w49_28 w49_24 g49_8 g49_27 g49_26 g49_25 g49_24 g49_23 g49_22 g49_21 g49_20 g49_19 g49_18 g49_9 g49_4 g49_3 g49_2 V49 E49 fR49 t49 fr49 rb49 s49 m49 u49 c49
  -- 0x18D4
  obtain ⟨n51, c51, u51⟩ := s50.block svEcW18d4 E50.self svEcW18d4_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m51 : n51.mem = n50.mem := u51.mem
  have s51 : St n51.mem SV n51 0x18E8 (reg n51) := ⟨u51.pc, rfl, fun _ => rfl⟩
  have rb51 : ∀ q, reg n51 q = (runBlock svEcW18d4 (n50.mem, reg n50)).2 q := fun q => by rw [u51.regs]
  have fr51 : ∀ x, SvR B x → n51.mem x = n50.mem x := fun x _ => by rw [m51]
  have t51 : Steps n0 n51 := t50.trans c51
  have fR51 : ∀ x, SvR B x → n51.mem x = M0 x := fun x hx => (fr51 x hx).trans (fR50 x hx)
  have E51 : SvCode n51.mem := E50.fr F fr51
  have V51 : SvSaves B n51.mem v := V50.same m51
  have g51_2 : reg n51 sp = B + 0x21A0 := by
    rw [rb51, runBlock_reg _ _ _ sp s50.zero (by decide), g50_2]
  have g51_3 : reg n51 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb51, runBlock_reg _ _ _ (3 : Fin 32) s50.zero (by decide), g50_3]
  have g51_4 : reg n51 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb51, runBlock_reg _ _ _ (4 : Fin 32) s50.zero (by decide), g50_4]
  have g51_8 : reg n51 (8 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb51, runBlock_reg _ _ _ (8 : Fin 32) s50.zero (by decide), g50_8]
  have g51_9 : reg n51 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by
    rw [rb51, runBlock_reg _ _ _ (9 : Fin 32) s50.zero (by decide), g50_9]
  have g51_18 : reg n51 (18 : Fin 32) = out := by
    rw [rb51, runBlock_reg _ _ _ (18 : Fin 32) s50.zero (by decide), g50_18]
  have g51_19 : reg n51 (19 : Fin 32) = bp := by
    rw [rb51, runBlock_reg _ _ _ (19 : Fin 32) s50.zero (by decide), g50_19]
  have g51_20 : reg n51 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb51, runBlock_reg _ _ _ (20 : Fin 32) s50.zero (by decide), g50_20]
  have g51_21 : reg n51 (21 : Fin 32) = s5v := by
    rw [rb51, runBlock_reg _ _ _ (21 : Fin 32) s50.zero (by decide), g50_21]
  have g51_22 : reg n51 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by
    rw [rb51, runBlock_reg _ _ _ (22 : Fin 32) s50.zero (by decide), g50_22]
  have g51_23 : reg n51 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by
    rw [rb51, runBlock_reg _ _ _ (23 : Fin 32) s50.zero (by decide), g50_23]
  have g51_24 : reg n51 (24 : Fin 32) = s8v := by
    rw [rb51, runBlock_reg _ _ _ (24 : Fin 32) s50.zero (by decide), g50_24]
  have g51_25 : reg n51 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by
    rw [rb51, runBlock_reg _ _ _ (25 : Fin 32) s50.zero (by decide), g50_25]
  have g51_26 : reg n51 (26 : Fin 32) = x26 := by
    rw [rb51, runBlock_reg _ _ _ (26 : Fin 32) s50.zero (by decide), g50_26]
  have g51_27 : reg n51 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb51, runBlock_reg _ _ _ (27 : Fin 32) s50.zero (by decide), g50_27]
  have g51_10 : reg n51 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1020 := by
    rw [rb51]; simp +decide only [runBlock, BInstr.run, svEcW18d4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g50_2, g50_3, g50_4, g50_8, g50_9, g50_18, g50_19, g50_20, g50_21, g50_22, g50_23, g50_24, g50_25, g50_26, g50_27, s50.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g51_11 : reg n51 a1 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb51]; simp +decide only [runBlock, BInstr.run, svEcW18d4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g50_2, g50_3, g50_4, g50_8, g50_9, g50_18, g50_19, g50_20, g50_21, g50_22, g50_23, g50_24, g50_25, g50_26, g50_27, s50.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g51_12 : reg n51 a2 = BitVec.ofNat 32 0x210 := by
    rw [rb51]; simp +decide only [runBlock, BInstr.run, svEcW18d4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g50_2, g50_3, g50_4, g50_8, g50_9, g50_18, g50_19, g50_20, g50_21, g50_22, g50_23, g50_24, g50_25, g50_26, g50_27, s50.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w51_24 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m51]; exact w50_24
  have w51_28 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m51]; exact w50_28
  have w51_2c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m51]; exact w50_2c
  have w51_30 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m51]; exact w50_30
  have w51_34 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m51]; exact w50_34
  have w51_38 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m51]; exact w50_38
  have w51_3c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m51]; exact w50_3c
  have w51_40 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m51]; exact w50_40
  have w51_44 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m51]; exact w50_44
  have w51_48 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m51]; exact w50_48
  have w51_4c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m51]; exact w50_4c
  have w51_50 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m51]; exact w50_50
  have w51_54 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m51]; exact w50_54
  have w51_58 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m51]; exact w50_58
  have w51_5c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m51]; exact w50_5c
  have w51_60 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m51]; exact w50_60
  have w51_64 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m51]; exact w50_64
  have w51_68 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m51]; exact w50_68
  have w51_6c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m51]; exact w50_6c
  have w51_70 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m51]; exact w50_70
  have w51_78 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m51]; exact w50_78
  have w51_7c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m51]; exact w50_7c
  have w51_80 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m51]; exact w50_80
  have w51_84 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m51]; exact w50_84
  have w51_88 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m51]; exact w50_88
  have w51_8c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m51]; exact w50_8c
  have w51_90 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m51]; exact w50_90
  have w51_94 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m51]; exact w50_94
  have w51_98 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m51]; exact w50_98
  have w51_9c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m51]; exact w50_9c
  have w51_a0 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m51]; exact w50_a0
  have w51_a4 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m51]; exact w50_a4
  have w51_a8 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m51]; exact w50_a8
  have w51_ac : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m51]; exact w50_ac
  have w51_b0 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m51]; exact w50_b0
  have w51_b4 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m51]; exact w50_b4
  have w51_b8 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m51]; exact w50_b8
  have w51_bc : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m51]; exact w50_bc
  have w51_c0 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m51]; exact w50_c0
  have w51_c4 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m51]; exact w50_c4
  have w51_c8 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m51]; exact w50_c8
  have w51_cc : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m51]; exact w50_cc
  have w51_d0 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m51]; exact w50_d0
  have w51_d4 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m51]; exact w50_d4
  have w51_d8 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m51]; exact w50_d8
  have w51_dc : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m51]; exact w50_dc
  have w51_e0 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m51]; exact w50_e0
  have w51_e4 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m51]; exact w50_e4
  have w51_e8 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m51]; exact w50_e8
  have w51_ec : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m51]; exact w50_ec
  have w51_f0 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m51]; exact w50_f0
  have w51_f4 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m51]; exact w50_f4
  have w51_f8 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m51]; exact w50_f8
  have w51_fc : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m51]; exact w50_fc
  have w51_100 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m51]; exact w50_100
  have w51_104 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m51]; exact w50_104
  have w51_108 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m51]; exact w50_108
  have w51_10c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m51]; exact w50_10c
  have w51_110 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m51]; exact w50_110
  have w51_114 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m51]; exact w50_114
  have w51_118 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m51]; exact w50_118
  have w51_11c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m51]; exact w50_11c
  have w51_120 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m51]; exact w50_120
  have w51_124 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m51]; exact w50_124
  have w51_128 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m51]; exact w50_128
  have w51_12c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m51]; exact w50_12c
  have w51_130 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m51]; exact w50_130
  have w51_a20 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m51]; exact w50_a20
  have w51_b28 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xB28) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by rw [m51]; exact w50_b28
  have w51_1020 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by rw [m51]; exact w50_1020
  have w51_1480 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by rw [m51]; exact w50_1480
  have a51_2a0 : accV n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m51]; exact a50_2a0
  have a51_2c0 : accV n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m51]; exact a50_2c0
  have a51_2e0 : accV n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m51]; exact a50_2e0
  have a51_380 : accV n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m51]; exact a50_380
  have a51_400 : accV n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m51]; exact a50_400
  have a51_13e0 : accV n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := by rw [m51]; exact a50_13e0
  have a51_1460 : accV n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := by rw [m51]; exact a50_1460
  have a51_1588 : accV n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U2 := by rw [m51]; exact a50_1588
  have p51_320 : ptF n51.mem B 0x320 = P0 := by rw [m51]; exact p50_320
  have p51_3a0 : ptF n51.mem B 0x3A0 = P1 := by rw [m51]; exact p50_3a0
  have p51_420 : ptF n51.mem B 0x420 = tbl2 P0 0 := by rw [m51]; exact p50_420
  have p51_480 : ptF n51.mem B 0x480 = tbl2 P0 1 := by rw [m51]; exact p50_480
  have p51_4e0 : ptF n51.mem B 0x4E0 = tbl2 P0 2 := by rw [m51]; exact p50_4e0
  have p51_540 : ptF n51.mem B 0x540 = tbl2 P0 3 := by rw [m51]; exact p50_540
  have p51_5a0 : ptF n51.mem B 0x5A0 = tbl2 P0 4 := by rw [m51]; exact p50_5a0
  have p51_600 : ptF n51.mem B 0x600 = tbl2 P0 5 := by rw [m51]; exact p50_600
  have p51_660 : ptF n51.mem B 0x660 = tbl2 P0 6 := by rw [m51]; exact p50_660
  have p51_6c0 : ptF n51.mem B 0x6C0 = tbl2 P0 7 := by rw [m51]; exact p50_6c0
  have p51_720 : ptF n51.mem B 0x720 = tbl2 P1 0 := by rw [m51]; exact p50_720
  have p51_780 : ptF n51.mem B 0x780 = tbl2 P1 1 := by rw [m51]; exact p50_780
  have p51_7e0 : ptF n51.mem B 0x7E0 = tbl2 P1 2 := by rw [m51]; exact p50_7e0
  have p51_840 : ptF n51.mem B 0x840 = tbl2 P1 3 := by rw [m51]; exact p50_840
  have p51_8a0 : ptF n51.mem B 0x8A0 = tbl2 P1 4 := by rw [m51]; exact p50_8a0
  have p51_900 : ptF n51.mem B 0x900 = tbl2 P1 5 := by rw [m51]; exact p50_900
  have p51_960 : ptF n51.mem B 0x960 = tbl2 P1 6 := by rw [m51]; exact p50_960
  have p51_9c0 : ptF n51.mem B 0x9C0 = tbl2 P1 7 := by rw [m51]; exact p50_9c0
  have p51_c60 : ptF n51.mem B 0xC60 = tbl2 P0 6 := by rw [m51]; exact p50_c60
  have p51_cc0 : ptF n51.mem B 0xCC0 = tbl2 P0 7 := by rw [m51]; exact p50_cc0
  have p51_d20 : ptF n51.mem B 0xD20 = tbl2 P1 0 := by rw [m51]; exact p50_d20
  have p51_d80 : ptF n51.mem B 0xD80 = tbl2 P1 1 := by rw [m51]; exact p50_d80
  have p51_de0 : ptF n51.mem B 0xDE0 = tbl2 P1 2 := by rw [m51]; exact p50_de0
  have p51_e40 : ptF n51.mem B 0xE40 = tbl2 P1 3 := by rw [m51]; exact p50_e40
  have p51_ea0 : ptF n51.mem B 0xEA0 = tbl2 P1 4 := by rw [m51]; exact p50_ea0
  have p51_f00 : ptF n51.mem B 0xF00 = tbl2 P1 5 := by rw [m51]; exact p50_f00
  have p51_f60 : ptF n51.mem B 0xF60 = tbl2 P1 6 := by rw [m51]; exact p50_f60
  have p51_fc0 : ptF n51.mem B 0xFC0 = tbl2 P1 7 := by rw [m51]; exact p50_fc0
  have p51_1380 : ptF n51.mem B 0x1380 = P0 := by rw [m51]; exact p50_1380
  have p51_1400 : ptF n51.mem B 0x1400 = P1 := by rw [m51]; exact p50_1400
  have mb51_a24 : memBytes n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m51]; exact mb50_a24
  have mb51_b2c : memBytes n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xB2C) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [m51]; exact mb50_b2c
  have mb51_1024 : memBytes n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [m51]; exact mb50_1024
  have mb51_1320 : leN (memBytes n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U2 := by rw [m51]; exact mb50_1320
  have mb51_1484 : memBytes n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [m51]; exact mb50_1484
  clear mb50_1484 mb50_1320 mb50_1024 mb50_b2c mb50_a24 p50_1400 p50_1380 p50_fc0 p50_f60 p50_f00 p50_ea0 p50_e40 p50_de0 p50_d80 p50_d20 p50_cc0 p50_c60 p50_9c0 p50_960 p50_900 p50_8a0 p50_840 p50_7e0 p50_780 p50_720 p50_6c0 p50_660 p50_600 p50_5a0 p50_540 p50_4e0 p50_480 p50_420 p50_3a0 p50_320 a50_1588 a50_1460 a50_13e0 a50_400 a50_380 a50_2e0 a50_2c0 a50_2a0 w50_1480 w50_1020 w50_b28 w50_a20 w50_130 w50_12c w50_128 w50_124 w50_120 w50_11c w50_118 w50_114 w50_110 w50_10c w50_108 w50_104 w50_100 w50_fc w50_f8 w50_f4 w50_f0 w50_ec w50_e8 w50_e4 w50_e0 w50_dc w50_d8 w50_d4 w50_d0 w50_cc w50_c8 w50_c4 w50_c0 w50_bc w50_b8 w50_b4 w50_b0 w50_ac w50_a8 w50_a4 w50_a0 w50_9c w50_98 w50_94 w50_90 w50_8c w50_88 w50_84 w50_80 w50_7c w50_78 w50_70 w50_6c w50_68 w50_64 w50_60 w50_5c w50_58 w50_54 w50_50 w50_4c w50_48 w50_44 w50_40 w50_3c w50_38 w50_34 w50_30 w50_2c w50_28 w50_24 g50_27 g50_26 g50_25 g50_24 g50_23 g50_22 g50_21 g50_20 g50_19 g50_18 g50_9 g50_8 g50_4 g50_3 g50_2 V50 E50 fR50 t50 fr50 m50 s50 u50 d50
  -- 0x18E8: memcpy
  obtain ⟨n52, P52, K52, X52⟩ := sv_mc (c := 0x1020) (d := 0xA20) (N := 0x210) F E51 s51 sv_at_18e8 sv_at_18ec
    (by decide) (by decide) g51_2 g51_10 g51_11 g51_12
    (by decide) (by decide) (by decide)
  have s52 := P52.st
  have fr52 := P52.fr
  have t52 : Steps n0 n52 := t51.trans P52.steps
  have fR52 : ∀ x, SvR B x → n52.mem x = M0 x := fun x hx => (fr52 x hx).trans (fR51 x hx)
  have E52 : SvCode n52.mem := E51.fr F fr52
  have V52 : SvSaves B n52.mem v := V51.keep K52 (by decide)
  have g52_2 : reg n52 sp = B + 0x21A0 := by rw [P52.regs sp (by decide), g51_2]
  have g52_3 : reg n52 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P52.regs (3 : Fin 32) (by decide), g51_3]
  have g52_4 : reg n52 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P52.regs (4 : Fin 32) (by decide), g51_4]
  have g52_8 : reg n52 (8 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P52.regs (8 : Fin 32) (by decide), g51_8]
  have g52_9 : reg n52 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by rw [P52.regs (9 : Fin 32) (by decide), g51_9]
  have g52_18 : reg n52 (18 : Fin 32) = out := by rw [P52.regs (18 : Fin 32) (by decide), g51_18]
  have g52_19 : reg n52 (19 : Fin 32) = bp := by rw [P52.regs (19 : Fin 32) (by decide), g51_19]
  have g52_20 : reg n52 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P52.regs (20 : Fin 32) (by decide), g51_20]
  have g52_21 : reg n52 (21 : Fin 32) = s5v := by rw [P52.regs (21 : Fin 32) (by decide), g51_21]
  have g52_22 : reg n52 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [P52.regs (22 : Fin 32) (by decide), g51_22]
  have g52_23 : reg n52 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by rw [P52.regs (23 : Fin 32) (by decide), g51_23]
  have g52_24 : reg n52 (24 : Fin 32) = s8v := by rw [P52.regs (24 : Fin 32) (by decide), g51_24]
  have g52_25 : reg n52 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [P52.regs (25 : Fin 32) (by decide), g51_25]
  have g52_26 : reg n52 (26 : Fin 32) = x26 := by rw [P52.regs (26 : Fin 32) (by decide), g51_26]
  have g52_27 : reg n52 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P52.regs (27 : Fin 32) (by decide), g51_27]
  have w52_24 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K52.w32 (by decide) (by decide)).trans w51_24
  have w52_28 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K52.w32 (by decide) (by decide)).trans w51_28
  have w52_2c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K52.w32 (by decide) (by decide)).trans w51_2c
  have w52_30 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K52.w32 (by decide) (by decide)).trans w51_30
  have w52_34 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K52.w32 (by decide) (by decide)).trans w51_34
  have w52_38 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K52.w32 (by decide) (by decide)).trans w51_38
  have w52_3c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K52.w32 (by decide) (by decide)).trans w51_3c
  have w52_40 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K52.w32 (by decide) (by decide)).trans w51_40
  have w52_44 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K52.w32 (by decide) (by decide)).trans w51_44
  have w52_48 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K52.w32 (by decide) (by decide)).trans w51_48
  have w52_4c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K52.w32 (by decide) (by decide)).trans w51_4c
  have w52_50 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K52.w32 (by decide) (by decide)).trans w51_50
  have w52_54 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K52.w32 (by decide) (by decide)).trans w51_54
  have w52_58 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K52.w32 (by decide) (by decide)).trans w51_58
  have w52_5c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K52.w32 (by decide) (by decide)).trans w51_5c
  have w52_60 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K52.w32 (by decide) (by decide)).trans w51_60
  have w52_64 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K52.w32 (by decide) (by decide)).trans w51_64
  have w52_68 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K52.w32 (by decide) (by decide)).trans w51_68
  have w52_6c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K52.w32 (by decide) (by decide)).trans w51_6c
  have w52_70 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K52.w32 (by decide) (by decide)).trans w51_70
  have w52_78 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := (K52.w32 (by decide) (by decide)).trans w51_78
  have w52_7c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K52.w32 (by decide) (by decide)).trans w51_7c
  have w52_80 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K52.w32 (by decide) (by decide)).trans w51_80
  have w52_84 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K52.w32 (by decide) (by decide)).trans w51_84
  have w52_88 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K52.w32 (by decide) (by decide)).trans w51_88
  have w52_8c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K52.w32 (by decide) (by decide)).trans w51_8c
  have w52_90 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K52.w32 (by decide) (by decide)).trans w51_90
  have w52_94 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K52.w32 (by decide) (by decide)).trans w51_94
  have w52_98 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K52.w32 (by decide) (by decide)).trans w51_98
  have w52_9c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K52.w32 (by decide) (by decide)).trans w51_9c
  have w52_a0 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K52.w32 (by decide) (by decide)).trans w51_a0
  have w52_a4 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K52.w32 (by decide) (by decide)).trans w51_a4
  have w52_a8 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K52.w32 (by decide) (by decide)).trans w51_a8
  have w52_ac : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K52.w32 (by decide) (by decide)).trans w51_ac
  have w52_b0 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K52.w32 (by decide) (by decide)).trans w51_b0
  have w52_b4 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K52.w32 (by decide) (by decide)).trans w51_b4
  have w52_b8 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K52.w32 (by decide) (by decide)).trans w51_b8
  have w52_bc : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K52.w32 (by decide) (by decide)).trans w51_bc
  have w52_c0 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K52.w32 (by decide) (by decide)).trans w51_c0
  have w52_c4 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K52.w32 (by decide) (by decide)).trans w51_c4
  have w52_c8 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K52.w32 (by decide) (by decide)).trans w51_c8
  have w52_cc : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K52.w32 (by decide) (by decide)).trans w51_cc
  have w52_d0 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K52.w32 (by decide) (by decide)).trans w51_d0
  have w52_d4 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K52.w32 (by decide) (by decide)).trans w51_d4
  have w52_d8 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K52.w32 (by decide) (by decide)).trans w51_d8
  have w52_dc : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K52.w32 (by decide) (by decide)).trans w51_dc
  have w52_e0 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K52.w32 (by decide) (by decide)).trans w51_e0
  have w52_e4 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K52.w32 (by decide) (by decide)).trans w51_e4
  have w52_e8 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K52.w32 (by decide) (by decide)).trans w51_e8
  have w52_ec : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K52.w32 (by decide) (by decide)).trans w51_ec
  have w52_f0 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K52.w32 (by decide) (by decide)).trans w51_f0
  have w52_f4 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K52.w32 (by decide) (by decide)).trans w51_f4
  have w52_f8 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K52.w32 (by decide) (by decide)).trans w51_f8
  have w52_fc : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K52.w32 (by decide) (by decide)).trans w51_fc
  have w52_100 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K52.w32 (by decide) (by decide)).trans w51_100
  have w52_104 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K52.w32 (by decide) (by decide)).trans w51_104
  have w52_108 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K52.w32 (by decide) (by decide)).trans w51_108
  have w52_10c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K52.w32 (by decide) (by decide)).trans w51_10c
  have w52_110 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K52.w32 (by decide) (by decide)).trans w51_110
  have w52_114 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K52.w32 (by decide) (by decide)).trans w51_114
  have w52_118 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K52.w32 (by decide) (by decide)).trans w51_118
  have w52_11c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K52.w32 (by decide) (by decide)).trans w51_11c
  have w52_120 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K52.w32 (by decide) (by decide)).trans w51_120
  have w52_124 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K52.w32 (by decide) (by decide)).trans w51_124
  have w52_128 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K52.w32 (by decide) (by decide)).trans w51_128
  have w52_12c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K52.w32 (by decide) (by decide)).trans w51_12c
  have w52_130 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K52.w32 (by decide) (by decide)).trans w51_130
  have w52_a20 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := (K52.w32 (by decide) (by decide)).trans w51_a20
  have w52_b28 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xB28) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := (K52.w32 (by decide) (by decide)).trans w51_b28
  have w52_1480 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := (K52.w32 (by decide) (by decide)).trans w51_1480
  have w52_1020 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by
    rw [← w51_a20]
    exact ld_cp fun q hq => by
      have := X52 (0x0 + q) (by omega)
      rwa [show 0x1020 + (0x0 + q) = 0x1020 + q by omega,
        show 0xA20 + (0x0 + q) = 0xA20 + q by omega] at this
  have w52_1128 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x1128) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by
    rw [← w51_b28]
    exact ld_cp fun q hq => by
      have := X52 (0x108 + q) (by omega)
      rwa [show 0x1020 + (0x108 + q) = 0x1128 + q by omega,
        show 0xA20 + (0x108 + q) = 0xB28 + q by omega] at this
  have a52_2a0 : accV n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K52.acc (by decide) (by decide)).trans a51_2a0
  have a52_2c0 : accV n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K52.acc (by decide) (by decide)).trans a51_2c0
  have a52_2e0 : accV n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K52.acc (by decide) (by decide)).trans a51_2e0
  have a52_380 : accV n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := (K52.acc (by decide) (by decide)).trans a51_380
  have a52_400 : accV n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := (K52.acc (by decide) (by decide)).trans a51_400
  have a52_13e0 : accV n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := (K52.acc (by decide) (by decide)).trans a51_13e0
  have a52_1460 : accV n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := (K52.acc (by decide) (by decide)).trans a51_1460
  have a52_1588 : accV n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U2 := (K52.acc (by decide) (by decide)).trans a51_1588
  have p52_320 : ptF n52.mem B 0x320 = P0 := (K52.pt (by decide) (by decide)).trans p51_320
  have p52_3a0 : ptF n52.mem B 0x3A0 = P1 := (K52.pt (by decide) (by decide)).trans p51_3a0
  have p52_420 : ptF n52.mem B 0x420 = tbl2 P0 0 := (K52.pt (by decide) (by decide)).trans p51_420
  have p52_480 : ptF n52.mem B 0x480 = tbl2 P0 1 := (K52.pt (by decide) (by decide)).trans p51_480
  have p52_4e0 : ptF n52.mem B 0x4E0 = tbl2 P0 2 := (K52.pt (by decide) (by decide)).trans p51_4e0
  have p52_540 : ptF n52.mem B 0x540 = tbl2 P0 3 := (K52.pt (by decide) (by decide)).trans p51_540
  have p52_5a0 : ptF n52.mem B 0x5A0 = tbl2 P0 4 := (K52.pt (by decide) (by decide)).trans p51_5a0
  have p52_600 : ptF n52.mem B 0x600 = tbl2 P0 5 := (K52.pt (by decide) (by decide)).trans p51_600
  have p52_660 : ptF n52.mem B 0x660 = tbl2 P0 6 := (K52.pt (by decide) (by decide)).trans p51_660
  have p52_6c0 : ptF n52.mem B 0x6C0 = tbl2 P0 7 := (K52.pt (by decide) (by decide)).trans p51_6c0
  have p52_720 : ptF n52.mem B 0x720 = tbl2 P1 0 := (K52.pt (by decide) (by decide)).trans p51_720
  have p52_780 : ptF n52.mem B 0x780 = tbl2 P1 1 := (K52.pt (by decide) (by decide)).trans p51_780
  have p52_7e0 : ptF n52.mem B 0x7E0 = tbl2 P1 2 := (K52.pt (by decide) (by decide)).trans p51_7e0
  have p52_840 : ptF n52.mem B 0x840 = tbl2 P1 3 := (K52.pt (by decide) (by decide)).trans p51_840
  have p52_8a0 : ptF n52.mem B 0x8A0 = tbl2 P1 4 := (K52.pt (by decide) (by decide)).trans p51_8a0
  have p52_900 : ptF n52.mem B 0x900 = tbl2 P1 5 := (K52.pt (by decide) (by decide)).trans p51_900
  have p52_960 : ptF n52.mem B 0x960 = tbl2 P1 6 := (K52.pt (by decide) (by decide)).trans p51_960
  have p52_9c0 : ptF n52.mem B 0x9C0 = tbl2 P1 7 := (K52.pt (by decide) (by decide)).trans p51_9c0
  have p52_c60 : ptF n52.mem B 0xC60 = tbl2 P0 6 := (K52.pt (by decide) (by decide)).trans p51_c60
  have p52_cc0 : ptF n52.mem B 0xCC0 = tbl2 P0 7 := (K52.pt (by decide) (by decide)).trans p51_cc0
  have p52_d20 : ptF n52.mem B 0xD20 = tbl2 P1 0 := (K52.pt (by decide) (by decide)).trans p51_d20
  have p52_d80 : ptF n52.mem B 0xD80 = tbl2 P1 1 := (K52.pt (by decide) (by decide)).trans p51_d80
  have p52_de0 : ptF n52.mem B 0xDE0 = tbl2 P1 2 := (K52.pt (by decide) (by decide)).trans p51_de0
  have p52_e40 : ptF n52.mem B 0xE40 = tbl2 P1 3 := (K52.pt (by decide) (by decide)).trans p51_e40
  have p52_ea0 : ptF n52.mem B 0xEA0 = tbl2 P1 4 := (K52.pt (by decide) (by decide)).trans p51_ea0
  have p52_f00 : ptF n52.mem B 0xF00 = tbl2 P1 5 := (K52.pt (by decide) (by decide)).trans p51_f00
  have p52_f60 : ptF n52.mem B 0xF60 = tbl2 P1 6 := (K52.pt (by decide) (by decide)).trans p51_f60
  have p52_fc0 : ptF n52.mem B 0xFC0 = tbl2 P1 7 := (K52.pt (by decide) (by decide)).trans p51_fc0
  have p52_1380 : ptF n52.mem B 0x1380 = P0 := (K52.pt (by decide) (by decide)).trans p51_1380
  have p52_1400 : ptF n52.mem B 0x1400 = P1 := (K52.pt (by decide) (by decide)).trans p51_1400
  have mb52_a24 : memBytes n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [K52.mb (by decide) (by decide)]; exact mb51_a24
  have mb52_b2c : memBytes n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xB2C) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [K52.mb (by decide) (by decide)]; exact mb51_b2c
  have mb52_1320 : leN (memBytes n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U2 := by rw [K52.mb (by decide) (by decide)]; exact mb51_1320
  have mb52_1484 : memBytes n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [K52.mb (by decide) (by decide)]; exact mb51_1484
  have mb52_1024 : memBytes n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by
    rw [memBytes_cp (S := B + 0x21A0) (c := 0x1024) (d := 0xA24) (N := 0x101) fun q hq => by
      rw [show 0x1024 + q = 0x1020 + (0x4 + q) by omega, X52 (0x4 + q) (by omega),
        show 0xA20 + (0x4 + q) = 0xA24 + q by omega]]; exact mb51_a24
  have mb52_112c : memBytes n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x112C) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by
    rw [memBytes_cp (S := B + 0x21A0) (c := 0x112C) (d := 0xB2C) (N := 0x101) fun q hq => by
      rw [show 0x112C + q = 0x1020 + (0x10C + q) by omega, X52 (0x10C + q) (by omega),
        show 0xA20 + (0x10C + q) = 0xB2C + q by omega]]; exact mb51_b2c
  clear mb51_1484 mb51_1320 mb51_1024 mb51_b2c mb51_a24 p51_1400 p51_1380 p51_fc0 p51_f60 p51_f00 p51_ea0 p51_e40 p51_de0 p51_d80 p51_d20 p51_cc0 p51_c60 p51_9c0 p51_960 p51_900 p51_8a0 p51_840 p51_7e0 p51_780 p51_720 p51_6c0 p51_660 p51_600 p51_5a0 p51_540 p51_4e0 p51_480 p51_420 p51_3a0 p51_320 a51_1588 a51_1460 a51_13e0 a51_400 a51_380 a51_2e0 a51_2c0 a51_2a0 w51_1480 w51_1020 w51_b28 w51_a20 w51_130 w51_12c w51_128 w51_124 w51_120 w51_11c w51_118 w51_114 w51_110 w51_10c w51_108 w51_104 w51_100 w51_fc w51_f8 w51_f4 w51_f0 w51_ec w51_e8 w51_e4 w51_e0 w51_dc w51_d8 w51_d4 w51_d0 w51_cc w51_c8 w51_c4 w51_c0 w51_bc w51_b8 w51_b4 w51_b0 w51_ac w51_a8 w51_a4 w51_a0 w51_9c w51_98 w51_94 w51_90 w51_8c w51_88 w51_84 w51_80 w51_7c w51_78 w51_70 w51_6c w51_68 w51_64 w51_60 w51_5c w51_58 w51_54 w51_50 w51_4c w51_48 w51_44 w51_40 w51_3c w51_38 w51_34 w51_30 w51_2c w51_28 w51_24 g51_12 g51_11 g51_10 g51_27 g51_26 g51_25 g51_24 g51_23 g51_22 g51_21 g51_20 g51_19 g51_18 g51_9 g51_8 g51_4 g51_3 g51_2 V51 E51 fR51 t51 fr51 rb51 s51 m51 u51 c51
  -- 0x18F0: lw
  obtain ⟨n53, d53, u53⟩ := s52.lw E52.self sv_at_18f0 (off' := 0x18F4) (by decide)
    (by rw [g52_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x600 = B + 0x21A0 + BitVec.ofNat 32 0x1020 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s53 : St n53.mem SV n53 0x18F4 (reg n53) := ⟨u53.pc, rfl, fun _ => rfl⟩
  have m53 : n53.mem = n52.mem := u53.mem
  have fr53 : ∀ x, SvR B x → n53.mem x = n52.mem x := fun x _ => by rw [m53]
  have t53 : Steps n0 n53 := t52.trans (.single d53)
  have fR53 : ∀ x, SvR B x → n53.mem x = M0 x := fun x hx => (fr53 x hx).trans (fR52 x hx)
  have E53 : SvCode n53.mem := E52.fr F fr53
  have V53 : SvSaves B n53.mem v := V52.same m53
  have g53_2 : reg n53 sp = B + 0x21A0 := by rw [u53.regs, upd_ne (by decide) (by decide), g52_2]
  have g53_3 : reg n53 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u53.regs, upd_ne (by decide) (by decide), g52_3]
  have g53_4 : reg n53 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u53.regs, upd_ne (by decide) (by decide), g52_4]
  have g53_8 : reg n53 (8 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u53.regs, upd_ne (by decide) (by decide), g52_8]
  have g53_18 : reg n53 (18 : Fin 32) = out := by rw [u53.regs, upd_ne (by decide) (by decide), g52_18]
  have g53_19 : reg n53 (19 : Fin 32) = bp := by rw [u53.regs, upd_ne (by decide) (by decide), g52_19]
  have g53_20 : reg n53 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u53.regs, upd_ne (by decide) (by decide), g52_20]
  have g53_21 : reg n53 (21 : Fin 32) = s5v := by rw [u53.regs, upd_ne (by decide) (by decide), g52_21]
  have g53_22 : reg n53 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [u53.regs, upd_ne (by decide) (by decide), g52_22]
  have g53_23 : reg n53 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by rw [u53.regs, upd_ne (by decide) (by decide), g52_23]
  have g53_24 : reg n53 (24 : Fin 32) = s8v := by rw [u53.regs, upd_ne (by decide) (by decide), g52_24]
  have g53_25 : reg n53 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u53.regs, upd_ne (by decide) (by decide), g52_25]
  have g53_26 : reg n53 (26 : Fin 32) = x26 := by rw [u53.regs, upd_ne (by decide) (by decide), g52_26]
  have g53_27 : reg n53 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u53.regs, upd_ne (by decide) (by decide), g52_27]
  have g53_9 : reg n53 (9 : Fin 32) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by
    rw [u53.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g52_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x600 = B + 0x21A0 + BitVec.ofNat 32 0x1020 by sv_addr, w52_1020]
  have w53_24 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m53]; exact w52_24
  have w53_28 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m53]; exact w52_28
  have w53_2c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m53]; exact w52_2c
  have w53_30 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m53]; exact w52_30
  have w53_34 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m53]; exact w52_34
  have w53_38 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m53]; exact w52_38
  have w53_3c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m53]; exact w52_3c
  have w53_40 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m53]; exact w52_40
  have w53_44 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m53]; exact w52_44
  have w53_48 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m53]; exact w52_48
  have w53_4c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m53]; exact w52_4c
  have w53_50 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m53]; exact w52_50
  have w53_54 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m53]; exact w52_54
  have w53_58 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m53]; exact w52_58
  have w53_5c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m53]; exact w52_5c
  have w53_60 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m53]; exact w52_60
  have w53_64 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m53]; exact w52_64
  have w53_68 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m53]; exact w52_68
  have w53_6c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m53]; exact w52_6c
  have w53_70 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m53]; exact w52_70
  have w53_78 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m53]; exact w52_78
  have w53_7c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m53]; exact w52_7c
  have w53_80 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m53]; exact w52_80
  have w53_84 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m53]; exact w52_84
  have w53_88 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m53]; exact w52_88
  have w53_8c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m53]; exact w52_8c
  have w53_90 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m53]; exact w52_90
  have w53_94 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m53]; exact w52_94
  have w53_98 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m53]; exact w52_98
  have w53_9c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m53]; exact w52_9c
  have w53_a0 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m53]; exact w52_a0
  have w53_a4 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m53]; exact w52_a4
  have w53_a8 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m53]; exact w52_a8
  have w53_ac : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m53]; exact w52_ac
  have w53_b0 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m53]; exact w52_b0
  have w53_b4 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m53]; exact w52_b4
  have w53_b8 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m53]; exact w52_b8
  have w53_bc : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m53]; exact w52_bc
  have w53_c0 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m53]; exact w52_c0
  have w53_c4 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m53]; exact w52_c4
  have w53_c8 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m53]; exact w52_c8
  have w53_cc : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m53]; exact w52_cc
  have w53_d0 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m53]; exact w52_d0
  have w53_d4 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m53]; exact w52_d4
  have w53_d8 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m53]; exact w52_d8
  have w53_dc : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m53]; exact w52_dc
  have w53_e0 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m53]; exact w52_e0
  have w53_e4 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m53]; exact w52_e4
  have w53_e8 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m53]; exact w52_e8
  have w53_ec : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m53]; exact w52_ec
  have w53_f0 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m53]; exact w52_f0
  have w53_f4 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m53]; exact w52_f4
  have w53_f8 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m53]; exact w52_f8
  have w53_fc : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m53]; exact w52_fc
  have w53_100 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m53]; exact w52_100
  have w53_104 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m53]; exact w52_104
  have w53_108 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m53]; exact w52_108
  have w53_10c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m53]; exact w52_10c
  have w53_110 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m53]; exact w52_110
  have w53_114 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m53]; exact w52_114
  have w53_118 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m53]; exact w52_118
  have w53_11c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m53]; exact w52_11c
  have w53_120 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m53]; exact w52_120
  have w53_124 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m53]; exact w52_124
  have w53_128 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m53]; exact w52_128
  have w53_12c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m53]; exact w52_12c
  have w53_130 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m53]; exact w52_130
  have w53_a20 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m53]; exact w52_a20
  have w53_b28 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xB28) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by rw [m53]; exact w52_b28
  have w53_1020 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m53]; exact w52_1020
  have w53_1128 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x1128) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by rw [m53]; exact w52_1128
  have w53_1480 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by rw [m53]; exact w52_1480
  have a53_2a0 : accV n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m53]; exact a52_2a0
  have a53_2c0 : accV n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m53]; exact a52_2c0
  have a53_2e0 : accV n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m53]; exact a52_2e0
  have a53_380 : accV n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m53]; exact a52_380
  have a53_400 : accV n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m53]; exact a52_400
  have a53_13e0 : accV n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := by rw [m53]; exact a52_13e0
  have a53_1460 : accV n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := by rw [m53]; exact a52_1460
  have a53_1588 : accV n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U2 := by rw [m53]; exact a52_1588
  have p53_320 : ptF n53.mem B 0x320 = P0 := by rw [m53]; exact p52_320
  have p53_3a0 : ptF n53.mem B 0x3A0 = P1 := by rw [m53]; exact p52_3a0
  have p53_420 : ptF n53.mem B 0x420 = tbl2 P0 0 := by rw [m53]; exact p52_420
  have p53_480 : ptF n53.mem B 0x480 = tbl2 P0 1 := by rw [m53]; exact p52_480
  have p53_4e0 : ptF n53.mem B 0x4E0 = tbl2 P0 2 := by rw [m53]; exact p52_4e0
  have p53_540 : ptF n53.mem B 0x540 = tbl2 P0 3 := by rw [m53]; exact p52_540
  have p53_5a0 : ptF n53.mem B 0x5A0 = tbl2 P0 4 := by rw [m53]; exact p52_5a0
  have p53_600 : ptF n53.mem B 0x600 = tbl2 P0 5 := by rw [m53]; exact p52_600
  have p53_660 : ptF n53.mem B 0x660 = tbl2 P0 6 := by rw [m53]; exact p52_660
  have p53_6c0 : ptF n53.mem B 0x6C0 = tbl2 P0 7 := by rw [m53]; exact p52_6c0
  have p53_720 : ptF n53.mem B 0x720 = tbl2 P1 0 := by rw [m53]; exact p52_720
  have p53_780 : ptF n53.mem B 0x780 = tbl2 P1 1 := by rw [m53]; exact p52_780
  have p53_7e0 : ptF n53.mem B 0x7E0 = tbl2 P1 2 := by rw [m53]; exact p52_7e0
  have p53_840 : ptF n53.mem B 0x840 = tbl2 P1 3 := by rw [m53]; exact p52_840
  have p53_8a0 : ptF n53.mem B 0x8A0 = tbl2 P1 4 := by rw [m53]; exact p52_8a0
  have p53_900 : ptF n53.mem B 0x900 = tbl2 P1 5 := by rw [m53]; exact p52_900
  have p53_960 : ptF n53.mem B 0x960 = tbl2 P1 6 := by rw [m53]; exact p52_960
  have p53_9c0 : ptF n53.mem B 0x9C0 = tbl2 P1 7 := by rw [m53]; exact p52_9c0
  have p53_c60 : ptF n53.mem B 0xC60 = tbl2 P0 6 := by rw [m53]; exact p52_c60
  have p53_cc0 : ptF n53.mem B 0xCC0 = tbl2 P0 7 := by rw [m53]; exact p52_cc0
  have p53_d20 : ptF n53.mem B 0xD20 = tbl2 P1 0 := by rw [m53]; exact p52_d20
  have p53_d80 : ptF n53.mem B 0xD80 = tbl2 P1 1 := by rw [m53]; exact p52_d80
  have p53_de0 : ptF n53.mem B 0xDE0 = tbl2 P1 2 := by rw [m53]; exact p52_de0
  have p53_e40 : ptF n53.mem B 0xE40 = tbl2 P1 3 := by rw [m53]; exact p52_e40
  have p53_ea0 : ptF n53.mem B 0xEA0 = tbl2 P1 4 := by rw [m53]; exact p52_ea0
  have p53_f00 : ptF n53.mem B 0xF00 = tbl2 P1 5 := by rw [m53]; exact p52_f00
  have p53_f60 : ptF n53.mem B 0xF60 = tbl2 P1 6 := by rw [m53]; exact p52_f60
  have p53_fc0 : ptF n53.mem B 0xFC0 = tbl2 P1 7 := by rw [m53]; exact p52_fc0
  have p53_1380 : ptF n53.mem B 0x1380 = P0 := by rw [m53]; exact p52_1380
  have p53_1400 : ptF n53.mem B 0x1400 = P1 := by rw [m53]; exact p52_1400
  have mb53_a24 : memBytes n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m53]; exact mb52_a24
  have mb53_b2c : memBytes n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xB2C) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [m53]; exact mb52_b2c
  have mb53_1024 : memBytes n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m53]; exact mb52_1024
  have mb53_112c : memBytes n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x112C) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [m53]; exact mb52_112c
  have mb53_1320 : leN (memBytes n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U2 := by rw [m53]; exact mb52_1320
  have mb53_1484 : memBytes n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [m53]; exact mb52_1484
  clear mb52_112c mb52_1024 mb52_1484 mb52_1320 mb52_b2c mb52_a24 p52_1400 p52_1380 p52_fc0 p52_f60 p52_f00 p52_ea0 p52_e40 p52_de0 p52_d80 p52_d20 p52_cc0 p52_c60 p52_9c0 p52_960 p52_900 p52_8a0 p52_840 p52_7e0 p52_780 p52_720 p52_6c0 p52_660 p52_600 p52_5a0 p52_540 p52_4e0 p52_480 p52_420 p52_3a0 p52_320 a52_1588 a52_1460 a52_13e0 a52_400 a52_380 a52_2e0 a52_2c0 a52_2a0 w52_1128 w52_1020 w52_1480 w52_b28 w52_a20 w52_130 w52_12c w52_128 w52_124 w52_120 w52_11c w52_118 w52_114 w52_110 w52_10c w52_108 w52_104 w52_100 w52_fc w52_f8 w52_f4 w52_f0 w52_ec w52_e8 w52_e4 w52_e0 w52_dc w52_d8 w52_d4 w52_d0 w52_cc w52_c8 w52_c4 w52_c0 w52_bc w52_b8 w52_b4 w52_b0 w52_ac w52_a8 w52_a4 w52_a0 w52_9c w52_98 w52_94 w52_90 w52_8c w52_88 w52_84 w52_80 w52_7c w52_78 w52_70 w52_6c w52_68 w52_64 w52_60 w52_5c w52_58 w52_54 w52_50 w52_4c w52_48 w52_44 w52_40 w52_3c w52_38 w52_34 w52_30 w52_2c w52_28 w52_24 g52_27 g52_26 g52_25 g52_24 g52_23 g52_22 g52_21 g52_20 g52_19 g52_18 g52_9 g52_8 g52_4 g52_3 g52_2 V52 E52 fR52 t52 fr52 s52 X52 K52 P52
  -- 0x18F4: lw
  obtain ⟨n54, d54, u54⟩ := s53.lw E53.self sv_at_18f4 (off' := 0x18F8) (by decide)
    (by rw [g53_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x708 = B + 0x21A0 + BitVec.ofNat 32 0x1128 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s54 : St n54.mem SV n54 0x18F8 (reg n54) := ⟨u54.pc, rfl, fun _ => rfl⟩
  have m54 : n54.mem = n53.mem := u54.mem
  have fr54 : ∀ x, SvR B x → n54.mem x = n53.mem x := fun x _ => by rw [m54]
  have t54 : Steps n0 n54 := t53.trans (.single d54)
  have fR54 : ∀ x, SvR B x → n54.mem x = M0 x := fun x hx => (fr54 x hx).trans (fR53 x hx)
  have E54 : SvCode n54.mem := E53.fr F fr54
  have V54 : SvSaves B n54.mem v := V53.same m54
  have g54_2 : reg n54 sp = B + 0x21A0 := by rw [u54.regs, upd_ne (by decide) (by decide), g53_2]
  have g54_3 : reg n54 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u54.regs, upd_ne (by decide) (by decide), g53_3]
  have g54_4 : reg n54 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u54.regs, upd_ne (by decide) (by decide), g53_4]
  have g54_8 : reg n54 (8 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u54.regs, upd_ne (by decide) (by decide), g53_8]
  have g54_9 : reg n54 (9 : Fin 32) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [u54.regs, upd_ne (by decide) (by decide), g53_9]
  have g54_18 : reg n54 (18 : Fin 32) = out := by rw [u54.regs, upd_ne (by decide) (by decide), g53_18]
  have g54_19 : reg n54 (19 : Fin 32) = bp := by rw [u54.regs, upd_ne (by decide) (by decide), g53_19]
  have g54_20 : reg n54 (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u54.regs, upd_ne (by decide) (by decide), g53_20]
  have g54_21 : reg n54 (21 : Fin 32) = s5v := by rw [u54.regs, upd_ne (by decide) (by decide), g53_21]
  have g54_22 : reg n54 (22 : Fin 32) = BitVec.ofNat 32 0x108 := by rw [u54.regs, upd_ne (by decide) (by decide), g53_22]
  have g54_23 : reg n54 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1024 := by rw [u54.regs, upd_ne (by decide) (by decide), g53_23]
  have g54_24 : reg n54 (24 : Fin 32) = s8v := by rw [u54.regs, upd_ne (by decide) (by decide), g53_24]
  have g54_25 : reg n54 (25 : Fin 32) = BitVec.ofNat 32 0x2 := by rw [u54.regs, upd_ne (by decide) (by decide), g53_25]
  have g54_26 : reg n54 (26 : Fin 32) = x26 := by rw [u54.regs, upd_ne (by decide) (by decide), g53_26]
  have g54_27 : reg n54 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u54.regs, upd_ne (by decide) (by decide), g53_27]
  have g54_10 : reg n54 a0 = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by
    rw [u54.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g53_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x708 = B + 0x21A0 + BitVec.ofNat 32 0x1128 by sv_addr, w53_1128]
  have w54_24 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m54]; exact w53_24
  have w54_28 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m54]; exact w53_28
  have w54_2c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m54]; exact w53_2c
  have w54_30 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m54]; exact w53_30
  have w54_34 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m54]; exact w53_34
  have w54_38 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m54]; exact w53_38
  have w54_3c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m54]; exact w53_3c
  have w54_40 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m54]; exact w53_40
  have w54_44 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m54]; exact w53_44
  have w54_48 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m54]; exact w53_48
  have w54_4c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m54]; exact w53_4c
  have w54_50 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m54]; exact w53_50
  have w54_54 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m54]; exact w53_54
  have w54_58 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m54]; exact w53_58
  have w54_5c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m54]; exact w53_5c
  have w54_60 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m54]; exact w53_60
  have w54_64 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m54]; exact w53_64
  have w54_68 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m54]; exact w53_68
  have w54_6c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m54]; exact w53_6c
  have w54_70 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m54]; exact w53_70
  have w54_78 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m54]; exact w53_78
  have w54_7c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m54]; exact w53_7c
  have w54_80 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m54]; exact w53_80
  have w54_84 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m54]; exact w53_84
  have w54_88 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m54]; exact w53_88
  have w54_8c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m54]; exact w53_8c
  have w54_90 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m54]; exact w53_90
  have w54_94 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m54]; exact w53_94
  have w54_98 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m54]; exact w53_98
  have w54_9c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m54]; exact w53_9c
  have w54_a0 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m54]; exact w53_a0
  have w54_a4 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m54]; exact w53_a4
  have w54_a8 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m54]; exact w53_a8
  have w54_ac : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m54]; exact w53_ac
  have w54_b0 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m54]; exact w53_b0
  have w54_b4 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m54]; exact w53_b4
  have w54_b8 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m54]; exact w53_b8
  have w54_bc : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m54]; exact w53_bc
  have w54_c0 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m54]; exact w53_c0
  have w54_c4 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m54]; exact w53_c4
  have w54_c8 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m54]; exact w53_c8
  have w54_cc : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m54]; exact w53_cc
  have w54_d0 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m54]; exact w53_d0
  have w54_d4 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m54]; exact w53_d4
  have w54_d8 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m54]; exact w53_d8
  have w54_dc : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m54]; exact w53_dc
  have w54_e0 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m54]; exact w53_e0
  have w54_e4 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m54]; exact w53_e4
  have w54_e8 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m54]; exact w53_e8
  have w54_ec : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m54]; exact w53_ec
  have w54_f0 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m54]; exact w53_f0
  have w54_f4 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m54]; exact w53_f4
  have w54_f8 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m54]; exact w53_f8
  have w54_fc : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m54]; exact w53_fc
  have w54_100 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m54]; exact w53_100
  have w54_104 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m54]; exact w53_104
  have w54_108 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m54]; exact w53_108
  have w54_10c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m54]; exact w53_10c
  have w54_110 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m54]; exact w53_110
  have w54_114 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m54]; exact w53_114
  have w54_118 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m54]; exact w53_118
  have w54_11c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m54]; exact w53_11c
  have w54_120 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m54]; exact w53_120
  have w54_124 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m54]; exact w53_124
  have w54_128 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m54]; exact w53_128
  have w54_12c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m54]; exact w53_12c
  have w54_130 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m54]; exact w53_130
  have w54_a20 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m54]; exact w53_a20
  have w54_b28 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xB28) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by rw [m54]; exact w53_b28
  have w54_1020 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = BitVec.ofNat 32 (wnafGo (U1) 0x100 0x101 0 0).length := by rw [m54]; exact w53_1020
  have w54_1128 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x1128) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by rw [m54]; exact w53_1128
  have w54_1480 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = BitVec.ofNat 32 (wnafGo (U2) 0x100 0x101 0 0).length := by rw [m54]; exact w53_1480
  have a54_2a0 : accV n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m54]; exact a53_2a0
  have a54_2c0 : accV n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m54]; exact a53_2c0
  have a54_2e0 : accV n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m54]; exact a53_2e0
  have a54_380 : accV n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) 8 = U1 := by rw [m54]; exact a53_380
  have a54_400 : accV n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) 8 = U2 := by rw [m54]; exact a53_400
  have a54_13e0 : accV n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x13E0) 8 = U1 := by rw [m54]; exact a53_13e0
  have a54_1460 : accV n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x1460) 8 = U2 := by rw [m54]; exact a53_1460
  have a54_1588 : accV n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) 8 = U2 := by rw [m54]; exact a53_1588
  have p54_320 : ptF n54.mem B 0x320 = P0 := by rw [m54]; exact p53_320
  have p54_3a0 : ptF n54.mem B 0x3A0 = P1 := by rw [m54]; exact p53_3a0
  have p54_420 : ptF n54.mem B 0x420 = tbl2 P0 0 := by rw [m54]; exact p53_420
  have p54_480 : ptF n54.mem B 0x480 = tbl2 P0 1 := by rw [m54]; exact p53_480
  have p54_4e0 : ptF n54.mem B 0x4E0 = tbl2 P0 2 := by rw [m54]; exact p53_4e0
  have p54_540 : ptF n54.mem B 0x540 = tbl2 P0 3 := by rw [m54]; exact p53_540
  have p54_5a0 : ptF n54.mem B 0x5A0 = tbl2 P0 4 := by rw [m54]; exact p53_5a0
  have p54_600 : ptF n54.mem B 0x600 = tbl2 P0 5 := by rw [m54]; exact p53_600
  have p54_660 : ptF n54.mem B 0x660 = tbl2 P0 6 := by rw [m54]; exact p53_660
  have p54_6c0 : ptF n54.mem B 0x6C0 = tbl2 P0 7 := by rw [m54]; exact p53_6c0
  have p54_720 : ptF n54.mem B 0x720 = tbl2 P1 0 := by rw [m54]; exact p53_720
  have p54_780 : ptF n54.mem B 0x780 = tbl2 P1 1 := by rw [m54]; exact p53_780
  have p54_7e0 : ptF n54.mem B 0x7E0 = tbl2 P1 2 := by rw [m54]; exact p53_7e0
  have p54_840 : ptF n54.mem B 0x840 = tbl2 P1 3 := by rw [m54]; exact p53_840
  have p54_8a0 : ptF n54.mem B 0x8A0 = tbl2 P1 4 := by rw [m54]; exact p53_8a0
  have p54_900 : ptF n54.mem B 0x900 = tbl2 P1 5 := by rw [m54]; exact p53_900
  have p54_960 : ptF n54.mem B 0x960 = tbl2 P1 6 := by rw [m54]; exact p53_960
  have p54_9c0 : ptF n54.mem B 0x9C0 = tbl2 P1 7 := by rw [m54]; exact p53_9c0
  have p54_c60 : ptF n54.mem B 0xC60 = tbl2 P0 6 := by rw [m54]; exact p53_c60
  have p54_cc0 : ptF n54.mem B 0xCC0 = tbl2 P0 7 := by rw [m54]; exact p53_cc0
  have p54_d20 : ptF n54.mem B 0xD20 = tbl2 P1 0 := by rw [m54]; exact p53_d20
  have p54_d80 : ptF n54.mem B 0xD80 = tbl2 P1 1 := by rw [m54]; exact p53_d80
  have p54_de0 : ptF n54.mem B 0xDE0 = tbl2 P1 2 := by rw [m54]; exact p53_de0
  have p54_e40 : ptF n54.mem B 0xE40 = tbl2 P1 3 := by rw [m54]; exact p53_e40
  have p54_ea0 : ptF n54.mem B 0xEA0 = tbl2 P1 4 := by rw [m54]; exact p53_ea0
  have p54_f00 : ptF n54.mem B 0xF00 = tbl2 P1 5 := by rw [m54]; exact p53_f00
  have p54_f60 : ptF n54.mem B 0xF60 = tbl2 P1 6 := by rw [m54]; exact p53_f60
  have p54_fc0 : ptF n54.mem B 0xFC0 = tbl2 P1 7 := by rw [m54]; exact p53_fc0
  have p54_1380 : ptF n54.mem B 0x1380 = P0 := by rw [m54]; exact p53_1380
  have p54_1400 : ptF n54.mem B 0x1400 = P1 := by rw [m54]; exact p53_1400
  have mb54_a24 : memBytes n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m54]; exact mb53_a24
  have mb54_b2c : memBytes n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xB2C) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [m54]; exact mb53_b2c
  have mb54_1024 : memBytes n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) 0x101 = wnafBytes (wnafGo (U1) 0x100 0x101 0 0) 0x101 := by rw [m54]; exact mb53_1024
  have mb54_112c : memBytes n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x112C) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [m54]; exact mb53_112c
  have mb54_1320 : leN (memBytes n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) 0x20) = U2 := by rw [m54]; exact mb53_1320
  have mb54_1484 : memBytes n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) 0x101 = wnafBytes (wnafGo (U2) 0x100 0x101 0 0) 0x101 := by rw [m54]; exact mb53_1484
  clear mb53_1484 mb53_1320 mb53_112c mb53_1024 mb53_b2c mb53_a24 p53_1400 p53_1380 p53_fc0 p53_f60 p53_f00 p53_ea0 p53_e40 p53_de0 p53_d80 p53_d20 p53_cc0 p53_c60 p53_9c0 p53_960 p53_900 p53_8a0 p53_840 p53_7e0 p53_780 p53_720 p53_6c0 p53_660 p53_600 p53_5a0 p53_540 p53_4e0 p53_480 p53_420 p53_3a0 p53_320 a53_1588 a53_1460 a53_13e0 a53_400 a53_380 a53_2e0 a53_2c0 a53_2a0 w53_1480 w53_1128 w53_1020 w53_b28 w53_a20 w53_130 w53_12c w53_128 w53_124 w53_120 w53_11c w53_118 w53_114 w53_110 w53_10c w53_108 w53_104 w53_100 w53_fc w53_f8 w53_f4 w53_f0 w53_ec w53_e8 w53_e4 w53_e0 w53_dc w53_d8 w53_d4 w53_d0 w53_cc w53_c8 w53_c4 w53_c0 w53_bc w53_b8 w53_b4 w53_b0 w53_ac w53_a8 w53_a4 w53_a0 w53_9c w53_98 w53_94 w53_90 w53_8c w53_88 w53_84 w53_80 w53_7c w53_78 w53_70 w53_6c w53_68 w53_64 w53_60 w53_5c w53_58 w53_54 w53_50 w53_4c w53_48 w53_44 w53_40 w53_3c w53_38 w53_34 w53_30 w53_2c w53_28 w53_24 g53_9 g53_27 g53_26 g53_25 g53_24 g53_23 g53_22 g53_21 g53_20 g53_19 g53_18 g53_8 g53_4 g53_3 g53_2 V53 E53 fR53 t53 fr53 m53 s53 u53 d53
  exact .inr ⟨n54, t54, s54, E54, V54, fR54, g54_2, g54_3, g54_4, g54_9, g54_10, g54_18, g54_19, g54_20, g54_21, g54_23, g54_24, g54_25, g54_26, g54_27, w54_24, w54_28, w54_2c, w54_30, w54_34, w54_38, w54_3c, w54_40, w54_44, w54_48, w54_4c, w54_50, w54_54, w54_58, w54_5c, w54_60, w54_64, w54_68, w54_6c, w54_70, w54_78, w54_7c, w54_80, w54_84, w54_88, w54_8c, w54_90, w54_94, w54_98, w54_9c, w54_a0, w54_a4, w54_a8, w54_ac, w54_b0, w54_b4, w54_b8, w54_bc, w54_c0, w54_c4, w54_c8, w54_cc, w54_d0, w54_d4, w54_d8, w54_dc, w54_e0, w54_e4, w54_e8, w54_ec, w54_f0, w54_f4, w54_f8, w54_fc, w54_100, w54_104, w54_108, w54_10c, w54_110, w54_114, w54_118, w54_11c, w54_120, w54_124, w54_128, w54_12c, w54_130, w54_a20, w54_b28, w54_1020, w54_1128, w54_1480, a54_2a0, a54_2c0, a54_2e0, a54_380, a54_400, a54_13e0, a54_1460, a54_1588, p54_320, p54_3a0, p54_420, p54_480, p54_4e0, p54_540, p54_5a0, p54_600, p54_660, p54_6c0, p54_720, p54_780, p54_7e0, p54_840, p54_8a0, p54_900, p54_960, p54_9c0, p54_c60, p54_cc0, p54_d20, p54_d80, p54_de0, p54_e40, p54_ea0, p54_f00, p54_f60, p54_fc0, p54_1380, p54_1400, mb54_a24, mb54_b2c, mb54_1024, mb54_112c, mb54_1320, mb54_1484⟩

end C3.RV32.Sv
