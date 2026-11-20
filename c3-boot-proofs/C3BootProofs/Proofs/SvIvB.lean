import C3BootProofs.Proofs.SvIvLib

/-!
# `sigstore::verify`: the end of a batch of the inversion of `s`

From the divstep loop's exit at 0x1478 back to the head at 0x1328: the batch's matrix is stored at 0x320, `update_fg` applies it to `f` and `g` and `update_de` to `d` and `e`, and the steps left drop by the batch's size.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svIvB1478 : List BInstr :=
  [.aluImm .add a0 sp 0x300]
set_option maxRecDepth 100000 in
theorem svIvB1478_end : blockEnd sigstoreVerifyCode 0x1478 svIvB1478 = some 0x147A := by decide

def svIvB1494 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x221, .lui a1 0x1000, .aluImm .add a1 a1 0x380, .alu .add a1 a1 sp, .lui a2 0x1000, .aluImm .add a2 a2 0x480, .alu .add a2 a2 sp, .aluImm .add a3 sp 0x320]
set_option maxRecDepth 100000 in
theorem svIvB1494_end : blockEnd sigstoreVerifyCode 0x1494 svIvB1494 = some 0x14AE := by decide

def svIvB14b0 : List BInstr :=
  [.alu .add a4 x0 (8 : Fin 32)]
set_option maxRecDepth 100000 in
theorem svIvB14b0_end : blockEnd sigstoreVerifyCode 0x14B0 svIvB14b0 = some 0x14B2 := by decide

def svIvB14ba : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x380, .alu .add a0 a0 sp, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x221, .aluImm .add a2 x0 0x24]
set_option maxRecDepth 100000 in
theorem svIvB14ba_end : blockEnd sigstoreVerifyCode 0x14BA svIvB14ba = some 0x14CE := by decide

def svIvB14d6 : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x480, .alu .add a0 a0 sp, .aluImm .add a2 x0 0x24, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x245]
set_option maxRecDepth 100000 in
theorem svIvB14d6_end : blockEnd sigstoreVerifyCode 0x14D6 svIvB14d6 = some 0x14EA := by decide

def svIvB14f2 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x221, .lui a1 0x1000, .aluImm .add a1 a1 0x20, .alu .add a1 a1 sp, .aluImm .add a2 sp 0x420, .aluImm .add a6 sp 0x320, .alu .add a3 x0 (24 : Fin 32)]
set_option maxRecDepth 100000 in
theorem svIvB14f2_end : blockEnd sigstoreVerifyCode 0x14F2 svIvB14f2 = some 0x150C := by decide

def svIvB1510 : List BInstr :=
  [.alu .add (17 : Fin 32) x0 (8 : Fin 32)]
set_option maxRecDepth 100000 in
theorem svIvB1510_end : blockEnd sigstoreVerifyCode 0x1510 svIvB1510 = some 0x1512 := by decide

def svIvB151a : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x20, .alu .add a0 a0 sp, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x221, .aluImm .add a2 x0 0x24]
set_option maxRecDepth 100000 in
theorem svIvB151a_end : blockEnd sigstoreVerifyCode 0x151A svIvB151a = some 0x152E := by decide

def svIvB1536 : List BInstr :=
  [.aluImm .add a0 sp 0x420, .aluImm .add a2 x0 0x24, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x245]
set_option maxRecDepth 100000 in
theorem svIvB1536_end : blockEnd sigstoreVerifyCode 0x1536 svIvB1536 = some 0x1546 := by decide

def svIvB1550 : List BInstr :=
  [.alu .sub a0 a0 (8 : Fin 32)]
set_option maxRecDepth 100000 in
theorem svIvB1550_end : blockEnd sigstoreVerifyCode 0x1550 svIvB1550 = some 0x1552 := by decide

set_option maxHeartbeats 0 in
theorem sv_ivb {B out bp x21 x26 s5v s8v dlo dhi rem ulo uhi vlo vhi qlo qhi rlo rhi : Word} {ns : Nat} {er es : Bytes} {fs gs ds es : BitVec 8} {qx qy qz rv sv zv fv gv dv ev : Nat} {w24 w28 w2c w30 w34 w38 w3c w40 w44 w48 w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w7c w80 w84 w88 w8c w90 w94 w98 w9c wa0 wa4 wa8 wac wb0 wb4 wb8 wbc wc0 wc4 wc8 wcc wd0 wd4 wd8 wdc we0 we4 we8 wec wf0 wf4 wf8 wfc w100 w104 w108 w10c w110 w114 w118 w11c w120 w124 w128 w12c w130 : Word} {v : Nat → Word} {n0 : Machine}
    (F : Fr B 0x3830) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x1478 (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_21 : reg n0 (21 : Fin 32) = s5v)
    (g0_23 : reg n0 (23 : Fin 32) = dlo)
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
    (a0_240 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx)
    (a0_260 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy)
    (a0_280 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz)
    (a0_2a0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv)
    (a0_2c0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv)
    (a0_2e0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv)
    (a0_420 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = ev)
    (a0_1020 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = dv)
    (a0_1380 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = fv)
    (a0_1480 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = gv)
    (b0_440 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) = es)
    (b0_1040 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = ds)
    (b0_13a0 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = fs)
    (b0_14a0 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs)
    (IC0 : SvIvCode M0)
    (EC0 : SvEcCode M0)
    (g0_24 : reg n0 (24 : Fin 32) = BitVec.ofNat 32 0x3FCC4268)
    (g0_14 : reg n0 a4 = ulo)
    (g0_5 : reg n0 (5 : Fin 32) = uhi)
    (g0_31 : reg n0 (31 : Fin 32) = vlo)
    (g0_17 : reg n0 a7 = vhi)
    (g0_8 : reg n0 (8 : Fin 32) = qlo)
    (g0_29 : reg n0 (29 : Fin 32) = qhi)
    (g0_12 : reg n0 a2 = rlo)
    (g0_6 : reg n0 (6 : Fin 32) = rhi)
    (w0_5c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 ns)
    (hns1 : 1 ≤ ns)
    (hns2 : ns ≤ 62)
    (UC0 : SvUpCode M0)
    (hfs : fs.toNat ≤ 1)
    (hgs : gs.toNat ≤ 1)
    (hds : ds.toNat ≤ 1)
    (hes : es.toNat ≤ 1) :
    (¬ (∃ σ13a A13a, sgnVal σ13a A13a = sgnVal (fs).toNat (fv) * i64Val ((ulo).toNat + 2 ^ 32 * (uhi).toNat) + sgnVal (gs).toNat (gv) * i64Val ((vlo).toNat + 2 ^ 32 * (vhi).toNat) ∧ (σ13a ≤ 1) ∧ ∃ σ13b A13b, sgnVal σ13b A13b = sgnVal (fs).toNat (fv) * i64Val ((qlo).toNat + 2 ^ 32 * (qhi).toNat) + sgnVal (gs).toNat (gv) * i64Val ((rlo).toNat + 2 ^ 32 * (rhi).toNat) ∧ (σ13b ≤ 1) ∧ ∃ σ22a A22a, sgnVal σ22a A22a = sgnVal (ds).toNat (dv) * i64Val ((ulo).toNat + 2 ^ 32 * (uhi).toNat) + sgnVal (es).toNat (ev) * i64Val ((vlo).toNat + 2 ^ 32 * (vhi).toNat) ∧ (σ22a ≤ 1) ∧ ∃ σ22b A22b, sgnVal σ22b A22b = sgnVal (ds).toNat (dv) * i64Val ((qlo).toNat + 2 ^ 32 * (qhi).toNat) + sgnVal (es).toNat (ev) * i64Val ((rlo).toNat + 2 ^ 32 * (rhi).toNat) ∧ (σ22b ≤ 1) ∧ True) ∧ SvErrRet B out v n0) ∨
    (∃ σ13a A13a, sgnVal σ13a A13a = sgnVal (fs).toNat (fv) * i64Val ((ulo).toNat + 2 ^ 32 * (uhi).toNat) + sgnVal (gs).toNat (gv) * i64Val ((vlo).toNat + 2 ^ 32 * (vhi).toNat) ∧
    (σ13a ≤ 1) ∧
    ∃ σ13b A13b, sgnVal σ13b A13b = sgnVal (fs).toNat (fv) * i64Val ((qlo).toNat + 2 ^ 32 * (qhi).toNat) + sgnVal (gs).toNat (gv) * i64Val ((rlo).toNat + 2 ^ 32 * (rhi).toNat) ∧
    (σ13b ≤ 1) ∧
    ∃ σ22a A22a, sgnVal σ22a A22a = sgnVal (ds).toNat (dv) * i64Val ((ulo).toNat + 2 ^ 32 * (uhi).toNat) + sgnVal (es).toNat (ev) * i64Val ((vlo).toNat + 2 ^ 32 * (vhi).toNat) ∧
    (σ22a ≤ 1) ∧
    ∃ σ22b A22b, sgnVal σ22b A22b = sgnVal (ds).toNat (dv) * i64Val ((qlo).toNat + 2 ^ 32 * (qhi).toNat) + sgnVal (es).toNat (ev) * i64Val ((rlo).toNat + 2 ^ 32 * (rhi).toNat) ∧
    (σ22b ≤ 1) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x1328 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (21 : Fin 32) = s5v ∧
        reg n' (23 : Fin 32) = dlo ∧
        reg n' (24 : Fin 32) = BitVec.ofNat 32 0x3FCC4268 ∧
        reg n' (25 : Fin 32) = dhi ∧
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
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 ns ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = (rem) - (BitVec.ofNat 32 ns) ∧
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
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ulo ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = uhi ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = vlo ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = vhi ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = qlo ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = qhi ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = rlo ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = rhi ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) = BitVec.ofNat 8 (lrsm8 σ22b A22b ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).1 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 8 (lrsm8 σ22a A22a ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).1 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA64) = BitVec.ofNat 8 (lrsm8 σ22b A22b ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).1 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = BitVec.ofNat 8 (lrsm8 σ22a A22a ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).1 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = BitVec.ofNat 8 σ13a ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = BitVec.ofNat 8 σ13b ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = (lrsm8 σ22b A22b ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).2 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 8 = (lrsm8 σ22a A22a ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).2 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) 8 = (lrsm8 σ22b A22b ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).2 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = (lrsm8 σ22a A22a ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).2 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = A13a / 2 ^ ns % 2 ^ 256 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = A13b / 2 ^ ns % 2 ^ 256) := by
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x1478
  obtain ⟨n1, c1, u1⟩ := s0.block svIvB1478 E0.self svIvB1478_end
    ⟨trivial, trivial⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have s1 : St n1.mem SV n1 0x147A (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have rb1 : ∀ q, reg n1 q = (runBlock svIvB1478 (n0.mem, reg n0)).2 q := fun q => by rw [u1.regs]
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
  have g1_5 : reg n1 (5 : Fin 32) = uhi := by
    rw [rb1, runBlock_reg _ _ _ (5 : Fin 32) s0.zero (by decide), g0_5]
  have g1_6 : reg n1 (6 : Fin 32) = rhi := by
    rw [rb1, runBlock_reg _ _ _ (6 : Fin 32) s0.zero (by decide), g0_6]
  have g1_8 : reg n1 (8 : Fin 32) = qlo := by
    rw [rb1, runBlock_reg _ _ _ (8 : Fin 32) s0.zero (by decide), g0_8]
  have g1_12 : reg n1 a2 = rlo := by
    rw [rb1, runBlock_reg _ _ _ a2 s0.zero (by decide), g0_12]
  have g1_14 : reg n1 a4 = ulo := by
    rw [rb1, runBlock_reg _ _ _ a4 s0.zero (by decide), g0_14]
  have g1_17 : reg n1 a7 = vhi := by
    rw [rb1, runBlock_reg _ _ _ a7 s0.zero (by decide), g0_17]
  have g1_18 : reg n1 (18 : Fin 32) = out := by
    rw [rb1, runBlock_reg _ _ _ (18 : Fin 32) s0.zero (by decide), g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = bp := by
    rw [rb1, runBlock_reg _ _ _ (19 : Fin 32) s0.zero (by decide), g0_19]
  have g1_21 : reg n1 (21 : Fin 32) = s5v := by
    rw [rb1, runBlock_reg _ _ _ (21 : Fin 32) s0.zero (by decide), g0_21]
  have g1_23 : reg n1 (23 : Fin 32) = dlo := by
    rw [rb1, runBlock_reg _ _ _ (23 : Fin 32) s0.zero (by decide), g0_23]
  have g1_24 : reg n1 (24 : Fin 32) = BitVec.ofNat 32 0x3FCC4268 := by
    rw [rb1, runBlock_reg _ _ _ (24 : Fin 32) s0.zero (by decide), g0_24]
  have g1_25 : reg n1 (25 : Fin 32) = dhi := by
    rw [rb1, runBlock_reg _ _ _ (25 : Fin 32) s0.zero (by decide), g0_25]
  have g1_26 : reg n1 (26 : Fin 32) = x26 := by
    rw [rb1, runBlock_reg _ _ _ (26 : Fin 32) s0.zero (by decide), g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb1, runBlock_reg _ _ _ (27 : Fin 32) s0.zero (by decide), g0_27]
  have g1_29 : reg n1 (29 : Fin 32) = qhi := by
    rw [rb1, runBlock_reg _ _ _ (29 : Fin 32) s0.zero (by decide), g0_29]
  have g1_31 : reg n1 (31 : Fin 32) = vlo := by
    rw [rb1, runBlock_reg _ _ _ (31 : Fin 32) s0.zero (by decide), g0_31]
  have g1_10 : reg n1 a0 = B + 0x21A0 + BitVec.ofNat 32 0x300 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svIvB1478, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_5, g0_6, g0_8, g0_12, g0_14, g0_17, g0_18, g0_19, g0_21, g0_23, g0_24, g0_25, g0_26, g0_27, g0_29, g0_31, s0.zero])
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
  have w1_5c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 ns := by rw [m1]; exact w0_5c
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
  have b1_440 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) = es := by rw [m1]; exact b0_440
  have b1_1040 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = ds := by rw [m1]; exact b0_1040
  have b1_13a0 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = fs := by rw [m1]; exact b0_13a0
  have b1_14a0 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := by rw [m1]; exact b0_14a0
  have a1_240 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m1]; exact a0_240
  have a1_260 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m1]; exact a0_260
  have a1_280 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m1]; exact a0_280
  have a1_2a0 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m1]; exact a0_2a0
  have a1_2c0 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m1]; exact a0_2c0
  have a1_2e0 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m1]; exact a0_2e0
  have a1_420 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = ev := by rw [m1]; exact a0_420
  have a1_1020 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = dv := by rw [m1]; exact a0_1020
  have a1_1380 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = fv := by rw [m1]; exact a0_1380
  have a1_1480 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = gv := by rw [m1]; exact a0_1480
  -- 0x147A: sw
  obtain ⟨n2, d2, s2, fr2, K2, W2, rg2⟩ := sv_sw F E1 s1 sv_at_147a (off' := 0x147C) (c := 0x320)
    (by decide) (by rw [g1_10]; sv_addr) (by decide) (by decide)
  have t2 : Steps n0 n2 := t1.trans d2
  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.keep K2 (by decide)
  have g2_2 : reg n2 sp = B + 0x21A0 := by rw [rg2 sp, g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg2 (3 : Fin 32), g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg2 (4 : Fin 32), g1_4]
  have g2_5 : reg n2 (5 : Fin 32) = uhi := by rw [rg2 (5 : Fin 32), g1_5]
  have g2_6 : reg n2 (6 : Fin 32) = rhi := by rw [rg2 (6 : Fin 32), g1_6]
  have g2_8 : reg n2 (8 : Fin 32) = qlo := by rw [rg2 (8 : Fin 32), g1_8]
  have g2_10 : reg n2 a0 = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [rg2 a0, g1_10]
  have g2_12 : reg n2 a2 = rlo := by rw [rg2 a2, g1_12]
  have g2_14 : reg n2 a4 = ulo := by rw [rg2 a4, g1_14]
  have g2_17 : reg n2 a7 = vhi := by rw [rg2 a7, g1_17]
  have g2_18 : reg n2 (18 : Fin 32) = out := by rw [rg2 (18 : Fin 32), g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [rg2 (19 : Fin 32), g1_19]
  have g2_21 : reg n2 (21 : Fin 32) = s5v := by rw [rg2 (21 : Fin 32), g1_21]
  have g2_23 : reg n2 (23 : Fin 32) = dlo := by rw [rg2 (23 : Fin 32), g1_23]
  have g2_24 : reg n2 (24 : Fin 32) = BitVec.ofNat 32 0x3FCC4268 := by rw [rg2 (24 : Fin 32), g1_24]
  have g2_25 : reg n2 (25 : Fin 32) = dhi := by rw [rg2 (25 : Fin 32), g1_25]
  have g2_26 : reg n2 (26 : Fin 32) = x26 := by rw [rg2 (26 : Fin 32), g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg2 (27 : Fin 32), g1_27]
  have g2_29 : reg n2 (29 : Fin 32) = qhi := by rw [rg2 (29 : Fin 32), g1_29]
  have g2_31 : reg n2 (31 : Fin 32) = vlo := by rw [rg2 (31 : Fin 32), g1_31]
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
  have w2_5c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 ns := (K2.w32 (by decide) (by decide)).trans w1_5c
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
  have b2_440 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) = es := (K2.b8 (by decide) (by decide)).trans b1_440
  have b2_1040 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = ds := (K2.b8 (by decide) (by decide)).trans b1_1040
  have b2_13a0 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = fs := (K2.b8 (by decide) (by decide)).trans b1_13a0
  have b2_14a0 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := (K2.b8 (by decide) (by decide)).trans b1_14a0
  have w2_320 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ulo := by rw [W2, g1_14]
  have a2_240 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := (K2.acc (by decide) (by decide)).trans a1_240
  have a2_260 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := (K2.acc (by decide) (by decide)).trans a1_260
  have a2_280 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := (K2.acc (by decide) (by decide)).trans a1_280
  have a2_2a0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K2.acc (by decide) (by decide)).trans a1_2a0
  have a2_2c0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K2.acc (by decide) (by decide)).trans a1_2c0
  have a2_2e0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K2.acc (by decide) (by decide)).trans a1_2e0
  have a2_420 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = ev := (K2.acc (by decide) (by decide)).trans a1_420
  have a2_1020 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = dv := (K2.acc (by decide) (by decide)).trans a1_1020
  have a2_1380 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = fv := (K2.acc (by decide) (by decide)).trans a1_1380
  have a2_1480 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = gv := (K2.acc (by decide) (by decide)).trans a1_1480
  clear a1_1480 a1_1380 a1_1020 a1_420 a1_2e0 a1_2c0 a1_2a0 a1_280 a1_260 a1_240 b1_14a0 b1_13a0 b1_1040 b1_440 w1_130 w1_12c w1_128 w1_124 w1_120 w1_11c w1_118 w1_114 w1_110 w1_10c w1_108 w1_104 w1_100 w1_fc w1_f8 w1_f4 w1_f0 w1_ec w1_e8 w1_e4 w1_e0 w1_dc w1_d8 w1_d4 w1_d0 w1_cc w1_c8 w1_c4 w1_c0 w1_bc w1_b8 w1_b4 w1_b0 w1_ac w1_a8 w1_a4 w1_a0 w1_9c w1_98 w1_94 w1_90 w1_8c w1_88 w1_84 w1_80 w1_7c w1_78 w1_70 w1_6c w1_68 w1_64 w1_60 w1_5c w1_58 w1_54 w1_50 w1_4c w1_48 w1_44 w1_40 w1_3c w1_38 w1_34 w1_30 w1_2c w1_28 w1_24 g1_10 g1_31 g1_29 g1_27 g1_26 g1_25 g1_24 g1_23 g1_21 g1_19 g1_18 g1_17 g1_14 g1_12 g1_8 g1_6 g1_5 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
  -- 0x147C: sw
  obtain ⟨n3, d3, s3, fr3, K3, W3, rg3⟩ := sv_sw F E2 s2 sv_at_147c (off' := 0x1480) (c := 0x324)
    (by decide) (by rw [g2_10]; sv_addr) (by decide) (by decide)
  have t3 : Steps n0 n3 := t2.trans d3
  have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : SvCode n3.mem := E2.fr F fr3
  have V3 : SvSaves B n3.mem v := V2.keep K3 (by decide)
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [rg3 sp, g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg3 (3 : Fin 32), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg3 (4 : Fin 32), g2_4]
  have g3_5 : reg n3 (5 : Fin 32) = uhi := by rw [rg3 (5 : Fin 32), g2_5]
  have g3_6 : reg n3 (6 : Fin 32) = rhi := by rw [rg3 (6 : Fin 32), g2_6]
  have g3_8 : reg n3 (8 : Fin 32) = qlo := by rw [rg3 (8 : Fin 32), g2_8]
  have g3_10 : reg n3 a0 = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [rg3 a0, g2_10]
  have g3_12 : reg n3 a2 = rlo := by rw [rg3 a2, g2_12]
  have g3_14 : reg n3 a4 = ulo := by rw [rg3 a4, g2_14]
  have g3_17 : reg n3 a7 = vhi := by rw [rg3 a7, g2_17]
  have g3_18 : reg n3 (18 : Fin 32) = out := by rw [rg3 (18 : Fin 32), g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [rg3 (19 : Fin 32), g2_19]
  have g3_21 : reg n3 (21 : Fin 32) = s5v := by rw [rg3 (21 : Fin 32), g2_21]
  have g3_23 : reg n3 (23 : Fin 32) = dlo := by rw [rg3 (23 : Fin 32), g2_23]
  have g3_24 : reg n3 (24 : Fin 32) = BitVec.ofNat 32 0x3FCC4268 := by rw [rg3 (24 : Fin 32), g2_24]
  have g3_25 : reg n3 (25 : Fin 32) = dhi := by rw [rg3 (25 : Fin 32), g2_25]
  have g3_26 : reg n3 (26 : Fin 32) = x26 := by rw [rg3 (26 : Fin 32), g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg3 (27 : Fin 32), g2_27]
  have g3_29 : reg n3 (29 : Fin 32) = qhi := by rw [rg3 (29 : Fin 32), g2_29]
  have g3_31 : reg n3 (31 : Fin 32) = vlo := by rw [rg3 (31 : Fin 32), g2_31]
  have w3_24 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K3.w32 (by decide) (by decide)).trans w2_24
  have w3_28 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K3.w32 (by decide) (by decide)).trans w2_28
  have w3_2c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K3.w32 (by decide) (by decide)).trans w2_2c
  have w3_30 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K3.w32 (by decide) (by decide)).trans w2_30
  have w3_34 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K3.w32 (by decide) (by decide)).trans w2_34
  have w3_38 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K3.w32 (by decide) (by decide)).trans w2_38
  have w3_3c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K3.w32 (by decide) (by decide)).trans w2_3c
  have w3_40 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K3.w32 (by decide) (by decide)).trans w2_40
  have w3_44 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K3.w32 (by decide) (by decide)).trans w2_44
  have w3_48 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K3.w32 (by decide) (by decide)).trans w2_48
  have w3_4c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K3.w32 (by decide) (by decide)).trans w2_4c
  have w3_50 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K3.w32 (by decide) (by decide)).trans w2_50
  have w3_54 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K3.w32 (by decide) (by decide)).trans w2_54
  have w3_58 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K3.w32 (by decide) (by decide)).trans w2_58
  have w3_5c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 ns := (K3.w32 (by decide) (by decide)).trans w2_5c
  have w3_60 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K3.w32 (by decide) (by decide)).trans w2_60
  have w3_64 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K3.w32 (by decide) (by decide)).trans w2_64
  have w3_68 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K3.w32 (by decide) (by decide)).trans w2_68
  have w3_6c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K3.w32 (by decide) (by decide)).trans w2_6c
  have w3_70 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K3.w32 (by decide) (by decide)).trans w2_70
  have w3_78 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := (K3.w32 (by decide) (by decide)).trans w2_78
  have w3_7c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K3.w32 (by decide) (by decide)).trans w2_7c
  have w3_80 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K3.w32 (by decide) (by decide)).trans w2_80
  have w3_84 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K3.w32 (by decide) (by decide)).trans w2_84
  have w3_88 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K3.w32 (by decide) (by decide)).trans w2_88
  have w3_8c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K3.w32 (by decide) (by decide)).trans w2_8c
  have w3_90 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K3.w32 (by decide) (by decide)).trans w2_90
  have w3_94 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K3.w32 (by decide) (by decide)).trans w2_94
  have w3_98 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K3.w32 (by decide) (by decide)).trans w2_98
  have w3_9c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K3.w32 (by decide) (by decide)).trans w2_9c
  have w3_a0 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K3.w32 (by decide) (by decide)).trans w2_a0
  have w3_a4 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K3.w32 (by decide) (by decide)).trans w2_a4
  have w3_a8 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K3.w32 (by decide) (by decide)).trans w2_a8
  have w3_ac : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K3.w32 (by decide) (by decide)).trans w2_ac
  have w3_b0 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K3.w32 (by decide) (by decide)).trans w2_b0
  have w3_b4 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K3.w32 (by decide) (by decide)).trans w2_b4
  have w3_b8 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K3.w32 (by decide) (by decide)).trans w2_b8
  have w3_bc : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K3.w32 (by decide) (by decide)).trans w2_bc
  have w3_c0 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K3.w32 (by decide) (by decide)).trans w2_c0
  have w3_c4 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K3.w32 (by decide) (by decide)).trans w2_c4
  have w3_c8 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K3.w32 (by decide) (by decide)).trans w2_c8
  have w3_cc : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K3.w32 (by decide) (by decide)).trans w2_cc
  have w3_d0 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K3.w32 (by decide) (by decide)).trans w2_d0
  have w3_d4 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K3.w32 (by decide) (by decide)).trans w2_d4
  have w3_d8 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K3.w32 (by decide) (by decide)).trans w2_d8
  have w3_dc : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K3.w32 (by decide) (by decide)).trans w2_dc
  have w3_e0 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K3.w32 (by decide) (by decide)).trans w2_e0
  have w3_e4 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K3.w32 (by decide) (by decide)).trans w2_e4
  have w3_e8 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K3.w32 (by decide) (by decide)).trans w2_e8
  have w3_ec : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K3.w32 (by decide) (by decide)).trans w2_ec
  have w3_f0 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K3.w32 (by decide) (by decide)).trans w2_f0
  have w3_f4 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K3.w32 (by decide) (by decide)).trans w2_f4
  have w3_f8 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K3.w32 (by decide) (by decide)).trans w2_f8
  have w3_fc : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K3.w32 (by decide) (by decide)).trans w2_fc
  have w3_100 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K3.w32 (by decide) (by decide)).trans w2_100
  have w3_104 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K3.w32 (by decide) (by decide)).trans w2_104
  have w3_108 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K3.w32 (by decide) (by decide)).trans w2_108
  have w3_10c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K3.w32 (by decide) (by decide)).trans w2_10c
  have w3_110 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K3.w32 (by decide) (by decide)).trans w2_110
  have w3_114 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K3.w32 (by decide) (by decide)).trans w2_114
  have w3_118 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K3.w32 (by decide) (by decide)).trans w2_118
  have w3_11c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K3.w32 (by decide) (by decide)).trans w2_11c
  have w3_120 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K3.w32 (by decide) (by decide)).trans w2_120
  have w3_124 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K3.w32 (by decide) (by decide)).trans w2_124
  have w3_128 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K3.w32 (by decide) (by decide)).trans w2_128
  have w3_12c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K3.w32 (by decide) (by decide)).trans w2_12c
  have w3_130 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K3.w32 (by decide) (by decide)).trans w2_130
  have w3_320 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ulo := (K3.w32 (by decide) (by decide)).trans w2_320
  have b3_440 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) = es := (K3.b8 (by decide) (by decide)).trans b2_440
  have b3_1040 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = ds := (K3.b8 (by decide) (by decide)).trans b2_1040
  have b3_13a0 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = fs := (K3.b8 (by decide) (by decide)).trans b2_13a0
  have b3_14a0 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := (K3.b8 (by decide) (by decide)).trans b2_14a0
  have w3_324 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = uhi := by rw [W3, g2_5]
  have a3_240 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := (K3.acc (by decide) (by decide)).trans a2_240
  have a3_260 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := (K3.acc (by decide) (by decide)).trans a2_260
  have a3_280 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := (K3.acc (by decide) (by decide)).trans a2_280
  have a3_2a0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K3.acc (by decide) (by decide)).trans a2_2a0
  have a3_2c0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K3.acc (by decide) (by decide)).trans a2_2c0
  have a3_2e0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K3.acc (by decide) (by decide)).trans a2_2e0
  have a3_420 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = ev := (K3.acc (by decide) (by decide)).trans a2_420
  have a3_1020 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = dv := (K3.acc (by decide) (by decide)).trans a2_1020
  have a3_1380 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = fv := (K3.acc (by decide) (by decide)).trans a2_1380
  have a3_1480 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = gv := (K3.acc (by decide) (by decide)).trans a2_1480
  clear a2_1480 a2_1380 a2_1020 a2_420 a2_2e0 a2_2c0 a2_2a0 a2_280 a2_260 a2_240 w2_320 b2_14a0 b2_13a0 b2_1040 b2_440 w2_130 w2_12c w2_128 w2_124 w2_120 w2_11c w2_118 w2_114 w2_110 w2_10c w2_108 w2_104 w2_100 w2_fc w2_f8 w2_f4 w2_f0 w2_ec w2_e8 w2_e4 w2_e0 w2_dc w2_d8 w2_d4 w2_d0 w2_cc w2_c8 w2_c4 w2_c0 w2_bc w2_b8 w2_b4 w2_b0 w2_ac w2_a8 w2_a4 w2_a0 w2_9c w2_98 w2_94 w2_90 w2_8c w2_88 w2_84 w2_80 w2_7c w2_78 w2_70 w2_6c w2_68 w2_64 w2_60 w2_5c w2_58 w2_54 w2_50 w2_4c w2_48 w2_44 w2_40 w2_3c w2_38 w2_34 w2_30 w2_2c w2_28 w2_24 g2_31 g2_29 g2_27 g2_26 g2_25 g2_24 g2_23 g2_21 g2_19 g2_18 g2_17 g2_14 g2_12 g2_10 g2_8 g2_6 g2_5 g2_4 g2_3 g2_2 V2 E2 fR2 t2 rg2 W2 K2 fr2 s2 d2
  -- 0x1480: sw
  obtain ⟨n4, d4, s4, fr4, K4, W4, rg4⟩ := sv_sw F E3 s3 sv_at_1480 (off' := 0x1484) (c := 0x328)
    (by decide) (by rw [g3_10]; sv_addr) (by decide) (by decide)
  have t4 : Steps n0 n4 := t3.trans d4
  have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : SvCode n4.mem := E3.fr F fr4
  have V4 : SvSaves B n4.mem v := V3.keep K4 (by decide)
  have g4_2 : reg n4 sp = B + 0x21A0 := by rw [rg4 sp, g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg4 (3 : Fin 32), g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg4 (4 : Fin 32), g3_4]
  have g4_5 : reg n4 (5 : Fin 32) = uhi := by rw [rg4 (5 : Fin 32), g3_5]
  have g4_6 : reg n4 (6 : Fin 32) = rhi := by rw [rg4 (6 : Fin 32), g3_6]
  have g4_8 : reg n4 (8 : Fin 32) = qlo := by rw [rg4 (8 : Fin 32), g3_8]
  have g4_10 : reg n4 a0 = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [rg4 a0, g3_10]
  have g4_12 : reg n4 a2 = rlo := by rw [rg4 a2, g3_12]
  have g4_14 : reg n4 a4 = ulo := by rw [rg4 a4, g3_14]
  have g4_17 : reg n4 a7 = vhi := by rw [rg4 a7, g3_17]
  have g4_18 : reg n4 (18 : Fin 32) = out := by rw [rg4 (18 : Fin 32), g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [rg4 (19 : Fin 32), g3_19]
  have g4_21 : reg n4 (21 : Fin 32) = s5v := by rw [rg4 (21 : Fin 32), g3_21]
  have g4_23 : reg n4 (23 : Fin 32) = dlo := by rw [rg4 (23 : Fin 32), g3_23]
  have g4_24 : reg n4 (24 : Fin 32) = BitVec.ofNat 32 0x3FCC4268 := by rw [rg4 (24 : Fin 32), g3_24]
  have g4_25 : reg n4 (25 : Fin 32) = dhi := by rw [rg4 (25 : Fin 32), g3_25]
  have g4_26 : reg n4 (26 : Fin 32) = x26 := by rw [rg4 (26 : Fin 32), g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg4 (27 : Fin 32), g3_27]
  have g4_29 : reg n4 (29 : Fin 32) = qhi := by rw [rg4 (29 : Fin 32), g3_29]
  have g4_31 : reg n4 (31 : Fin 32) = vlo := by rw [rg4 (31 : Fin 32), g3_31]
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
  have w4_5c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 ns := (K4.w32 (by decide) (by decide)).trans w3_5c
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
  have w4_320 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ulo := (K4.w32 (by decide) (by decide)).trans w3_320
  have w4_324 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = uhi := (K4.w32 (by decide) (by decide)).trans w3_324
  have b4_440 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) = es := (K4.b8 (by decide) (by decide)).trans b3_440
  have b4_1040 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = ds := (K4.b8 (by decide) (by decide)).trans b3_1040
  have b4_13a0 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = fs := (K4.b8 (by decide) (by decide)).trans b3_13a0
  have b4_14a0 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := (K4.b8 (by decide) (by decide)).trans b3_14a0
  have w4_328 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = vlo := by rw [W4, g3_31]
  have a4_240 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := (K4.acc (by decide) (by decide)).trans a3_240
  have a4_260 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := (K4.acc (by decide) (by decide)).trans a3_260
  have a4_280 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := (K4.acc (by decide) (by decide)).trans a3_280
  have a4_2a0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K4.acc (by decide) (by decide)).trans a3_2a0
  have a4_2c0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K4.acc (by decide) (by decide)).trans a3_2c0
  have a4_2e0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K4.acc (by decide) (by decide)).trans a3_2e0
  have a4_420 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = ev := (K4.acc (by decide) (by decide)).trans a3_420
  have a4_1020 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = dv := (K4.acc (by decide) (by decide)).trans a3_1020
  have a4_1380 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = fv := (K4.acc (by decide) (by decide)).trans a3_1380
  have a4_1480 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = gv := (K4.acc (by decide) (by decide)).trans a3_1480
  clear a3_1480 a3_1380 a3_1020 a3_420 a3_2e0 a3_2c0 a3_2a0 a3_280 a3_260 a3_240 w3_324 b3_14a0 b3_13a0 b3_1040 b3_440 w3_320 w3_130 w3_12c w3_128 w3_124 w3_120 w3_11c w3_118 w3_114 w3_110 w3_10c w3_108 w3_104 w3_100 w3_fc w3_f8 w3_f4 w3_f0 w3_ec w3_e8 w3_e4 w3_e0 w3_dc w3_d8 w3_d4 w3_d0 w3_cc w3_c8 w3_c4 w3_c0 w3_bc w3_b8 w3_b4 w3_b0 w3_ac w3_a8 w3_a4 w3_a0 w3_9c w3_98 w3_94 w3_90 w3_8c w3_88 w3_84 w3_80 w3_7c w3_78 w3_70 w3_6c w3_68 w3_64 w3_60 w3_5c w3_58 w3_54 w3_50 w3_4c w3_48 w3_44 w3_40 w3_3c w3_38 w3_34 w3_30 w3_2c w3_28 w3_24 g3_31 g3_29 g3_27 g3_26 g3_25 g3_24 g3_23 g3_21 g3_19 g3_18 g3_17 g3_14 g3_12 g3_10 g3_8 g3_6 g3_5 g3_4 g3_3 g3_2 V3 E3 fR3 t3 rg3 W3 K3 fr3 s3 d3
  -- 0x1484: sw
  obtain ⟨n5, d5, s5, fr5, K5, W5, rg5⟩ := sv_sw F E4 s4 sv_at_1484 (off' := 0x1488) (c := 0x32C)
    (by decide) (by rw [g4_10]; sv_addr) (by decide) (by decide)
  have t5 : Steps n0 n5 := t4.trans d5
  have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : SvCode n5.mem := E4.fr F fr5
  have V5 : SvSaves B n5.mem v := V4.keep K5 (by decide)
  have g5_2 : reg n5 sp = B + 0x21A0 := by rw [rg5 sp, g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg5 (3 : Fin 32), g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg5 (4 : Fin 32), g4_4]
  have g5_5 : reg n5 (5 : Fin 32) = uhi := by rw [rg5 (5 : Fin 32), g4_5]
  have g5_6 : reg n5 (6 : Fin 32) = rhi := by rw [rg5 (6 : Fin 32), g4_6]
  have g5_8 : reg n5 (8 : Fin 32) = qlo := by rw [rg5 (8 : Fin 32), g4_8]
  have g5_10 : reg n5 a0 = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [rg5 a0, g4_10]
  have g5_12 : reg n5 a2 = rlo := by rw [rg5 a2, g4_12]
  have g5_14 : reg n5 a4 = ulo := by rw [rg5 a4, g4_14]
  have g5_17 : reg n5 a7 = vhi := by rw [rg5 a7, g4_17]
  have g5_18 : reg n5 (18 : Fin 32) = out := by rw [rg5 (18 : Fin 32), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [rg5 (19 : Fin 32), g4_19]
  have g5_21 : reg n5 (21 : Fin 32) = s5v := by rw [rg5 (21 : Fin 32), g4_21]
  have g5_23 : reg n5 (23 : Fin 32) = dlo := by rw [rg5 (23 : Fin 32), g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = BitVec.ofNat 32 0x3FCC4268 := by rw [rg5 (24 : Fin 32), g4_24]
  have g5_25 : reg n5 (25 : Fin 32) = dhi := by rw [rg5 (25 : Fin 32), g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = x26 := by rw [rg5 (26 : Fin 32), g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg5 (27 : Fin 32), g4_27]
  have g5_29 : reg n5 (29 : Fin 32) = qhi := by rw [rg5 (29 : Fin 32), g4_29]
  have g5_31 : reg n5 (31 : Fin 32) = vlo := by rw [rg5 (31 : Fin 32), g4_31]
  have w5_24 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K5.w32 (by decide) (by decide)).trans w4_24
  have w5_28 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K5.w32 (by decide) (by decide)).trans w4_28
  have w5_2c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K5.w32 (by decide) (by decide)).trans w4_2c
  have w5_30 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K5.w32 (by decide) (by decide)).trans w4_30
  have w5_34 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K5.w32 (by decide) (by decide)).trans w4_34
  have w5_38 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K5.w32 (by decide) (by decide)).trans w4_38
  have w5_3c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K5.w32 (by decide) (by decide)).trans w4_3c
  have w5_40 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K5.w32 (by decide) (by decide)).trans w4_40
  have w5_44 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K5.w32 (by decide) (by decide)).trans w4_44
  have w5_48 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K5.w32 (by decide) (by decide)).trans w4_48
  have w5_4c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K5.w32 (by decide) (by decide)).trans w4_4c
  have w5_50 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K5.w32 (by decide) (by decide)).trans w4_50
  have w5_54 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K5.w32 (by decide) (by decide)).trans w4_54
  have w5_58 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K5.w32 (by decide) (by decide)).trans w4_58
  have w5_5c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 ns := (K5.w32 (by decide) (by decide)).trans w4_5c
  have w5_60 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K5.w32 (by decide) (by decide)).trans w4_60
  have w5_64 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K5.w32 (by decide) (by decide)).trans w4_64
  have w5_68 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K5.w32 (by decide) (by decide)).trans w4_68
  have w5_6c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K5.w32 (by decide) (by decide)).trans w4_6c
  have w5_70 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K5.w32 (by decide) (by decide)).trans w4_70
  have w5_78 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := (K5.w32 (by decide) (by decide)).trans w4_78
  have w5_7c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K5.w32 (by decide) (by decide)).trans w4_7c
  have w5_80 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K5.w32 (by decide) (by decide)).trans w4_80
  have w5_84 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K5.w32 (by decide) (by decide)).trans w4_84
  have w5_88 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K5.w32 (by decide) (by decide)).trans w4_88
  have w5_8c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K5.w32 (by decide) (by decide)).trans w4_8c
  have w5_90 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K5.w32 (by decide) (by decide)).trans w4_90
  have w5_94 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K5.w32 (by decide) (by decide)).trans w4_94
  have w5_98 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K5.w32 (by decide) (by decide)).trans w4_98
  have w5_9c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K5.w32 (by decide) (by decide)).trans w4_9c
  have w5_a0 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K5.w32 (by decide) (by decide)).trans w4_a0
  have w5_a4 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K5.w32 (by decide) (by decide)).trans w4_a4
  have w5_a8 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K5.w32 (by decide) (by decide)).trans w4_a8
  have w5_ac : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K5.w32 (by decide) (by decide)).trans w4_ac
  have w5_b0 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K5.w32 (by decide) (by decide)).trans w4_b0
  have w5_b4 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K5.w32 (by decide) (by decide)).trans w4_b4
  have w5_b8 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K5.w32 (by decide) (by decide)).trans w4_b8
  have w5_bc : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K5.w32 (by decide) (by decide)).trans w4_bc
  have w5_c0 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K5.w32 (by decide) (by decide)).trans w4_c0
  have w5_c4 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K5.w32 (by decide) (by decide)).trans w4_c4
  have w5_c8 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K5.w32 (by decide) (by decide)).trans w4_c8
  have w5_cc : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K5.w32 (by decide) (by decide)).trans w4_cc
  have w5_d0 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K5.w32 (by decide) (by decide)).trans w4_d0
  have w5_d4 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K5.w32 (by decide) (by decide)).trans w4_d4
  have w5_d8 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K5.w32 (by decide) (by decide)).trans w4_d8
  have w5_dc : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K5.w32 (by decide) (by decide)).trans w4_dc
  have w5_e0 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K5.w32 (by decide) (by decide)).trans w4_e0
  have w5_e4 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K5.w32 (by decide) (by decide)).trans w4_e4
  have w5_e8 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K5.w32 (by decide) (by decide)).trans w4_e8
  have w5_ec : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K5.w32 (by decide) (by decide)).trans w4_ec
  have w5_f0 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K5.w32 (by decide) (by decide)).trans w4_f0
  have w5_f4 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K5.w32 (by decide) (by decide)).trans w4_f4
  have w5_f8 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K5.w32 (by decide) (by decide)).trans w4_f8
  have w5_fc : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K5.w32 (by decide) (by decide)).trans w4_fc
  have w5_100 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K5.w32 (by decide) (by decide)).trans w4_100
  have w5_104 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K5.w32 (by decide) (by decide)).trans w4_104
  have w5_108 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K5.w32 (by decide) (by decide)).trans w4_108
  have w5_10c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K5.w32 (by decide) (by decide)).trans w4_10c
  have w5_110 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K5.w32 (by decide) (by decide)).trans w4_110
  have w5_114 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K5.w32 (by decide) (by decide)).trans w4_114
  have w5_118 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K5.w32 (by decide) (by decide)).trans w4_118
  have w5_11c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K5.w32 (by decide) (by decide)).trans w4_11c
  have w5_120 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K5.w32 (by decide) (by decide)).trans w4_120
  have w5_124 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K5.w32 (by decide) (by decide)).trans w4_124
  have w5_128 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K5.w32 (by decide) (by decide)).trans w4_128
  have w5_12c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K5.w32 (by decide) (by decide)).trans w4_12c
  have w5_130 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K5.w32 (by decide) (by decide)).trans w4_130
  have w5_320 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ulo := (K5.w32 (by decide) (by decide)).trans w4_320
  have w5_324 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = uhi := (K5.w32 (by decide) (by decide)).trans w4_324
  have w5_328 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = vlo := (K5.w32 (by decide) (by decide)).trans w4_328
  have b5_440 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) = es := (K5.b8 (by decide) (by decide)).trans b4_440
  have b5_1040 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = ds := (K5.b8 (by decide) (by decide)).trans b4_1040
  have b5_13a0 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = fs := (K5.b8 (by decide) (by decide)).trans b4_13a0
  have b5_14a0 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := (K5.b8 (by decide) (by decide)).trans b4_14a0
  have w5_32c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = vhi := by rw [W5, g4_17]
  have a5_240 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := (K5.acc (by decide) (by decide)).trans a4_240
  have a5_260 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := (K5.acc (by decide) (by decide)).trans a4_260
  have a5_280 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := (K5.acc (by decide) (by decide)).trans a4_280
  have a5_2a0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K5.acc (by decide) (by decide)).trans a4_2a0
  have a5_2c0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K5.acc (by decide) (by decide)).trans a4_2c0
  have a5_2e0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K5.acc (by decide) (by decide)).trans a4_2e0
  have a5_420 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = ev := (K5.acc (by decide) (by decide)).trans a4_420
  have a5_1020 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = dv := (K5.acc (by decide) (by decide)).trans a4_1020
  have a5_1380 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = fv := (K5.acc (by decide) (by decide)).trans a4_1380
  have a5_1480 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = gv := (K5.acc (by decide) (by decide)).trans a4_1480
  clear a4_1480 a4_1380 a4_1020 a4_420 a4_2e0 a4_2c0 a4_2a0 a4_280 a4_260 a4_240 w4_328 b4_14a0 b4_13a0 b4_1040 b4_440 w4_324 w4_320 w4_130 w4_12c w4_128 w4_124 w4_120 w4_11c w4_118 w4_114 w4_110 w4_10c w4_108 w4_104 w4_100 w4_fc w4_f8 w4_f4 w4_f0 w4_ec w4_e8 w4_e4 w4_e0 w4_dc w4_d8 w4_d4 w4_d0 w4_cc w4_c8 w4_c4 w4_c0 w4_bc w4_b8 w4_b4 w4_b0 w4_ac w4_a8 w4_a4 w4_a0 w4_9c w4_98 w4_94 w4_90 w4_8c w4_88 w4_84 w4_80 w4_7c w4_78 w4_70 w4_6c w4_68 w4_64 w4_60 w4_5c w4_58 w4_54 w4_50 w4_4c w4_48 w4_44 w4_40 w4_3c w4_38 w4_34 w4_30 w4_2c w4_28 w4_24 g4_31 g4_29 g4_27 g4_26 g4_25 g4_24 g4_23 g4_21 g4_19 g4_18 g4_17 g4_14 g4_12 g4_10 g4_8 g4_6 g4_5 g4_4 g4_3 g4_2 V4 E4 fR4 t4 rg4 W4 K4 fr4 s4 d4
  -- 0x1488: sw
  obtain ⟨n6, d6, s6, fr6, K6, W6, rg6⟩ := sv_sw F E5 s5 sv_at_1488 (off' := 0x148A) (c := 0x330)
    (by decide) (by rw [g5_10]; sv_addr) (by decide) (by decide)
  have t6 : Steps n0 n6 := t5.trans d6
  have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : SvCode n6.mem := E5.fr F fr6
  have V6 : SvSaves B n6.mem v := V5.keep K6 (by decide)
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [rg6 sp, g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg6 (3 : Fin 32), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg6 (4 : Fin 32), g5_4]
  have g6_5 : reg n6 (5 : Fin 32) = uhi := by rw [rg6 (5 : Fin 32), g5_5]
  have g6_6 : reg n6 (6 : Fin 32) = rhi := by rw [rg6 (6 : Fin 32), g5_6]
  have g6_8 : reg n6 (8 : Fin 32) = qlo := by rw [rg6 (8 : Fin 32), g5_8]
  have g6_10 : reg n6 a0 = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [rg6 a0, g5_10]
  have g6_12 : reg n6 a2 = rlo := by rw [rg6 a2, g5_12]
  have g6_14 : reg n6 a4 = ulo := by rw [rg6 a4, g5_14]
  have g6_17 : reg n6 a7 = vhi := by rw [rg6 a7, g5_17]
  have g6_18 : reg n6 (18 : Fin 32) = out := by rw [rg6 (18 : Fin 32), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [rg6 (19 : Fin 32), g5_19]
  have g6_21 : reg n6 (21 : Fin 32) = s5v := by rw [rg6 (21 : Fin 32), g5_21]
  have g6_23 : reg n6 (23 : Fin 32) = dlo := by rw [rg6 (23 : Fin 32), g5_23]
  have g6_24 : reg n6 (24 : Fin 32) = BitVec.ofNat 32 0x3FCC4268 := by rw [rg6 (24 : Fin 32), g5_24]
  have g6_25 : reg n6 (25 : Fin 32) = dhi := by rw [rg6 (25 : Fin 32), g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = x26 := by rw [rg6 (26 : Fin 32), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg6 (27 : Fin 32), g5_27]
  have g6_29 : reg n6 (29 : Fin 32) = qhi := by rw [rg6 (29 : Fin 32), g5_29]
  have g6_31 : reg n6 (31 : Fin 32) = vlo := by rw [rg6 (31 : Fin 32), g5_31]
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
  have w6_5c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 ns := (K6.w32 (by decide) (by decide)).trans w5_5c
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
  have w6_320 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ulo := (K6.w32 (by decide) (by decide)).trans w5_320
  have w6_324 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = uhi := (K6.w32 (by decide) (by decide)).trans w5_324
  have w6_328 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = vlo := (K6.w32 (by decide) (by decide)).trans w5_328
  have w6_32c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = vhi := (K6.w32 (by decide) (by decide)).trans w5_32c
  have b6_440 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) = es := (K6.b8 (by decide) (by decide)).trans b5_440
  have b6_1040 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = ds := (K6.b8 (by decide) (by decide)).trans b5_1040
  have b6_13a0 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = fs := (K6.b8 (by decide) (by decide)).trans b5_13a0
  have b6_14a0 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := (K6.b8 (by decide) (by decide)).trans b5_14a0
  have w6_330 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = qlo := by rw [W6, g5_8]
  have a6_240 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := (K6.acc (by decide) (by decide)).trans a5_240
  have a6_260 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := (K6.acc (by decide) (by decide)).trans a5_260
  have a6_280 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := (K6.acc (by decide) (by decide)).trans a5_280
  have a6_2a0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K6.acc (by decide) (by decide)).trans a5_2a0
  have a6_2c0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K6.acc (by decide) (by decide)).trans a5_2c0
  have a6_2e0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K6.acc (by decide) (by decide)).trans a5_2e0
  have a6_420 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = ev := (K6.acc (by decide) (by decide)).trans a5_420
  have a6_1020 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = dv := (K6.acc (by decide) (by decide)).trans a5_1020
  have a6_1380 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = fv := (K6.acc (by decide) (by decide)).trans a5_1380
  have a6_1480 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = gv := (K6.acc (by decide) (by decide)).trans a5_1480
  clear a5_1480 a5_1380 a5_1020 a5_420 a5_2e0 a5_2c0 a5_2a0 a5_280 a5_260 a5_240 w5_32c b5_14a0 b5_13a0 b5_1040 b5_440 w5_328 w5_324 w5_320 w5_130 w5_12c w5_128 w5_124 w5_120 w5_11c w5_118 w5_114 w5_110 w5_10c w5_108 w5_104 w5_100 w5_fc w5_f8 w5_f4 w5_f0 w5_ec w5_e8 w5_e4 w5_e0 w5_dc w5_d8 w5_d4 w5_d0 w5_cc w5_c8 w5_c4 w5_c0 w5_bc w5_b8 w5_b4 w5_b0 w5_ac w5_a8 w5_a4 w5_a0 w5_9c w5_98 w5_94 w5_90 w5_8c w5_88 w5_84 w5_80 w5_7c w5_78 w5_70 w5_6c w5_68 w5_64 w5_60 w5_5c w5_58 w5_54 w5_50 w5_4c w5_48 w5_44 w5_40 w5_3c w5_38 w5_34 w5_30 w5_2c w5_28 w5_24 g5_31 g5_29 g5_27 g5_26 g5_25 g5_24 g5_23 g5_21 g5_19 g5_18 g5_17 g5_14 g5_12 g5_10 g5_8 g5_6 g5_5 g5_4 g5_3 g5_2 V5 E5 fR5 t5 rg5 W5 K5 fr5 s5 d5
  -- 0x148A: sw
  obtain ⟨n7, d7, s7, fr7, K7, W7, rg7⟩ := sv_sw F E6 s6 sv_at_148a (off' := 0x148E) (c := 0x334)
    (by decide) (by rw [g6_10]; sv_addr) (by decide) (by decide)
  have t7 : Steps n0 n7 := t6.trans d7
  have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : SvCode n7.mem := E6.fr F fr7
  have V7 : SvSaves B n7.mem v := V6.keep K7 (by decide)
  have g7_2 : reg n7 sp = B + 0x21A0 := by rw [rg7 sp, g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg7 (3 : Fin 32), g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg7 (4 : Fin 32), g6_4]
  have g7_5 : reg n7 (5 : Fin 32) = uhi := by rw [rg7 (5 : Fin 32), g6_5]
  have g7_6 : reg n7 (6 : Fin 32) = rhi := by rw [rg7 (6 : Fin 32), g6_6]
  have g7_8 : reg n7 (8 : Fin 32) = qlo := by rw [rg7 (8 : Fin 32), g6_8]
  have g7_10 : reg n7 a0 = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [rg7 a0, g6_10]
  have g7_12 : reg n7 a2 = rlo := by rw [rg7 a2, g6_12]
  have g7_14 : reg n7 a4 = ulo := by rw [rg7 a4, g6_14]
  have g7_17 : reg n7 a7 = vhi := by rw [rg7 a7, g6_17]
  have g7_18 : reg n7 (18 : Fin 32) = out := by rw [rg7 (18 : Fin 32), g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [rg7 (19 : Fin 32), g6_19]
  have g7_21 : reg n7 (21 : Fin 32) = s5v := by rw [rg7 (21 : Fin 32), g6_21]
  have g7_23 : reg n7 (23 : Fin 32) = dlo := by rw [rg7 (23 : Fin 32), g6_23]
  have g7_24 : reg n7 (24 : Fin 32) = BitVec.ofNat 32 0x3FCC4268 := by rw [rg7 (24 : Fin 32), g6_24]
  have g7_25 : reg n7 (25 : Fin 32) = dhi := by rw [rg7 (25 : Fin 32), g6_25]
  have g7_26 : reg n7 (26 : Fin 32) = x26 := by rw [rg7 (26 : Fin 32), g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg7 (27 : Fin 32), g6_27]
  have g7_29 : reg n7 (29 : Fin 32) = qhi := by rw [rg7 (29 : Fin 32), g6_29]
  have g7_31 : reg n7 (31 : Fin 32) = vlo := by rw [rg7 (31 : Fin 32), g6_31]
  have w7_24 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K7.w32 (by decide) (by decide)).trans w6_24
  have w7_28 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K7.w32 (by decide) (by decide)).trans w6_28
  have w7_2c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K7.w32 (by decide) (by decide)).trans w6_2c
  have w7_30 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K7.w32 (by decide) (by decide)).trans w6_30
  have w7_34 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K7.w32 (by decide) (by decide)).trans w6_34
  have w7_38 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K7.w32 (by decide) (by decide)).trans w6_38
  have w7_3c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K7.w32 (by decide) (by decide)).trans w6_3c
  have w7_40 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K7.w32 (by decide) (by decide)).trans w6_40
  have w7_44 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K7.w32 (by decide) (by decide)).trans w6_44
  have w7_48 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K7.w32 (by decide) (by decide)).trans w6_48
  have w7_4c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K7.w32 (by decide) (by decide)).trans w6_4c
  have w7_50 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K7.w32 (by decide) (by decide)).trans w6_50
  have w7_54 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K7.w32 (by decide) (by decide)).trans w6_54
  have w7_58 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K7.w32 (by decide) (by decide)).trans w6_58
  have w7_5c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 ns := (K7.w32 (by decide) (by decide)).trans w6_5c
  have w7_60 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K7.w32 (by decide) (by decide)).trans w6_60
  have w7_64 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K7.w32 (by decide) (by decide)).trans w6_64
  have w7_68 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K7.w32 (by decide) (by decide)).trans w6_68
  have w7_6c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K7.w32 (by decide) (by decide)).trans w6_6c
  have w7_70 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K7.w32 (by decide) (by decide)).trans w6_70
  have w7_78 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := (K7.w32 (by decide) (by decide)).trans w6_78
  have w7_7c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K7.w32 (by decide) (by decide)).trans w6_7c
  have w7_80 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K7.w32 (by decide) (by decide)).trans w6_80
  have w7_84 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K7.w32 (by decide) (by decide)).trans w6_84
  have w7_88 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K7.w32 (by decide) (by decide)).trans w6_88
  have w7_8c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K7.w32 (by decide) (by decide)).trans w6_8c
  have w7_90 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K7.w32 (by decide) (by decide)).trans w6_90
  have w7_94 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K7.w32 (by decide) (by decide)).trans w6_94
  have w7_98 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K7.w32 (by decide) (by decide)).trans w6_98
  have w7_9c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K7.w32 (by decide) (by decide)).trans w6_9c
  have w7_a0 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K7.w32 (by decide) (by decide)).trans w6_a0
  have w7_a4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K7.w32 (by decide) (by decide)).trans w6_a4
  have w7_a8 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K7.w32 (by decide) (by decide)).trans w6_a8
  have w7_ac : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K7.w32 (by decide) (by decide)).trans w6_ac
  have w7_b0 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K7.w32 (by decide) (by decide)).trans w6_b0
  have w7_b4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K7.w32 (by decide) (by decide)).trans w6_b4
  have w7_b8 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K7.w32 (by decide) (by decide)).trans w6_b8
  have w7_bc : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K7.w32 (by decide) (by decide)).trans w6_bc
  have w7_c0 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K7.w32 (by decide) (by decide)).trans w6_c0
  have w7_c4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K7.w32 (by decide) (by decide)).trans w6_c4
  have w7_c8 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K7.w32 (by decide) (by decide)).trans w6_c8
  have w7_cc : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K7.w32 (by decide) (by decide)).trans w6_cc
  have w7_d0 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K7.w32 (by decide) (by decide)).trans w6_d0
  have w7_d4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K7.w32 (by decide) (by decide)).trans w6_d4
  have w7_d8 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K7.w32 (by decide) (by decide)).trans w6_d8
  have w7_dc : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K7.w32 (by decide) (by decide)).trans w6_dc
  have w7_e0 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K7.w32 (by decide) (by decide)).trans w6_e0
  have w7_e4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K7.w32 (by decide) (by decide)).trans w6_e4
  have w7_e8 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K7.w32 (by decide) (by decide)).trans w6_e8
  have w7_ec : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K7.w32 (by decide) (by decide)).trans w6_ec
  have w7_f0 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K7.w32 (by decide) (by decide)).trans w6_f0
  have w7_f4 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K7.w32 (by decide) (by decide)).trans w6_f4
  have w7_f8 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K7.w32 (by decide) (by decide)).trans w6_f8
  have w7_fc : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K7.w32 (by decide) (by decide)).trans w6_fc
  have w7_100 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K7.w32 (by decide) (by decide)).trans w6_100
  have w7_104 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K7.w32 (by decide) (by decide)).trans w6_104
  have w7_108 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K7.w32 (by decide) (by decide)).trans w6_108
  have w7_10c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K7.w32 (by decide) (by decide)).trans w6_10c
  have w7_110 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K7.w32 (by decide) (by decide)).trans w6_110
  have w7_114 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K7.w32 (by decide) (by decide)).trans w6_114
  have w7_118 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K7.w32 (by decide) (by decide)).trans w6_118
  have w7_11c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K7.w32 (by decide) (by decide)).trans w6_11c
  have w7_120 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K7.w32 (by decide) (by decide)).trans w6_120
  have w7_124 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K7.w32 (by decide) (by decide)).trans w6_124
  have w7_128 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K7.w32 (by decide) (by decide)).trans w6_128
  have w7_12c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K7.w32 (by decide) (by decide)).trans w6_12c
  have w7_130 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K7.w32 (by decide) (by decide)).trans w6_130
  have w7_320 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ulo := (K7.w32 (by decide) (by decide)).trans w6_320
  have w7_324 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = uhi := (K7.w32 (by decide) (by decide)).trans w6_324
  have w7_328 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = vlo := (K7.w32 (by decide) (by decide)).trans w6_328
  have w7_32c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = vhi := (K7.w32 (by decide) (by decide)).trans w6_32c
  have w7_330 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = qlo := (K7.w32 (by decide) (by decide)).trans w6_330
  have b7_440 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) = es := (K7.b8 (by decide) (by decide)).trans b6_440
  have b7_1040 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = ds := (K7.b8 (by decide) (by decide)).trans b6_1040
  have b7_13a0 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = fs := (K7.b8 (by decide) (by decide)).trans b6_13a0
  have b7_14a0 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := (K7.b8 (by decide) (by decide)).trans b6_14a0
  have w7_334 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = qhi := by rw [W7, g6_29]
  have a7_240 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := (K7.acc (by decide) (by decide)).trans a6_240
  have a7_260 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := (K7.acc (by decide) (by decide)).trans a6_260
  have a7_280 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := (K7.acc (by decide) (by decide)).trans a6_280
  have a7_2a0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K7.acc (by decide) (by decide)).trans a6_2a0
  have a7_2c0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K7.acc (by decide) (by decide)).trans a6_2c0
  have a7_2e0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K7.acc (by decide) (by decide)).trans a6_2e0
  have a7_420 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = ev := (K7.acc (by decide) (by decide)).trans a6_420
  have a7_1020 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = dv := (K7.acc (by decide) (by decide)).trans a6_1020
  have a7_1380 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = fv := (K7.acc (by decide) (by decide)).trans a6_1380
  have a7_1480 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = gv := (K7.acc (by decide) (by decide)).trans a6_1480
  clear a6_1480 a6_1380 a6_1020 a6_420 a6_2e0 a6_2c0 a6_2a0 a6_280 a6_260 a6_240 w6_330 b6_14a0 b6_13a0 b6_1040 b6_440 w6_32c w6_328 w6_324 w6_320 w6_130 w6_12c w6_128 w6_124 w6_120 w6_11c w6_118 w6_114 w6_110 w6_10c w6_108 w6_104 w6_100 w6_fc w6_f8 w6_f4 w6_f0 w6_ec w6_e8 w6_e4 w6_e0 w6_dc w6_d8 w6_d4 w6_d0 w6_cc w6_c8 w6_c4 w6_c0 w6_bc w6_b8 w6_b4 w6_b0 w6_ac w6_a8 w6_a4 w6_a0 w6_9c w6_98 w6_94 w6_90 w6_8c w6_88 w6_84 w6_80 w6_7c w6_78 w6_70 w6_6c w6_68 w6_64 w6_60 w6_5c w6_58 w6_54 w6_50 w6_4c w6_48 w6_44 w6_40 w6_3c w6_38 w6_34 w6_30 w6_2c w6_28 w6_24 g6_31 g6_29 g6_27 g6_26 g6_25 g6_24 g6_23 g6_21 g6_19 g6_18 g6_17 g6_14 g6_12 g6_10 g6_8 g6_6 g6_5 g6_4 g6_3 g6_2 V6 E6 fR6 t6 rg6 W6 K6 fr6 s6 d6
  -- 0x148E: sw
  obtain ⟨n8, d8, s8, fr8, K8, W8, rg8⟩ := sv_sw F E7 s7 sv_at_148e (off' := 0x1490) (c := 0x338)
    (by decide) (by rw [g7_10]; sv_addr) (by decide) (by decide)
  have t8 : Steps n0 n8 := t7.trans d8
  have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : SvCode n8.mem := E7.fr F fr8
  have V8 : SvSaves B n8.mem v := V7.keep K8 (by decide)
  have g8_2 : reg n8 sp = B + 0x21A0 := by rw [rg8 sp, g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg8 (3 : Fin 32), g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg8 (4 : Fin 32), g7_4]
  have g8_5 : reg n8 (5 : Fin 32) = uhi := by rw [rg8 (5 : Fin 32), g7_5]
  have g8_6 : reg n8 (6 : Fin 32) = rhi := by rw [rg8 (6 : Fin 32), g7_6]
  have g8_8 : reg n8 (8 : Fin 32) = qlo := by rw [rg8 (8 : Fin 32), g7_8]
  have g8_10 : reg n8 a0 = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [rg8 a0, g7_10]
  have g8_12 : reg n8 a2 = rlo := by rw [rg8 a2, g7_12]
  have g8_14 : reg n8 a4 = ulo := by rw [rg8 a4, g7_14]
  have g8_17 : reg n8 a7 = vhi := by rw [rg8 a7, g7_17]
  have g8_18 : reg n8 (18 : Fin 32) = out := by rw [rg8 (18 : Fin 32), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [rg8 (19 : Fin 32), g7_19]
  have g8_21 : reg n8 (21 : Fin 32) = s5v := by rw [rg8 (21 : Fin 32), g7_21]
  have g8_23 : reg n8 (23 : Fin 32) = dlo := by rw [rg8 (23 : Fin 32), g7_23]
  have g8_24 : reg n8 (24 : Fin 32) = BitVec.ofNat 32 0x3FCC4268 := by rw [rg8 (24 : Fin 32), g7_24]
  have g8_25 : reg n8 (25 : Fin 32) = dhi := by rw [rg8 (25 : Fin 32), g7_25]
  have g8_26 : reg n8 (26 : Fin 32) = x26 := by rw [rg8 (26 : Fin 32), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg8 (27 : Fin 32), g7_27]
  have g8_29 : reg n8 (29 : Fin 32) = qhi := by rw [rg8 (29 : Fin 32), g7_29]
  have g8_31 : reg n8 (31 : Fin 32) = vlo := by rw [rg8 (31 : Fin 32), g7_31]
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
  have w8_5c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 ns := (K8.w32 (by decide) (by decide)).trans w7_5c
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
  have w8_320 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ulo := (K8.w32 (by decide) (by decide)).trans w7_320
  have w8_324 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = uhi := (K8.w32 (by decide) (by decide)).trans w7_324
  have w8_328 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = vlo := (K8.w32 (by decide) (by decide)).trans w7_328
  have w8_32c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = vhi := (K8.w32 (by decide) (by decide)).trans w7_32c
  have w8_330 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = qlo := (K8.w32 (by decide) (by decide)).trans w7_330
  have w8_334 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = qhi := (K8.w32 (by decide) (by decide)).trans w7_334
  have b8_440 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) = es := (K8.b8 (by decide) (by decide)).trans b7_440
  have b8_1040 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = ds := (K8.b8 (by decide) (by decide)).trans b7_1040
  have b8_13a0 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = fs := (K8.b8 (by decide) (by decide)).trans b7_13a0
  have b8_14a0 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := (K8.b8 (by decide) (by decide)).trans b7_14a0
  have w8_338 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = rlo := by rw [W8, g7_12]
  have a8_240 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := (K8.acc (by decide) (by decide)).trans a7_240
  have a8_260 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := (K8.acc (by decide) (by decide)).trans a7_260
  have a8_280 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := (K8.acc (by decide) (by decide)).trans a7_280
  have a8_2a0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K8.acc (by decide) (by decide)).trans a7_2a0
  have a8_2c0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K8.acc (by decide) (by decide)).trans a7_2c0
  have a8_2e0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K8.acc (by decide) (by decide)).trans a7_2e0
  have a8_420 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = ev := (K8.acc (by decide) (by decide)).trans a7_420
  have a8_1020 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = dv := (K8.acc (by decide) (by decide)).trans a7_1020
  have a8_1380 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = fv := (K8.acc (by decide) (by decide)).trans a7_1380
  have a8_1480 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = gv := (K8.acc (by decide) (by decide)).trans a7_1480
  clear a7_1480 a7_1380 a7_1020 a7_420 a7_2e0 a7_2c0 a7_2a0 a7_280 a7_260 a7_240 w7_334 b7_14a0 b7_13a0 b7_1040 b7_440 w7_330 w7_32c w7_328 w7_324 w7_320 w7_130 w7_12c w7_128 w7_124 w7_120 w7_11c w7_118 w7_114 w7_110 w7_10c w7_108 w7_104 w7_100 w7_fc w7_f8 w7_f4 w7_f0 w7_ec w7_e8 w7_e4 w7_e0 w7_dc w7_d8 w7_d4 w7_d0 w7_cc w7_c8 w7_c4 w7_c0 w7_bc w7_b8 w7_b4 w7_b0 w7_ac w7_a8 w7_a4 w7_a0 w7_9c w7_98 w7_94 w7_90 w7_8c w7_88 w7_84 w7_80 w7_7c w7_78 w7_70 w7_6c w7_68 w7_64 w7_60 w7_5c w7_58 w7_54 w7_50 w7_4c w7_48 w7_44 w7_40 w7_3c w7_38 w7_34 w7_30 w7_2c w7_28 w7_24 g7_31 g7_29 g7_27 g7_26 g7_25 g7_24 g7_23 g7_21 g7_19 g7_18 g7_17 g7_14 g7_12 g7_10 g7_8 g7_6 g7_5 g7_4 g7_3 g7_2 V7 E7 fR7 t7 rg7 W7 K7 fr7 s7 d7
  -- 0x1490: sw
  obtain ⟨n9, d9, s9, fr9, K9, W9, rg9⟩ := sv_sw F E8 s8 sv_at_1490 (off' := 0x1494) (c := 0x33C)
    (by decide) (by rw [g8_10]; sv_addr) (by decide) (by decide)
  have t9 : Steps n0 n9 := t8.trans d9
  have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : SvCode n9.mem := E8.fr F fr9
  have V9 : SvSaves B n9.mem v := V8.keep K9 (by decide)
  have g9_2 : reg n9 sp = B + 0x21A0 := by rw [rg9 sp, g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg9 (3 : Fin 32), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg9 (4 : Fin 32), g8_4]
  have g9_5 : reg n9 (5 : Fin 32) = uhi := by rw [rg9 (5 : Fin 32), g8_5]
  have g9_6 : reg n9 (6 : Fin 32) = rhi := by rw [rg9 (6 : Fin 32), g8_6]
  have g9_8 : reg n9 (8 : Fin 32) = qlo := by rw [rg9 (8 : Fin 32), g8_8]
  have g9_10 : reg n9 a0 = B + 0x21A0 + BitVec.ofNat 32 0x300 := by rw [rg9 a0, g8_10]
  have g9_12 : reg n9 a2 = rlo := by rw [rg9 a2, g8_12]
  have g9_14 : reg n9 a4 = ulo := by rw [rg9 a4, g8_14]
  have g9_17 : reg n9 a7 = vhi := by rw [rg9 a7, g8_17]
  have g9_18 : reg n9 (18 : Fin 32) = out := by rw [rg9 (18 : Fin 32), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [rg9 (19 : Fin 32), g8_19]
  have g9_21 : reg n9 (21 : Fin 32) = s5v := by rw [rg9 (21 : Fin 32), g8_21]
  have g9_23 : reg n9 (23 : Fin 32) = dlo := by rw [rg9 (23 : Fin 32), g8_23]
  have g9_24 : reg n9 (24 : Fin 32) = BitVec.ofNat 32 0x3FCC4268 := by rw [rg9 (24 : Fin 32), g8_24]
  have g9_25 : reg n9 (25 : Fin 32) = dhi := by rw [rg9 (25 : Fin 32), g8_25]
  have g9_26 : reg n9 (26 : Fin 32) = x26 := by rw [rg9 (26 : Fin 32), g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg9 (27 : Fin 32), g8_27]
  have g9_29 : reg n9 (29 : Fin 32) = qhi := by rw [rg9 (29 : Fin 32), g8_29]
  have g9_31 : reg n9 (31 : Fin 32) = vlo := by rw [rg9 (31 : Fin 32), g8_31]
  have w9_24 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K9.w32 (by decide) (by decide)).trans w8_24
  have w9_28 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K9.w32 (by decide) (by decide)).trans w8_28
  have w9_2c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K9.w32 (by decide) (by decide)).trans w8_2c
  have w9_30 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K9.w32 (by decide) (by decide)).trans w8_30
  have w9_34 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K9.w32 (by decide) (by decide)).trans w8_34
  have w9_38 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K9.w32 (by decide) (by decide)).trans w8_38
  have w9_3c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K9.w32 (by decide) (by decide)).trans w8_3c
  have w9_40 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K9.w32 (by decide) (by decide)).trans w8_40
  have w9_44 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K9.w32 (by decide) (by decide)).trans w8_44
  have w9_48 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K9.w32 (by decide) (by decide)).trans w8_48
  have w9_4c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K9.w32 (by decide) (by decide)).trans w8_4c
  have w9_50 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K9.w32 (by decide) (by decide)).trans w8_50
  have w9_54 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K9.w32 (by decide) (by decide)).trans w8_54
  have w9_58 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K9.w32 (by decide) (by decide)).trans w8_58
  have w9_5c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 ns := (K9.w32 (by decide) (by decide)).trans w8_5c
  have w9_60 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K9.w32 (by decide) (by decide)).trans w8_60
  have w9_64 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K9.w32 (by decide) (by decide)).trans w8_64
  have w9_68 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K9.w32 (by decide) (by decide)).trans w8_68
  have w9_6c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K9.w32 (by decide) (by decide)).trans w8_6c
  have w9_70 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K9.w32 (by decide) (by decide)).trans w8_70
  have w9_78 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := (K9.w32 (by decide) (by decide)).trans w8_78
  have w9_7c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K9.w32 (by decide) (by decide)).trans w8_7c
  have w9_80 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K9.w32 (by decide) (by decide)).trans w8_80
  have w9_84 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K9.w32 (by decide) (by decide)).trans w8_84
  have w9_88 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K9.w32 (by decide) (by decide)).trans w8_88
  have w9_8c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K9.w32 (by decide) (by decide)).trans w8_8c
  have w9_90 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K9.w32 (by decide) (by decide)).trans w8_90
  have w9_94 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K9.w32 (by decide) (by decide)).trans w8_94
  have w9_98 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K9.w32 (by decide) (by decide)).trans w8_98
  have w9_9c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K9.w32 (by decide) (by decide)).trans w8_9c
  have w9_a0 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K9.w32 (by decide) (by decide)).trans w8_a0
  have w9_a4 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K9.w32 (by decide) (by decide)).trans w8_a4
  have w9_a8 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K9.w32 (by decide) (by decide)).trans w8_a8
  have w9_ac : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K9.w32 (by decide) (by decide)).trans w8_ac
  have w9_b0 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K9.w32 (by decide) (by decide)).trans w8_b0
  have w9_b4 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K9.w32 (by decide) (by decide)).trans w8_b4
  have w9_b8 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K9.w32 (by decide) (by decide)).trans w8_b8
  have w9_bc : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K9.w32 (by decide) (by decide)).trans w8_bc
  have w9_c0 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K9.w32 (by decide) (by decide)).trans w8_c0
  have w9_c4 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K9.w32 (by decide) (by decide)).trans w8_c4
  have w9_c8 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K9.w32 (by decide) (by decide)).trans w8_c8
  have w9_cc : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K9.w32 (by decide) (by decide)).trans w8_cc
  have w9_d0 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K9.w32 (by decide) (by decide)).trans w8_d0
  have w9_d4 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K9.w32 (by decide) (by decide)).trans w8_d4
  have w9_d8 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K9.w32 (by decide) (by decide)).trans w8_d8
  have w9_dc : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K9.w32 (by decide) (by decide)).trans w8_dc
  have w9_e0 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K9.w32 (by decide) (by decide)).trans w8_e0
  have w9_e4 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K9.w32 (by decide) (by decide)).trans w8_e4
  have w9_e8 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K9.w32 (by decide) (by decide)).trans w8_e8
  have w9_ec : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K9.w32 (by decide) (by decide)).trans w8_ec
  have w9_f0 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K9.w32 (by decide) (by decide)).trans w8_f0
  have w9_f4 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K9.w32 (by decide) (by decide)).trans w8_f4
  have w9_f8 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K9.w32 (by decide) (by decide)).trans w8_f8
  have w9_fc : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K9.w32 (by decide) (by decide)).trans w8_fc
  have w9_100 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K9.w32 (by decide) (by decide)).trans w8_100
  have w9_104 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K9.w32 (by decide) (by decide)).trans w8_104
  have w9_108 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K9.w32 (by decide) (by decide)).trans w8_108
  have w9_10c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K9.w32 (by decide) (by decide)).trans w8_10c
  have w9_110 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K9.w32 (by decide) (by decide)).trans w8_110
  have w9_114 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K9.w32 (by decide) (by decide)).trans w8_114
  have w9_118 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K9.w32 (by decide) (by decide)).trans w8_118
  have w9_11c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K9.w32 (by decide) (by decide)).trans w8_11c
  have w9_120 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K9.w32 (by decide) (by decide)).trans w8_120
  have w9_124 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K9.w32 (by decide) (by decide)).trans w8_124
  have w9_128 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K9.w32 (by decide) (by decide)).trans w8_128
  have w9_12c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K9.w32 (by decide) (by decide)).trans w8_12c
  have w9_130 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K9.w32 (by decide) (by decide)).trans w8_130
  have w9_320 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ulo := (K9.w32 (by decide) (by decide)).trans w8_320
  have w9_324 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = uhi := (K9.w32 (by decide) (by decide)).trans w8_324
  have w9_328 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = vlo := (K9.w32 (by decide) (by decide)).trans w8_328
  have w9_32c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = vhi := (K9.w32 (by decide) (by decide)).trans w8_32c
  have w9_330 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = qlo := (K9.w32 (by decide) (by decide)).trans w8_330
  have w9_334 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = qhi := (K9.w32 (by decide) (by decide)).trans w8_334
  have w9_338 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = rlo := (K9.w32 (by decide) (by decide)).trans w8_338
  have b9_440 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) = es := (K9.b8 (by decide) (by decide)).trans b8_440
  have b9_1040 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = ds := (K9.b8 (by decide) (by decide)).trans b8_1040
  have b9_13a0 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = fs := (K9.b8 (by decide) (by decide)).trans b8_13a0
  have b9_14a0 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := (K9.b8 (by decide) (by decide)).trans b8_14a0
  have w9_33c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = rhi := by rw [W9, g8_6]
  have a9_240 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := (K9.acc (by decide) (by decide)).trans a8_240
  have a9_260 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := (K9.acc (by decide) (by decide)).trans a8_260
  have a9_280 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := (K9.acc (by decide) (by decide)).trans a8_280
  have a9_2a0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K9.acc (by decide) (by decide)).trans a8_2a0
  have a9_2c0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K9.acc (by decide) (by decide)).trans a8_2c0
  have a9_2e0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K9.acc (by decide) (by decide)).trans a8_2e0
  have a9_420 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = ev := (K9.acc (by decide) (by decide)).trans a8_420
  have a9_1020 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = dv := (K9.acc (by decide) (by decide)).trans a8_1020
  have a9_1380 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = fv := (K9.acc (by decide) (by decide)).trans a8_1380
  have a9_1480 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = gv := (K9.acc (by decide) (by decide)).trans a8_1480
  clear a8_1480 a8_1380 a8_1020 a8_420 a8_2e0 a8_2c0 a8_2a0 a8_280 a8_260 a8_240 w8_338 b8_14a0 b8_13a0 b8_1040 b8_440 w8_334 w8_330 w8_32c w8_328 w8_324 w8_320 w8_130 w8_12c w8_128 w8_124 w8_120 w8_11c w8_118 w8_114 w8_110 w8_10c w8_108 w8_104 w8_100 w8_fc w8_f8 w8_f4 w8_f0 w8_ec w8_e8 w8_e4 w8_e0 w8_dc w8_d8 w8_d4 w8_d0 w8_cc w8_c8 w8_c4 w8_c0 w8_bc w8_b8 w8_b4 w8_b0 w8_ac w8_a8 w8_a4 w8_a0 w8_9c w8_98 w8_94 w8_90 w8_8c w8_88 w8_84 w8_80 w8_7c w8_78 w8_70 w8_6c w8_68 w8_64 w8_60 w8_5c w8_58 w8_54 w8_50 w8_4c w8_48 w8_44 w8_40 w8_3c w8_38 w8_34 w8_30 w8_2c w8_28 w8_24 g8_31 g8_29 g8_27 g8_26 g8_25 g8_24 g8_23 g8_21 g8_19 g8_18 g8_17 g8_14 g8_12 g8_10 g8_8 g8_6 g8_5 g8_4 g8_3 g8_2 V8 E8 fR8 t8 rg8 W8 K8 fr8 s8 d8
  -- 0x1494
  obtain ⟨n10, c10, u10⟩ := s9.block svIvB1494 E9.self svIvB1494_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have s10 : St n10.mem SV n10 0x14AE (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have rb10 : ∀ q, reg n10 q = (runBlock svIvB1494 (n9.mem, reg n9)).2 q := fun q => by rw [u10.regs]
  have fr10 : ∀ x, SvR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
  have t10 : Steps n0 n10 := t9.trans c10
  have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : SvCode n10.mem := E9.fr F fr10
  have V10 : SvSaves B n10.mem v := V9.same m10
  have g10_2 : reg n10 sp = B + 0x21A0 := by
    rw [rb10, runBlock_reg _ _ _ sp s9.zero (by decide), g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb10, runBlock_reg _ _ _ (3 : Fin 32) s9.zero (by decide), g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb10, runBlock_reg _ _ _ (4 : Fin 32) s9.zero (by decide), g9_4]
  have g10_5 : reg n10 (5 : Fin 32) = uhi := by
    rw [rb10, runBlock_reg _ _ _ (5 : Fin 32) s9.zero (by decide), g9_5]
  have g10_6 : reg n10 (6 : Fin 32) = rhi := by
    rw [rb10, runBlock_reg _ _ _ (6 : Fin 32) s9.zero (by decide), g9_6]
  have g10_8 : reg n10 (8 : Fin 32) = qlo := by
    rw [rb10, runBlock_reg _ _ _ (8 : Fin 32) s9.zero (by decide), g9_8]
  have g10_14 : reg n10 a4 = ulo := by
    rw [rb10, runBlock_reg _ _ _ a4 s9.zero (by decide), g9_14]
  have g10_17 : reg n10 a7 = vhi := by
    rw [rb10, runBlock_reg _ _ _ a7 s9.zero (by decide), g9_17]
  have g10_18 : reg n10 (18 : Fin 32) = out := by
    rw [rb10, runBlock_reg _ _ _ (18 : Fin 32) s9.zero (by decide), g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = bp := by
    rw [rb10, runBlock_reg _ _ _ (19 : Fin 32) s9.zero (by decide), g9_19]
  have g10_21 : reg n10 (21 : Fin 32) = s5v := by
    rw [rb10, runBlock_reg _ _ _ (21 : Fin 32) s9.zero (by decide), g9_21]
  have g10_23 : reg n10 (23 : Fin 32) = dlo := by
    rw [rb10, runBlock_reg _ _ _ (23 : Fin 32) s9.zero (by decide), g9_23]
  have g10_24 : reg n10 (24 : Fin 32) = BitVec.ofNat 32 0x3FCC4268 := by
    rw [rb10, runBlock_reg _ _ _ (24 : Fin 32) s9.zero (by decide), g9_24]
  have g10_25 : reg n10 (25 : Fin 32) = dhi := by
    rw [rb10, runBlock_reg _ _ _ (25 : Fin 32) s9.zero (by decide), g9_25]
  have g10_26 : reg n10 (26 : Fin 32) = x26 := by
    rw [rb10, runBlock_reg _ _ _ (26 : Fin 32) s9.zero (by decide), g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb10, runBlock_reg _ _ _ (27 : Fin 32) s9.zero (by decide), g9_27]
  have g10_29 : reg n10 (29 : Fin 32) = qhi := by
    rw [rb10, runBlock_reg _ _ _ (29 : Fin 32) s9.zero (by decide), g9_29]
  have g10_31 : reg n10 (31 : Fin 32) = vlo := by
    rw [rb10, runBlock_reg _ _ _ (31 : Fin 32) s9.zero (by decide), g9_31]
  have g10_10 : reg n10 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, svIvB1494, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g9_2, g9_3, g9_4, g9_5, g9_6, g9_8, g9_10, g9_12, g9_14, g9_17, g9_18, g9_19, g9_21, g9_23, g9_24, g9_25, g9_26, g9_27, g9_29, g9_31, s9.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g10_11 : reg n10 a1 = B + 0x21A0 + BitVec.ofNat 32 0x1380 := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, svIvB1494, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g9_2, g9_3, g9_4, g9_5, g9_6, g9_8, g9_10, g9_12, g9_14, g9_17, g9_18, g9_19, g9_21, g9_23, g9_24, g9_25, g9_26, g9_27, g9_29, g9_31, s9.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g10_12 : reg n10 a2 = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, svIvB1494, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g9_2, g9_3, g9_4, g9_5, g9_6, g9_8, g9_10, g9_12, g9_14, g9_17, g9_18, g9_19, g9_21, g9_23, g9_24, g9_25, g9_26, g9_27, g9_29, g9_31, s9.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g10_13 : reg n10 a3 = B + 0x21A0 + BitVec.ofNat 32 0x320 := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, svIvB1494, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g9_2, g9_3, g9_4, g9_5, g9_6, g9_8, g9_10, g9_12, g9_14, g9_17, g9_18, g9_19, g9_21, g9_23, g9_24, g9_25, g9_26, g9_27, g9_29, g9_31, s9.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w10_24 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m10]; exact w9_24
  have w10_28 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m10]; exact w9_28
  have w10_2c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m10]; exact w9_2c
  have w10_30 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m10]; exact w9_30
  have w10_34 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m10]; exact w9_34
  have w10_38 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m10]; exact w9_38
  have w10_3c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m10]; exact w9_3c
  have w10_40 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m10]; exact w9_40
  have w10_44 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m10]; exact w9_44
  have w10_48 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m10]; exact w9_48
  have w10_4c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m10]; exact w9_4c
  have w10_50 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m10]; exact w9_50
  have w10_54 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m10]; exact w9_54
  have w10_58 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m10]; exact w9_58
  have w10_5c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 ns := by rw [m10]; exact w9_5c
  have w10_60 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m10]; exact w9_60
  have w10_64 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m10]; exact w9_64
  have w10_68 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m10]; exact w9_68
  have w10_6c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m10]; exact w9_6c
  have w10_70 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m10]; exact w9_70
  have w10_78 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m10]; exact w9_78
  have w10_7c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m10]; exact w9_7c
  have w10_80 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m10]; exact w9_80
  have w10_84 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m10]; exact w9_84
  have w10_88 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m10]; exact w9_88
  have w10_8c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m10]; exact w9_8c
  have w10_90 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m10]; exact w9_90
  have w10_94 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m10]; exact w9_94
  have w10_98 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m10]; exact w9_98
  have w10_9c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m10]; exact w9_9c
  have w10_a0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m10]; exact w9_a0
  have w10_a4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m10]; exact w9_a4
  have w10_a8 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m10]; exact w9_a8
  have w10_ac : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m10]; exact w9_ac
  have w10_b0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m10]; exact w9_b0
  have w10_b4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m10]; exact w9_b4
  have w10_b8 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m10]; exact w9_b8
  have w10_bc : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m10]; exact w9_bc
  have w10_c0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m10]; exact w9_c0
  have w10_c4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m10]; exact w9_c4
  have w10_c8 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m10]; exact w9_c8
  have w10_cc : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m10]; exact w9_cc
  have w10_d0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m10]; exact w9_d0
  have w10_d4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m10]; exact w9_d4
  have w10_d8 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m10]; exact w9_d8
  have w10_dc : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m10]; exact w9_dc
  have w10_e0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m10]; exact w9_e0
  have w10_e4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m10]; exact w9_e4
  have w10_e8 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m10]; exact w9_e8
  have w10_ec : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m10]; exact w9_ec
  have w10_f0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m10]; exact w9_f0
  have w10_f4 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m10]; exact w9_f4
  have w10_f8 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m10]; exact w9_f8
  have w10_fc : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m10]; exact w9_fc
  have w10_100 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m10]; exact w9_100
  have w10_104 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m10]; exact w9_104
  have w10_108 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m10]; exact w9_108
  have w10_10c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m10]; exact w9_10c
  have w10_110 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m10]; exact w9_110
  have w10_114 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m10]; exact w9_114
  have w10_118 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m10]; exact w9_118
  have w10_11c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m10]; exact w9_11c
  have w10_120 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m10]; exact w9_120
  have w10_124 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m10]; exact w9_124
  have w10_128 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m10]; exact w9_128
  have w10_12c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m10]; exact w9_12c
  have w10_130 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m10]; exact w9_130
  have w10_320 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ulo := by rw [m10]; exact w9_320
  have w10_324 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = uhi := by rw [m10]; exact w9_324
  have w10_328 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = vlo := by rw [m10]; exact w9_328
  have w10_32c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = vhi := by rw [m10]; exact w9_32c
  have w10_330 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = qlo := by rw [m10]; exact w9_330
  have w10_334 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = qhi := by rw [m10]; exact w9_334
  have w10_338 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = rlo := by rw [m10]; exact w9_338
  have w10_33c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = rhi := by rw [m10]; exact w9_33c
  have b10_440 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) = es := by rw [m10]; exact b9_440
  have b10_1040 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = ds := by rw [m10]; exact b9_1040
  have b10_13a0 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = fs := by rw [m10]; exact b9_13a0
  have b10_14a0 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := by rw [m10]; exact b9_14a0
  have a10_240 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m10]; exact a9_240
  have a10_260 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m10]; exact a9_260
  have a10_280 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m10]; exact a9_280
  have a10_2a0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m10]; exact a9_2a0
  have a10_2c0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m10]; exact a9_2c0
  have a10_2e0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m10]; exact a9_2e0
  have a10_420 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = ev := by rw [m10]; exact a9_420
  have a10_1020 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = dv := by rw [m10]; exact a9_1020
  have a10_1380 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = fv := by rw [m10]; exact a9_1380
  have a10_1480 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = gv := by rw [m10]; exact a9_1480
  clear a9_1480 a9_1380 a9_1020 a9_420 a9_2e0 a9_2c0 a9_2a0 a9_280 a9_260 a9_240 w9_33c b9_14a0 b9_13a0 b9_1040 b9_440 w9_338 w9_334 w9_330 w9_32c w9_328 w9_324 w9_320 w9_130 w9_12c w9_128 w9_124 w9_120 w9_11c w9_118 w9_114 w9_110 w9_10c w9_108 w9_104 w9_100 w9_fc w9_f8 w9_f4 w9_f0 w9_ec w9_e8 w9_e4 w9_e0 w9_dc w9_d8 w9_d4 w9_d0 w9_cc w9_c8 w9_c4 w9_c0 w9_bc w9_b8 w9_b4 w9_b0 w9_ac w9_a8 w9_a4 w9_a0 w9_9c w9_98 w9_94 w9_90 w9_8c w9_88 w9_84 w9_80 w9_7c w9_78 w9_70 w9_6c w9_68 w9_64 w9_60 w9_5c w9_58 w9_54 w9_50 w9_4c w9_48 w9_44 w9_40 w9_3c w9_38 w9_34 w9_30 w9_2c w9_28 w9_24 g9_31 g9_29 g9_27 g9_26 g9_25 g9_24 g9_23 g9_21 g9_19 g9_18 g9_17 g9_14 g9_12 g9_10 g9_8 g9_6 g9_5 g9_4 g9_3 g9_2 V9 E9 fR9 t9 rg9 W9 K9 fr9 s9 d9
  -- 0x14AE: lw
  obtain ⟨n11, d11, u11⟩ := s10.lw E10.self sv_at_14ae (off' := 0x14B0) (by decide)
    (by rw [g10_2, show B + 0x21A0 + 0x5C = B + 0x21A0 + BitVec.ofNat 32 0x5C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s11 : St n11.mem SV n11 0x14B0 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
  have t11 : Steps n0 n11 := t10.trans (.single d11)
  have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : SvCode n11.mem := E10.fr F fr11
  have V11 : SvSaves B n11.mem v := V10.same m11
  have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, upd_ne (by decide) (by decide), g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, upd_ne (by decide) (by decide), g10_4]
  have g11_5 : reg n11 (5 : Fin 32) = uhi := by rw [u11.regs, upd_ne (by decide) (by decide), g10_5]
  have g11_6 : reg n11 (6 : Fin 32) = rhi := by rw [u11.regs, upd_ne (by decide) (by decide), g10_6]
  have g11_10 : reg n11 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_10]
  have g11_11 : reg n11 a1 = B + 0x21A0 + BitVec.ofNat 32 0x1380 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_11]
  have g11_12 : reg n11 a2 = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_12]
  have g11_13 : reg n11 a3 = B + 0x21A0 + BitVec.ofNat 32 0x320 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_13]
  have g11_14 : reg n11 a4 = ulo := by rw [u11.regs, upd_ne (by decide) (by decide), g10_14]
  have g11_17 : reg n11 a7 = vhi := by rw [u11.regs, upd_ne (by decide) (by decide), g10_17]
  have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, upd_ne (by decide) (by decide), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_19]
  have g11_21 : reg n11 (21 : Fin 32) = s5v := by rw [u11.regs, upd_ne (by decide) (by decide), g10_21]
  have g11_23 : reg n11 (23 : Fin 32) = dlo := by rw [u11.regs, upd_ne (by decide) (by decide), g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = BitVec.ofNat 32 0x3FCC4268 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_24]
  have g11_25 : reg n11 (25 : Fin 32) = dhi := by rw [u11.regs, upd_ne (by decide) (by decide), g10_25]
  have g11_26 : reg n11 (26 : Fin 32) = x26 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_27]
  have g11_29 : reg n11 (29 : Fin 32) = qhi := by rw [u11.regs, upd_ne (by decide) (by decide), g10_29]
  have g11_31 : reg n11 (31 : Fin 32) = vlo := by rw [u11.regs, upd_ne (by decide) (by decide), g10_31]
  have g11_8 : reg n11 (8 : Fin 32) = BitVec.ofNat 32 ns := by
    rw [u11.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g10_2, show B + 0x21A0 + 0x5C = B + 0x21A0 + BitVec.ofNat 32 0x5C by sv_addr, w10_5c]
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
  have w11_5c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 ns := by rw [m11]; exact w10_5c
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
  have w11_320 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ulo := by rw [m11]; exact w10_320
  have w11_324 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = uhi := by rw [m11]; exact w10_324
  have w11_328 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = vlo := by rw [m11]; exact w10_328
  have w11_32c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = vhi := by rw [m11]; exact w10_32c
  have w11_330 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = qlo := by rw [m11]; exact w10_330
  have w11_334 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = qhi := by rw [m11]; exact w10_334
  have w11_338 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = rlo := by rw [m11]; exact w10_338
  have w11_33c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = rhi := by rw [m11]; exact w10_33c
  have b11_440 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) = es := by rw [m11]; exact b10_440
  have b11_1040 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = ds := by rw [m11]; exact b10_1040
  have b11_13a0 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = fs := by rw [m11]; exact b10_13a0
  have b11_14a0 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := by rw [m11]; exact b10_14a0
  have a11_240 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m11]; exact a10_240
  have a11_260 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m11]; exact a10_260
  have a11_280 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m11]; exact a10_280
  have a11_2a0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m11]; exact a10_2a0
  have a11_2c0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m11]; exact a10_2c0
  have a11_2e0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m11]; exact a10_2e0
  have a11_420 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = ev := by rw [m11]; exact a10_420
  have a11_1020 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = dv := by rw [m11]; exact a10_1020
  have a11_1380 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = fv := by rw [m11]; exact a10_1380
  have a11_1480 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = gv := by rw [m11]; exact a10_1480
  clear a10_1480 a10_1380 a10_1020 a10_420 a10_2e0 a10_2c0 a10_2a0 a10_280 a10_260 a10_240 b10_14a0 b10_13a0 b10_1040 b10_440 w10_33c w10_338 w10_334 w10_330 w10_32c w10_328 w10_324 w10_320 w10_130 w10_12c w10_128 w10_124 w10_120 w10_11c w10_118 w10_114 w10_110 w10_10c w10_108 w10_104 w10_100 w10_fc w10_f8 w10_f4 w10_f0 w10_ec w10_e8 w10_e4 w10_e0 w10_dc w10_d8 w10_d4 w10_d0 w10_cc w10_c8 w10_c4 w10_c0 w10_bc w10_b8 w10_b4 w10_b0 w10_ac w10_a8 w10_a4 w10_a0 w10_9c w10_98 w10_94 w10_90 w10_8c w10_88 w10_84 w10_80 w10_7c w10_78 w10_70 w10_6c w10_68 w10_64 w10_60 w10_5c w10_58 w10_54 w10_50 w10_4c w10_48 w10_44 w10_40 w10_3c w10_38 w10_34 w10_30 w10_2c w10_28 w10_24 g10_13 g10_12 g10_11 g10_10 g10_31 g10_29 g10_27 g10_26 g10_25 g10_24 g10_23 g10_21 g10_19 g10_18 g10_17 g10_14 g10_8 g10_6 g10_5 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 rb10 s10 m10 u10 c10
  -- 0x14B0
  obtain ⟨n12, c12, u12⟩ := s11.block svIvB14b0 E11.self svIvB14b0_end
    ⟨trivial, trivial⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have s12 : St n12.mem SV n12 0x14B2 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have rb12 : ∀ q, reg n12 q = (runBlock svIvB14b0 (n11.mem, reg n11)).2 q := fun q => by rw [u12.regs]
  have fr12 : ∀ x, SvR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
  have t12 : Steps n0 n12 := t11.trans c12
  have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : SvCode n12.mem := E11.fr F fr12
  have V12 : SvSaves B n12.mem v := V11.same m12
  have g12_2 : reg n12 sp = B + 0x21A0 := by
    rw [rb12, runBlock_reg _ _ _ sp s11.zero (by decide), g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb12, runBlock_reg _ _ _ (3 : Fin 32) s11.zero (by decide), g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb12, runBlock_reg _ _ _ (4 : Fin 32) s11.zero (by decide), g11_4]
  have g12_5 : reg n12 (5 : Fin 32) = uhi := by
    rw [rb12, runBlock_reg _ _ _ (5 : Fin 32) s11.zero (by decide), g11_5]
  have g12_6 : reg n12 (6 : Fin 32) = rhi := by
    rw [rb12, runBlock_reg _ _ _ (6 : Fin 32) s11.zero (by decide), g11_6]
  have g12_8 : reg n12 (8 : Fin 32) = BitVec.ofNat 32 ns := by
    rw [rb12, runBlock_reg _ _ _ (8 : Fin 32) s11.zero (by decide), g11_8]
  have g12_10 : reg n12 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb12, runBlock_reg _ _ _ a0 s11.zero (by decide), g11_10]
  have g12_11 : reg n12 a1 = B + 0x21A0 + BitVec.ofNat 32 0x1380 := by
    rw [rb12, runBlock_reg _ _ _ a1 s11.zero (by decide), g11_11]
  have g12_12 : reg n12 a2 = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by
    rw [rb12, runBlock_reg _ _ _ a2 s11.zero (by decide), g11_12]
  have g12_13 : reg n12 a3 = B + 0x21A0 + BitVec.ofNat 32 0x320 := by
    rw [rb12, runBlock_reg _ _ _ a3 s11.zero (by decide), g11_13]
  have g12_17 : reg n12 a7 = vhi := by
    rw [rb12, runBlock_reg _ _ _ a7 s11.zero (by decide), g11_17]
  have g12_18 : reg n12 (18 : Fin 32) = out := by
    rw [rb12, runBlock_reg _ _ _ (18 : Fin 32) s11.zero (by decide), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by
    rw [rb12, runBlock_reg _ _ _ (19 : Fin 32) s11.zero (by decide), g11_19]
  have g12_21 : reg n12 (21 : Fin 32) = s5v := by
    rw [rb12, runBlock_reg _ _ _ (21 : Fin 32) s11.zero (by decide), g11_21]
  have g12_23 : reg n12 (23 : Fin 32) = dlo := by
    rw [rb12, runBlock_reg _ _ _ (23 : Fin 32) s11.zero (by decide), g11_23]
  have g12_24 : reg n12 (24 : Fin 32) = BitVec.ofNat 32 0x3FCC4268 := by
    rw [rb12, runBlock_reg _ _ _ (24 : Fin 32) s11.zero (by decide), g11_24]
  have g12_25 : reg n12 (25 : Fin 32) = dhi := by
    rw [rb12, runBlock_reg _ _ _ (25 : Fin 32) s11.zero (by decide), g11_25]
  have g12_26 : reg n12 (26 : Fin 32) = x26 := by
    rw [rb12, runBlock_reg _ _ _ (26 : Fin 32) s11.zero (by decide), g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb12, runBlock_reg _ _ _ (27 : Fin 32) s11.zero (by decide), g11_27]
  have g12_29 : reg n12 (29 : Fin 32) = qhi := by
    rw [rb12, runBlock_reg _ _ _ (29 : Fin 32) s11.zero (by decide), g11_29]
  have g12_31 : reg n12 (31 : Fin 32) = vlo := by
    rw [rb12, runBlock_reg _ _ _ (31 : Fin 32) s11.zero (by decide), g11_31]
  have g12_14 : reg n12 a4 = BitVec.ofNat 32 ns := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, svIvB14b0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g11_2, g11_3, g11_4, g11_5, g11_6, g11_8, g11_10, g11_11, g11_12, g11_13, g11_14, g11_17, g11_18, g11_19, g11_21, g11_23, g11_24, g11_25, g11_26, g11_27, g11_29, g11_31, s11.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
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
  have w12_5c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 ns := by rw [m12]; exact w11_5c
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
  have w12_320 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ulo := by rw [m12]; exact w11_320
  have w12_324 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = uhi := by rw [m12]; exact w11_324
  have w12_328 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = vlo := by rw [m12]; exact w11_328
  have w12_32c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = vhi := by rw [m12]; exact w11_32c
  have w12_330 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = qlo := by rw [m12]; exact w11_330
  have w12_334 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = qhi := by rw [m12]; exact w11_334
  have w12_338 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = rlo := by rw [m12]; exact w11_338
  have w12_33c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = rhi := by rw [m12]; exact w11_33c
  have b12_440 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) = es := by rw [m12]; exact b11_440
  have b12_1040 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = ds := by rw [m12]; exact b11_1040
  have b12_13a0 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = fs := by rw [m12]; exact b11_13a0
  have b12_14a0 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := by rw [m12]; exact b11_14a0
  have a12_240 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m12]; exact a11_240
  have a12_260 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m12]; exact a11_260
  have a12_280 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m12]; exact a11_280
  have a12_2a0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m12]; exact a11_2a0
  have a12_2c0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m12]; exact a11_2c0
  have a12_2e0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m12]; exact a11_2e0
  have a12_420 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = ev := by rw [m12]; exact a11_420
  have a12_1020 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = dv := by rw [m12]; exact a11_1020
  have a12_1380 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = fv := by rw [m12]; exact a11_1380
  have a12_1480 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = gv := by rw [m12]; exact a11_1480
  clear a11_1480 a11_1380 a11_1020 a11_420 a11_2e0 a11_2c0 a11_2a0 a11_280 a11_260 a11_240 b11_14a0 b11_13a0 b11_1040 b11_440 w11_33c w11_338 w11_334 w11_330 w11_32c w11_328 w11_324 w11_320 w11_130 w11_12c w11_128 w11_124 w11_120 w11_11c w11_118 w11_114 w11_110 w11_10c w11_108 w11_104 w11_100 w11_fc w11_f8 w11_f4 w11_f0 w11_ec w11_e8 w11_e4 w11_e0 w11_dc w11_d8 w11_d4 w11_d0 w11_cc w11_c8 w11_c4 w11_c0 w11_bc w11_b8 w11_b4 w11_b0 w11_ac w11_a8 w11_a4 w11_a0 w11_9c w11_98 w11_94 w11_90 w11_8c w11_88 w11_84 w11_80 w11_7c w11_78 w11_70 w11_6c w11_68 w11_64 w11_60 w11_5c w11_58 w11_54 w11_50 w11_4c w11_48 w11_44 w11_40 w11_3c w11_38 w11_34 w11_30 w11_2c w11_28 w11_24 g11_8 g11_31 g11_29 g11_27 g11_26 g11_25 g11_24 g11_23 g11_21 g11_19 g11_18 g11_17 g11_14 g11_13 g11_12 g11_11 g11_10 g11_6 g11_5 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 m11 s11 u11 d11
  -- 0x14B2: sv_ufg8F
  obtain ⟨n13, c13, s13, sp13, rk13, R1_13, R2_13, K13, fr13⟩ := sv_ufg8F (co := 0xA20) (ca := 0x1380) (cb := 0x1480) (ct := 0x320) (s := ns)
    F E12 (UC0.sv F fR12) s12 sv_at_14b2 sv_at_14b6 (by decide) (by decide) g12_2
    g12_10 g12_11 g12_12 g12_13 g12_14 hns1 (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) 
    (by rw [show 0x1380 + 0x20 = 0x13A0 from rfl, b12_13a0]; exact hfs)
    (by rw [show 0x1480 + 0x20 = 0x14A0 from rfl, b12_14a0]; exact hgs)
  obtain ⟨σ13a, A13a, hσ0_13, e0_13, bb0_13, vv0_13⟩ := R1_13
  simp only [svI, svM, show 0x1380 + 0x20 = 0x13A0 from rfl, show 0x1480 + 0x20 = 0x14A0 from rfl,
    show 0x320 + 0x0 = 0x320 from rfl, show 0x320 + 0x8 = 0x328 from rfl] at e0_13
  rw [b12_13a0, a12_1380, b12_14a0, a12_1480,
    acc2_frame w12_320 w12_324, acc2_frame w12_328 w12_32c] at e0_13
  obtain ⟨σ13b, A13b, hσ1_13, e1_13, bb1_13, vv1_13⟩ := R2_13
  simp only [svI, svM, show 0x1380 + 0x20 = 0x13A0 from rfl, show 0x1480 + 0x20 = 0x14A0 from rfl,
    show 0x320 + 0x10 = 0x330 from rfl, show 0x320 + 0x18 = 0x338 from rfl] at e1_13
  rw [b12_13a0, a12_1380, b12_14a0, a12_1480,
    acc2_frame w12_330 w12_334, acc2_frame w12_338 w12_33c] at e1_13
  have t13 : Steps n0 n13 := t12.trans c13
  have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : SvCode n13.mem := E12.fr F fr13
  have V13 : SvSaves B n13.mem v := V12.keepL K13 (by decide)
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk13 (3 : Fin 32) (by decide), g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk13 (4 : Fin 32) (by decide), g12_4]
  have g13_8 : reg n13 (8 : Fin 32) = BitVec.ofNat 32 ns := by rw [rk13 (8 : Fin 32) (by decide), g12_8]
  have g13_18 : reg n13 (18 : Fin 32) = out := by rw [rk13 (18 : Fin 32) (by decide), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [rk13 (19 : Fin 32) (by decide), g12_19]
  have g13_21 : reg n13 (21 : Fin 32) = s5v := by rw [rk13 (21 : Fin 32) (by decide), g12_21]
  have g13_23 : reg n13 (23 : Fin 32) = dlo := by rw [rk13 (23 : Fin 32) (by decide), g12_23]
  have g13_24 : reg n13 (24 : Fin 32) = BitVec.ofNat 32 0x3FCC4268 := by rw [rk13 (24 : Fin 32) (by decide), g12_24]
  have g13_25 : reg n13 (25 : Fin 32) = dhi := by rw [rk13 (25 : Fin 32) (by decide), g12_25]
  have g13_26 : reg n13 (26 : Fin 32) = x26 := by rw [rk13 (26 : Fin 32) (by decide), g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk13 (27 : Fin 32) (by decide), g12_27]
  have g13_2 : reg n13 sp = B + 0x21A0 := sp13
  have w13_24 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K13.w32 (by decide) (by decide)).trans w12_24
  have w13_28 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K13.w32 (by decide) (by decide)).trans w12_28
  have w13_2c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K13.w32 (by decide) (by decide)).trans w12_2c
  have w13_30 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K13.w32 (by decide) (by decide)).trans w12_30
  have w13_34 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K13.w32 (by decide) (by decide)).trans w12_34
  have w13_38 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K13.w32 (by decide) (by decide)).trans w12_38
  have w13_3c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K13.w32 (by decide) (by decide)).trans w12_3c
  have w13_40 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K13.w32 (by decide) (by decide)).trans w12_40
  have w13_44 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K13.w32 (by decide) (by decide)).trans w12_44
  have w13_48 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K13.w32 (by decide) (by decide)).trans w12_48
  have w13_4c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K13.w32 (by decide) (by decide)).trans w12_4c
  have w13_50 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K13.w32 (by decide) (by decide)).trans w12_50
  have w13_54 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K13.w32 (by decide) (by decide)).trans w12_54
  have w13_58 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K13.w32 (by decide) (by decide)).trans w12_58
  have w13_5c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 ns := (K13.w32 (by decide) (by decide)).trans w12_5c
  have w13_60 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K13.w32 (by decide) (by decide)).trans w12_60
  have w13_64 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K13.w32 (by decide) (by decide)).trans w12_64
  have w13_68 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K13.w32 (by decide) (by decide)).trans w12_68
  have w13_6c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K13.w32 (by decide) (by decide)).trans w12_6c
  have w13_70 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K13.w32 (by decide) (by decide)).trans w12_70
  have w13_78 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := (K13.w32 (by decide) (by decide)).trans w12_78
  have w13_7c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K13.w32 (by decide) (by decide)).trans w12_7c
  have w13_80 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K13.w32 (by decide) (by decide)).trans w12_80
  have w13_84 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K13.w32 (by decide) (by decide)).trans w12_84
  have w13_88 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K13.w32 (by decide) (by decide)).trans w12_88
  have w13_8c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K13.w32 (by decide) (by decide)).trans w12_8c
  have w13_90 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K13.w32 (by decide) (by decide)).trans w12_90
  have w13_94 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K13.w32 (by decide) (by decide)).trans w12_94
  have w13_98 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K13.w32 (by decide) (by decide)).trans w12_98
  have w13_9c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K13.w32 (by decide) (by decide)).trans w12_9c
  have w13_a0 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K13.w32 (by decide) (by decide)).trans w12_a0
  have w13_a4 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K13.w32 (by decide) (by decide)).trans w12_a4
  have w13_a8 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K13.w32 (by decide) (by decide)).trans w12_a8
  have w13_ac : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K13.w32 (by decide) (by decide)).trans w12_ac
  have w13_b0 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K13.w32 (by decide) (by decide)).trans w12_b0
  have w13_b4 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K13.w32 (by decide) (by decide)).trans w12_b4
  have w13_b8 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K13.w32 (by decide) (by decide)).trans w12_b8
  have w13_bc : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K13.w32 (by decide) (by decide)).trans w12_bc
  have w13_c0 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K13.w32 (by decide) (by decide)).trans w12_c0
  have w13_c4 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K13.w32 (by decide) (by decide)).trans w12_c4
  have w13_c8 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K13.w32 (by decide) (by decide)).trans w12_c8
  have w13_cc : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K13.w32 (by decide) (by decide)).trans w12_cc
  have w13_d0 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K13.w32 (by decide) (by decide)).trans w12_d0
  have w13_d4 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K13.w32 (by decide) (by decide)).trans w12_d4
  have w13_d8 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K13.w32 (by decide) (by decide)).trans w12_d8
  have w13_dc : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K13.w32 (by decide) (by decide)).trans w12_dc
  have w13_e0 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K13.w32 (by decide) (by decide)).trans w12_e0
  have w13_e4 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K13.w32 (by decide) (by decide)).trans w12_e4
  have w13_e8 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K13.w32 (by decide) (by decide)).trans w12_e8
  have w13_ec : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K13.w32 (by decide) (by decide)).trans w12_ec
  have w13_f0 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K13.w32 (by decide) (by decide)).trans w12_f0
  have w13_f4 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K13.w32 (by decide) (by decide)).trans w12_f4
  have w13_f8 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K13.w32 (by decide) (by decide)).trans w12_f8
  have w13_fc : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K13.w32 (by decide) (by decide)).trans w12_fc
  have w13_100 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K13.w32 (by decide) (by decide)).trans w12_100
  have w13_104 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K13.w32 (by decide) (by decide)).trans w12_104
  have w13_108 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K13.w32 (by decide) (by decide)).trans w12_108
  have w13_10c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K13.w32 (by decide) (by decide)).trans w12_10c
  have w13_110 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K13.w32 (by decide) (by decide)).trans w12_110
  have w13_114 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K13.w32 (by decide) (by decide)).trans w12_114
  have w13_118 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K13.w32 (by decide) (by decide)).trans w12_118
  have w13_11c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K13.w32 (by decide) (by decide)).trans w12_11c
  have w13_120 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K13.w32 (by decide) (by decide)).trans w12_120
  have w13_124 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K13.w32 (by decide) (by decide)).trans w12_124
  have w13_128 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K13.w32 (by decide) (by decide)).trans w12_128
  have w13_12c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K13.w32 (by decide) (by decide)).trans w12_12c
  have w13_130 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K13.w32 (by decide) (by decide)).trans w12_130
  have w13_320 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ulo := (K13.w32 (by decide) (by decide)).trans w12_320
  have w13_324 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = uhi := (K13.w32 (by decide) (by decide)).trans w12_324
  have w13_328 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = vlo := (K13.w32 (by decide) (by decide)).trans w12_328
  have w13_32c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = vhi := (K13.w32 (by decide) (by decide)).trans w12_32c
  have w13_330 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = qlo := (K13.w32 (by decide) (by decide)).trans w12_330
  have w13_334 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = qhi := (K13.w32 (by decide) (by decide)).trans w12_334
  have w13_338 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = rlo := (K13.w32 (by decide) (by decide)).trans w12_338
  have w13_33c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = rhi := (K13.w32 (by decide) (by decide)).trans w12_33c
  have b13_440 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) = es := (K13.b8 (by decide) (by decide)).trans b12_440
  have b13_1040 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = ds := (K13.b8 (by decide) (by decide)).trans b12_1040
  have b13_13a0 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = fs := (K13.b8 (by decide) (by decide)).trans b12_13a0
  have b13_14a0 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := (K13.b8 (by decide) (by decide)).trans b12_14a0
  have a13_240 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := (K13.acc (by decide) (by decide)).trans a12_240
  have a13_260 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := (K13.acc (by decide) (by decide)).trans a12_260
  have a13_280 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := (K13.acc (by decide) (by decide)).trans a12_280
  have a13_2a0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K13.acc (by decide) (by decide)).trans a12_2a0
  have a13_2c0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K13.acc (by decide) (by decide)).trans a12_2c0
  have a13_2e0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K13.acc (by decide) (by decide)).trans a12_2e0
  have a13_420 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = ev := (K13.acc (by decide) (by decide)).trans a12_420
  have a13_1020 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = dv := (K13.acc (by decide) (by decide)).trans a12_1020
  have a13_1380 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = fv := (K13.acc (by decide) (by decide)).trans a12_1380
  have a13_1480 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = gv := (K13.acc (by decide) (by decide)).trans a12_1480
  have a13_a20 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 8 = A13a / 2 ^ ns % 2 ^ 256 := vv0_13
  have a13_a44 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) 8 = A13b / 2 ^ ns % 2 ^ 256 := vv1_13
  have b13_a40 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 8 σ13a := byte_of_toNat bb0_13
  have b13_a64 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA64) = BitVec.ofNat 8 σ13b := byte_of_toNat bb1_13
  clear a12_1480 a12_1380 a12_1020 a12_420 a12_2e0 a12_2c0 a12_2a0 a12_280 a12_260 a12_240 b12_14a0 b12_13a0 b12_1040 b12_440 w12_33c w12_338 w12_334 w12_330 w12_32c w12_328 w12_324 w12_320 w12_130 w12_12c w12_128 w12_124 w12_120 w12_11c w12_118 w12_114 w12_110 w12_10c w12_108 w12_104 w12_100 w12_fc w12_f8 w12_f4 w12_f0 w12_ec w12_e8 w12_e4 w12_e0 w12_dc w12_d8 w12_d4 w12_d0 w12_cc w12_c8 w12_c4 w12_c0 w12_bc w12_b8 w12_b4 w12_b0 w12_ac w12_a8 w12_a4 w12_a0 w12_9c w12_98 w12_94 w12_90 w12_8c w12_88 w12_84 w12_80 w12_7c w12_78 w12_70 w12_6c w12_68 w12_64 w12_60 w12_5c w12_58 w12_54 w12_50 w12_4c w12_48 w12_44 w12_40 w12_3c w12_38 w12_34 w12_30 w12_2c w12_28 w12_24 g12_14 g12_31 g12_29 g12_27 g12_26 g12_25 g12_24 g12_23 g12_21 g12_19 g12_18 g12_17 g12_13 g12_12 g12_11 g12_10 g12_8 g12_6 g12_5 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 rb12 s12 m12 u12 c12
  -- 0x14BA
  obtain ⟨n14, c14, u14⟩ := s13.block svIvB14ba E13.self svIvB14ba_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m14 : n14.mem = n13.mem := u14.mem
  have s14 : St n14.mem SV n14 0x14CE (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
  have rb14 : ∀ q, reg n14 q = (runBlock svIvB14ba (n13.mem, reg n13)).2 q := fun q => by rw [u14.regs]
  have fr14 : ∀ x, SvR B x → n14.mem x = n13.mem x := fun x _ => by rw [m14]
  have t14 : Steps n0 n14 := t13.trans c14
  have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : SvCode n14.mem := E13.fr F fr14
  have V14 : SvSaves B n14.mem v := V13.same m14
  have g14_2 : reg n14 sp = B + 0x21A0 := by
    rw [rb14, runBlock_reg _ _ _ sp s13.zero (by decide), g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb14, runBlock_reg _ _ _ (3 : Fin 32) s13.zero (by decide), g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb14, runBlock_reg _ _ _ (4 : Fin 32) s13.zero (by decide), g13_4]
  have g14_8 : reg n14 (8 : Fin 32) = BitVec.ofNat 32 ns := by
    rw [rb14, runBlock_reg _ _ _ (8 : Fin 32) s13.zero (by decide), g13_8]
  have g14_18 : reg n14 (18 : Fin 32) = out := by
    rw [rb14, runBlock_reg _ _ _ (18 : Fin 32) s13.zero (by decide), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = bp := by
    rw [rb14, runBlock_reg _ _ _ (19 : Fin 32) s13.zero (by decide), g13_19]
  have g14_21 : reg n14 (21 : Fin 32) = s5v := by
    rw [rb14, runBlock_reg _ _ _ (21 : Fin 32) s13.zero (by decide), g13_21]
  have g14_23 : reg n14 (23 : Fin 32) = dlo := by
    rw [rb14, runBlock_reg _ _ _ (23 : Fin 32) s13.zero (by decide), g13_23]
  have g14_24 : reg n14 (24 : Fin 32) = BitVec.ofNat 32 0x3FCC4268 := by
    rw [rb14, runBlock_reg _ _ _ (24 : Fin 32) s13.zero (by decide), g13_24]
  have g14_25 : reg n14 (25 : Fin 32) = dhi := by
    rw [rb14, runBlock_reg _ _ _ (25 : Fin 32) s13.zero (by decide), g13_25]
  have g14_26 : reg n14 (26 : Fin 32) = x26 := by
    rw [rb14, runBlock_reg _ _ _ (26 : Fin 32) s13.zero (by decide), g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb14, runBlock_reg _ _ _ (27 : Fin 32) s13.zero (by decide), g13_27]
  have g14_10 : reg n14 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1380 := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, svIvB14ba, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_8, g13_18, g13_19, g13_21, g13_23, g13_24, g13_25, g13_26, g13_27, s13.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g14_11 : reg n14 a1 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, svIvB14ba, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_8, g13_18, g13_19, g13_21, g13_23, g13_24, g13_25, g13_26, g13_27, s13.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g14_12 : reg n14 a2 = BitVec.ofNat 32 0x24 := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, svIvB14ba, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_8, g13_18, g13_19, g13_21, g13_23, g13_24, g13_25, g13_26, g13_27, s13.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w14_24 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m14]; exact w13_24
  have w14_28 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m14]; exact w13_28
  have w14_2c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m14]; exact w13_2c
  have w14_30 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m14]; exact w13_30
  have w14_34 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m14]; exact w13_34
  have w14_38 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m14]; exact w13_38
  have w14_3c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m14]; exact w13_3c
  have w14_40 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m14]; exact w13_40
  have w14_44 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m14]; exact w13_44
  have w14_48 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m14]; exact w13_48
  have w14_4c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m14]; exact w13_4c
  have w14_50 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m14]; exact w13_50
  have w14_54 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m14]; exact w13_54
  have w14_58 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m14]; exact w13_58
  have w14_5c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 ns := by rw [m14]; exact w13_5c
  have w14_60 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m14]; exact w13_60
  have w14_64 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m14]; exact w13_64
  have w14_68 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m14]; exact w13_68
  have w14_6c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m14]; exact w13_6c
  have w14_70 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m14]; exact w13_70
  have w14_78 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := by rw [m14]; exact w13_78
  have w14_7c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m14]; exact w13_7c
  have w14_80 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m14]; exact w13_80
  have w14_84 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m14]; exact w13_84
  have w14_88 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m14]; exact w13_88
  have w14_8c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m14]; exact w13_8c
  have w14_90 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m14]; exact w13_90
  have w14_94 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m14]; exact w13_94
  have w14_98 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m14]; exact w13_98
  have w14_9c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m14]; exact w13_9c
  have w14_a0 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m14]; exact w13_a0
  have w14_a4 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m14]; exact w13_a4
  have w14_a8 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m14]; exact w13_a8
  have w14_ac : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m14]; exact w13_ac
  have w14_b0 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m14]; exact w13_b0
  have w14_b4 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m14]; exact w13_b4
  have w14_b8 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m14]; exact w13_b8
  have w14_bc : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m14]; exact w13_bc
  have w14_c0 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m14]; exact w13_c0
  have w14_c4 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m14]; exact w13_c4
  have w14_c8 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m14]; exact w13_c8
  have w14_cc : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m14]; exact w13_cc
  have w14_d0 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m14]; exact w13_d0
  have w14_d4 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m14]; exact w13_d4
  have w14_d8 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m14]; exact w13_d8
  have w14_dc : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m14]; exact w13_dc
  have w14_e0 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m14]; exact w13_e0
  have w14_e4 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m14]; exact w13_e4
  have w14_e8 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m14]; exact w13_e8
  have w14_ec : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m14]; exact w13_ec
  have w14_f0 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m14]; exact w13_f0
  have w14_f4 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m14]; exact w13_f4
  have w14_f8 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m14]; exact w13_f8
  have w14_fc : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m14]; exact w13_fc
  have w14_100 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m14]; exact w13_100
  have w14_104 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m14]; exact w13_104
  have w14_108 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m14]; exact w13_108
  have w14_10c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m14]; exact w13_10c
  have w14_110 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m14]; exact w13_110
  have w14_114 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m14]; exact w13_114
  have w14_118 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m14]; exact w13_118
  have w14_11c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m14]; exact w13_11c
  have w14_120 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m14]; exact w13_120
  have w14_124 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m14]; exact w13_124
  have w14_128 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m14]; exact w13_128
  have w14_12c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m14]; exact w13_12c
  have w14_130 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m14]; exact w13_130
  have w14_320 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ulo := by rw [m14]; exact w13_320
  have w14_324 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = uhi := by rw [m14]; exact w13_324
  have w14_328 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = vlo := by rw [m14]; exact w13_328
  have w14_32c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = vhi := by rw [m14]; exact w13_32c
  have w14_330 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = qlo := by rw [m14]; exact w13_330
  have w14_334 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = qhi := by rw [m14]; exact w13_334
  have w14_338 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = rlo := by rw [m14]; exact w13_338
  have w14_33c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = rhi := by rw [m14]; exact w13_33c
  have b14_440 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) = es := by rw [m14]; exact b13_440
  have b14_a40 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 8 σ13a := by rw [m14]; exact b13_a40
  have b14_a64 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA64) = BitVec.ofNat 8 σ13b := by rw [m14]; exact b13_a64
  have b14_1040 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = ds := by rw [m14]; exact b13_1040
  have b14_13a0 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = fs := by rw [m14]; exact b13_13a0
  have b14_14a0 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := by rw [m14]; exact b13_14a0
  have a14_240 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m14]; exact a13_240
  have a14_260 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m14]; exact a13_260
  have a14_280 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m14]; exact a13_280
  have a14_2a0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m14]; exact a13_2a0
  have a14_2c0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m14]; exact a13_2c0
  have a14_2e0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m14]; exact a13_2e0
  have a14_420 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = ev := by rw [m14]; exact a13_420
  have a14_a20 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 8 = A13a / 2 ^ ns % 2 ^ 256 := by rw [m14]; exact a13_a20
  have a14_a44 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) 8 = A13b / 2 ^ ns % 2 ^ 256 := by rw [m14]; exact a13_a44
  have a14_1020 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = dv := by rw [m14]; exact a13_1020
  have a14_1380 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = fv := by rw [m14]; exact a13_1380
  have a14_1480 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = gv := by rw [m14]; exact a13_1480
  clear b13_a64 b13_a40 a13_a44 a13_a20 a13_1480 a13_1380 a13_1020 a13_420 a13_2e0 a13_2c0 a13_2a0 a13_280 a13_260 a13_240 b13_14a0 b13_13a0 b13_1040 b13_440 w13_33c w13_338 w13_334 w13_330 w13_32c w13_328 w13_324 w13_320 w13_130 w13_12c w13_128 w13_124 w13_120 w13_11c w13_118 w13_114 w13_110 w13_10c w13_108 w13_104 w13_100 w13_fc w13_f8 w13_f4 w13_f0 w13_ec w13_e8 w13_e4 w13_e0 w13_dc w13_d8 w13_d4 w13_d0 w13_cc w13_c8 w13_c4 w13_c0 w13_bc w13_b8 w13_b4 w13_b0 w13_ac w13_a8 w13_a4 w13_a0 w13_9c w13_98 w13_94 w13_90 w13_8c w13_88 w13_84 w13_80 w13_7c w13_78 w13_70 w13_6c w13_68 w13_64 w13_60 w13_5c w13_58 w13_54 w13_50 w13_4c w13_48 w13_44 w13_40 w13_3c w13_38 w13_34 w13_30 w13_2c w13_28 w13_24 g13_2 g13_27 g13_26 g13_25 g13_24 g13_23 g13_21 g13_19 g13_18 g13_8 g13_4 g13_3 V13 E13 fR13 t13 vv1_13 bb1_13 vv0_13 bb0_13 fr13 K13 rk13 sp13 s13 c13
  -- 0x14CE: memcpy
  obtain ⟨n15, P15, K15, X15⟩ := sv_mc (c := 0x1380) (d := 0xA20) (N := 0x24) F E14 s14 sv_at_14ce sv_at_14d2
    (by decide) (by decide) g14_2 g14_10 g14_11 g14_12
    (by decide) (by decide) (by decide)
  have s15 := P15.st
  have fr15 := P15.fr
  have t15 : Steps n0 n15 := t14.trans P15.steps
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.keep K15 (by decide)
  have g15_2 : reg n15 sp = B + 0x21A0 := by rw [P15.regs sp (by decide), g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P15.regs (3 : Fin 32) (by decide), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P15.regs (4 : Fin 32) (by decide), g14_4]
  have g15_8 : reg n15 (8 : Fin 32) = BitVec.ofNat 32 ns := by rw [P15.regs (8 : Fin 32) (by decide), g14_8]
  have g15_18 : reg n15 (18 : Fin 32) = out := by rw [P15.regs (18 : Fin 32) (by decide), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [P15.regs (19 : Fin 32) (by decide), g14_19]
  have g15_21 : reg n15 (21 : Fin 32) = s5v := by rw [P15.regs (21 : Fin 32) (by decide), g14_21]
  have g15_23 : reg n15 (23 : Fin 32) = dlo := by rw [P15.regs (23 : Fin 32) (by decide), g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = BitVec.ofNat 32 0x3FCC4268 := by rw [P15.regs (24 : Fin 32) (by decide), g14_24]
  have g15_25 : reg n15 (25 : Fin 32) = dhi := by rw [P15.regs (25 : Fin 32) (by decide), g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = x26 := by rw [P15.regs (26 : Fin 32) (by decide), g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P15.regs (27 : Fin 32) (by decide), g14_27]
  have w15_24 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K15.w32 (by decide) (by decide)).trans w14_24
  have w15_28 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K15.w32 (by decide) (by decide)).trans w14_28
  have w15_2c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K15.w32 (by decide) (by decide)).trans w14_2c
  have w15_30 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K15.w32 (by decide) (by decide)).trans w14_30
  have w15_34 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K15.w32 (by decide) (by decide)).trans w14_34
  have w15_38 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K15.w32 (by decide) (by decide)).trans w14_38
  have w15_3c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K15.w32 (by decide) (by decide)).trans w14_3c
  have w15_40 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K15.w32 (by decide) (by decide)).trans w14_40
  have w15_44 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K15.w32 (by decide) (by decide)).trans w14_44
  have w15_48 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K15.w32 (by decide) (by decide)).trans w14_48
  have w15_4c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K15.w32 (by decide) (by decide)).trans w14_4c
  have w15_50 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K15.w32 (by decide) (by decide)).trans w14_50
  have w15_54 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K15.w32 (by decide) (by decide)).trans w14_54
  have w15_58 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K15.w32 (by decide) (by decide)).trans w14_58
  have w15_5c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 ns := (K15.w32 (by decide) (by decide)).trans w14_5c
  have w15_60 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K15.w32 (by decide) (by decide)).trans w14_60
  have w15_64 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K15.w32 (by decide) (by decide)).trans w14_64
  have w15_68 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K15.w32 (by decide) (by decide)).trans w14_68
  have w15_6c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K15.w32 (by decide) (by decide)).trans w14_6c
  have w15_70 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K15.w32 (by decide) (by decide)).trans w14_70
  have w15_78 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := (K15.w32 (by decide) (by decide)).trans w14_78
  have w15_7c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K15.w32 (by decide) (by decide)).trans w14_7c
  have w15_80 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K15.w32 (by decide) (by decide)).trans w14_80
  have w15_84 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K15.w32 (by decide) (by decide)).trans w14_84
  have w15_88 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K15.w32 (by decide) (by decide)).trans w14_88
  have w15_8c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K15.w32 (by decide) (by decide)).trans w14_8c
  have w15_90 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K15.w32 (by decide) (by decide)).trans w14_90
  have w15_94 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K15.w32 (by decide) (by decide)).trans w14_94
  have w15_98 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K15.w32 (by decide) (by decide)).trans w14_98
  have w15_9c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K15.w32 (by decide) (by decide)).trans w14_9c
  have w15_a0 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K15.w32 (by decide) (by decide)).trans w14_a0
  have w15_a4 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K15.w32 (by decide) (by decide)).trans w14_a4
  have w15_a8 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K15.w32 (by decide) (by decide)).trans w14_a8
  have w15_ac : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K15.w32 (by decide) (by decide)).trans w14_ac
  have w15_b0 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K15.w32 (by decide) (by decide)).trans w14_b0
  have w15_b4 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K15.w32 (by decide) (by decide)).trans w14_b4
  have w15_b8 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K15.w32 (by decide) (by decide)).trans w14_b8
  have w15_bc : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K15.w32 (by decide) (by decide)).trans w14_bc
  have w15_c0 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K15.w32 (by decide) (by decide)).trans w14_c0
  have w15_c4 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K15.w32 (by decide) (by decide)).trans w14_c4
  have w15_c8 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K15.w32 (by decide) (by decide)).trans w14_c8
  have w15_cc : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K15.w32 (by decide) (by decide)).trans w14_cc
  have w15_d0 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K15.w32 (by decide) (by decide)).trans w14_d0
  have w15_d4 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K15.w32 (by decide) (by decide)).trans w14_d4
  have w15_d8 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K15.w32 (by decide) (by decide)).trans w14_d8
  have w15_dc : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K15.w32 (by decide) (by decide)).trans w14_dc
  have w15_e0 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K15.w32 (by decide) (by decide)).trans w14_e0
  have w15_e4 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K15.w32 (by decide) (by decide)).trans w14_e4
  have w15_e8 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K15.w32 (by decide) (by decide)).trans w14_e8
  have w15_ec : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K15.w32 (by decide) (by decide)).trans w14_ec
  have w15_f0 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K15.w32 (by decide) (by decide)).trans w14_f0
  have w15_f4 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K15.w32 (by decide) (by decide)).trans w14_f4
  have w15_f8 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K15.w32 (by decide) (by decide)).trans w14_f8
  have w15_fc : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K15.w32 (by decide) (by decide)).trans w14_fc
  have w15_100 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K15.w32 (by decide) (by decide)).trans w14_100
  have w15_104 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K15.w32 (by decide) (by decide)).trans w14_104
  have w15_108 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K15.w32 (by decide) (by decide)).trans w14_108
  have w15_10c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K15.w32 (by decide) (by decide)).trans w14_10c
  have w15_110 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K15.w32 (by decide) (by decide)).trans w14_110
  have w15_114 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K15.w32 (by decide) (by decide)).trans w14_114
  have w15_118 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K15.w32 (by decide) (by decide)).trans w14_118
  have w15_11c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K15.w32 (by decide) (by decide)).trans w14_11c
  have w15_120 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K15.w32 (by decide) (by decide)).trans w14_120
  have w15_124 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K15.w32 (by decide) (by decide)).trans w14_124
  have w15_128 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K15.w32 (by decide) (by decide)).trans w14_128
  have w15_12c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K15.w32 (by decide) (by decide)).trans w14_12c
  have w15_130 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K15.w32 (by decide) (by decide)).trans w14_130
  have w15_320 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ulo := (K15.w32 (by decide) (by decide)).trans w14_320
  have w15_324 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = uhi := (K15.w32 (by decide) (by decide)).trans w14_324
  have w15_328 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = vlo := (K15.w32 (by decide) (by decide)).trans w14_328
  have w15_32c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = vhi := (K15.w32 (by decide) (by decide)).trans w14_32c
  have w15_330 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = qlo := (K15.w32 (by decide) (by decide)).trans w14_330
  have w15_334 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = qhi := (K15.w32 (by decide) (by decide)).trans w14_334
  have w15_338 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = rlo := (K15.w32 (by decide) (by decide)).trans w14_338
  have w15_33c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = rhi := (K15.w32 (by decide) (by decide)).trans w14_33c
  have b15_440 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) = es := (K15.b8 (by decide) (by decide)).trans b14_440
  have b15_a40 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 8 σ13a := (K15.b8 (by decide) (by decide)).trans b14_a40
  have b15_a64 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA64) = BitVec.ofNat 8 σ13b := (K15.b8 (by decide) (by decide)).trans b14_a64
  have b15_1040 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = ds := (K15.b8 (by decide) (by decide)).trans b14_1040
  have b15_14a0 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := (K15.b8 (by decide) (by decide)).trans b14_14a0
  have b15_13a0 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = BitVec.ofNat 8 σ13a := by rw [show 0x13A0 = 0x1380 + 0x20 from rfl, X15 0x20 (by decide)]; exact b14_a40
  have a15_240 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := (K15.acc (by decide) (by decide)).trans a14_240
  have a15_260 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := (K15.acc (by decide) (by decide)).trans a14_260
  have a15_280 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := (K15.acc (by decide) (by decide)).trans a14_280
  have a15_2a0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K15.acc (by decide) (by decide)).trans a14_2a0
  have a15_2c0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K15.acc (by decide) (by decide)).trans a14_2c0
  have a15_2e0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K15.acc (by decide) (by decide)).trans a14_2e0
  have a15_420 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = ev := (K15.acc (by decide) (by decide)).trans a14_420
  have a15_a20 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 8 = A13a / 2 ^ ns % 2 ^ 256 := (K15.acc (by decide) (by decide)).trans a14_a20
  have a15_a44 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) 8 = A13b / 2 ^ ns % 2 ^ 256 := (K15.acc (by decide) (by decide)).trans a14_a44
  have a15_1020 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = dv := (K15.acc (by decide) (by decide)).trans a14_1020
  have a15_1480 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = gv := (K15.acc (by decide) (by decide)).trans a14_1480
  have a15_1380 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = A13a / 2 ^ ns % 2 ^ 256 := (accV_S 8 fun q hq => by
    rw [show 0x1380 + q = 0x1380 + (0x0 + q) by omega, X15 (0x0 + q) (by omega),
      show 0xA20 + (0x0 + q) = 0xA20 + q by omega]).trans a14_a20
  clear a14_1480 a14_1380 a14_1020 a14_a44 a14_a20 a14_420 a14_2e0 a14_2c0 a14_2a0 a14_280 a14_260 a14_240 b14_14a0 b14_13a0 b14_1040 b14_a64 b14_a40 b14_440 w14_33c w14_338 w14_334 w14_330 w14_32c w14_328 w14_324 w14_320 w14_130 w14_12c w14_128 w14_124 w14_120 w14_11c w14_118 w14_114 w14_110 w14_10c w14_108 w14_104 w14_100 w14_fc w14_f8 w14_f4 w14_f0 w14_ec w14_e8 w14_e4 w14_e0 w14_dc w14_d8 w14_d4 w14_d0 w14_cc w14_c8 w14_c4 w14_c0 w14_bc w14_b8 w14_b4 w14_b0 w14_ac w14_a8 w14_a4 w14_a0 w14_9c w14_98 w14_94 w14_90 w14_8c w14_88 w14_84 w14_80 w14_7c w14_78 w14_70 w14_6c w14_68 w14_64 w14_60 w14_5c w14_58 w14_54 w14_50 w14_4c w14_48 w14_44 w14_40 w14_3c w14_38 w14_34 w14_30 w14_2c w14_28 w14_24 g14_12 g14_11 g14_10 g14_27 g14_26 g14_25 g14_24 g14_23 g14_21 g14_19 g14_18 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 rb14 s14 m14 u14 c14
  -- 0x14D6
  obtain ⟨n16, c16, u16⟩ := s15.block svIvB14d6 E15.self svIvB14d6_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m16 : n16.mem = n15.mem := u16.mem
  have s16 : St n16.mem SV n16 0x14EA (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
  have rb16 : ∀ q, reg n16 q = (runBlock svIvB14d6 (n15.mem, reg n15)).2 q := fun q => by rw [u16.regs]
  have fr16 : ∀ x, SvR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
  have t16 : Steps n0 n16 := t15.trans c16
  have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : SvCode n16.mem := E15.fr F fr16
  have V16 : SvSaves B n16.mem v := V15.same m16
  have g16_2 : reg n16 sp = B + 0x21A0 := by
    rw [rb16, runBlock_reg _ _ _ sp s15.zero (by decide), g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb16, runBlock_reg _ _ _ (3 : Fin 32) s15.zero (by decide), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb16, runBlock_reg _ _ _ (4 : Fin 32) s15.zero (by decide), g15_4]
  have g16_8 : reg n16 (8 : Fin 32) = BitVec.ofNat 32 ns := by
    rw [rb16, runBlock_reg _ _ _ (8 : Fin 32) s15.zero (by decide), g15_8]
  have g16_18 : reg n16 (18 : Fin 32) = out := by
    rw [rb16, runBlock_reg _ _ _ (18 : Fin 32) s15.zero (by decide), g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = bp := by
    rw [rb16, runBlock_reg _ _ _ (19 : Fin 32) s15.zero (by decide), g15_19]
  have g16_21 : reg n16 (21 : Fin 32) = s5v := by
    rw [rb16, runBlock_reg _ _ _ (21 : Fin 32) s15.zero (by decide), g15_21]
  have g16_23 : reg n16 (23 : Fin 32) = dlo := by
    rw [rb16, runBlock_reg _ _ _ (23 : Fin 32) s15.zero (by decide), g15_23]
  have g16_24 : reg n16 (24 : Fin 32) = BitVec.ofNat 32 0x3FCC4268 := by
    rw [rb16, runBlock_reg _ _ _ (24 : Fin 32) s15.zero (by decide), g15_24]
  have g16_25 : reg n16 (25 : Fin 32) = dhi := by
    rw [rb16, runBlock_reg _ _ _ (25 : Fin 32) s15.zero (by decide), g15_25]
  have g16_26 : reg n16 (26 : Fin 32) = x26 := by
    rw [rb16, runBlock_reg _ _ _ (26 : Fin 32) s15.zero (by decide), g15_26]
  have g16_27 : reg n16 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb16, runBlock_reg _ _ _ (27 : Fin 32) s15.zero (by decide), g15_27]
  have g16_10 : reg n16 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by
    rw [rb16]; simp +decide only [runBlock, BInstr.run, svIvB14d6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g15_2, g15_3, g15_4, g15_8, g15_18, g15_19, g15_21, g15_23, g15_24, g15_25, g15_26, g15_27, s15.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g16_11 : reg n16 a1 = B + 0x21A0 + BitVec.ofNat 32 0xA44 := by
    rw [rb16]; simp +decide only [runBlock, BInstr.run, svIvB14d6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g15_2, g15_3, g15_4, g15_8, g15_18, g15_19, g15_21, g15_23, g15_24, g15_25, g15_26, g15_27, s15.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g16_12 : reg n16 a2 = BitVec.ofNat 32 0x24 := by
    rw [rb16]; simp +decide only [runBlock, BInstr.run, svIvB14d6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g15_2, g15_3, g15_4, g15_8, g15_18, g15_19, g15_21, g15_23, g15_24, g15_25, g15_26, g15_27, s15.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
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
  have w16_5c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 ns := by rw [m16]; exact w15_5c
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
  have w16_320 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ulo := by rw [m16]; exact w15_320
  have w16_324 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = uhi := by rw [m16]; exact w15_324
  have w16_328 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = vlo := by rw [m16]; exact w15_328
  have w16_32c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = vhi := by rw [m16]; exact w15_32c
  have w16_330 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = qlo := by rw [m16]; exact w15_330
  have w16_334 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = qhi := by rw [m16]; exact w15_334
  have w16_338 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = rlo := by rw [m16]; exact w15_338
  have w16_33c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = rhi := by rw [m16]; exact w15_33c
  have b16_440 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) = es := by rw [m16]; exact b15_440
  have b16_a40 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 8 σ13a := by rw [m16]; exact b15_a40
  have b16_a64 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA64) = BitVec.ofNat 8 σ13b := by rw [m16]; exact b15_a64
  have b16_1040 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = ds := by rw [m16]; exact b15_1040
  have b16_13a0 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = BitVec.ofNat 8 σ13a := by rw [m16]; exact b15_13a0
  have b16_14a0 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = gs := by rw [m16]; exact b15_14a0
  have a16_240 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m16]; exact a15_240
  have a16_260 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m16]; exact a15_260
  have a16_280 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m16]; exact a15_280
  have a16_2a0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m16]; exact a15_2a0
  have a16_2c0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m16]; exact a15_2c0
  have a16_2e0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m16]; exact a15_2e0
  have a16_420 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = ev := by rw [m16]; exact a15_420
  have a16_a20 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 8 = A13a / 2 ^ ns % 2 ^ 256 := by rw [m16]; exact a15_a20
  have a16_a44 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) 8 = A13b / 2 ^ ns % 2 ^ 256 := by rw [m16]; exact a15_a44
  have a16_1020 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = dv := by rw [m16]; exact a15_1020
  have a16_1380 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = A13a / 2 ^ ns % 2 ^ 256 := by rw [m16]; exact a15_1380
  have a16_1480 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = gv := by rw [m16]; exact a15_1480
  clear a15_1380 a15_1480 a15_1020 a15_a44 a15_a20 a15_420 a15_2e0 a15_2c0 a15_2a0 a15_280 a15_260 a15_240 b15_13a0 b15_14a0 b15_1040 b15_a64 b15_a40 b15_440 w15_33c w15_338 w15_334 w15_330 w15_32c w15_328 w15_324 w15_320 w15_130 w15_12c w15_128 w15_124 w15_120 w15_11c w15_118 w15_114 w15_110 w15_10c w15_108 w15_104 w15_100 w15_fc w15_f8 w15_f4 w15_f0 w15_ec w15_e8 w15_e4 w15_e0 w15_dc w15_d8 w15_d4 w15_d0 w15_cc w15_c8 w15_c4 w15_c0 w15_bc w15_b8 w15_b4 w15_b0 w15_ac w15_a8 w15_a4 w15_a0 w15_9c w15_98 w15_94 w15_90 w15_8c w15_88 w15_84 w15_80 w15_7c w15_78 w15_70 w15_6c w15_68 w15_64 w15_60 w15_5c w15_58 w15_54 w15_50 w15_4c w15_48 w15_44 w15_40 w15_3c w15_38 w15_34 w15_30 w15_2c w15_28 w15_24 g15_27 g15_26 g15_25 g15_24 g15_23 g15_21 g15_19 g15_18 g15_8 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 s15 X15 K15 P15
  -- 0x14EA: memcpy
  obtain ⟨n17, P17, K17, X17⟩ := sv_mc (c := 0x1480) (d := 0xA44) (N := 0x24) F E16 s16 sv_at_14ea sv_at_14ee
    (by decide) (by decide) g16_2 g16_10 g16_11 g16_12
    (by decide) (by decide) (by decide)
  have s17 := P17.st
  have fr17 := P17.fr
  have t17 : Steps n0 n17 := t16.trans P17.steps
  have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
  have E17 : SvCode n17.mem := E16.fr F fr17
  have V17 : SvSaves B n17.mem v := V16.keep K17 (by decide)
  have g17_2 : reg n17 sp = B + 0x21A0 := by rw [P17.regs sp (by decide), g16_2]
  have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P17.regs (3 : Fin 32) (by decide), g16_3]
  have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P17.regs (4 : Fin 32) (by decide), g16_4]
  have g17_8 : reg n17 (8 : Fin 32) = BitVec.ofNat 32 ns := by rw [P17.regs (8 : Fin 32) (by decide), g16_8]
  have g17_18 : reg n17 (18 : Fin 32) = out := by rw [P17.regs (18 : Fin 32) (by decide), g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [P17.regs (19 : Fin 32) (by decide), g16_19]
  have g17_21 : reg n17 (21 : Fin 32) = s5v := by rw [P17.regs (21 : Fin 32) (by decide), g16_21]
  have g17_23 : reg n17 (23 : Fin 32) = dlo := by rw [P17.regs (23 : Fin 32) (by decide), g16_23]
  have g17_24 : reg n17 (24 : Fin 32) = BitVec.ofNat 32 0x3FCC4268 := by rw [P17.regs (24 : Fin 32) (by decide), g16_24]
  have g17_25 : reg n17 (25 : Fin 32) = dhi := by rw [P17.regs (25 : Fin 32) (by decide), g16_25]
  have g17_26 : reg n17 (26 : Fin 32) = x26 := by rw [P17.regs (26 : Fin 32) (by decide), g16_26]
  have g17_27 : reg n17 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P17.regs (27 : Fin 32) (by decide), g16_27]
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
  have w17_5c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 ns := (K17.w32 (by decide) (by decide)).trans w16_5c
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
  have w17_320 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ulo := (K17.w32 (by decide) (by decide)).trans w16_320
  have w17_324 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = uhi := (K17.w32 (by decide) (by decide)).trans w16_324
  have w17_328 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = vlo := (K17.w32 (by decide) (by decide)).trans w16_328
  have w17_32c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = vhi := (K17.w32 (by decide) (by decide)).trans w16_32c
  have w17_330 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = qlo := (K17.w32 (by decide) (by decide)).trans w16_330
  have w17_334 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = qhi := (K17.w32 (by decide) (by decide)).trans w16_334
  have w17_338 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = rlo := (K17.w32 (by decide) (by decide)).trans w16_338
  have w17_33c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = rhi := (K17.w32 (by decide) (by decide)).trans w16_33c
  have b17_440 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) = es := (K17.b8 (by decide) (by decide)).trans b16_440
  have b17_a40 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 8 σ13a := (K17.b8 (by decide) (by decide)).trans b16_a40
  have b17_a64 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA64) = BitVec.ofNat 8 σ13b := (K17.b8 (by decide) (by decide)).trans b16_a64
  have b17_1040 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = ds := (K17.b8 (by decide) (by decide)).trans b16_1040
  have b17_13a0 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = BitVec.ofNat 8 σ13a := (K17.b8 (by decide) (by decide)).trans b16_13a0
  have b17_14a0 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = BitVec.ofNat 8 σ13b := by rw [show 0x14A0 = 0x1480 + 0x20 from rfl, X17 0x20 (by decide)]; exact b16_a64
  have a17_240 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := (K17.acc (by decide) (by decide)).trans a16_240
  have a17_260 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := (K17.acc (by decide) (by decide)).trans a16_260
  have a17_280 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := (K17.acc (by decide) (by decide)).trans a16_280
  have a17_2a0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K17.acc (by decide) (by decide)).trans a16_2a0
  have a17_2c0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K17.acc (by decide) (by decide)).trans a16_2c0
  have a17_2e0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K17.acc (by decide) (by decide)).trans a16_2e0
  have a17_420 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = ev := (K17.acc (by decide) (by decide)).trans a16_420
  have a17_a20 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 8 = A13a / 2 ^ ns % 2 ^ 256 := (K17.acc (by decide) (by decide)).trans a16_a20
  have a17_a44 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) 8 = A13b / 2 ^ ns % 2 ^ 256 := (K17.acc (by decide) (by decide)).trans a16_a44
  have a17_1020 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = dv := (K17.acc (by decide) (by decide)).trans a16_1020
  have a17_1380 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = A13a / 2 ^ ns % 2 ^ 256 := (K17.acc (by decide) (by decide)).trans a16_1380
  have a17_1480 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = A13b / 2 ^ ns % 2 ^ 256 := (accV_S 8 fun q hq => by
    rw [show 0x1480 + q = 0x1480 + (0x0 + q) by omega, X17 (0x0 + q) (by omega),
      show 0xA44 + (0x0 + q) = 0xA44 + q by omega]).trans a16_a44
  clear a16_1480 a16_1380 a16_1020 a16_a44 a16_a20 a16_420 a16_2e0 a16_2c0 a16_2a0 a16_280 a16_260 a16_240 b16_14a0 b16_13a0 b16_1040 b16_a64 b16_a40 b16_440 w16_33c w16_338 w16_334 w16_330 w16_32c w16_328 w16_324 w16_320 w16_130 w16_12c w16_128 w16_124 w16_120 w16_11c w16_118 w16_114 w16_110 w16_10c w16_108 w16_104 w16_100 w16_fc w16_f8 w16_f4 w16_f0 w16_ec w16_e8 w16_e4 w16_e0 w16_dc w16_d8 w16_d4 w16_d0 w16_cc w16_c8 w16_c4 w16_c0 w16_bc w16_b8 w16_b4 w16_b0 w16_ac w16_a8 w16_a4 w16_a0 w16_9c w16_98 w16_94 w16_90 w16_8c w16_88 w16_84 w16_80 w16_7c w16_78 w16_70 w16_6c w16_68 w16_64 w16_60 w16_5c w16_58 w16_54 w16_50 w16_4c w16_48 w16_44 w16_40 w16_3c w16_38 w16_34 w16_30 w16_2c w16_28 w16_24 g16_12 g16_11 g16_10 g16_27 g16_26 g16_25 g16_24 g16_23 g16_21 g16_19 g16_18 g16_8 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 rb16 s16 m16 u16 c16
  -- 0x14F2
  obtain ⟨n18, c18, u18⟩ := s17.block svIvB14f2 E17.self svIvB14f2_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m18 : n18.mem = n17.mem := u18.mem
  have s18 : St n18.mem SV n18 0x150C (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
  have rb18 : ∀ q, reg n18 q = (runBlock svIvB14f2 (n17.mem, reg n17)).2 q := fun q => by rw [u18.regs]
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
  have g18_8 : reg n18 (8 : Fin 32) = BitVec.ofNat 32 ns := by
    rw [rb18, runBlock_reg _ _ _ (8 : Fin 32) s17.zero (by decide), g17_8]
  have g18_18 : reg n18 (18 : Fin 32) = out := by
    rw [rb18, runBlock_reg _ _ _ (18 : Fin 32) s17.zero (by decide), g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = bp := by
    rw [rb18, runBlock_reg _ _ _ (19 : Fin 32) s17.zero (by decide), g17_19]
  have g18_21 : reg n18 (21 : Fin 32) = s5v := by
    rw [rb18, runBlock_reg _ _ _ (21 : Fin 32) s17.zero (by decide), g17_21]
  have g18_23 : reg n18 (23 : Fin 32) = dlo := by
    rw [rb18, runBlock_reg _ _ _ (23 : Fin 32) s17.zero (by decide), g17_23]
  have g18_24 : reg n18 (24 : Fin 32) = BitVec.ofNat 32 0x3FCC4268 := by
    rw [rb18, runBlock_reg _ _ _ (24 : Fin 32) s17.zero (by decide), g17_24]
  have g18_25 : reg n18 (25 : Fin 32) = dhi := by
    rw [rb18, runBlock_reg _ _ _ (25 : Fin 32) s17.zero (by decide), g17_25]
  have g18_26 : reg n18 (26 : Fin 32) = x26 := by
    rw [rb18, runBlock_reg _ _ _ (26 : Fin 32) s17.zero (by decide), g17_26]
  have g18_27 : reg n18 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb18, runBlock_reg _ _ _ (27 : Fin 32) s17.zero (by decide), g17_27]
  have g18_10 : reg n18 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb18]; simp +decide only [runBlock, BInstr.run, svIvB14f2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g17_2, g17_3, g17_4, g17_8, g17_18, g17_19, g17_21, g17_23, g17_24, g17_25, g17_26, g17_27, s17.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g18_11 : reg n18 a1 = B + 0x21A0 + BitVec.ofNat 32 0x1020 := by
    rw [rb18]; simp +decide only [runBlock, BInstr.run, svIvB14f2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g17_2, g17_3, g17_4, g17_8, g17_18, g17_19, g17_21, g17_23, g17_24, g17_25, g17_26, g17_27, s17.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g18_12 : reg n18 a2 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb18]; simp +decide only [runBlock, BInstr.run, svIvB14f2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g17_2, g17_3, g17_4, g17_8, g17_18, g17_19, g17_21, g17_23, g17_24, g17_25, g17_26, g17_27, s17.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g18_13 : reg n18 a3 = BitVec.ofNat 32 0x3FCC4268 := by
    rw [rb18]; simp +decide only [runBlock, BInstr.run, svIvB14f2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g17_2, g17_3, g17_4, g17_8, g17_18, g17_19, g17_21, g17_23, g17_24, g17_25, g17_26, g17_27, s17.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g18_16 : reg n18 a6 = B + 0x21A0 + BitVec.ofNat 32 0x320 := by
    rw [rb18]; simp +decide only [runBlock, BInstr.run, svIvB14f2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g17_2, g17_3, g17_4, g17_8, g17_18, g17_19, g17_21, g17_23, g17_24, g17_25, g17_26, g17_27, s17.zero])
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
  have w18_5c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 ns := by rw [m18]; exact w17_5c
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
  have w18_320 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ulo := by rw [m18]; exact w17_320
  have w18_324 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = uhi := by rw [m18]; exact w17_324
  have w18_328 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = vlo := by rw [m18]; exact w17_328
  have w18_32c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = vhi := by rw [m18]; exact w17_32c
  have w18_330 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = qlo := by rw [m18]; exact w17_330
  have w18_334 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = qhi := by rw [m18]; exact w17_334
  have w18_338 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = rlo := by rw [m18]; exact w17_338
  have w18_33c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = rhi := by rw [m18]; exact w17_33c
  have b18_440 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) = es := by rw [m18]; exact b17_440
  have b18_a40 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 8 σ13a := by rw [m18]; exact b17_a40
  have b18_a64 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA64) = BitVec.ofNat 8 σ13b := by rw [m18]; exact b17_a64
  have b18_1040 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = ds := by rw [m18]; exact b17_1040
  have b18_13a0 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = BitVec.ofNat 8 σ13a := by rw [m18]; exact b17_13a0
  have b18_14a0 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = BitVec.ofNat 8 σ13b := by rw [m18]; exact b17_14a0
  have a18_240 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m18]; exact a17_240
  have a18_260 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m18]; exact a17_260
  have a18_280 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m18]; exact a17_280
  have a18_2a0 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m18]; exact a17_2a0
  have a18_2c0 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m18]; exact a17_2c0
  have a18_2e0 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m18]; exact a17_2e0
  have a18_420 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = ev := by rw [m18]; exact a17_420
  have a18_a20 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 8 = A13a / 2 ^ ns % 2 ^ 256 := by rw [m18]; exact a17_a20
  have a18_a44 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) 8 = A13b / 2 ^ ns % 2 ^ 256 := by rw [m18]; exact a17_a44
  have a18_1020 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = dv := by rw [m18]; exact a17_1020
  have a18_1380 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = A13a / 2 ^ ns % 2 ^ 256 := by rw [m18]; exact a17_1380
  have a18_1480 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = A13b / 2 ^ ns % 2 ^ 256 := by rw [m18]; exact a17_1480
  clear a17_1480 a17_1380 a17_1020 a17_a44 a17_a20 a17_420 a17_2e0 a17_2c0 a17_2a0 a17_280 a17_260 a17_240 b17_14a0 b17_13a0 b17_1040 b17_a64 b17_a40 b17_440 w17_33c w17_338 w17_334 w17_330 w17_32c w17_328 w17_324 w17_320 w17_130 w17_12c w17_128 w17_124 w17_120 w17_11c w17_118 w17_114 w17_110 w17_10c w17_108 w17_104 w17_100 w17_fc w17_f8 w17_f4 w17_f0 w17_ec w17_e8 w17_e4 w17_e0 w17_dc w17_d8 w17_d4 w17_d0 w17_cc w17_c8 w17_c4 w17_c0 w17_bc w17_b8 w17_b4 w17_b0 w17_ac w17_a8 w17_a4 w17_a0 w17_9c w17_98 w17_94 w17_90 w17_8c w17_88 w17_84 w17_80 w17_7c w17_78 w17_70 w17_6c w17_68 w17_64 w17_60 w17_5c w17_58 w17_54 w17_50 w17_4c w17_48 w17_44 w17_40 w17_3c w17_38 w17_34 w17_30 w17_2c w17_28 w17_24 g17_27 g17_26 g17_25 g17_24 g17_23 g17_21 g17_19 g17_18 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 s17 X17 K17 P17
  -- 0x150C: lw
  obtain ⟨n19, d19, u19⟩ := s18.lw E18.self sv_at_150c (off' := 0x150E) (by decide)
    (by rw [g18_2, show B + 0x21A0 + 0x70 = B + 0x21A0 + BitVec.ofNat 32 0x70 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s19 : St n19.mem SV n19 0x150E (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
  have m19 : n19.mem = n18.mem := u19.mem
  have fr19 : ∀ x, SvR B x → n19.mem x = n18.mem x := fun x _ => by rw [m19]
  have t19 : Steps n0 n19 := t18.trans (.single d19)
  have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
  have E19 : SvCode n19.mem := E18.fr F fr19
  have V19 : SvSaves B n19.mem v := V18.same m19
  have g19_2 : reg n19 sp = B + 0x21A0 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_2]
  have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_3]
  have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_4]
  have g19_8 : reg n19 (8 : Fin 32) = BitVec.ofNat 32 ns := by rw [u19.regs, upd_ne (by decide) (by decide), g18_8]
  have g19_10 : reg n19 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_10]
  have g19_11 : reg n19 a1 = B + 0x21A0 + BitVec.ofNat 32 0x1020 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_11]
  have g19_12 : reg n19 a2 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_12]
  have g19_13 : reg n19 a3 = BitVec.ofNat 32 0x3FCC4268 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_13]
  have g19_16 : reg n19 a6 = B + 0x21A0 + BitVec.ofNat 32 0x320 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_16]
  have g19_18 : reg n19 (18 : Fin 32) = out := by rw [u19.regs, upd_ne (by decide) (by decide), g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [u19.regs, upd_ne (by decide) (by decide), g18_19]
  have g19_21 : reg n19 (21 : Fin 32) = s5v := by rw [u19.regs, upd_ne (by decide) (by decide), g18_21]
  have g19_23 : reg n19 (23 : Fin 32) = dlo := by rw [u19.regs, upd_ne (by decide) (by decide), g18_23]
  have g19_24 : reg n19 (24 : Fin 32) = BitVec.ofNat 32 0x3FCC4268 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_24]
  have g19_25 : reg n19 (25 : Fin 32) = dhi := by rw [u19.regs, upd_ne (by decide) (by decide), g18_25]
  have g19_26 : reg n19 (26 : Fin 32) = x26 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_26]
  have g19_27 : reg n19 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_27]
  have g19_14 : reg n19 a4 = w70 := by
    rw [u19.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g18_2, show B + 0x21A0 + 0x70 = B + 0x21A0 + BitVec.ofNat 32 0x70 by sv_addr, w18_70]
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
  have w19_5c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 ns := by rw [m19]; exact w18_5c
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
  have w19_320 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ulo := by rw [m19]; exact w18_320
  have w19_324 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = uhi := by rw [m19]; exact w18_324
  have w19_328 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = vlo := by rw [m19]; exact w18_328
  have w19_32c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = vhi := by rw [m19]; exact w18_32c
  have w19_330 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = qlo := by rw [m19]; exact w18_330
  have w19_334 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = qhi := by rw [m19]; exact w18_334
  have w19_338 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = rlo := by rw [m19]; exact w18_338
  have w19_33c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = rhi := by rw [m19]; exact w18_33c
  have b19_440 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) = es := by rw [m19]; exact b18_440
  have b19_a40 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 8 σ13a := by rw [m19]; exact b18_a40
  have b19_a64 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA64) = BitVec.ofNat 8 σ13b := by rw [m19]; exact b18_a64
  have b19_1040 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = ds := by rw [m19]; exact b18_1040
  have b19_13a0 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = BitVec.ofNat 8 σ13a := by rw [m19]; exact b18_13a0
  have b19_14a0 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = BitVec.ofNat 8 σ13b := by rw [m19]; exact b18_14a0
  have a19_240 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m19]; exact a18_240
  have a19_260 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m19]; exact a18_260
  have a19_280 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m19]; exact a18_280
  have a19_2a0 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m19]; exact a18_2a0
  have a19_2c0 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m19]; exact a18_2c0
  have a19_2e0 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m19]; exact a18_2e0
  have a19_420 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = ev := by rw [m19]; exact a18_420
  have a19_a20 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 8 = A13a / 2 ^ ns % 2 ^ 256 := by rw [m19]; exact a18_a20
  have a19_a44 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) 8 = A13b / 2 ^ ns % 2 ^ 256 := by rw [m19]; exact a18_a44
  have a19_1020 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = dv := by rw [m19]; exact a18_1020
  have a19_1380 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = A13a / 2 ^ ns % 2 ^ 256 := by rw [m19]; exact a18_1380
  have a19_1480 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = A13b / 2 ^ ns % 2 ^ 256 := by rw [m19]; exact a18_1480
  clear a18_1480 a18_1380 a18_1020 a18_a44 a18_a20 a18_420 a18_2e0 a18_2c0 a18_2a0 a18_280 a18_260 a18_240 b18_14a0 b18_13a0 b18_1040 b18_a64 b18_a40 b18_440 w18_33c w18_338 w18_334 w18_330 w18_32c w18_328 w18_324 w18_320 w18_130 w18_12c w18_128 w18_124 w18_120 w18_11c w18_118 w18_114 w18_110 w18_10c w18_108 w18_104 w18_100 w18_fc w18_f8 w18_f4 w18_f0 w18_ec w18_e8 w18_e4 w18_e0 w18_dc w18_d8 w18_d4 w18_d0 w18_cc w18_c8 w18_c4 w18_c0 w18_bc w18_b8 w18_b4 w18_b0 w18_ac w18_a8 w18_a4 w18_a0 w18_9c w18_98 w18_94 w18_90 w18_8c w18_88 w18_84 w18_80 w18_7c w18_78 w18_70 w18_6c w18_68 w18_64 w18_60 w18_5c w18_58 w18_54 w18_50 w18_4c w18_48 w18_44 w18_40 w18_3c w18_38 w18_34 w18_30 w18_2c w18_28 w18_24 g18_16 g18_13 g18_12 g18_11 g18_10 g18_27 g18_26 g18_25 g18_24 g18_23 g18_21 g18_19 g18_18 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 rb18 s18 m18 u18 c18
  -- 0x150E: lw
  obtain ⟨n20, d20, u20⟩ := s19.lw E19.self sv_at_150e (off' := 0x1510) (by decide)
    (by rw [g19_2, show B + 0x21A0 + 0x60 = B + 0x21A0 + BitVec.ofNat 32 0x60 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s20 : St n20.mem SV n20 0x1510 (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
  have m20 : n20.mem = n19.mem := u20.mem
  have fr20 : ∀ x, SvR B x → n20.mem x = n19.mem x := fun x _ => by rw [m20]
  have t20 : Steps n0 n20 := t19.trans (.single d20)
  have fR20 : ∀ x, SvR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
  have E20 : SvCode n20.mem := E19.fr F fr20
  have V20 : SvSaves B n20.mem v := V19.same m20
  have g20_2 : reg n20 sp = B + 0x21A0 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_2]
  have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u20.regs, upd_ne (by decide) (by decide), g19_3]
  have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u20.regs, upd_ne (by decide) (by decide), g19_4]
  have g20_8 : reg n20 (8 : Fin 32) = BitVec.ofNat 32 ns := by rw [u20.regs, upd_ne (by decide) (by decide), g19_8]
  have g20_10 : reg n20 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_10]
  have g20_11 : reg n20 a1 = B + 0x21A0 + BitVec.ofNat 32 0x1020 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_11]
  have g20_12 : reg n20 a2 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_12]
  have g20_13 : reg n20 a3 = BitVec.ofNat 32 0x3FCC4268 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_13]
  have g20_14 : reg n20 a4 = w70 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_14]
  have g20_16 : reg n20 a6 = B + 0x21A0 + BitVec.ofNat 32 0x320 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_16]
  have g20_18 : reg n20 (18 : Fin 32) = out := by rw [u20.regs, upd_ne (by decide) (by decide), g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = bp := by rw [u20.regs, upd_ne (by decide) (by decide), g19_19]
  have g20_21 : reg n20 (21 : Fin 32) = s5v := by rw [u20.regs, upd_ne (by decide) (by decide), g19_21]
  have g20_23 : reg n20 (23 : Fin 32) = dlo := by rw [u20.regs, upd_ne (by decide) (by decide), g19_23]
  have g20_24 : reg n20 (24 : Fin 32) = BitVec.ofNat 32 0x3FCC4268 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_24]
  have g20_25 : reg n20 (25 : Fin 32) = dhi := by rw [u20.regs, upd_ne (by decide) (by decide), g19_25]
  have g20_26 : reg n20 (26 : Fin 32) = x26 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_26]
  have g20_27 : reg n20 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_27]
  have g20_15 : reg n20 a5 = w60 := by
    rw [u20.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g19_2, show B + 0x21A0 + 0x60 = B + 0x21A0 + BitVec.ofNat 32 0x60 by sv_addr, w19_60]
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
  have w20_5c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 ns := by rw [m20]; exact w19_5c
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
  have w20_320 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ulo := by rw [m20]; exact w19_320
  have w20_324 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = uhi := by rw [m20]; exact w19_324
  have w20_328 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = vlo := by rw [m20]; exact w19_328
  have w20_32c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = vhi := by rw [m20]; exact w19_32c
  have w20_330 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = qlo := by rw [m20]; exact w19_330
  have w20_334 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = qhi := by rw [m20]; exact w19_334
  have w20_338 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = rlo := by rw [m20]; exact w19_338
  have w20_33c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = rhi := by rw [m20]; exact w19_33c
  have b20_440 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) = es := by rw [m20]; exact b19_440
  have b20_a40 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 8 σ13a := by rw [m20]; exact b19_a40
  have b20_a64 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA64) = BitVec.ofNat 8 σ13b := by rw [m20]; exact b19_a64
  have b20_1040 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = ds := by rw [m20]; exact b19_1040
  have b20_13a0 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = BitVec.ofNat 8 σ13a := by rw [m20]; exact b19_13a0
  have b20_14a0 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = BitVec.ofNat 8 σ13b := by rw [m20]; exact b19_14a0
  have a20_240 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m20]; exact a19_240
  have a20_260 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m20]; exact a19_260
  have a20_280 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m20]; exact a19_280
  have a20_2a0 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m20]; exact a19_2a0
  have a20_2c0 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m20]; exact a19_2c0
  have a20_2e0 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m20]; exact a19_2e0
  have a20_420 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = ev := by rw [m20]; exact a19_420
  have a20_a20 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 8 = A13a / 2 ^ ns % 2 ^ 256 := by rw [m20]; exact a19_a20
  have a20_a44 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) 8 = A13b / 2 ^ ns % 2 ^ 256 := by rw [m20]; exact a19_a44
  have a20_1020 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = dv := by rw [m20]; exact a19_1020
  have a20_1380 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = A13a / 2 ^ ns % 2 ^ 256 := by rw [m20]; exact a19_1380
  have a20_1480 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = A13b / 2 ^ ns % 2 ^ 256 := by rw [m20]; exact a19_1480
  clear a19_1480 a19_1380 a19_1020 a19_a44 a19_a20 a19_420 a19_2e0 a19_2c0 a19_2a0 a19_280 a19_260 a19_240 b19_14a0 b19_13a0 b19_1040 b19_a64 b19_a40 b19_440 w19_33c w19_338 w19_334 w19_330 w19_32c w19_328 w19_324 w19_320 w19_130 w19_12c w19_128 w19_124 w19_120 w19_11c w19_118 w19_114 w19_110 w19_10c w19_108 w19_104 w19_100 w19_fc w19_f8 w19_f4 w19_f0 w19_ec w19_e8 w19_e4 w19_e0 w19_dc w19_d8 w19_d4 w19_d0 w19_cc w19_c8 w19_c4 w19_c0 w19_bc w19_b8 w19_b4 w19_b0 w19_ac w19_a8 w19_a4 w19_a0 w19_9c w19_98 w19_94 w19_90 w19_8c w19_88 w19_84 w19_80 w19_7c w19_78 w19_70 w19_6c w19_68 w19_64 w19_60 w19_5c w19_58 w19_54 w19_50 w19_4c w19_48 w19_44 w19_40 w19_3c w19_38 w19_34 w19_30 w19_2c w19_28 w19_24 g19_14 g19_27 g19_26 g19_25 g19_24 g19_23 g19_21 g19_19 g19_18 g19_16 g19_13 g19_12 g19_11 g19_10 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 m19 s19 u19 d19
  -- 0x1510
  obtain ⟨n21, c21, u21⟩ := s20.block svIvB1510 E20.self svIvB1510_end
    ⟨trivial, trivial⟩
  have m21 : n21.mem = n20.mem := u21.mem
  have s21 : St n21.mem SV n21 0x1512 (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
  have rb21 : ∀ q, reg n21 q = (runBlock svIvB1510 (n20.mem, reg n20)).2 q := fun q => by rw [u21.regs]
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
  have g21_8 : reg n21 (8 : Fin 32) = BitVec.ofNat 32 ns := by
    rw [rb21, runBlock_reg _ _ _ (8 : Fin 32) s20.zero (by decide), g20_8]
  have g21_10 : reg n21 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb21, runBlock_reg _ _ _ a0 s20.zero (by decide), g20_10]
  have g21_11 : reg n21 a1 = B + 0x21A0 + BitVec.ofNat 32 0x1020 := by
    rw [rb21, runBlock_reg _ _ _ a1 s20.zero (by decide), g20_11]
  have g21_12 : reg n21 a2 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb21, runBlock_reg _ _ _ a2 s20.zero (by decide), g20_12]
  have g21_13 : reg n21 a3 = BitVec.ofNat 32 0x3FCC4268 := by
    rw [rb21, runBlock_reg _ _ _ a3 s20.zero (by decide), g20_13]
  have g21_14 : reg n21 a4 = w70 := by
    rw [rb21, runBlock_reg _ _ _ a4 s20.zero (by decide), g20_14]
  have g21_15 : reg n21 a5 = w60 := by
    rw [rb21, runBlock_reg _ _ _ a5 s20.zero (by decide), g20_15]
  have g21_16 : reg n21 a6 = B + 0x21A0 + BitVec.ofNat 32 0x320 := by
    rw [rb21, runBlock_reg _ _ _ a6 s20.zero (by decide), g20_16]
  have g21_18 : reg n21 (18 : Fin 32) = out := by
    rw [rb21, runBlock_reg _ _ _ (18 : Fin 32) s20.zero (by decide), g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = bp := by
    rw [rb21, runBlock_reg _ _ _ (19 : Fin 32) s20.zero (by decide), g20_19]
  have g21_21 : reg n21 (21 : Fin 32) = s5v := by
    rw [rb21, runBlock_reg _ _ _ (21 : Fin 32) s20.zero (by decide), g20_21]
  have g21_23 : reg n21 (23 : Fin 32) = dlo := by
    rw [rb21, runBlock_reg _ _ _ (23 : Fin 32) s20.zero (by decide), g20_23]
  have g21_24 : reg n21 (24 : Fin 32) = BitVec.ofNat 32 0x3FCC4268 := by
    rw [rb21, runBlock_reg _ _ _ (24 : Fin 32) s20.zero (by decide), g20_24]
  have g21_25 : reg n21 (25 : Fin 32) = dhi := by
    rw [rb21, runBlock_reg _ _ _ (25 : Fin 32) s20.zero (by decide), g20_25]
  have g21_26 : reg n21 (26 : Fin 32) = x26 := by
    rw [rb21, runBlock_reg _ _ _ (26 : Fin 32) s20.zero (by decide), g20_26]
  have g21_27 : reg n21 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb21, runBlock_reg _ _ _ (27 : Fin 32) s20.zero (by decide), g20_27]
  have g21_17 : reg n21 a7 = BitVec.ofNat 32 ns := by
    rw [rb21]; simp +decide only [runBlock, BInstr.run, svIvB1510, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g20_2, g20_3, g20_4, g20_8, g20_10, g20_11, g20_12, g20_13, g20_14, g20_15, g20_16, g20_18, g20_19, g20_21, g20_23, g20_24, g20_25, g20_26, g20_27, s20.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
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
  have w21_5c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 ns := by rw [m21]; exact w20_5c
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
  have w21_320 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ulo := by rw [m21]; exact w20_320
  have w21_324 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = uhi := by rw [m21]; exact w20_324
  have w21_328 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = vlo := by rw [m21]; exact w20_328
  have w21_32c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = vhi := by rw [m21]; exact w20_32c
  have w21_330 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = qlo := by rw [m21]; exact w20_330
  have w21_334 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = qhi := by rw [m21]; exact w20_334
  have w21_338 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = rlo := by rw [m21]; exact w20_338
  have w21_33c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = rhi := by rw [m21]; exact w20_33c
  have b21_440 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) = es := by rw [m21]; exact b20_440
  have b21_a40 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 8 σ13a := by rw [m21]; exact b20_a40
  have b21_a64 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA64) = BitVec.ofNat 8 σ13b := by rw [m21]; exact b20_a64
  have b21_1040 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = ds := by rw [m21]; exact b20_1040
  have b21_13a0 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = BitVec.ofNat 8 σ13a := by rw [m21]; exact b20_13a0
  have b21_14a0 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = BitVec.ofNat 8 σ13b := by rw [m21]; exact b20_14a0
  have a21_240 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m21]; exact a20_240
  have a21_260 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m21]; exact a20_260
  have a21_280 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m21]; exact a20_280
  have a21_2a0 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m21]; exact a20_2a0
  have a21_2c0 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m21]; exact a20_2c0
  have a21_2e0 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m21]; exact a20_2e0
  have a21_420 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = ev := by rw [m21]; exact a20_420
  have a21_a20 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 8 = A13a / 2 ^ ns % 2 ^ 256 := by rw [m21]; exact a20_a20
  have a21_a44 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) 8 = A13b / 2 ^ ns % 2 ^ 256 := by rw [m21]; exact a20_a44
  have a21_1020 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = dv := by rw [m21]; exact a20_1020
  have a21_1380 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = A13a / 2 ^ ns % 2 ^ 256 := by rw [m21]; exact a20_1380
  have a21_1480 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = A13b / 2 ^ ns % 2 ^ 256 := by rw [m21]; exact a20_1480
  clear a20_1480 a20_1380 a20_1020 a20_a44 a20_a20 a20_420 a20_2e0 a20_2c0 a20_2a0 a20_280 a20_260 a20_240 b20_14a0 b20_13a0 b20_1040 b20_a64 b20_a40 b20_440 w20_33c w20_338 w20_334 w20_330 w20_32c w20_328 w20_324 w20_320 w20_130 w20_12c w20_128 w20_124 w20_120 w20_11c w20_118 w20_114 w20_110 w20_10c w20_108 w20_104 w20_100 w20_fc w20_f8 w20_f4 w20_f0 w20_ec w20_e8 w20_e4 w20_e0 w20_dc w20_d8 w20_d4 w20_d0 w20_cc w20_c8 w20_c4 w20_c0 w20_bc w20_b8 w20_b4 w20_b0 w20_ac w20_a8 w20_a4 w20_a0 w20_9c w20_98 w20_94 w20_90 w20_8c w20_88 w20_84 w20_80 w20_7c w20_78 w20_70 w20_6c w20_68 w20_64 w20_60 w20_5c w20_58 w20_54 w20_50 w20_4c w20_48 w20_44 w20_40 w20_3c w20_38 w20_34 w20_30 w20_2c w20_28 w20_24 g20_15 g20_27 g20_26 g20_25 g20_24 g20_23 g20_21 g20_19 g20_18 g20_16 g20_14 g20_13 g20_12 g20_11 g20_10 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 m20 s20 u20 d20
  -- 0x1512: sv_ude8F
  obtain ⟨n22, c22, s22, sp22, rk22, R1_22, R2_22, K22, fr22⟩ := sv_ude8F (co := 0xA20) (ca := 0x1020) (cb := 0x420) (ct := 0x320) (s := ns)
    F E21 (UC0.sv F fR21) s21 sv_at_1512 sv_at_1516 (by decide) (by decide) g21_2
    g21_10 g21_11 g21_12 g21_13 g21_14 g21_15 g21_16 g21_17 hns1 (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [show 0x1020 + 0x20 = 0x1040 from rfl, b21_1040]; exact hds)
    (by rw [show 0x420 + 0x20 = 0x440 from rfl, b21_440]; exact hes)
  obtain ⟨σ22a, A22a, hσ0_22, e0_22, bb0_22, vv0_22⟩ := R1_22
  simp only [svI, svM, show 0x1020 + 0x20 = 0x1040 from rfl, show 0x420 + 0x20 = 0x440 from rfl,
    show 0x320 + 0x0 = 0x320 from rfl, show 0x320 + 0x8 = 0x328 from rfl] at e0_22
  rw [b21_1040, a21_1020, b21_440, a21_420,
    acc2_frame w21_320 w21_324, acc2_frame w21_328 w21_32c] at e0_22
  obtain ⟨σ22b, A22b, hσ1_22, e1_22, bb1_22, vv1_22⟩ := R2_22
  simp only [svI, svM, show 0x1020 + 0x20 = 0x1040 from rfl, show 0x420 + 0x20 = 0x440 from rfl,
    show 0x320 + 0x10 = 0x330 from rfl, show 0x320 + 0x18 = 0x338 from rfl] at e1_22
  rw [b21_1040, a21_1020, b21_440, a21_420,
    acc2_frame w21_330 w21_334, acc2_frame w21_338 w21_33c] at e1_22
  rw [accV_dataR F fR21 (by decide) (by decide)] at bb0_22 vv0_22 bb1_22 vv1_22
  have t22 : Steps n0 n22 := t21.trans c22
  have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
  have E22 : SvCode n22.mem := E21.fr F fr22
  have V22 : SvSaves B n22.mem v := V21.keepL K22 (by decide)
  have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk22 (3 : Fin 32) (by decide), g21_3]
  have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk22 (4 : Fin 32) (by decide), g21_4]
  have g22_8 : reg n22 (8 : Fin 32) = BitVec.ofNat 32 ns := by rw [rk22 (8 : Fin 32) (by decide), g21_8]
  have g22_18 : reg n22 (18 : Fin 32) = out := by rw [rk22 (18 : Fin 32) (by decide), g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [rk22 (19 : Fin 32) (by decide), g21_19]
  have g22_21 : reg n22 (21 : Fin 32) = s5v := by rw [rk22 (21 : Fin 32) (by decide), g21_21]
  have g22_23 : reg n22 (23 : Fin 32) = dlo := by rw [rk22 (23 : Fin 32) (by decide), g21_23]
  have g22_24 : reg n22 (24 : Fin 32) = BitVec.ofNat 32 0x3FCC4268 := by rw [rk22 (24 : Fin 32) (by decide), g21_24]
  have g22_25 : reg n22 (25 : Fin 32) = dhi := by rw [rk22 (25 : Fin 32) (by decide), g21_25]
  have g22_26 : reg n22 (26 : Fin 32) = x26 := by rw [rk22 (26 : Fin 32) (by decide), g21_26]
  have g22_27 : reg n22 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk22 (27 : Fin 32) (by decide), g21_27]
  have g22_2 : reg n22 sp = B + 0x21A0 := sp22
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
  have w22_5c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 ns := (K22.w32 (by decide) (by decide)).trans w21_5c
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
  have w22_320 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ulo := (K22.w32 (by decide) (by decide)).trans w21_320
  have w22_324 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = uhi := (K22.w32 (by decide) (by decide)).trans w21_324
  have w22_328 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = vlo := (K22.w32 (by decide) (by decide)).trans w21_328
  have w22_32c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = vhi := (K22.w32 (by decide) (by decide)).trans w21_32c
  have w22_330 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = qlo := (K22.w32 (by decide) (by decide)).trans w21_330
  have w22_334 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = qhi := (K22.w32 (by decide) (by decide)).trans w21_334
  have w22_338 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = rlo := (K22.w32 (by decide) (by decide)).trans w21_338
  have w22_33c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = rhi := (K22.w32 (by decide) (by decide)).trans w21_33c
  have b22_440 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) = es := (K22.b8 (by decide) (by decide)).trans b21_440
  have b22_1040 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = ds := (K22.b8 (by decide) (by decide)).trans b21_1040
  have b22_13a0 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = BitVec.ofNat 8 σ13a := (K22.b8 (by decide) (by decide)).trans b21_13a0
  have b22_14a0 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = BitVec.ofNat 8 σ13b := (K22.b8 (by decide) (by decide)).trans b21_14a0
  have a22_240 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := (K22.acc (by decide) (by decide)).trans a21_240
  have a22_260 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := (K22.acc (by decide) (by decide)).trans a21_260
  have a22_280 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := (K22.acc (by decide) (by decide)).trans a21_280
  have a22_2a0 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K22.acc (by decide) (by decide)).trans a21_2a0
  have a22_2c0 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K22.acc (by decide) (by decide)).trans a21_2c0
  have a22_2e0 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K22.acc (by decide) (by decide)).trans a21_2e0
  have a22_420 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = ev := (K22.acc (by decide) (by decide)).trans a21_420
  have a22_1020 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = dv := (K22.acc (by decide) (by decide)).trans a21_1020
  have a22_1380 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = A13a / 2 ^ ns % 2 ^ 256 := (K22.acc (by decide) (by decide)).trans a21_1380
  have a22_1480 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = A13b / 2 ^ ns % 2 ^ 256 := (K22.acc (by decide) (by decide)).trans a21_1480
  have a22_a20 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 8 = (lrsm8 σ22a A22a ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).2 := vv0_22
  have a22_a44 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) 8 = (lrsm8 σ22b A22b ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).2 := vv1_22
  have b22_a40 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 8 (lrsm8 σ22a A22a ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).1 := byte_of_toNat bb0_22
  have b22_a64 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA64) = BitVec.ofNat 8 (lrsm8 σ22b A22b ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).1 := byte_of_toNat bb1_22
  clear a21_1480 a21_1380 a21_1020 a21_a44 a21_a20 a21_420 a21_2e0 a21_2c0 a21_2a0 a21_280 a21_260 a21_240 b21_14a0 b21_13a0 b21_1040 b21_a64 b21_a40 b21_440 w21_33c w21_338 w21_334 w21_330 w21_32c w21_328 w21_324 w21_320 w21_130 w21_12c w21_128 w21_124 w21_120 w21_11c w21_118 w21_114 w21_110 w21_10c w21_108 w21_104 w21_100 w21_fc w21_f8 w21_f4 w21_f0 w21_ec w21_e8 w21_e4 w21_e0 w21_dc w21_d8 w21_d4 w21_d0 w21_cc w21_c8 w21_c4 w21_c0 w21_bc w21_b8 w21_b4 w21_b0 w21_ac w21_a8 w21_a4 w21_a0 w21_9c w21_98 w21_94 w21_90 w21_8c w21_88 w21_84 w21_80 w21_7c w21_78 w21_70 w21_6c w21_68 w21_64 w21_60 w21_5c w21_58 w21_54 w21_50 w21_4c w21_48 w21_44 w21_40 w21_3c w21_38 w21_34 w21_30 w21_2c w21_28 w21_24 g21_17 g21_27 g21_26 g21_25 g21_24 g21_23 g21_21 g21_19 g21_18 g21_16 g21_15 g21_14 g21_13 g21_12 g21_11 g21_10 g21_8 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 rb21 s21 m21 u21 c21
  -- 0x151A
  obtain ⟨n23, c23, u23⟩ := s22.block svIvB151a E22.self svIvB151a_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m23 : n23.mem = n22.mem := u23.mem
  have s23 : St n23.mem SV n23 0x152E (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
  have rb23 : ∀ q, reg n23 q = (runBlock svIvB151a (n22.mem, reg n22)).2 q := fun q => by rw [u23.regs]
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
  have g23_8 : reg n23 (8 : Fin 32) = BitVec.ofNat 32 ns := by
    rw [rb23, runBlock_reg _ _ _ (8 : Fin 32) s22.zero (by decide), g22_8]
  have g23_18 : reg n23 (18 : Fin 32) = out := by
    rw [rb23, runBlock_reg _ _ _ (18 : Fin 32) s22.zero (by decide), g22_18]
  have g23_19 : reg n23 (19 : Fin 32) = bp := by
    rw [rb23, runBlock_reg _ _ _ (19 : Fin 32) s22.zero (by decide), g22_19]
  have g23_21 : reg n23 (21 : Fin 32) = s5v := by
    rw [rb23, runBlock_reg _ _ _ (21 : Fin 32) s22.zero (by decide), g22_21]
  have g23_23 : reg n23 (23 : Fin 32) = dlo := by
    rw [rb23, runBlock_reg _ _ _ (23 : Fin 32) s22.zero (by decide), g22_23]
  have g23_24 : reg n23 (24 : Fin 32) = BitVec.ofNat 32 0x3FCC4268 := by
    rw [rb23, runBlock_reg _ _ _ (24 : Fin 32) s22.zero (by decide), g22_24]
  have g23_25 : reg n23 (25 : Fin 32) = dhi := by
    rw [rb23, runBlock_reg _ _ _ (25 : Fin 32) s22.zero (by decide), g22_25]
  have g23_26 : reg n23 (26 : Fin 32) = x26 := by
    rw [rb23, runBlock_reg _ _ _ (26 : Fin 32) s22.zero (by decide), g22_26]
  have g23_27 : reg n23 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb23, runBlock_reg _ _ _ (27 : Fin 32) s22.zero (by decide), g22_27]
  have g23_10 : reg n23 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1020 := by
    rw [rb23]; simp +decide only [runBlock, BInstr.run, svIvB151a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g22_2, g22_3, g22_4, g22_8, g22_18, g22_19, g22_21, g22_23, g22_24, g22_25, g22_26, g22_27, s22.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g23_11 : reg n23 a1 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb23]; simp +decide only [runBlock, BInstr.run, svIvB151a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g22_2, g22_3, g22_4, g22_8, g22_18, g22_19, g22_21, g22_23, g22_24, g22_25, g22_26, g22_27, s22.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g23_12 : reg n23 a2 = BitVec.ofNat 32 0x24 := by
    rw [rb23]; simp +decide only [runBlock, BInstr.run, svIvB151a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g22_2, g22_3, g22_4, g22_8, g22_18, g22_19, g22_21, g22_23, g22_24, g22_25, g22_26, g22_27, s22.zero])
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
  have w23_5c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 ns := by rw [m23]; exact w22_5c
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
  have w23_320 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ulo := by rw [m23]; exact w22_320
  have w23_324 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = uhi := by rw [m23]; exact w22_324
  have w23_328 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = vlo := by rw [m23]; exact w22_328
  have w23_32c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = vhi := by rw [m23]; exact w22_32c
  have w23_330 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = qlo := by rw [m23]; exact w22_330
  have w23_334 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = qhi := by rw [m23]; exact w22_334
  have w23_338 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = rlo := by rw [m23]; exact w22_338
  have w23_33c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = rhi := by rw [m23]; exact w22_33c
  have b23_440 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) = es := by rw [m23]; exact b22_440
  have b23_a40 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 8 (lrsm8 σ22a A22a ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).1 := by rw [m23]; exact b22_a40
  have b23_a64 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA64) = BitVec.ofNat 8 (lrsm8 σ22b A22b ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).1 := by rw [m23]; exact b22_a64
  have b23_1040 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = ds := by rw [m23]; exact b22_1040
  have b23_13a0 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = BitVec.ofNat 8 σ13a := by rw [m23]; exact b22_13a0
  have b23_14a0 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = BitVec.ofNat 8 σ13b := by rw [m23]; exact b22_14a0
  have a23_240 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m23]; exact a22_240
  have a23_260 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m23]; exact a22_260
  have a23_280 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m23]; exact a22_280
  have a23_2a0 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m23]; exact a22_2a0
  have a23_2c0 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m23]; exact a22_2c0
  have a23_2e0 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m23]; exact a22_2e0
  have a23_420 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = ev := by rw [m23]; exact a22_420
  have a23_a20 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 8 = (lrsm8 σ22a A22a ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).2 := by rw [m23]; exact a22_a20
  have a23_a44 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) 8 = (lrsm8 σ22b A22b ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).2 := by rw [m23]; exact a22_a44
  have a23_1020 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = dv := by rw [m23]; exact a22_1020
  have a23_1380 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = A13a / 2 ^ ns % 2 ^ 256 := by rw [m23]; exact a22_1380
  have a23_1480 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = A13b / 2 ^ ns % 2 ^ 256 := by rw [m23]; exact a22_1480
  clear b22_a64 b22_a40 a22_a44 a22_a20 a22_1480 a22_1380 a22_1020 a22_420 a22_2e0 a22_2c0 a22_2a0 a22_280 a22_260 a22_240 b22_14a0 b22_13a0 b22_1040 b22_440 w22_33c w22_338 w22_334 w22_330 w22_32c w22_328 w22_324 w22_320 w22_130 w22_12c w22_128 w22_124 w22_120 w22_11c w22_118 w22_114 w22_110 w22_10c w22_108 w22_104 w22_100 w22_fc w22_f8 w22_f4 w22_f0 w22_ec w22_e8 w22_e4 w22_e0 w22_dc w22_d8 w22_d4 w22_d0 w22_cc w22_c8 w22_c4 w22_c0 w22_bc w22_b8 w22_b4 w22_b0 w22_ac w22_a8 w22_a4 w22_a0 w22_9c w22_98 w22_94 w22_90 w22_8c w22_88 w22_84 w22_80 w22_7c w22_78 w22_70 w22_6c w22_68 w22_64 w22_60 w22_5c w22_58 w22_54 w22_50 w22_4c w22_48 w22_44 w22_40 w22_3c w22_38 w22_34 w22_30 w22_2c w22_28 w22_24 g22_2 g22_27 g22_26 g22_25 g22_24 g22_23 g22_21 g22_19 g22_18 g22_8 g22_4 g22_3 V22 E22 fR22 t22 vv1_22 bb1_22 vv0_22 bb0_22 fr22 K22 rk22 sp22 s22 c22
  -- 0x152E: memcpy
  obtain ⟨n24, P24, K24, X24⟩ := sv_mc (c := 0x1020) (d := 0xA20) (N := 0x24) F E23 s23 sv_at_152e sv_at_1532
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
  have g24_8 : reg n24 (8 : Fin 32) = BitVec.ofNat 32 ns := by rw [P24.regs (8 : Fin 32) (by decide), g23_8]
  have g24_18 : reg n24 (18 : Fin 32) = out := by rw [P24.regs (18 : Fin 32) (by decide), g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = bp := by rw [P24.regs (19 : Fin 32) (by decide), g23_19]
  have g24_21 : reg n24 (21 : Fin 32) = s5v := by rw [P24.regs (21 : Fin 32) (by decide), g23_21]
  have g24_23 : reg n24 (23 : Fin 32) = dlo := by rw [P24.regs (23 : Fin 32) (by decide), g23_23]
  have g24_24 : reg n24 (24 : Fin 32) = BitVec.ofNat 32 0x3FCC4268 := by rw [P24.regs (24 : Fin 32) (by decide), g23_24]
  have g24_25 : reg n24 (25 : Fin 32) = dhi := by rw [P24.regs (25 : Fin 32) (by decide), g23_25]
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
  have w24_5c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 ns := (K24.w32 (by decide) (by decide)).trans w23_5c
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
  have w24_320 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ulo := (K24.w32 (by decide) (by decide)).trans w23_320
  have w24_324 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = uhi := (K24.w32 (by decide) (by decide)).trans w23_324
  have w24_328 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = vlo := (K24.w32 (by decide) (by decide)).trans w23_328
  have w24_32c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = vhi := (K24.w32 (by decide) (by decide)).trans w23_32c
  have w24_330 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = qlo := (K24.w32 (by decide) (by decide)).trans w23_330
  have w24_334 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = qhi := (K24.w32 (by decide) (by decide)).trans w23_334
  have w24_338 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = rlo := (K24.w32 (by decide) (by decide)).trans w23_338
  have w24_33c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = rhi := (K24.w32 (by decide) (by decide)).trans w23_33c
  have b24_440 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) = es := (K24.b8 (by decide) (by decide)).trans b23_440
  have b24_a40 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 8 (lrsm8 σ22a A22a ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).1 := (K24.b8 (by decide) (by decide)).trans b23_a40
  have b24_a64 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA64) = BitVec.ofNat 8 (lrsm8 σ22b A22b ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).1 := (K24.b8 (by decide) (by decide)).trans b23_a64
  have b24_13a0 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = BitVec.ofNat 8 σ13a := (K24.b8 (by decide) (by decide)).trans b23_13a0
  have b24_14a0 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = BitVec.ofNat 8 σ13b := (K24.b8 (by decide) (by decide)).trans b23_14a0
  have b24_1040 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = BitVec.ofNat 8 (lrsm8 σ22a A22a ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).1 := by rw [show 0x1040 = 0x1020 + 0x20 from rfl, X24 0x20 (by decide)]; exact b23_a40
  have a24_240 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := (K24.acc (by decide) (by decide)).trans a23_240
  have a24_260 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := (K24.acc (by decide) (by decide)).trans a23_260
  have a24_280 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := (K24.acc (by decide) (by decide)).trans a23_280
  have a24_2a0 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K24.acc (by decide) (by decide)).trans a23_2a0
  have a24_2c0 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K24.acc (by decide) (by decide)).trans a23_2c0
  have a24_2e0 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K24.acc (by decide) (by decide)).trans a23_2e0
  have a24_420 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = ev := (K24.acc (by decide) (by decide)).trans a23_420
  have a24_a20 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 8 = (lrsm8 σ22a A22a ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).2 := (K24.acc (by decide) (by decide)).trans a23_a20
  have a24_a44 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) 8 = (lrsm8 σ22b A22b ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).2 := (K24.acc (by decide) (by decide)).trans a23_a44
  have a24_1380 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = A13a / 2 ^ ns % 2 ^ 256 := (K24.acc (by decide) (by decide)).trans a23_1380
  have a24_1480 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = A13b / 2 ^ ns % 2 ^ 256 := (K24.acc (by decide) (by decide)).trans a23_1480
  have a24_1020 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = (lrsm8 σ22a A22a ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).2 := (accV_S 8 fun q hq => by
    rw [show 0x1020 + q = 0x1020 + (0x0 + q) by omega, X24 (0x0 + q) (by omega),
      show 0xA20 + (0x0 + q) = 0xA20 + q by omega]).trans a23_a20
  clear a23_1480 a23_1380 a23_1020 a23_a44 a23_a20 a23_420 a23_2e0 a23_2c0 a23_2a0 a23_280 a23_260 a23_240 b23_14a0 b23_13a0 b23_1040 b23_a64 b23_a40 b23_440 w23_33c w23_338 w23_334 w23_330 w23_32c w23_328 w23_324 w23_320 w23_130 w23_12c w23_128 w23_124 w23_120 w23_11c w23_118 w23_114 w23_110 w23_10c w23_108 w23_104 w23_100 w23_fc w23_f8 w23_f4 w23_f0 w23_ec w23_e8 w23_e4 w23_e0 w23_dc w23_d8 w23_d4 w23_d0 w23_cc w23_c8 w23_c4 w23_c0 w23_bc w23_b8 w23_b4 w23_b0 w23_ac w23_a8 w23_a4 w23_a0 w23_9c w23_98 w23_94 w23_90 w23_8c w23_88 w23_84 w23_80 w23_7c w23_78 w23_70 w23_6c w23_68 w23_64 w23_60 w23_5c w23_58 w23_54 w23_50 w23_4c w23_48 w23_44 w23_40 w23_3c w23_38 w23_34 w23_30 w23_2c w23_28 w23_24 g23_12 g23_11 g23_10 g23_27 g23_26 g23_25 g23_24 g23_23 g23_21 g23_19 g23_18 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 rb23 s23 m23 u23 c23
  -- 0x1536
  obtain ⟨n25, c25, u25⟩ := s24.block svIvB1536 E24.self svIvB1536_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m25 : n25.mem = n24.mem := u25.mem
  have s25 : St n25.mem SV n25 0x1546 (reg n25) := ⟨u25.pc, rfl, fun _ => rfl⟩
  have rb25 : ∀ q, reg n25 q = (runBlock svIvB1536 (n24.mem, reg n24)).2 q := fun q => by rw [u25.regs]
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
  have g25_8 : reg n25 (8 : Fin 32) = BitVec.ofNat 32 ns := by
    rw [rb25, runBlock_reg _ _ _ (8 : Fin 32) s24.zero (by decide), g24_8]
  have g25_18 : reg n25 (18 : Fin 32) = out := by
    rw [rb25, runBlock_reg _ _ _ (18 : Fin 32) s24.zero (by decide), g24_18]
  have g25_19 : reg n25 (19 : Fin 32) = bp := by
    rw [rb25, runBlock_reg _ _ _ (19 : Fin 32) s24.zero (by decide), g24_19]
  have g25_21 : reg n25 (21 : Fin 32) = s5v := by
    rw [rb25, runBlock_reg _ _ _ (21 : Fin 32) s24.zero (by decide), g24_21]
  have g25_23 : reg n25 (23 : Fin 32) = dlo := by
    rw [rb25, runBlock_reg _ _ _ (23 : Fin 32) s24.zero (by decide), g24_23]
  have g25_24 : reg n25 (24 : Fin 32) = BitVec.ofNat 32 0x3FCC4268 := by
    rw [rb25, runBlock_reg _ _ _ (24 : Fin 32) s24.zero (by decide), g24_24]
  have g25_25 : reg n25 (25 : Fin 32) = dhi := by
    rw [rb25, runBlock_reg _ _ _ (25 : Fin 32) s24.zero (by decide), g24_25]
  have g25_26 : reg n25 (26 : Fin 32) = x26 := by
    rw [rb25, runBlock_reg _ _ _ (26 : Fin 32) s24.zero (by decide), g24_26]
  have g25_27 : reg n25 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb25, runBlock_reg _ _ _ (27 : Fin 32) s24.zero (by decide), g24_27]
  have g25_10 : reg n25 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb25]; simp +decide only [runBlock, BInstr.run, svIvB1536, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_18, g24_19, g24_21, g24_23, g24_24, g24_25, g24_26, g24_27, s24.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g25_11 : reg n25 a1 = B + 0x21A0 + BitVec.ofNat 32 0xA44 := by
    rw [rb25]; simp +decide only [runBlock, BInstr.run, svIvB1536, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_18, g24_19, g24_21, g24_23, g24_24, g24_25, g24_26, g24_27, s24.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g25_12 : reg n25 a2 = BitVec.ofNat 32 0x24 := by
    rw [rb25]; simp +decide only [runBlock, BInstr.run, svIvB1536, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_18, g24_19, g24_21, g24_23, g24_24, g24_25, g24_26, g24_27, s24.zero])
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
  have w25_5c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 ns := by rw [m25]; exact w24_5c
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
  have w25_320 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ulo := by rw [m25]; exact w24_320
  have w25_324 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = uhi := by rw [m25]; exact w24_324
  have w25_328 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = vlo := by rw [m25]; exact w24_328
  have w25_32c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = vhi := by rw [m25]; exact w24_32c
  have w25_330 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = qlo := by rw [m25]; exact w24_330
  have w25_334 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = qhi := by rw [m25]; exact w24_334
  have w25_338 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = rlo := by rw [m25]; exact w24_338
  have w25_33c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = rhi := by rw [m25]; exact w24_33c
  have b25_440 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) = es := by rw [m25]; exact b24_440
  have b25_a40 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 8 (lrsm8 σ22a A22a ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).1 := by rw [m25]; exact b24_a40
  have b25_a64 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA64) = BitVec.ofNat 8 (lrsm8 σ22b A22b ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).1 := by rw [m25]; exact b24_a64
  have b25_1040 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = BitVec.ofNat 8 (lrsm8 σ22a A22a ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).1 := by rw [m25]; exact b24_1040
  have b25_13a0 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = BitVec.ofNat 8 σ13a := by rw [m25]; exact b24_13a0
  have b25_14a0 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = BitVec.ofNat 8 σ13b := by rw [m25]; exact b24_14a0
  have a25_240 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m25]; exact a24_240
  have a25_260 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m25]; exact a24_260
  have a25_280 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m25]; exact a24_280
  have a25_2a0 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m25]; exact a24_2a0
  have a25_2c0 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m25]; exact a24_2c0
  have a25_2e0 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m25]; exact a24_2e0
  have a25_420 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = ev := by rw [m25]; exact a24_420
  have a25_a20 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 8 = (lrsm8 σ22a A22a ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).2 := by rw [m25]; exact a24_a20
  have a25_a44 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) 8 = (lrsm8 σ22b A22b ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).2 := by rw [m25]; exact a24_a44
  have a25_1020 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = (lrsm8 σ22a A22a ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).2 := by rw [m25]; exact a24_1020
  have a25_1380 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = A13a / 2 ^ ns % 2 ^ 256 := by rw [m25]; exact a24_1380
  have a25_1480 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = A13b / 2 ^ ns % 2 ^ 256 := by rw [m25]; exact a24_1480
  clear a24_1020 a24_1480 a24_1380 a24_a44 a24_a20 a24_420 a24_2e0 a24_2c0 a24_2a0 a24_280 a24_260 a24_240 b24_1040 b24_14a0 b24_13a0 b24_a64 b24_a40 b24_440 w24_33c w24_338 w24_334 w24_330 w24_32c w24_328 w24_324 w24_320 w24_130 w24_12c w24_128 w24_124 w24_120 w24_11c w24_118 w24_114 w24_110 w24_10c w24_108 w24_104 w24_100 w24_fc w24_f8 w24_f4 w24_f0 w24_ec w24_e8 w24_e4 w24_e0 w24_dc w24_d8 w24_d4 w24_d0 w24_cc w24_c8 w24_c4 w24_c0 w24_bc w24_b8 w24_b4 w24_b0 w24_ac w24_a8 w24_a4 w24_a0 w24_9c w24_98 w24_94 w24_90 w24_8c w24_88 w24_84 w24_80 w24_7c w24_78 w24_70 w24_6c w24_68 w24_64 w24_60 w24_5c w24_58 w24_54 w24_50 w24_4c w24_48 w24_44 w24_40 w24_3c w24_38 w24_34 w24_30 w24_2c w24_28 w24_24 g24_27 g24_26 g24_25 g24_24 g24_23 g24_21 g24_19 g24_18 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 s24 X24 K24 P24
  -- 0x1546: memcpy
  obtain ⟨n26, P26, K26, X26⟩ := sv_mc (c := 0x420) (d := 0xA44) (N := 0x24) F E25 s25 sv_at_1546 sv_at_154a
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
  have g26_8 : reg n26 (8 : Fin 32) = BitVec.ofNat 32 ns := by rw [P26.regs (8 : Fin 32) (by decide), g25_8]
  have g26_18 : reg n26 (18 : Fin 32) = out := by rw [P26.regs (18 : Fin 32) (by decide), g25_18]
  have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [P26.regs (19 : Fin 32) (by decide), g25_19]
  have g26_21 : reg n26 (21 : Fin 32) = s5v := by rw [P26.regs (21 : Fin 32) (by decide), g25_21]
  have g26_23 : reg n26 (23 : Fin 32) = dlo := by rw [P26.regs (23 : Fin 32) (by decide), g25_23]
  have g26_24 : reg n26 (24 : Fin 32) = BitVec.ofNat 32 0x3FCC4268 := by rw [P26.regs (24 : Fin 32) (by decide), g25_24]
  have g26_25 : reg n26 (25 : Fin 32) = dhi := by rw [P26.regs (25 : Fin 32) (by decide), g25_25]
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
  have w26_5c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 ns := (K26.w32 (by decide) (by decide)).trans w25_5c
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
  have w26_320 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ulo := (K26.w32 (by decide) (by decide)).trans w25_320
  have w26_324 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = uhi := (K26.w32 (by decide) (by decide)).trans w25_324
  have w26_328 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = vlo := (K26.w32 (by decide) (by decide)).trans w25_328
  have w26_32c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = vhi := (K26.w32 (by decide) (by decide)).trans w25_32c
  have w26_330 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = qlo := (K26.w32 (by decide) (by decide)).trans w25_330
  have w26_334 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = qhi := (K26.w32 (by decide) (by decide)).trans w25_334
  have w26_338 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = rlo := (K26.w32 (by decide) (by decide)).trans w25_338
  have w26_33c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = rhi := (K26.w32 (by decide) (by decide)).trans w25_33c
  have b26_a40 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 8 (lrsm8 σ22a A22a ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).1 := (K26.b8 (by decide) (by decide)).trans b25_a40
  have b26_a64 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA64) = BitVec.ofNat 8 (lrsm8 σ22b A22b ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).1 := (K26.b8 (by decide) (by decide)).trans b25_a64
  have b26_1040 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = BitVec.ofNat 8 (lrsm8 σ22a A22a ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).1 := (K26.b8 (by decide) (by decide)).trans b25_1040
  have b26_13a0 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = BitVec.ofNat 8 σ13a := (K26.b8 (by decide) (by decide)).trans b25_13a0
  have b26_14a0 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = BitVec.ofNat 8 σ13b := (K26.b8 (by decide) (by decide)).trans b25_14a0
  have b26_440 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) = BitVec.ofNat 8 (lrsm8 σ22b A22b ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).1 := by rw [show 0x440 = 0x420 + 0x20 from rfl, X26 0x20 (by decide)]; exact b25_a64
  have a26_240 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := (K26.acc (by decide) (by decide)).trans a25_240
  have a26_260 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := (K26.acc (by decide) (by decide)).trans a25_260
  have a26_280 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := (K26.acc (by decide) (by decide)).trans a25_280
  have a26_2a0 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K26.acc (by decide) (by decide)).trans a25_2a0
  have a26_2c0 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K26.acc (by decide) (by decide)).trans a25_2c0
  have a26_2e0 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K26.acc (by decide) (by decide)).trans a25_2e0
  have a26_a20 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 8 = (lrsm8 σ22a A22a ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).2 := (K26.acc (by decide) (by decide)).trans a25_a20
  have a26_a44 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) 8 = (lrsm8 σ22b A22b ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).2 := (K26.acc (by decide) (by decide)).trans a25_a44
  have a26_1020 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = (lrsm8 σ22a A22a ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).2 := (K26.acc (by decide) (by decide)).trans a25_1020
  have a26_1380 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = A13a / 2 ^ ns % 2 ^ 256 := (K26.acc (by decide) (by decide)).trans a25_1380
  have a26_1480 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = A13b / 2 ^ ns % 2 ^ 256 := (K26.acc (by decide) (by decide)).trans a25_1480
  have a26_420 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = (lrsm8 σ22b A22b ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).2 := (accV_S 8 fun q hq => by
    rw [show 0x420 + q = 0x420 + (0x0 + q) by omega, X26 (0x0 + q) (by omega),
      show 0xA44 + (0x0 + q) = 0xA44 + q by omega]).trans a25_a44
  clear a25_1480 a25_1380 a25_1020 a25_a44 a25_a20 a25_420 a25_2e0 a25_2c0 a25_2a0 a25_280 a25_260 a25_240 b25_14a0 b25_13a0 b25_1040 b25_a64 b25_a40 b25_440 w25_33c w25_338 w25_334 w25_330 w25_32c w25_328 w25_324 w25_320 w25_130 w25_12c w25_128 w25_124 w25_120 w25_11c w25_118 w25_114 w25_110 w25_10c w25_108 w25_104 w25_100 w25_fc w25_f8 w25_f4 w25_f0 w25_ec w25_e8 w25_e4 w25_e0 w25_dc w25_d8 w25_d4 w25_d0 w25_cc w25_c8 w25_c4 w25_c0 w25_bc w25_b8 w25_b4 w25_b0 w25_ac w25_a8 w25_a4 w25_a0 w25_9c w25_98 w25_94 w25_90 w25_8c w25_88 w25_84 w25_80 w25_7c w25_78 w25_70 w25_6c w25_68 w25_64 w25_60 w25_5c w25_58 w25_54 w25_50 w25_4c w25_48 w25_44 w25_40 w25_3c w25_38 w25_34 w25_30 w25_2c w25_28 w25_24 g25_12 g25_11 g25_10 g25_27 g25_26 g25_25 g25_24 g25_23 g25_21 g25_19 g25_18 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 fr25 rb25 s25 m25 u25 c25
  -- 0x154E: lw
  obtain ⟨n27, d27, u27⟩ := s26.lw E26.self sv_at_154e (off' := 0x1550) (by decide)
    (by rw [g26_2, show B + 0x21A0 + 0x78 = B + 0x21A0 + BitVec.ofNat 32 0x78 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s27 : St n27.mem SV n27 0x1550 (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
  have m27 : n27.mem = n26.mem := u27.mem
  have fr27 : ∀ x, SvR B x → n27.mem x = n26.mem x := fun x _ => by rw [m27]
  have t27 : Steps n0 n27 := t26.trans (.single d27)
  have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
  have E27 : SvCode n27.mem := E26.fr F fr27
  have V27 : SvSaves B n27.mem v := V26.same m27
  have g27_2 : reg n27 sp = B + 0x21A0 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_2]
  have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u27.regs, upd_ne (by decide) (by decide), g26_3]
  have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u27.regs, upd_ne (by decide) (by decide), g26_4]
  have g27_8 : reg n27 (8 : Fin 32) = BitVec.ofNat 32 ns := by rw [u27.regs, upd_ne (by decide) (by decide), g26_8]
  have g27_18 : reg n27 (18 : Fin 32) = out := by rw [u27.regs, upd_ne (by decide) (by decide), g26_18]
  have g27_19 : reg n27 (19 : Fin 32) = bp := by rw [u27.regs, upd_ne (by decide) (by decide), g26_19]
  have g27_21 : reg n27 (21 : Fin 32) = s5v := by rw [u27.regs, upd_ne (by decide) (by decide), g26_21]
  have g27_23 : reg n27 (23 : Fin 32) = dlo := by rw [u27.regs, upd_ne (by decide) (by decide), g26_23]
  have g27_24 : reg n27 (24 : Fin 32) = BitVec.ofNat 32 0x3FCC4268 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_24]
  have g27_25 : reg n27 (25 : Fin 32) = dhi := by rw [u27.regs, upd_ne (by decide) (by decide), g26_25]
  have g27_26 : reg n27 (26 : Fin 32) = x26 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_26]
  have g27_27 : reg n27 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_27]
  have g27_10 : reg n27 a0 = rem := by
    rw [u27.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g26_2, show B + 0x21A0 + 0x78 = B + 0x21A0 + BitVec.ofNat 32 0x78 by sv_addr, w26_78]
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
  have w27_5c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 ns := by rw [m27]; exact w26_5c
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
  have w27_320 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ulo := by rw [m27]; exact w26_320
  have w27_324 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = uhi := by rw [m27]; exact w26_324
  have w27_328 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = vlo := by rw [m27]; exact w26_328
  have w27_32c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = vhi := by rw [m27]; exact w26_32c
  have w27_330 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = qlo := by rw [m27]; exact w26_330
  have w27_334 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = qhi := by rw [m27]; exact w26_334
  have w27_338 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = rlo := by rw [m27]; exact w26_338
  have w27_33c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = rhi := by rw [m27]; exact w26_33c
  have b27_440 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) = BitVec.ofNat 8 (lrsm8 σ22b A22b ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).1 := by rw [m27]; exact b26_440
  have b27_a40 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 8 (lrsm8 σ22a A22a ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).1 := by rw [m27]; exact b26_a40
  have b27_a64 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA64) = BitVec.ofNat 8 (lrsm8 σ22b A22b ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).1 := by rw [m27]; exact b26_a64
  have b27_1040 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = BitVec.ofNat 8 (lrsm8 σ22a A22a ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).1 := by rw [m27]; exact b26_1040
  have b27_13a0 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = BitVec.ofNat 8 σ13a := by rw [m27]; exact b26_13a0
  have b27_14a0 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = BitVec.ofNat 8 σ13b := by rw [m27]; exact b26_14a0
  have a27_240 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m27]; exact a26_240
  have a27_260 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m27]; exact a26_260
  have a27_280 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m27]; exact a26_280
  have a27_2a0 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m27]; exact a26_2a0
  have a27_2c0 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m27]; exact a26_2c0
  have a27_2e0 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m27]; exact a26_2e0
  have a27_420 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = (lrsm8 σ22b A22b ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).2 := by rw [m27]; exact a26_420
  have a27_a20 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 8 = (lrsm8 σ22a A22a ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).2 := by rw [m27]; exact a26_a20
  have a27_a44 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) 8 = (lrsm8 σ22b A22b ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).2 := by rw [m27]; exact a26_a44
  have a27_1020 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = (lrsm8 σ22a A22a ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).2 := by rw [m27]; exact a26_1020
  have a27_1380 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = A13a / 2 ^ ns % 2 ^ 256 := by rw [m27]; exact a26_1380
  have a27_1480 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = A13b / 2 ^ ns % 2 ^ 256 := by rw [m27]; exact a26_1480
  clear a26_420 a26_1480 a26_1380 a26_1020 a26_a44 a26_a20 a26_2e0 a26_2c0 a26_2a0 a26_280 a26_260 a26_240 b26_440 b26_14a0 b26_13a0 b26_1040 b26_a64 b26_a40 w26_33c w26_338 w26_334 w26_330 w26_32c w26_328 w26_324 w26_320 w26_130 w26_12c w26_128 w26_124 w26_120 w26_11c w26_118 w26_114 w26_110 w26_10c w26_108 w26_104 w26_100 w26_fc w26_f8 w26_f4 w26_f0 w26_ec w26_e8 w26_e4 w26_e0 w26_dc w26_d8 w26_d4 w26_d0 w26_cc w26_c8 w26_c4 w26_c0 w26_bc w26_b8 w26_b4 w26_b0 w26_ac w26_a8 w26_a4 w26_a0 w26_9c w26_98 w26_94 w26_90 w26_8c w26_88 w26_84 w26_80 w26_7c w26_78 w26_70 w26_6c w26_68 w26_64 w26_60 w26_5c w26_58 w26_54 w26_50 w26_4c w26_48 w26_44 w26_40 w26_3c w26_38 w26_34 w26_30 w26_2c w26_28 w26_24 g26_27 g26_26 g26_25 g26_24 g26_23 g26_21 g26_19 g26_18 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 s26 X26 K26 P26
  -- 0x1550
  obtain ⟨n28, c28, u28⟩ := s27.block svIvB1550 E27.self svIvB1550_end
    ⟨trivial, trivial⟩
  have m28 : n28.mem = n27.mem := u28.mem
  have s28 : St n28.mem SV n28 0x1552 (reg n28) := ⟨u28.pc, rfl, fun _ => rfl⟩
  have rb28 : ∀ q, reg n28 q = (runBlock svIvB1550 (n27.mem, reg n27)).2 q := fun q => by rw [u28.regs]
  have fr28 : ∀ x, SvR B x → n28.mem x = n27.mem x := fun x _ => by rw [m28]
  have t28 : Steps n0 n28 := t27.trans c28
  have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
  have E28 : SvCode n28.mem := E27.fr F fr28
  have V28 : SvSaves B n28.mem v := V27.same m28
  have g28_2 : reg n28 sp = B + 0x21A0 := by
    rw [rb28, runBlock_reg _ _ _ sp s27.zero (by decide), g27_2]
  have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb28, runBlock_reg _ _ _ (3 : Fin 32) s27.zero (by decide), g27_3]
  have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb28, runBlock_reg _ _ _ (4 : Fin 32) s27.zero (by decide), g27_4]
  have g28_8 : reg n28 (8 : Fin 32) = BitVec.ofNat 32 ns := by
    rw [rb28, runBlock_reg _ _ _ (8 : Fin 32) s27.zero (by decide), g27_8]
  have g28_18 : reg n28 (18 : Fin 32) = out := by
    rw [rb28, runBlock_reg _ _ _ (18 : Fin 32) s27.zero (by decide), g27_18]
  have g28_19 : reg n28 (19 : Fin 32) = bp := by
    rw [rb28, runBlock_reg _ _ _ (19 : Fin 32) s27.zero (by decide), g27_19]
  have g28_21 : reg n28 (21 : Fin 32) = s5v := by
    rw [rb28, runBlock_reg _ _ _ (21 : Fin 32) s27.zero (by decide), g27_21]
  have g28_23 : reg n28 (23 : Fin 32) = dlo := by
    rw [rb28, runBlock_reg _ _ _ (23 : Fin 32) s27.zero (by decide), g27_23]
  have g28_24 : reg n28 (24 : Fin 32) = BitVec.ofNat 32 0x3FCC4268 := by
    rw [rb28, runBlock_reg _ _ _ (24 : Fin 32) s27.zero (by decide), g27_24]
  have g28_25 : reg n28 (25 : Fin 32) = dhi := by
    rw [rb28, runBlock_reg _ _ _ (25 : Fin 32) s27.zero (by decide), g27_25]
  have g28_26 : reg n28 (26 : Fin 32) = x26 := by
    rw [rb28, runBlock_reg _ _ _ (26 : Fin 32) s27.zero (by decide), g27_26]
  have g28_27 : reg n28 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb28, runBlock_reg _ _ _ (27 : Fin 32) s27.zero (by decide), g27_27]
  have g28_10 : reg n28 a0 = (rem) - (BitVec.ofNat 32 ns) := by
    rw [rb28]; simp +decide only [runBlock, BInstr.run, svIvB1550, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g27_2, g27_3, g27_4, g27_8, g27_10, g27_18, g27_19, g27_21, g27_23, g27_24, g27_25, g27_26, g27_27, s27.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
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
  have w28_5c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 ns := by rw [m28]; exact w27_5c
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
  have w28_320 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ulo := by rw [m28]; exact w27_320
  have w28_324 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = uhi := by rw [m28]; exact w27_324
  have w28_328 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = vlo := by rw [m28]; exact w27_328
  have w28_32c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = vhi := by rw [m28]; exact w27_32c
  have w28_330 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = qlo := by rw [m28]; exact w27_330
  have w28_334 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = qhi := by rw [m28]; exact w27_334
  have w28_338 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = rlo := by rw [m28]; exact w27_338
  have w28_33c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = rhi := by rw [m28]; exact w27_33c
  have b28_440 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) = BitVec.ofNat 8 (lrsm8 σ22b A22b ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).1 := by rw [m28]; exact b27_440
  have b28_a40 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 8 (lrsm8 σ22a A22a ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).1 := by rw [m28]; exact b27_a40
  have b28_a64 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA64) = BitVec.ofNat 8 (lrsm8 σ22b A22b ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).1 := by rw [m28]; exact b27_a64
  have b28_1040 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = BitVec.ofNat 8 (lrsm8 σ22a A22a ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).1 := by rw [m28]; exact b27_1040
  have b28_13a0 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = BitVec.ofNat 8 σ13a := by rw [m28]; exact b27_13a0
  have b28_14a0 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = BitVec.ofNat 8 σ13b := by rw [m28]; exact b27_14a0
  have a28_240 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m28]; exact a27_240
  have a28_260 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m28]; exact a27_260
  have a28_280 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m28]; exact a27_280
  have a28_2a0 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m28]; exact a27_2a0
  have a28_2c0 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m28]; exact a27_2c0
  have a28_2e0 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m28]; exact a27_2e0
  have a28_420 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = (lrsm8 σ22b A22b ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).2 := by rw [m28]; exact a27_420
  have a28_a20 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 8 = (lrsm8 σ22a A22a ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).2 := by rw [m28]; exact a27_a20
  have a28_a44 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) 8 = (lrsm8 σ22b A22b ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).2 := by rw [m28]; exact a27_a44
  have a28_1020 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = (lrsm8 σ22a A22a ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).2 := by rw [m28]; exact a27_1020
  have a28_1380 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = A13a / 2 ^ ns % 2 ^ 256 := by rw [m28]; exact a27_1380
  have a28_1480 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = A13b / 2 ^ ns % 2 ^ 256 := by rw [m28]; exact a27_1480
  clear a27_1480 a27_1380 a27_1020 a27_a44 a27_a20 a27_420 a27_2e0 a27_2c0 a27_2a0 a27_280 a27_260 a27_240 b27_14a0 b27_13a0 b27_1040 b27_a64 b27_a40 b27_440 w27_33c w27_338 w27_334 w27_330 w27_32c w27_328 w27_324 w27_320 w27_130 w27_12c w27_128 w27_124 w27_120 w27_11c w27_118 w27_114 w27_110 w27_10c w27_108 w27_104 w27_100 w27_fc w27_f8 w27_f4 w27_f0 w27_ec w27_e8 w27_e4 w27_e0 w27_dc w27_d8 w27_d4 w27_d0 w27_cc w27_c8 w27_c4 w27_c0 w27_bc w27_b8 w27_b4 w27_b0 w27_ac w27_a8 w27_a4 w27_a0 w27_9c w27_98 w27_94 w27_90 w27_8c w27_88 w27_84 w27_80 w27_7c w27_78 w27_70 w27_6c w27_68 w27_64 w27_60 w27_5c w27_58 w27_54 w27_50 w27_4c w27_48 w27_44 w27_40 w27_3c w27_38 w27_34 w27_30 w27_2c w27_28 w27_24 g27_10 g27_27 g27_26 g27_25 g27_24 g27_23 g27_21 g27_19 g27_18 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 m27 s27 u27 d27
  -- 0x1552: sw
  obtain ⟨n29, d29, s29, fr29, K29, W29, rg29⟩ := sv_sw F E28 s28 sv_at_1552 (off' := 0x1554) (c := 0x78)
    (by decide) (by rw [g28_2]; sv_addr) (by decide) (by decide)
  have t29 : Steps n0 n29 := t28.trans d29
  have fR29 : ∀ x, SvR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
  have E29 : SvCode n29.mem := E28.fr F fr29
  have V29 : SvSaves B n29.mem v := V28.keep K29 (by decide)
  have g29_2 : reg n29 sp = B + 0x21A0 := by rw [rg29 sp, g28_2]
  have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg29 (3 : Fin 32), g28_3]
  have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg29 (4 : Fin 32), g28_4]
  have g29_8 : reg n29 (8 : Fin 32) = BitVec.ofNat 32 ns := by rw [rg29 (8 : Fin 32), g28_8]
  have g29_10 : reg n29 a0 = (rem) - (BitVec.ofNat 32 ns) := by rw [rg29 a0, g28_10]
  have g29_18 : reg n29 (18 : Fin 32) = out := by rw [rg29 (18 : Fin 32), g28_18]
  have g29_19 : reg n29 (19 : Fin 32) = bp := by rw [rg29 (19 : Fin 32), g28_19]
  have g29_21 : reg n29 (21 : Fin 32) = s5v := by rw [rg29 (21 : Fin 32), g28_21]
  have g29_23 : reg n29 (23 : Fin 32) = dlo := by rw [rg29 (23 : Fin 32), g28_23]
  have g29_24 : reg n29 (24 : Fin 32) = BitVec.ofNat 32 0x3FCC4268 := by rw [rg29 (24 : Fin 32), g28_24]
  have g29_25 : reg n29 (25 : Fin 32) = dhi := by rw [rg29 (25 : Fin 32), g28_25]
  have g29_26 : reg n29 (26 : Fin 32) = x26 := by rw [rg29 (26 : Fin 32), g28_26]
  have g29_27 : reg n29 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg29 (27 : Fin 32), g28_27]
  have w29_24 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K29.w32 (by decide) (by decide)).trans w28_24
  have w29_28 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K29.w32 (by decide) (by decide)).trans w28_28
  have w29_2c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K29.w32 (by decide) (by decide)).trans w28_2c
  have w29_30 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K29.w32 (by decide) (by decide)).trans w28_30
  have w29_34 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K29.w32 (by decide) (by decide)).trans w28_34
  have w29_38 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K29.w32 (by decide) (by decide)).trans w28_38
  have w29_3c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K29.w32 (by decide) (by decide)).trans w28_3c
  have w29_40 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K29.w32 (by decide) (by decide)).trans w28_40
  have w29_44 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K29.w32 (by decide) (by decide)).trans w28_44
  have w29_48 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K29.w32 (by decide) (by decide)).trans w28_48
  have w29_4c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K29.w32 (by decide) (by decide)).trans w28_4c
  have w29_50 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K29.w32 (by decide) (by decide)).trans w28_50
  have w29_54 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K29.w32 (by decide) (by decide)).trans w28_54
  have w29_58 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K29.w32 (by decide) (by decide)).trans w28_58
  have w29_5c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 ns := (K29.w32 (by decide) (by decide)).trans w28_5c
  have w29_60 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K29.w32 (by decide) (by decide)).trans w28_60
  have w29_64 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K29.w32 (by decide) (by decide)).trans w28_64
  have w29_68 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K29.w32 (by decide) (by decide)).trans w28_68
  have w29_6c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K29.w32 (by decide) (by decide)).trans w28_6c
  have w29_70 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K29.w32 (by decide) (by decide)).trans w28_70
  have w29_7c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K29.w32 (by decide) (by decide)).trans w28_7c
  have w29_80 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K29.w32 (by decide) (by decide)).trans w28_80
  have w29_84 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K29.w32 (by decide) (by decide)).trans w28_84
  have w29_88 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K29.w32 (by decide) (by decide)).trans w28_88
  have w29_8c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K29.w32 (by decide) (by decide)).trans w28_8c
  have w29_90 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K29.w32 (by decide) (by decide)).trans w28_90
  have w29_94 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K29.w32 (by decide) (by decide)).trans w28_94
  have w29_98 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K29.w32 (by decide) (by decide)).trans w28_98
  have w29_9c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K29.w32 (by decide) (by decide)).trans w28_9c
  have w29_a0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K29.w32 (by decide) (by decide)).trans w28_a0
  have w29_a4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K29.w32 (by decide) (by decide)).trans w28_a4
  have w29_a8 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K29.w32 (by decide) (by decide)).trans w28_a8
  have w29_ac : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K29.w32 (by decide) (by decide)).trans w28_ac
  have w29_b0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K29.w32 (by decide) (by decide)).trans w28_b0
  have w29_b4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K29.w32 (by decide) (by decide)).trans w28_b4
  have w29_b8 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K29.w32 (by decide) (by decide)).trans w28_b8
  have w29_bc : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K29.w32 (by decide) (by decide)).trans w28_bc
  have w29_c0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K29.w32 (by decide) (by decide)).trans w28_c0
  have w29_c4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K29.w32 (by decide) (by decide)).trans w28_c4
  have w29_c8 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K29.w32 (by decide) (by decide)).trans w28_c8
  have w29_cc : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K29.w32 (by decide) (by decide)).trans w28_cc
  have w29_d0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K29.w32 (by decide) (by decide)).trans w28_d0
  have w29_d4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K29.w32 (by decide) (by decide)).trans w28_d4
  have w29_d8 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K29.w32 (by decide) (by decide)).trans w28_d8
  have w29_dc : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K29.w32 (by decide) (by decide)).trans w28_dc
  have w29_e0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K29.w32 (by decide) (by decide)).trans w28_e0
  have w29_e4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K29.w32 (by decide) (by decide)).trans w28_e4
  have w29_e8 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K29.w32 (by decide) (by decide)).trans w28_e8
  have w29_ec : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K29.w32 (by decide) (by decide)).trans w28_ec
  have w29_f0 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K29.w32 (by decide) (by decide)).trans w28_f0
  have w29_f4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K29.w32 (by decide) (by decide)).trans w28_f4
  have w29_f8 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K29.w32 (by decide) (by decide)).trans w28_f8
  have w29_fc : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K29.w32 (by decide) (by decide)).trans w28_fc
  have w29_100 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K29.w32 (by decide) (by decide)).trans w28_100
  have w29_104 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K29.w32 (by decide) (by decide)).trans w28_104
  have w29_108 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K29.w32 (by decide) (by decide)).trans w28_108
  have w29_10c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K29.w32 (by decide) (by decide)).trans w28_10c
  have w29_110 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K29.w32 (by decide) (by decide)).trans w28_110
  have w29_114 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K29.w32 (by decide) (by decide)).trans w28_114
  have w29_118 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K29.w32 (by decide) (by decide)).trans w28_118
  have w29_11c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K29.w32 (by decide) (by decide)).trans w28_11c
  have w29_120 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K29.w32 (by decide) (by decide)).trans w28_120
  have w29_124 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K29.w32 (by decide) (by decide)).trans w28_124
  have w29_128 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K29.w32 (by decide) (by decide)).trans w28_128
  have w29_12c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K29.w32 (by decide) (by decide)).trans w28_12c
  have w29_130 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K29.w32 (by decide) (by decide)).trans w28_130
  have w29_320 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ulo := (K29.w32 (by decide) (by decide)).trans w28_320
  have w29_324 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = uhi := (K29.w32 (by decide) (by decide)).trans w28_324
  have w29_328 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = vlo := (K29.w32 (by decide) (by decide)).trans w28_328
  have w29_32c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = vhi := (K29.w32 (by decide) (by decide)).trans w28_32c
  have w29_330 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = qlo := (K29.w32 (by decide) (by decide)).trans w28_330
  have w29_334 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = qhi := (K29.w32 (by decide) (by decide)).trans w28_334
  have w29_338 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = rlo := (K29.w32 (by decide) (by decide)).trans w28_338
  have w29_33c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = rhi := (K29.w32 (by decide) (by decide)).trans w28_33c
  have b29_440 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) = BitVec.ofNat 8 (lrsm8 σ22b A22b ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).1 := (K29.b8 (by decide) (by decide)).trans b28_440
  have b29_a40 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 8 (lrsm8 σ22a A22a ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).1 := (K29.b8 (by decide) (by decide)).trans b28_a40
  have b29_a64 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA64) = BitVec.ofNat 8 (lrsm8 σ22b A22b ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).1 := (K29.b8 (by decide) (by decide)).trans b28_a64
  have b29_1040 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = BitVec.ofNat 8 (lrsm8 σ22a A22a ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).1 := (K29.b8 (by decide) (by decide)).trans b28_1040
  have b29_13a0 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = BitVec.ofNat 8 σ13a := (K29.b8 (by decide) (by decide)).trans b28_13a0
  have b29_14a0 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = BitVec.ofNat 8 σ13b := (K29.b8 (by decide) (by decide)).trans b28_14a0
  have w29_78 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = (rem) - (BitVec.ofNat 32 ns) := by rw [W29, g28_10]
  have a29_240 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := (K29.acc (by decide) (by decide)).trans a28_240
  have a29_260 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := (K29.acc (by decide) (by decide)).trans a28_260
  have a29_280 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := (K29.acc (by decide) (by decide)).trans a28_280
  have a29_2a0 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K29.acc (by decide) (by decide)).trans a28_2a0
  have a29_2c0 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K29.acc (by decide) (by decide)).trans a28_2c0
  have a29_2e0 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K29.acc (by decide) (by decide)).trans a28_2e0
  have a29_420 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = (lrsm8 σ22b A22b ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).2 := (K29.acc (by decide) (by decide)).trans a28_420
  have a29_a20 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 8 = (lrsm8 σ22a A22a ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).2 := (K29.acc (by decide) (by decide)).trans a28_a20
  have a29_a44 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) 8 = (lrsm8 σ22b A22b ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).2 := (K29.acc (by decide) (by decide)).trans a28_a44
  have a29_1020 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = (lrsm8 σ22a A22a ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).2 := (K29.acc (by decide) (by decide)).trans a28_1020
  have a29_1380 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = A13a / 2 ^ ns % 2 ^ 256 := (K29.acc (by decide) (by decide)).trans a28_1380
  have a29_1480 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = A13b / 2 ^ ns % 2 ^ 256 := (K29.acc (by decide) (by decide)).trans a28_1480
  clear a28_1480 a28_1380 a28_1020 a28_a44 a28_a20 a28_420 a28_2e0 a28_2c0 a28_2a0 a28_280 a28_260 a28_240 b28_14a0 b28_13a0 b28_1040 b28_a64 b28_a40 b28_440 w28_33c w28_338 w28_334 w28_330 w28_32c w28_328 w28_324 w28_320 w28_130 w28_12c w28_128 w28_124 w28_120 w28_11c w28_118 w28_114 w28_110 w28_10c w28_108 w28_104 w28_100 w28_fc w28_f8 w28_f4 w28_f0 w28_ec w28_e8 w28_e4 w28_e0 w28_dc w28_d8 w28_d4 w28_d0 w28_cc w28_c8 w28_c4 w28_c0 w28_bc w28_b8 w28_b4 w28_b0 w28_ac w28_a8 w28_a4 w28_a0 w28_9c w28_98 w28_94 w28_90 w28_8c w28_88 w28_84 w28_80 w28_7c w28_78 w28_70 w28_6c w28_68 w28_64 w28_60 w28_5c w28_58 w28_54 w28_50 w28_4c w28_48 w28_44 w28_40 w28_3c w28_38 w28_34 w28_30 w28_2c w28_28 w28_24 g28_10 g28_27 g28_26 g28_25 g28_24 g28_23 g28_21 g28_19 g28_18 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 rb28 s28 m28 u28 c28
  -- 0x1554: j
  obtain ⟨n30, d30, u30⟩ := s29.jump E29.self sv_at_1554 (off' := 0x1328) (by decide)
    (by rw [s29.pc]; decide)
  have s30 : St n30.mem SV n30 0x1328 (reg n30) := ⟨u30.pc, rfl, fun _ => rfl⟩
  have m30 : n30.mem = n29.mem := u30.mem
  have fr30 : ∀ x, SvR B x → n30.mem x = n29.mem x := fun x _ => by rw [m30]
  have t30 : Steps n0 n30 := t29.trans (.single d30)
  have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
  have E30 : SvCode n30.mem := E29.fr F fr30
  have V30 : SvSaves B n30.mem v := V29.same m30
  have g30_2 : reg n30 sp = B + 0x21A0 := by rw [u30.regs, g29_2]
  have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u30.regs, g29_3]
  have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u30.regs, g29_4]
  have g30_8 : reg n30 (8 : Fin 32) = BitVec.ofNat 32 ns := by rw [u30.regs, g29_8]
  have g30_10 : reg n30 a0 = (rem) - (BitVec.ofNat 32 ns) := by rw [u30.regs, g29_10]
  have g30_18 : reg n30 (18 : Fin 32) = out := by rw [u30.regs, g29_18]
  have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [u30.regs, g29_19]
  have g30_21 : reg n30 (21 : Fin 32) = s5v := by rw [u30.regs, g29_21]
  have g30_23 : reg n30 (23 : Fin 32) = dlo := by rw [u30.regs, g29_23]
  have g30_24 : reg n30 (24 : Fin 32) = BitVec.ofNat 32 0x3FCC4268 := by rw [u30.regs, g29_24]
  have g30_25 : reg n30 (25 : Fin 32) = dhi := by rw [u30.regs, g29_25]
  have g30_26 : reg n30 (26 : Fin 32) = x26 := by rw [u30.regs, g29_26]
  have g30_27 : reg n30 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u30.regs, g29_27]
  have w30_24 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m30]; exact w29_24
  have w30_28 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m30]; exact w29_28
  have w30_2c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m30]; exact w29_2c
  have w30_30 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m30]; exact w29_30
  have w30_34 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m30]; exact w29_34
  have w30_38 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m30]; exact w29_38
  have w30_3c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m30]; exact w29_3c
  have w30_40 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m30]; exact w29_40
  have w30_44 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m30]; exact w29_44
  have w30_48 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m30]; exact w29_48
  have w30_4c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m30]; exact w29_4c
  have w30_50 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m30]; exact w29_50
  have w30_54 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m30]; exact w29_54
  have w30_58 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m30]; exact w29_58
  have w30_5c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = BitVec.ofNat 32 ns := by rw [m30]; exact w29_5c
  have w30_60 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m30]; exact w29_60
  have w30_64 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m30]; exact w29_64
  have w30_68 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m30]; exact w29_68
  have w30_6c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m30]; exact w29_6c
  have w30_70 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m30]; exact w29_70
  have w30_78 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = (rem) - (BitVec.ofNat 32 ns) := by rw [m30]; exact w29_78
  have w30_7c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m30]; exact w29_7c
  have w30_80 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m30]; exact w29_80
  have w30_84 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m30]; exact w29_84
  have w30_88 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := by rw [m30]; exact w29_88
  have w30_8c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := by rw [m30]; exact w29_8c
  have w30_90 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := by rw [m30]; exact w29_90
  have w30_94 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := by rw [m30]; exact w29_94
  have w30_98 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := by rw [m30]; exact w29_98
  have w30_9c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := by rw [m30]; exact w29_9c
  have w30_a0 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := by rw [m30]; exact w29_a0
  have w30_a4 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := by rw [m30]; exact w29_a4
  have w30_a8 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := by rw [m30]; exact w29_a8
  have w30_ac : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := by rw [m30]; exact w29_ac
  have w30_b0 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := by rw [m30]; exact w29_b0
  have w30_b4 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := by rw [m30]; exact w29_b4
  have w30_b8 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := by rw [m30]; exact w29_b8
  have w30_bc : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := by rw [m30]; exact w29_bc
  have w30_c0 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := by rw [m30]; exact w29_c0
  have w30_c4 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := by rw [m30]; exact w29_c4
  have w30_c8 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := by rw [m30]; exact w29_c8
  have w30_cc : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := by rw [m30]; exact w29_cc
  have w30_d0 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := by rw [m30]; exact w29_d0
  have w30_d4 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := by rw [m30]; exact w29_d4
  have w30_d8 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := by rw [m30]; exact w29_d8
  have w30_dc : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := by rw [m30]; exact w29_dc
  have w30_e0 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := by rw [m30]; exact w29_e0
  have w30_e4 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := by rw [m30]; exact w29_e4
  have w30_e8 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := by rw [m30]; exact w29_e8
  have w30_ec : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := by rw [m30]; exact w29_ec
  have w30_f0 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := by rw [m30]; exact w29_f0
  have w30_f4 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := by rw [m30]; exact w29_f4
  have w30_f8 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := by rw [m30]; exact w29_f8
  have w30_fc : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := by rw [m30]; exact w29_fc
  have w30_100 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := by rw [m30]; exact w29_100
  have w30_104 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := by rw [m30]; exact w29_104
  have w30_108 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := by rw [m30]; exact w29_108
  have w30_10c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := by rw [m30]; exact w29_10c
  have w30_110 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := by rw [m30]; exact w29_110
  have w30_114 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := by rw [m30]; exact w29_114
  have w30_118 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := by rw [m30]; exact w29_118
  have w30_11c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := by rw [m30]; exact w29_11c
  have w30_120 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := by rw [m30]; exact w29_120
  have w30_124 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := by rw [m30]; exact w29_124
  have w30_128 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := by rw [m30]; exact w29_128
  have w30_12c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := by rw [m30]; exact w29_12c
  have w30_130 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := by rw [m30]; exact w29_130
  have w30_320 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ulo := by rw [m30]; exact w29_320
  have w30_324 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = uhi := by rw [m30]; exact w29_324
  have w30_328 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = vlo := by rw [m30]; exact w29_328
  have w30_32c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = vhi := by rw [m30]; exact w29_32c
  have w30_330 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x330) = qlo := by rw [m30]; exact w29_330
  have w30_334 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x334) = qhi := by rw [m30]; exact w29_334
  have w30_338 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x338) = rlo := by rw [m30]; exact w29_338
  have w30_33c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x33C) = rhi := by rw [m30]; exact w29_33c
  have b30_440 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) = BitVec.ofNat 8 (lrsm8 σ22b A22b ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).1 := by rw [m30]; exact b29_440
  have b30_a40 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 8 (lrsm8 σ22a A22a ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).1 := by rw [m30]; exact b29_a40
  have b30_a64 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA64) = BitVec.ofNat 8 (lrsm8 σ22b A22b ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).1 := by rw [m30]; exact b29_a64
  have b30_1040 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = BitVec.ofNat 8 (lrsm8 σ22a A22a ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).1 := by rw [m30]; exact b29_1040
  have b30_13a0 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = BitVec.ofNat 8 σ13a := by rw [m30]; exact b29_13a0
  have b30_14a0 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = BitVec.ofNat 8 σ13b := by rw [m30]; exact b29_14a0
  have a30_240 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) 8 = qx := by rw [m30]; exact a29_240
  have a30_260 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8 = qy := by rw [m30]; exact a29_260
  have a30_280 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) 8 = qz := by rw [m30]; exact a29_280
  have a30_2a0 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m30]; exact a29_2a0
  have a30_2c0 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m30]; exact a29_2c0
  have a30_2e0 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m30]; exact a29_2e0
  have a30_420 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = (lrsm8 σ22b A22b ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).2 := by rw [m30]; exact a29_420
  have a30_a20 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 8 = (lrsm8 σ22a A22a ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).2 := by rw [m30]; exact a29_a20
  have a30_a44 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) 8 = (lrsm8 σ22b A22b ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).2 := by rw [m30]; exact a29_a44
  have a30_1020 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = (lrsm8 σ22a A22a ((w70).toNat + 2 ^ 32 * (w60).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)).2 := by rw [m30]; exact a29_1020
  have a30_1380 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = A13a / 2 ^ ns % 2 ^ 256 := by rw [m30]; exact a29_1380
  have a30_1480 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = A13b / 2 ^ ns % 2 ^ 256 := by rw [m30]; exact a29_1480
  clear a29_1480 a29_1380 a29_1020 a29_a44 a29_a20 a29_420 a29_2e0 a29_2c0 a29_2a0 a29_280 a29_260 a29_240 w29_78 b29_14a0 b29_13a0 b29_1040 b29_a64 b29_a40 b29_440 w29_33c w29_338 w29_334 w29_330 w29_32c w29_328 w29_324 w29_320 w29_130 w29_12c w29_128 w29_124 w29_120 w29_11c w29_118 w29_114 w29_110 w29_10c w29_108 w29_104 w29_100 w29_fc w29_f8 w29_f4 w29_f0 w29_ec w29_e8 w29_e4 w29_e0 w29_dc w29_d8 w29_d4 w29_d0 w29_cc w29_c8 w29_c4 w29_c0 w29_bc w29_b8 w29_b4 w29_b0 w29_ac w29_a8 w29_a4 w29_a0 w29_9c w29_98 w29_94 w29_90 w29_8c w29_88 w29_84 w29_80 w29_7c w29_70 w29_6c w29_68 w29_64 w29_60 w29_5c w29_58 w29_54 w29_50 w29_4c w29_48 w29_44 w29_40 w29_3c w29_38 w29_34 w29_30 w29_2c w29_28 w29_24 g29_27 g29_26 g29_25 g29_24 g29_23 g29_21 g29_19 g29_18 g29_10 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 rg29 W29 K29 fr29 s29 d29
  exact .inr ⟨σ13a, A13a, e0_13, hσ0_13, σ13b, A13b, e1_13, hσ1_13, σ22a, A22a, e0_22, hσ0_22, σ22b, A22b, e1_22, hσ1_22, n30, t30, s30, E30, V30, fR30, g30_2, g30_3, g30_4, g30_18, g30_19, g30_21, g30_23, g30_24, g30_25, g30_26, g30_27, w30_24, w30_28, w30_2c, w30_30, w30_34, w30_38, w30_3c, w30_40, w30_44, w30_48, w30_4c, w30_50, w30_54, w30_58, w30_5c, w30_60, w30_64, w30_68, w30_6c, w30_70, w30_78, w30_7c, w30_80, w30_84, w30_88, w30_8c, w30_90, w30_94, w30_98, w30_9c, w30_a0, w30_a4, w30_a8, w30_ac, w30_b0, w30_b4, w30_b8, w30_bc, w30_c0, w30_c4, w30_c8, w30_cc, w30_d0, w30_d4, w30_d8, w30_dc, w30_e0, w30_e4, w30_e8, w30_ec, w30_f0, w30_f4, w30_f8, w30_fc, w30_100, w30_104, w30_108, w30_10c, w30_110, w30_114, w30_118, w30_11c, w30_120, w30_124, w30_128, w30_12c, w30_130, w30_320, w30_324, w30_328, w30_32c, w30_330, w30_334, w30_338, w30_33c, b30_440, b30_a40, b30_a64, b30_1040, b30_13a0, b30_14a0, a30_240, a30_260, a30_280, a30_2a0, a30_2c0, a30_2e0, a30_420, a30_a20, a30_a44, a30_1020, a30_1380, a30_1480⟩

end C3.RV32.Sv
