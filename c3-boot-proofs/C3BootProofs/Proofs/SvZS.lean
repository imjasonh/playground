import C3BootProofs.Proofs.SvZLib

/-!
# `sigstore::verify`: the start of the inversion of `Z`

From 0x1A72 to the inversion's head at 0x1B54: the sum moves to 0x15A8, the word at 0x20 records whether its `Z` is nonzero, and the inversion of `Z` starts from `f = p`, `g = Z`, `d = 0`, `e = R²`, and `δ = 1`, with 591 steps left.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svZS1a72 : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x5A8, .alu .add a0 a0 sp, .lui a1 0x1000, .aluImm .add a1 a1 0x480, .alu .add a1 a1 sp, .aluImm .add a2 x0 0x60]
theorem svZS1a72_end : blockEnd sigstoreVerifyCode 0x1A72 svZS1a72 = some 0x1A86 := by
  simp only [svZS1a72]
  rw [blockEnd, sv_at_1a72]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1a74]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1a78]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1a7a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1a7c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1a80]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1a82]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svZS1a8e : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x5E8, .alu .add (22 : Fin 32) sp a0, .lui (23 : Fin 32) 0x3FCC5000, .aluImm .add (23 : Fin 32) (23 : Fin 32) 0xFFFFFB38, .aluImm .add a0 sp 0x420, .aluImm .add a2 x0 0x20, .alu .add a1 x0 (23 : Fin 32)]
theorem svZS1a8e_end : blockEnd sigstoreVerifyCode 0x1A8E svZS1a8e = some 0x1AAA := by
  simp only [svZS1a8e]
  rw [blockEnd, sv_at_1a8e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1a90]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1a94]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1a98]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1a9c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1aa0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1aa4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1aa8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svZS1ab2 : List BInstr :=
  [.aluImm .add a0 x0 0xFFFFFFFF]
theorem svZS1ab2_end : blockEnd sigstoreVerifyCode 0x1AB2 svZS1ab2 = some 0x1AB4 := by
  simp only [svZS1ab2]
  rw [blockEnd, sv_at_1ab2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svZS1abc : List BInstr :=
  [.aluImm .add a0 sp 0x440, .aluImm .add (8 : Fin 32) (23 : Fin 32) 0x40, .aluImm .add a2 x0 0x20, .alu .add a1 x0 (8 : Fin 32)]
theorem svZS1abc_end : blockEnd sigstoreVerifyCode 0x1ABC svZS1abc = some 0x1ACA := by
  simp only [svZS1abc]
  rw [blockEnd, sv_at_1abc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1ac0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1ac4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1ac8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svZS1ad2 : List BInstr :=
  [.alu .add a0 x0 (22 : Fin 32)]
theorem svZS1ad2_end : blockEnd sigstoreVerifyCode 0x1AD2 svZS1ad2 = some 0x1AD4 := by
  simp only [svZS1ad2]
  rw [blockEnd, sv_at_1ad2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svZS1adc : List BInstr :=
  [.aluImm .and a0 a0 0xFF]
theorem svZS1adc_end : blockEnd sigstoreVerifyCode 0x1ADC svZS1adc = some 0x1AE0 := by
  simp only [svZS1adc]
  rw [blockEnd, sv_at_1adc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svZS1ae2 : List BInstr :=
  [.aluImm .add a0 sp 0x320, .aluImm .add a2 x0 0x20, .alu .add a1 x0 (23 : Fin 32)]
theorem svZS1ae2_end : blockEnd sigstoreVerifyCode 0x1AE2 svZS1ae2 = some 0x1AEA := by
  simp only [svZS1ae2]
  rw [blockEnd, sv_at_1ae2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1ae4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1ae8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svZS1af6 : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x380, .alu .add a0 a0 sp, .aluImm .add a2 x0 0x20, .alu .add a1 x0 (22 : Fin 32)]
theorem svZS1af6_end : blockEnd sigstoreVerifyCode 0x1AF6 svZS1af6 = some 0x1B04 := by
  simp only [svZS1af6]
  rw [blockEnd, sv_at_1af6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1af8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1afc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1afe]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1b02]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svZS1b0c : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x320, .alu .add a0 a0 sp]
theorem svZS1b0c_end : blockEnd sigstoreVerifyCode 0x1B0C svZS1b0c = some 0x1B14 := by
  simp only [svZS1b0c]
  rw [blockEnd, sv_at_1b0c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1b0e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1b12]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svZS1b18 : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x480, .alu .add a0 a0 sp, .aluImm .add a2 x0 0x24, .aluImm .add a1 x0 0x0]
theorem svZS1b18_end : blockEnd sigstoreVerifyCode 0x1B18 svZS1b18 = some 0x1B26 := by
  simp only [svZS1b18]
  rw [blockEnd, sv_at_1b18]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1b1a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1b1e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1b20]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1b24]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svZS1b2e : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x20, .alu .add a0 a0 sp, .aluImm .add a2 x0 0x20, .alu .add a1 x0 (8 : Fin 32)]
theorem svZS1b2e_end : blockEnd sigstoreVerifyCode 0x1B2E svZS1b2e = some 0x1B3C := by
  simp only [svZS1b2e]
  rw [blockEnd, sv_at_1b2e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1b30]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1b34]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1b36]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1b3a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svZS1b4a : List BInstr :=
  [.aluImm .add a0 x0 0x1]
theorem svZS1b4a_end : blockEnd sigstoreVerifyCode 0x1B4A svZS1b4a = some 0x1B4C := by
  simp only [svZS1b4a]
  rw [blockEnd, sv_at_1b4a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svZS1b4e : List BInstr :=
  [.aluImm .add a0 x0 0x24F]
theorem svZS1b4e_end : blockEnd sigstoreVerifyCode 0x1B4E svZS1b4e = some 0x1B52 := by
  simp only [svZS1b4e]
  rw [blockEnd, sv_at_1b4e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_zs {B out bp x26 : Word} {rv sv zv X Y Z : Nat} {w24 w28 w2c w30 w34 w38 w3c w40 w44 w48 w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w7c w80 w84 w88 w8c w90 w94 w98 w9c wa0 wa4 wa8 wac wb0 wb4 wb8 wbc wc0 wc4 wc8 wcc wd0 wd4 wd8 wdc we0 we4 we8 wec wf0 wf4 wf8 wfc w100 w104 w108 w10c w110 w114 w118 w11c w120 w124 w128 w12c w130 : Word} {v : Nat → Word} {n0 : Machine}
    (F : Fr B 0x3830) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x1A72 (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = BitVec.ofNat 32 0x60)
    (g0_21 : reg n0 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40)
    (g0_22 : reg n0 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1023)
    (g0_24 : reg n0 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA60)
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
    (a0_2a0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv)
    (a0_2c0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv)
    (a0_2e0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv)
    (a0_1480 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = X)
    (a0_14a0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) 8 = Y)
    (a0_14c0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x14C0) 8 = Z)
    (RS : SvRoSep B)
    (EC0 : SvEcCode M0) :
    (¬ (True) ∧ SvErrRet B out v n0) ∨
    (∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x1B54 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = BitVec.ofNat 32 0x60 ∧
        reg n' (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 ∧
        reg n' (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x15E8 ∧
        reg n' (23 : Fin 32) = BitVec.ofNat 32 0x3FCC4B38 ∧
        reg n' (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA60 ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = ((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = BitVec.ofNat 32 0x1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = BitVec.ofNat 32 0x0 ∧
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
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 0x24F ∧
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
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = 0 ∧
        (∀ j, j < 32 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 32 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 32 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x440 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B78) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 32 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1020 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B78) + BitVec.ofNat 32 j)) ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = Z ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = 0 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x14C0) 8 = Z ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x15E8) 8 = Z) := by
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x1A72
  obtain ⟨n1, c1, u1⟩ := s0.block svZS1a72 E0.self svZS1a72_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have s1 : St n1.mem SV n1 0x1A86 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have rb1 : ∀ q, reg n1 q = (runBlock svZS1a72 (n0.mem, reg n0)).2 q := fun q => by rw [u1.regs]
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
  have g1_20 : reg n1 (20 : Fin 32) = BitVec.ofNat 32 0x60 := by
    rw [rb1, runBlock_reg _ _ _ (20 : Fin 32) s0.zero (by decide), g0_20]
  have g1_21 : reg n1 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by
    rw [rb1, runBlock_reg _ _ _ (21 : Fin 32) s0.zero (by decide), g0_21]
  have g1_22 : reg n1 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1023 := by
    rw [rb1, runBlock_reg _ _ _ (22 : Fin 32) s0.zero (by decide), g0_22]
  have g1_24 : reg n1 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA60 := by
    rw [rb1, runBlock_reg _ _ _ (24 : Fin 32) s0.zero (by decide), g0_24]
  have g1_26 : reg n1 (26 : Fin 32) = x26 := by
    rw [rb1, runBlock_reg _ _ _ (26 : Fin 32) s0.zero (by decide), g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb1, runBlock_reg _ _ _ (27 : Fin 32) s0.zero (by decide), g0_27]
  have g1_10 : reg n1 a0 = B + 0x21A0 + BitVec.ofNat 32 0x15A8 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svZS1a72, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_18, g0_19, g0_20, g0_21, g0_22, g0_24, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g1_11 : reg n1 a1 = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svZS1a72, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_18, g0_19, g0_20, g0_21, g0_22, g0_24, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g1_12 : reg n1 a2 = BitVec.ofNat 32 0x60 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svZS1a72, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_18, g0_19, g0_20, g0_21, g0_22, g0_24, g0_26, g0_27, s0.zero])
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
  have a1_1480 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = X := by rw [m1]; exact a0_1480
  have a1_14a0 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) 8 = Y := by rw [m1]; exact a0_14a0
  have a1_14c0 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x14C0) 8 = Z := by rw [m1]; exact a0_14c0
  -- 0x1A86: memcpy
  obtain ⟨n2, P2, K2, X2⟩ := sv_mc (c := 0x15A8) (d := 0x1480) (N := 0x60) F E1 s1 sv_at_1a86 sv_at_1a8a
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
  have g2_20 : reg n2 (20 : Fin 32) = BitVec.ofNat 32 0x60 := by rw [P2.regs (20 : Fin 32) (by decide), g1_20]
  have g2_21 : reg n2 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [P2.regs (21 : Fin 32) (by decide), g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1023 := by rw [P2.regs (22 : Fin 32) (by decide), g1_22]
  have g2_24 : reg n2 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA60 := by rw [P2.regs (24 : Fin 32) (by decide), g1_24]
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
  have a2_1480 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = X := (K2.acc (by decide) (by decide)).trans a1_1480
  have a2_14a0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) 8 = Y := (K2.acc (by decide) (by decide)).trans a1_14a0
  have a2_14c0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x14C0) 8 = Z := (K2.acc (by decide) (by decide)).trans a1_14c0
  have a2_15a8 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := (accV_S 8 fun q hq => by
    rw [show 0x15A8 + q = 0x15A8 + (0x0 + q) by omega, X2 (0x0 + q) (by omega),
      show 0x1480 + (0x0 + q) = 0x1480 + q by omega]).trans a1_1480
  have a2_15c8 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := (accV_S 8 fun q hq => by
    rw [show 0x15C8 + q = 0x15A8 + (0x20 + q) by omega, X2 (0x20 + q) (by omega),
      show 0x1480 + (0x20 + q) = 0x14A0 + q by omega]).trans a1_14a0
  have a2_15e8 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x15E8) 8 = Z := (accV_S 8 fun q hq => by
    rw [show 0x15E8 + q = 0x15A8 + (0x40 + q) by omega, X2 (0x40 + q) (by omega),
      show 0x1480 + (0x40 + q) = 0x14C0 + q by omega]).trans a1_14c0
  clear a1_14c0 a1_14a0 a1_1480 a1_2e0 a1_2c0 a1_2a0 w1_130 w1_12c w1_128 w1_124 w1_120 w1_11c w1_118 w1_114 w1_110 w1_10c w1_108 w1_104 w1_100 w1_fc w1_f8 w1_f4 w1_f0 w1_ec w1_e8 w1_e4 w1_e0 w1_dc w1_d8 w1_d4 w1_d0 w1_cc w1_c8 w1_c4 w1_c0 w1_bc w1_b8 w1_b4 w1_b0 w1_ac w1_a8 w1_a4 w1_a0 w1_9c w1_98 w1_94 w1_90 w1_8c w1_88 w1_84 w1_80 w1_7c w1_70 w1_6c w1_68 w1_64 w1_60 w1_5c w1_58 w1_54 w1_50 w1_4c w1_48 w1_44 w1_40 w1_3c w1_38 w1_34 w1_30 w1_2c w1_28 w1_24 g1_12 g1_11 g1_10 g1_27 g1_26 g1_24 g1_22 g1_21 g1_20 g1_19 g1_18 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
  -- 0x1A8E
  obtain ⟨n3, c3, u3⟩ := s2.block svZS1a8e E2.self svZS1a8e_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have s3 : St n3.mem SV n3 0x1AAA (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have rb3 : ∀ q, reg n3 q = (runBlock svZS1a8e (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
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
  have g3_20 : reg n3 (20 : Fin 32) = BitVec.ofNat 32 0x60 := by
    rw [rb3, runBlock_reg _ _ _ (20 : Fin 32) s2.zero (by decide), g2_20]
  have g3_21 : reg n3 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by
    rw [rb3, runBlock_reg _ _ _ (21 : Fin 32) s2.zero (by decide), g2_21]
  have g3_24 : reg n3 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA60 := by
    rw [rb3, runBlock_reg _ _ _ (24 : Fin 32) s2.zero (by decide), g2_24]
  have g3_26 : reg n3 (26 : Fin 32) = x26 := by
    rw [rb3, runBlock_reg _ _ _ (26 : Fin 32) s2.zero (by decide), g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb3, runBlock_reg _ _ _ (27 : Fin 32) s2.zero (by decide), g2_27]
  have g3_10 : reg n3 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb3]; simp +decide only [runBlock, BInstr.run, svZS1a8e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g2_2, g2_3, g2_4, g2_18, g2_19, g2_20, g2_21, g2_22, g2_24, g2_26, g2_27, s2.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g3_11 : reg n3 a1 = BitVec.ofNat 32 0x3FCC4B38 := by
    rw [rb3]; simp +decide only [runBlock, BInstr.run, svZS1a8e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g2_2, g2_3, g2_4, g2_18, g2_19, g2_20, g2_21, g2_22, g2_24, g2_26, g2_27, s2.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g3_12 : reg n3 a2 = BitVec.ofNat 32 0x20 := by
    rw [rb3]; simp +decide only [runBlock, BInstr.run, svZS1a8e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g2_2, g2_3, g2_4, g2_18, g2_19, g2_20, g2_21, g2_22, g2_24, g2_26, g2_27, s2.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g3_22 : reg n3 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x15E8 := by
    rw [rb3]; simp +decide only [runBlock, BInstr.run, svZS1a8e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g2_2, g2_3, g2_4, g2_18, g2_19, g2_20, g2_21, g2_22, g2_24, g2_26, g2_27, s2.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g3_23 : reg n3 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC4B38 := by
    rw [rb3]; simp +decide only [runBlock, BInstr.run, svZS1a8e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g2_2, g2_3, g2_4, g2_18, g2_19, g2_20, g2_21, g2_22, g2_24, g2_26, g2_27, s2.zero])
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
  have a3_1480 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = X := by rw [m3]; exact a2_1480
  have a3_14a0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) 8 = Y := by rw [m3]; exact a2_14a0
  have a3_14c0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x14C0) 8 = Z := by rw [m3]; exact a2_14c0
  have a3_15a8 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := by rw [m3]; exact a2_15a8
  have a3_15c8 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := by rw [m3]; exact a2_15c8
  have a3_15e8 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x15E8) 8 = Z := by rw [m3]; exact a2_15e8
  clear a2_15e8 a2_15c8 a2_15a8 a2_14c0 a2_14a0 a2_1480 a2_2e0 a2_2c0 a2_2a0 w2_130 w2_12c w2_128 w2_124 w2_120 w2_11c w2_118 w2_114 w2_110 w2_10c w2_108 w2_104 w2_100 w2_fc w2_f8 w2_f4 w2_f0 w2_ec w2_e8 w2_e4 w2_e0 w2_dc w2_d8 w2_d4 w2_d0 w2_cc w2_c8 w2_c4 w2_c0 w2_bc w2_b8 w2_b4 w2_b0 w2_ac w2_a8 w2_a4 w2_a0 w2_9c w2_98 w2_94 w2_90 w2_8c w2_88 w2_84 w2_80 w2_7c w2_70 w2_6c w2_68 w2_64 w2_60 w2_5c w2_58 w2_54 w2_50 w2_4c w2_48 w2_44 w2_40 w2_3c w2_38 w2_34 w2_30 w2_2c w2_28 w2_24 g2_27 g2_26 g2_24 g2_22 g2_21 g2_20 g2_19 g2_18 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 s2 X2 K2 P2
  -- 0x1AAA: memcpy from outside the stack
  obtain ⟨n4, P4, K4, X4⟩ := sv_mcRo2 (c := 0x420) (N := 0x20) F RS E3 s3 sv_at_1aaa sv_at_1aae
    (by decide) (by decide) g3_2 g3_10 g3_11 g3_12 (by decide) (Or.inr ⟨by decide, by decide⟩)
  have s4 := P4.st
  have fr4 := P4.fr
  have t4 : Steps n0 n4 := t3.trans P4.steps
  have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : SvCode n4.mem := E3.fr F fr4
  have V4 : SvSaves B n4.mem v := V3.keep K4 (by decide)
  have g4_2 : reg n4 sp = B + 0x21A0 := by rw [P4.regs sp (by decide), g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P4.regs (3 : Fin 32) (by decide), g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P4.regs (4 : Fin 32) (by decide), g3_4]
  have g4_18 : reg n4 (18 : Fin 32) = out := by rw [P4.regs (18 : Fin 32) (by decide), g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [P4.regs (19 : Fin 32) (by decide), g3_19]
  have g4_20 : reg n4 (20 : Fin 32) = BitVec.ofNat 32 0x60 := by rw [P4.regs (20 : Fin 32) (by decide), g3_20]
  have g4_21 : reg n4 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [P4.regs (21 : Fin 32) (by decide), g3_21]
  have g4_22 : reg n4 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x15E8 := by rw [P4.regs (22 : Fin 32) (by decide), g3_22]
  have g4_23 : reg n4 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC4B38 := by rw [P4.regs (23 : Fin 32) (by decide), g3_23]
  have g4_24 : reg n4 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA60 := by rw [P4.regs (24 : Fin 32) (by decide), g3_24]
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
  have a4_1480 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = X := (K4.acc (by decide) (by decide)).trans a3_1480
  have a4_14a0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) 8 = Y := (K4.acc (by decide) (by decide)).trans a3_14a0
  have a4_14c0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x14C0) 8 = Z := (K4.acc (by decide) (by decide)).trans a3_14c0
  have a4_15a8 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := (K4.acc (by decide) (by decide)).trans a3_15a8
  have a4_15c8 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := (K4.acc (by decide) (by decide)).trans a3_15c8
  have a4_15e8 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x15E8) 8 = Z := (K4.acc (by decide) (by decide)).trans a3_15e8
  have q4_420 : ∀ j, j < 32 → n4.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) :=
    fun j hj => (X4 j hj).trans (fR3 _ (SvRo2.r RS (Or.inr ⟨by decide, by decide⟩) hj))
  have a4_420 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := acc_of_frame q4_420
  clear a3_15e8 a3_15c8 a3_15a8 a3_14c0 a3_14a0 a3_1480 a3_2e0 a3_2c0 a3_2a0 w3_130 w3_12c w3_128 w3_124 w3_120 w3_11c w3_118 w3_114 w3_110 w3_10c w3_108 w3_104 w3_100 w3_fc w3_f8 w3_f4 w3_f0 w3_ec w3_e8 w3_e4 w3_e0 w3_dc w3_d8 w3_d4 w3_d0 w3_cc w3_c8 w3_c4 w3_c0 w3_bc w3_b8 w3_b4 w3_b0 w3_ac w3_a8 w3_a4 w3_a0 w3_9c w3_98 w3_94 w3_90 w3_8c w3_88 w3_84 w3_80 w3_7c w3_70 w3_6c w3_68 w3_64 w3_60 w3_5c w3_58 w3_54 w3_50 w3_4c w3_48 w3_44 w3_40 w3_3c w3_38 w3_34 w3_30 w3_2c w3_28 w3_24 g3_23 g3_22 g3_12 g3_11 g3_10 g3_27 g3_26 g3_24 g3_21 g3_20 g3_19 g3_18 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 rb3 s3 m3 u3 c3
  -- 0x1AB2
  obtain ⟨n5, c5, u5⟩ := s4.block svZS1ab2 E4.self svZS1ab2_end
    ⟨trivial, trivial⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have s5 : St n5.mem SV n5 0x1AB4 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have rb5 : ∀ q, reg n5 q = (runBlock svZS1ab2 (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
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
  have g5_18 : reg n5 (18 : Fin 32) = out := by
    rw [rb5, runBlock_reg _ _ _ (18 : Fin 32) s4.zero (by decide), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by
    rw [rb5, runBlock_reg _ _ _ (19 : Fin 32) s4.zero (by decide), g4_19]
  have g5_20 : reg n5 (20 : Fin 32) = BitVec.ofNat 32 0x60 := by
    rw [rb5, runBlock_reg _ _ _ (20 : Fin 32) s4.zero (by decide), g4_20]
  have g5_21 : reg n5 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by
    rw [rb5, runBlock_reg _ _ _ (21 : Fin 32) s4.zero (by decide), g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x15E8 := by
    rw [rb5, runBlock_reg _ _ _ (22 : Fin 32) s4.zero (by decide), g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC4B38 := by
    rw [rb5, runBlock_reg _ _ _ (23 : Fin 32) s4.zero (by decide), g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA60 := by
    rw [rb5, runBlock_reg _ _ _ (24 : Fin 32) s4.zero (by decide), g4_24]
  have g5_26 : reg n5 (26 : Fin 32) = x26 := by
    rw [rb5, runBlock_reg _ _ _ (26 : Fin 32) s4.zero (by decide), g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb5, runBlock_reg _ _ _ (27 : Fin 32) s4.zero (by decide), g4_27]
  have g5_10 : reg n5 a0 = BitVec.ofNat 32 0xFFFFFFFF := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, svZS1ab2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_18, g4_19, g4_20, g4_21, g4_22, g4_23, g4_24, g4_26, g4_27, s4.zero])
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
  have q5_420 : ∀ j, j < 32 → n5.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) := fun j hj => by rw [m5]; exact q4_420 j hj
  have a5_2a0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m5]; exact a4_2a0
  have a5_2c0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m5]; exact a4_2c0
  have a5_2e0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m5]; exact a4_2e0
  have a5_420 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := by rw [m5]; exact a4_420
  have a5_1480 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = X := by rw [m5]; exact a4_1480
  have a5_14a0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) 8 = Y := by rw [m5]; exact a4_14a0
  have a5_14c0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x14C0) 8 = Z := by rw [m5]; exact a4_14c0
  have a5_15a8 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := by rw [m5]; exact a4_15a8
  have a5_15c8 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := by rw [m5]; exact a4_15c8
  have a5_15e8 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x15E8) 8 = Z := by rw [m5]; exact a4_15e8
  clear a4_420 q4_420 a4_15e8 a4_15c8 a4_15a8 a4_14c0 a4_14a0 a4_1480 a4_2e0 a4_2c0 a4_2a0 w4_130 w4_12c w4_128 w4_124 w4_120 w4_11c w4_118 w4_114 w4_110 w4_10c w4_108 w4_104 w4_100 w4_fc w4_f8 w4_f4 w4_f0 w4_ec w4_e8 w4_e4 w4_e0 w4_dc w4_d8 w4_d4 w4_d0 w4_cc w4_c8 w4_c4 w4_c0 w4_bc w4_b8 w4_b4 w4_b0 w4_ac w4_a8 w4_a4 w4_a0 w4_9c w4_98 w4_94 w4_90 w4_8c w4_88 w4_84 w4_80 w4_7c w4_70 w4_6c w4_68 w4_64 w4_60 w4_5c w4_58 w4_54 w4_50 w4_4c w4_48 w4_44 w4_40 w4_3c w4_38 w4_34 w4_30 w4_2c w4_28 w4_24 g4_27 g4_26 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 s4 X4 K4 P4
  -- 0x1AB4: sw
  obtain ⟨n6, d6, s6, fr6, K6, W6, rg6⟩ := sv_sw F E5 s5 sv_at_1ab4 (off' := 0x1AB8) (c := 0x460)
    (by decide) (by rw [g5_2]; sv_addr) (by decide) (by decide)
  have t6 : Steps n0 n6 := t5.trans d6
  have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : SvCode n6.mem := E5.fr F fr6
  have V6 : SvSaves B n6.mem v := V5.keep K6 (by decide)
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [rg6 sp, g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg6 (3 : Fin 32), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg6 (4 : Fin 32), g5_4]
  have g6_10 : reg n6 a0 = BitVec.ofNat 32 0xFFFFFFFF := by rw [rg6 a0, g5_10]
  have g6_18 : reg n6 (18 : Fin 32) = out := by rw [rg6 (18 : Fin 32), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [rg6 (19 : Fin 32), g5_19]
  have g6_20 : reg n6 (20 : Fin 32) = BitVec.ofNat 32 0x60 := by rw [rg6 (20 : Fin 32), g5_20]
  have g6_21 : reg n6 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [rg6 (21 : Fin 32), g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x15E8 := by rw [rg6 (22 : Fin 32), g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC4B38 := by rw [rg6 (23 : Fin 32), g5_23]
  have g6_24 : reg n6 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA60 := by rw [rg6 (24 : Fin 32), g5_24]
  have g6_26 : reg n6 (26 : Fin 32) = x26 := by rw [rg6 (26 : Fin 32), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg6 (27 : Fin 32), g5_27]
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
  have w6_460 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := by rw [W6, g5_10]
  have q6_420 : ∀ j, j < 32 → n6.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) := fun j hj => (K6.range (by decide) (by decide) j hj).trans (q5_420 j hj)
  have a6_2a0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K6.acc (by decide) (by decide)).trans a5_2a0
  have a6_2c0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K6.acc (by decide) (by decide)).trans a5_2c0
  have a6_2e0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K6.acc (by decide) (by decide)).trans a5_2e0
  have a6_420 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := (K6.acc (by decide) (by decide)).trans a5_420
  have a6_1480 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = X := (K6.acc (by decide) (by decide)).trans a5_1480
  have a6_14a0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) 8 = Y := (K6.acc (by decide) (by decide)).trans a5_14a0
  have a6_14c0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x14C0) 8 = Z := (K6.acc (by decide) (by decide)).trans a5_14c0
  have a6_15a8 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := (K6.acc (by decide) (by decide)).trans a5_15a8
  have a6_15c8 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := (K6.acc (by decide) (by decide)).trans a5_15c8
  have a6_15e8 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x15E8) 8 = Z := (K6.acc (by decide) (by decide)).trans a5_15e8
  clear a5_15e8 a5_15c8 a5_15a8 a5_14c0 a5_14a0 a5_1480 a5_420 a5_2e0 a5_2c0 a5_2a0 q5_420 w5_130 w5_12c w5_128 w5_124 w5_120 w5_11c w5_118 w5_114 w5_110 w5_10c w5_108 w5_104 w5_100 w5_fc w5_f8 w5_f4 w5_f0 w5_ec w5_e8 w5_e4 w5_e0 w5_dc w5_d8 w5_d4 w5_d0 w5_cc w5_c8 w5_c4 w5_c0 w5_bc w5_b8 w5_b4 w5_b0 w5_ac w5_a8 w5_a4 w5_a0 w5_9c w5_98 w5_94 w5_90 w5_8c w5_88 w5_84 w5_80 w5_7c w5_70 w5_6c w5_68 w5_64 w5_60 w5_5c w5_58 w5_54 w5_50 w5_4c w5_48 w5_44 w5_40 w5_3c w5_38 w5_34 w5_30 w5_2c w5_28 w5_24 g5_10 g5_27 g5_26 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 rb5 s5 m5 u5 c5
  -- 0x1AB8: sw
  obtain ⟨n7, d7, s7, fr7, K7, W7, rg7⟩ := sv_sw F E6 s6 sv_at_1ab8 (off' := 0x1ABC) (c := 0x464)
    (by decide) (by rw [g6_2]; sv_addr) (by decide) (by decide)
  have t7 : Steps n0 n7 := t6.trans d7
  have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : SvCode n7.mem := E6.fr F fr7
  have V7 : SvSaves B n7.mem v := V6.keep K7 (by decide)
  have g7_2 : reg n7 sp = B + 0x21A0 := by rw [rg7 sp, g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg7 (3 : Fin 32), g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg7 (4 : Fin 32), g6_4]
  have g7_10 : reg n7 a0 = BitVec.ofNat 32 0xFFFFFFFF := by rw [rg7 a0, g6_10]
  have g7_18 : reg n7 (18 : Fin 32) = out := by rw [rg7 (18 : Fin 32), g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [rg7 (19 : Fin 32), g6_19]
  have g7_20 : reg n7 (20 : Fin 32) = BitVec.ofNat 32 0x60 := by rw [rg7 (20 : Fin 32), g6_20]
  have g7_21 : reg n7 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [rg7 (21 : Fin 32), g6_21]
  have g7_22 : reg n7 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x15E8 := by rw [rg7 (22 : Fin 32), g6_22]
  have g7_23 : reg n7 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC4B38 := by rw [rg7 (23 : Fin 32), g6_23]
  have g7_24 : reg n7 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA60 := by rw [rg7 (24 : Fin 32), g6_24]
  have g7_26 : reg n7 (26 : Fin 32) = x26 := by rw [rg7 (26 : Fin 32), g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg7 (27 : Fin 32), g6_27]
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
  have w7_5c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K7.w32 (by decide) (by decide)).trans w6_5c
  have w7_60 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K7.w32 (by decide) (by decide)).trans w6_60
  have w7_64 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K7.w32 (by decide) (by decide)).trans w6_64
  have w7_68 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K7.w32 (by decide) (by decide)).trans w6_68
  have w7_6c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K7.w32 (by decide) (by decide)).trans w6_6c
  have w7_70 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K7.w32 (by decide) (by decide)).trans w6_70
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
  have w7_460 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := (K7.w32 (by decide) (by decide)).trans w6_460
  have w7_464 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := by rw [W7, g6_10]
  have q7_420 : ∀ j, j < 32 → n7.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) := fun j hj => (K7.range (by decide) (by decide) j hj).trans (q6_420 j hj)
  have a7_2a0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K7.acc (by decide) (by decide)).trans a6_2a0
  have a7_2c0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K7.acc (by decide) (by decide)).trans a6_2c0
  have a7_2e0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K7.acc (by decide) (by decide)).trans a6_2e0
  have a7_420 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := (K7.acc (by decide) (by decide)).trans a6_420
  have a7_1480 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = X := (K7.acc (by decide) (by decide)).trans a6_1480
  have a7_14a0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) 8 = Y := (K7.acc (by decide) (by decide)).trans a6_14a0
  have a7_14c0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x14C0) 8 = Z := (K7.acc (by decide) (by decide)).trans a6_14c0
  have a7_15a8 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := (K7.acc (by decide) (by decide)).trans a6_15a8
  have a7_15c8 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := (K7.acc (by decide) (by decide)).trans a6_15c8
  have a7_15e8 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x15E8) 8 = Z := (K7.acc (by decide) (by decide)).trans a6_15e8
  clear a6_15e8 a6_15c8 a6_15a8 a6_14c0 a6_14a0 a6_1480 a6_420 a6_2e0 a6_2c0 a6_2a0 q6_420 w6_460 w6_130 w6_12c w6_128 w6_124 w6_120 w6_11c w6_118 w6_114 w6_110 w6_10c w6_108 w6_104 w6_100 w6_fc w6_f8 w6_f4 w6_f0 w6_ec w6_e8 w6_e4 w6_e0 w6_dc w6_d8 w6_d4 w6_d0 w6_cc w6_c8 w6_c4 w6_c0 w6_bc w6_b8 w6_b4 w6_b0 w6_ac w6_a8 w6_a4 w6_a0 w6_9c w6_98 w6_94 w6_90 w6_8c w6_88 w6_84 w6_80 w6_7c w6_70 w6_6c w6_68 w6_64 w6_60 w6_5c w6_58 w6_54 w6_50 w6_4c w6_48 w6_44 w6_40 w6_3c w6_38 w6_34 w6_30 w6_2c w6_28 w6_24 g6_27 g6_26 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_10 g6_4 g6_3 g6_2 V6 E6 fR6 t6 rg6 W6 K6 fr6 s6 d6
  -- 0x1ABC
  obtain ⟨n8, c8, u8⟩ := s7.block svZS1abc E7.self svZS1abc_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m8 : n8.mem = n7.mem := u8.mem
  have s8 : St n8.mem SV n8 0x1ACA (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
  have rb8 : ∀ q, reg n8 q = (runBlock svZS1abc (n7.mem, reg n7)).2 q := fun q => by rw [u8.regs]
  have fr8 : ∀ x, SvR B x → n8.mem x = n7.mem x := fun x _ => by rw [m8]
  have t8 : Steps n0 n8 := t7.trans c8
  have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : SvCode n8.mem := E7.fr F fr8
  have V8 : SvSaves B n8.mem v := V7.same m8
  have g8_2 : reg n8 sp = B + 0x21A0 := by
    rw [rb8, runBlock_reg _ _ _ sp s7.zero (by decide), g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb8, runBlock_reg _ _ _ (3 : Fin 32) s7.zero (by decide), g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb8, runBlock_reg _ _ _ (4 : Fin 32) s7.zero (by decide), g7_4]
  have g8_18 : reg n8 (18 : Fin 32) = out := by
    rw [rb8, runBlock_reg _ _ _ (18 : Fin 32) s7.zero (by decide), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by
    rw [rb8, runBlock_reg _ _ _ (19 : Fin 32) s7.zero (by decide), g7_19]
  have g8_20 : reg n8 (20 : Fin 32) = BitVec.ofNat 32 0x60 := by
    rw [rb8, runBlock_reg _ _ _ (20 : Fin 32) s7.zero (by decide), g7_20]
  have g8_21 : reg n8 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by
    rw [rb8, runBlock_reg _ _ _ (21 : Fin 32) s7.zero (by decide), g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x15E8 := by
    rw [rb8, runBlock_reg _ _ _ (22 : Fin 32) s7.zero (by decide), g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC4B38 := by
    rw [rb8, runBlock_reg _ _ _ (23 : Fin 32) s7.zero (by decide), g7_23]
  have g8_24 : reg n8 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA60 := by
    rw [rb8, runBlock_reg _ _ _ (24 : Fin 32) s7.zero (by decide), g7_24]
  have g8_26 : reg n8 (26 : Fin 32) = x26 := by
    rw [rb8, runBlock_reg _ _ _ (26 : Fin 32) s7.zero (by decide), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb8, runBlock_reg _ _ _ (27 : Fin 32) s7.zero (by decide), g7_27]
  have g8_8 : reg n8 (8 : Fin 32) = BitVec.ofNat 32 0x3FCC4B78 := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, svZS1abc, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g7_2, g7_3, g7_4, g7_10, g7_18, g7_19, g7_20, g7_21, g7_22, g7_23, g7_24, g7_26, g7_27, s7.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g8_10 : reg n8 a0 = B + 0x21A0 + BitVec.ofNat 32 0x440 := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, svZS1abc, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g7_2, g7_3, g7_4, g7_10, g7_18, g7_19, g7_20, g7_21, g7_22, g7_23, g7_24, g7_26, g7_27, s7.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g8_11 : reg n8 a1 = BitVec.ofNat 32 0x3FCC4B78 := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, svZS1abc, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g7_2, g7_3, g7_4, g7_10, g7_18, g7_19, g7_20, g7_21, g7_22, g7_23, g7_24, g7_26, g7_27, s7.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g8_12 : reg n8 a2 = BitVec.ofNat 32 0x20 := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, svZS1abc, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g7_2, g7_3, g7_4, g7_10, g7_18, g7_19, g7_20, g7_21, g7_22, g7_23, g7_24, g7_26, g7_27, s7.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
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
  have w8_460 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m8]; exact w7_460
  have w8_464 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m8]; exact w7_464
  have q8_420 : ∀ j, j < 32 → n8.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) := fun j hj => by rw [m8]; exact q7_420 j hj
  have a8_2a0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m8]; exact a7_2a0
  have a8_2c0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m8]; exact a7_2c0
  have a8_2e0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m8]; exact a7_2e0
  have a8_420 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := by rw [m8]; exact a7_420
  have a8_1480 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = X := by rw [m8]; exact a7_1480
  have a8_14a0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) 8 = Y := by rw [m8]; exact a7_14a0
  have a8_14c0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x14C0) 8 = Z := by rw [m8]; exact a7_14c0
  have a8_15a8 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := by rw [m8]; exact a7_15a8
  have a8_15c8 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := by rw [m8]; exact a7_15c8
  have a8_15e8 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x15E8) 8 = Z := by rw [m8]; exact a7_15e8
  clear a7_15e8 a7_15c8 a7_15a8 a7_14c0 a7_14a0 a7_1480 a7_420 a7_2e0 a7_2c0 a7_2a0 q7_420 w7_464 w7_460 w7_130 w7_12c w7_128 w7_124 w7_120 w7_11c w7_118 w7_114 w7_110 w7_10c w7_108 w7_104 w7_100 w7_fc w7_f8 w7_f4 w7_f0 w7_ec w7_e8 w7_e4 w7_e0 w7_dc w7_d8 w7_d4 w7_d0 w7_cc w7_c8 w7_c4 w7_c0 w7_bc w7_b8 w7_b4 w7_b0 w7_ac w7_a8 w7_a4 w7_a0 w7_9c w7_98 w7_94 w7_90 w7_8c w7_88 w7_84 w7_80 w7_7c w7_70 w7_6c w7_68 w7_64 w7_60 w7_5c w7_58 w7_54 w7_50 w7_4c w7_48 w7_44 w7_40 w7_3c w7_38 w7_34 w7_30 w7_2c w7_28 w7_24 g7_27 g7_26 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_10 g7_4 g7_3 g7_2 V7 E7 fR7 t7 rg7 W7 K7 fr7 s7 d7
  -- 0x1ACA: memcpy from outside the stack
  obtain ⟨n9, P9, K9, X9⟩ := sv_mcRo2 (c := 0x440) (N := 0x20) F RS E8 s8 sv_at_1aca sv_at_1ace
    (by decide) (by decide) g8_2 g8_10 g8_11 g8_12 (by decide) (Or.inr ⟨by decide, by decide⟩)
  have s9 := P9.st
  have fr9 := P9.fr
  have t9 : Steps n0 n9 := t8.trans P9.steps
  have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : SvCode n9.mem := E8.fr F fr9
  have V9 : SvSaves B n9.mem v := V8.keep K9 (by decide)
  have g9_2 : reg n9 sp = B + 0x21A0 := by rw [P9.regs sp (by decide), g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P9.regs (3 : Fin 32) (by decide), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P9.regs (4 : Fin 32) (by decide), g8_4]
  have g9_8 : reg n9 (8 : Fin 32) = BitVec.ofNat 32 0x3FCC4B78 := by rw [P9.regs (8 : Fin 32) (by decide), g8_8]
  have g9_18 : reg n9 (18 : Fin 32) = out := by rw [P9.regs (18 : Fin 32) (by decide), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [P9.regs (19 : Fin 32) (by decide), g8_19]
  have g9_20 : reg n9 (20 : Fin 32) = BitVec.ofNat 32 0x60 := by rw [P9.regs (20 : Fin 32) (by decide), g8_20]
  have g9_21 : reg n9 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [P9.regs (21 : Fin 32) (by decide), g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x15E8 := by rw [P9.regs (22 : Fin 32) (by decide), g8_22]
  have g9_23 : reg n9 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC4B38 := by rw [P9.regs (23 : Fin 32) (by decide), g8_23]
  have g9_24 : reg n9 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA60 := by rw [P9.regs (24 : Fin 32) (by decide), g8_24]
  have g9_26 : reg n9 (26 : Fin 32) = x26 := by rw [P9.regs (26 : Fin 32) (by decide), g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P9.regs (27 : Fin 32) (by decide), g8_27]
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
  have w9_5c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K9.w32 (by decide) (by decide)).trans w8_5c
  have w9_60 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K9.w32 (by decide) (by decide)).trans w8_60
  have w9_64 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K9.w32 (by decide) (by decide)).trans w8_64
  have w9_68 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K9.w32 (by decide) (by decide)).trans w8_68
  have w9_6c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K9.w32 (by decide) (by decide)).trans w8_6c
  have w9_70 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K9.w32 (by decide) (by decide)).trans w8_70
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
  have w9_460 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := (K9.w32 (by decide) (by decide)).trans w8_460
  have w9_464 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := (K9.w32 (by decide) (by decide)).trans w8_464
  have q9_420 : ∀ j, j < 32 → n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) := fun j hj => (K9.range (by decide) (by decide) j hj).trans (q8_420 j hj)
  have a9_2a0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K9.acc (by decide) (by decide)).trans a8_2a0
  have a9_2c0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K9.acc (by decide) (by decide)).trans a8_2c0
  have a9_2e0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K9.acc (by decide) (by decide)).trans a8_2e0
  have a9_420 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := (K9.acc (by decide) (by decide)).trans a8_420
  have a9_1480 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = X := (K9.acc (by decide) (by decide)).trans a8_1480
  have a9_14a0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) 8 = Y := (K9.acc (by decide) (by decide)).trans a8_14a0
  have a9_14c0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x14C0) 8 = Z := (K9.acc (by decide) (by decide)).trans a8_14c0
  have a9_15a8 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := (K9.acc (by decide) (by decide)).trans a8_15a8
  have a9_15c8 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := (K9.acc (by decide) (by decide)).trans a8_15c8
  have a9_15e8 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x15E8) 8 = Z := (K9.acc (by decide) (by decide)).trans a8_15e8
  have q9_440 : ∀ j, j < 32 → n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0x440 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B78) + BitVec.ofNat 32 j) :=
    fun j hj => (X9 j hj).trans (fR8 _ (SvRo2.r RS (Or.inr ⟨by decide, by decide⟩) hj))
  have a9_440 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := acc_of_frame q9_440
  clear a8_15e8 a8_15c8 a8_15a8 a8_14c0 a8_14a0 a8_1480 a8_420 a8_2e0 a8_2c0 a8_2a0 q8_420 w8_464 w8_460 w8_130 w8_12c w8_128 w8_124 w8_120 w8_11c w8_118 w8_114 w8_110 w8_10c w8_108 w8_104 w8_100 w8_fc w8_f8 w8_f4 w8_f0 w8_ec w8_e8 w8_e4 w8_e0 w8_dc w8_d8 w8_d4 w8_d0 w8_cc w8_c8 w8_c4 w8_c0 w8_bc w8_b8 w8_b4 w8_b0 w8_ac w8_a8 w8_a4 w8_a0 w8_9c w8_98 w8_94 w8_90 w8_8c w8_88 w8_84 w8_80 w8_7c w8_70 w8_6c w8_68 w8_64 w8_60 w8_5c w8_58 w8_54 w8_50 w8_4c w8_48 w8_44 w8_40 w8_3c w8_38 w8_34 w8_30 w8_2c w8_28 w8_24 g8_12 g8_11 g8_10 g8_8 g8_27 g8_26 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 rb8 s8 m8 u8 c8
  -- 0x1AD2
  obtain ⟨n10, c10, u10⟩ := s9.block svZS1ad2 E9.self svZS1ad2_end
    ⟨trivial, trivial⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have s10 : St n10.mem SV n10 0x1AD4 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have rb10 : ∀ q, reg n10 q = (runBlock svZS1ad2 (n9.mem, reg n9)).2 q := fun q => by rw [u10.regs]
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
  have g10_8 : reg n10 (8 : Fin 32) = BitVec.ofNat 32 0x3FCC4B78 := by
    rw [rb10, runBlock_reg _ _ _ (8 : Fin 32) s9.zero (by decide), g9_8]
  have g10_18 : reg n10 (18 : Fin 32) = out := by
    rw [rb10, runBlock_reg _ _ _ (18 : Fin 32) s9.zero (by decide), g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = bp := by
    rw [rb10, runBlock_reg _ _ _ (19 : Fin 32) s9.zero (by decide), g9_19]
  have g10_20 : reg n10 (20 : Fin 32) = BitVec.ofNat 32 0x60 := by
    rw [rb10, runBlock_reg _ _ _ (20 : Fin 32) s9.zero (by decide), g9_20]
  have g10_21 : reg n10 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by
    rw [rb10, runBlock_reg _ _ _ (21 : Fin 32) s9.zero (by decide), g9_21]
  have g10_22 : reg n10 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x15E8 := by
    rw [rb10, runBlock_reg _ _ _ (22 : Fin 32) s9.zero (by decide), g9_22]
  have g10_23 : reg n10 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC4B38 := by
    rw [rb10, runBlock_reg _ _ _ (23 : Fin 32) s9.zero (by decide), g9_23]
  have g10_24 : reg n10 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA60 := by
    rw [rb10, runBlock_reg _ _ _ (24 : Fin 32) s9.zero (by decide), g9_24]
  have g10_26 : reg n10 (26 : Fin 32) = x26 := by
    rw [rb10, runBlock_reg _ _ _ (26 : Fin 32) s9.zero (by decide), g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb10, runBlock_reg _ _ _ (27 : Fin 32) s9.zero (by decide), g9_27]
  have g10_10 : reg n10 a0 = B + 0x21A0 + BitVec.ofNat 32 0x15E8 := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, svZS1ad2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g9_2, g9_3, g9_4, g9_8, g9_18, g9_19, g9_20, g9_21, g9_22, g9_23, g9_24, g9_26, g9_27, s9.zero])
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
  have w10_5c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m10]; exact w9_5c
  have w10_60 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m10]; exact w9_60
  have w10_64 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m10]; exact w9_64
  have w10_68 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m10]; exact w9_68
  have w10_6c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m10]; exact w9_6c
  have w10_70 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m10]; exact w9_70
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
  have w10_460 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m10]; exact w9_460
  have w10_464 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m10]; exact w9_464
  have q10_420 : ∀ j, j < 32 → n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) := fun j hj => by rw [m10]; exact q9_420 j hj
  have q10_440 : ∀ j, j < 32 → n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0x440 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B78) + BitVec.ofNat 32 j) := fun j hj => by rw [m10]; exact q9_440 j hj
  have a10_2a0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m10]; exact a9_2a0
  have a10_2c0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m10]; exact a9_2c0
  have a10_2e0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m10]; exact a9_2e0
  have a10_420 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := by rw [m10]; exact a9_420
  have a10_440 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := by rw [m10]; exact a9_440
  have a10_1480 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = X := by rw [m10]; exact a9_1480
  have a10_14a0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) 8 = Y := by rw [m10]; exact a9_14a0
  have a10_14c0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x14C0) 8 = Z := by rw [m10]; exact a9_14c0
  have a10_15a8 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := by rw [m10]; exact a9_15a8
  have a10_15c8 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := by rw [m10]; exact a9_15c8
  have a10_15e8 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x15E8) 8 = Z := by rw [m10]; exact a9_15e8
  clear a9_440 q9_440 a9_15e8 a9_15c8 a9_15a8 a9_14c0 a9_14a0 a9_1480 a9_420 a9_2e0 a9_2c0 a9_2a0 q9_420 w9_464 w9_460 w9_130 w9_12c w9_128 w9_124 w9_120 w9_11c w9_118 w9_114 w9_110 w9_10c w9_108 w9_104 w9_100 w9_fc w9_f8 w9_f4 w9_f0 w9_ec w9_e8 w9_e4 w9_e0 w9_dc w9_d8 w9_d4 w9_d0 w9_cc w9_c8 w9_c4 w9_c0 w9_bc w9_b8 w9_b4 w9_b0 w9_ac w9_a8 w9_a4 w9_a0 w9_9c w9_98 w9_94 w9_90 w9_8c w9_88 w9_84 w9_80 w9_7c w9_70 w9_6c w9_68 w9_64 w9_60 w9_5c w9_58 w9_54 w9_50 w9_4c w9_48 w9_44 w9_40 w9_3c w9_38 w9_34 w9_30 w9_2c w9_28 w9_24 g9_27 g9_26 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 s9 X9 K9 P9
  -- 0x1AD4: sv_unz8F
  obtain ⟨n11, c11, s11, sp11, rk11, a0_11, K11, fr11⟩ := sv_unz8F (cx := 0x15E8)
    F E10 (EC0.sv F fR10) s10 sv_at_1ad4 sv_at_1ad8 (by decide) (by decide) g10_2
    g10_10 (by decide) (by decide)
  simp only [limbs0_iff a10_15e8] at a0_11
  have t11 : Steps n0 n11 := t10.trans c11
  have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : SvCode n11.mem := E10.fr F fr11
  have V11 : SvSaves B n11.mem v := V10.keepL K11 (by decide)
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk11 (3 : Fin 32) (by decide), g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk11 (4 : Fin 32) (by decide), g10_4]
  have g11_8 : reg n11 (8 : Fin 32) = BitVec.ofNat 32 0x3FCC4B78 := by rw [rk11 (8 : Fin 32) (by decide), g10_8]
  have g11_18 : reg n11 (18 : Fin 32) = out := by rw [rk11 (18 : Fin 32) (by decide), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [rk11 (19 : Fin 32) (by decide), g10_19]
  have g11_20 : reg n11 (20 : Fin 32) = BitVec.ofNat 32 0x60 := by rw [rk11 (20 : Fin 32) (by decide), g10_20]
  have g11_21 : reg n11 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [rk11 (21 : Fin 32) (by decide), g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x15E8 := by rw [rk11 (22 : Fin 32) (by decide), g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC4B38 := by rw [rk11 (23 : Fin 32) (by decide), g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA60 := by rw [rk11 (24 : Fin 32) (by decide), g10_24]
  have g11_26 : reg n11 (26 : Fin 32) = x26 := by rw [rk11 (26 : Fin 32) (by decide), g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk11 (27 : Fin 32) (by decide), g10_27]
  have g11_2 : reg n11 sp = B + 0x21A0 := sp11
  have w11_24 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K11.w32 (by decide) (by decide)).trans w10_24
  have w11_28 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K11.w32 (by decide) (by decide)).trans w10_28
  have w11_2c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K11.w32 (by decide) (by decide)).trans w10_2c
  have w11_30 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K11.w32 (by decide) (by decide)).trans w10_30
  have w11_34 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K11.w32 (by decide) (by decide)).trans w10_34
  have w11_38 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K11.w32 (by decide) (by decide)).trans w10_38
  have w11_3c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K11.w32 (by decide) (by decide)).trans w10_3c
  have w11_40 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K11.w32 (by decide) (by decide)).trans w10_40
  have w11_44 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K11.w32 (by decide) (by decide)).trans w10_44
  have w11_48 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K11.w32 (by decide) (by decide)).trans w10_48
  have w11_4c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K11.w32 (by decide) (by decide)).trans w10_4c
  have w11_50 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K11.w32 (by decide) (by decide)).trans w10_50
  have w11_54 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K11.w32 (by decide) (by decide)).trans w10_54
  have w11_58 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K11.w32 (by decide) (by decide)).trans w10_58
  have w11_5c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K11.w32 (by decide) (by decide)).trans w10_5c
  have w11_60 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K11.w32 (by decide) (by decide)).trans w10_60
  have w11_64 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K11.w32 (by decide) (by decide)).trans w10_64
  have w11_68 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K11.w32 (by decide) (by decide)).trans w10_68
  have w11_6c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K11.w32 (by decide) (by decide)).trans w10_6c
  have w11_70 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K11.w32 (by decide) (by decide)).trans w10_70
  have w11_7c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K11.w32 (by decide) (by decide)).trans w10_7c
  have w11_80 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K11.w32 (by decide) (by decide)).trans w10_80
  have w11_84 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K11.w32 (by decide) (by decide)).trans w10_84
  have w11_88 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K11.w32 (by decide) (by decide)).trans w10_88
  have w11_8c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K11.w32 (by decide) (by decide)).trans w10_8c
  have w11_90 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K11.w32 (by decide) (by decide)).trans w10_90
  have w11_94 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K11.w32 (by decide) (by decide)).trans w10_94
  have w11_98 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K11.w32 (by decide) (by decide)).trans w10_98
  have w11_9c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K11.w32 (by decide) (by decide)).trans w10_9c
  have w11_a0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K11.w32 (by decide) (by decide)).trans w10_a0
  have w11_a4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K11.w32 (by decide) (by decide)).trans w10_a4
  have w11_a8 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K11.w32 (by decide) (by decide)).trans w10_a8
  have w11_ac : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K11.w32 (by decide) (by decide)).trans w10_ac
  have w11_b0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K11.w32 (by decide) (by decide)).trans w10_b0
  have w11_b4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K11.w32 (by decide) (by decide)).trans w10_b4
  have w11_b8 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K11.w32 (by decide) (by decide)).trans w10_b8
  have w11_bc : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K11.w32 (by decide) (by decide)).trans w10_bc
  have w11_c0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K11.w32 (by decide) (by decide)).trans w10_c0
  have w11_c4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K11.w32 (by decide) (by decide)).trans w10_c4
  have w11_c8 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K11.w32 (by decide) (by decide)).trans w10_c8
  have w11_cc : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K11.w32 (by decide) (by decide)).trans w10_cc
  have w11_d0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K11.w32 (by decide) (by decide)).trans w10_d0
  have w11_d4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K11.w32 (by decide) (by decide)).trans w10_d4
  have w11_d8 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K11.w32 (by decide) (by decide)).trans w10_d8
  have w11_dc : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K11.w32 (by decide) (by decide)).trans w10_dc
  have w11_e0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K11.w32 (by decide) (by decide)).trans w10_e0
  have w11_e4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K11.w32 (by decide) (by decide)).trans w10_e4
  have w11_e8 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K11.w32 (by decide) (by decide)).trans w10_e8
  have w11_ec : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K11.w32 (by decide) (by decide)).trans w10_ec
  have w11_f0 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K11.w32 (by decide) (by decide)).trans w10_f0
  have w11_f4 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K11.w32 (by decide) (by decide)).trans w10_f4
  have w11_f8 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K11.w32 (by decide) (by decide)).trans w10_f8
  have w11_fc : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K11.w32 (by decide) (by decide)).trans w10_fc
  have w11_100 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K11.w32 (by decide) (by decide)).trans w10_100
  have w11_104 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K11.w32 (by decide) (by decide)).trans w10_104
  have w11_108 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K11.w32 (by decide) (by decide)).trans w10_108
  have w11_10c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K11.w32 (by decide) (by decide)).trans w10_10c
  have w11_110 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K11.w32 (by decide) (by decide)).trans w10_110
  have w11_114 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K11.w32 (by decide) (by decide)).trans w10_114
  have w11_118 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K11.w32 (by decide) (by decide)).trans w10_118
  have w11_11c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K11.w32 (by decide) (by decide)).trans w10_11c
  have w11_120 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K11.w32 (by decide) (by decide)).trans w10_120
  have w11_124 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K11.w32 (by decide) (by decide)).trans w10_124
  have w11_128 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K11.w32 (by decide) (by decide)).trans w10_128
  have w11_12c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K11.w32 (by decide) (by decide)).trans w10_12c
  have w11_130 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K11.w32 (by decide) (by decide)).trans w10_130
  have w11_460 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := (K11.w32 (by decide) (by decide)).trans w10_460
  have w11_464 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := (K11.w32 (by decide) (by decide)).trans w10_464
  have q11_420 : ∀ j, j < 32 → n11.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) := fun j hj => (K11.range (by decide) (by decide) j hj).trans (q10_420 j hj)
  have q11_440 : ∀ j, j < 32 → n11.mem (B + 0x21A0 + BitVec.ofNat 32 (0x440 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B78) + BitVec.ofNat 32 j) := fun j hj => (K11.range (by decide) (by decide) j hj).trans (q10_440 j hj)
  have a11_2a0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K11.acc (by decide) (by decide)).trans a10_2a0
  have a11_2c0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K11.acc (by decide) (by decide)).trans a10_2c0
  have a11_2e0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K11.acc (by decide) (by decide)).trans a10_2e0
  have a11_420 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := (K11.acc (by decide) (by decide)).trans a10_420
  have a11_440 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := (K11.acc (by decide) (by decide)).trans a10_440
  have a11_1480 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = X := (K11.acc (by decide) (by decide)).trans a10_1480
  have a11_14a0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) 8 = Y := (K11.acc (by decide) (by decide)).trans a10_14a0
  have a11_14c0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x14C0) 8 = Z := (K11.acc (by decide) (by decide)).trans a10_14c0
  have a11_15a8 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := (K11.acc (by decide) (by decide)).trans a10_15a8
  have a11_15c8 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := (K11.acc (by decide) (by decide)).trans a10_15c8
  have a11_15e8 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x15E8) 8 = Z := (K11.acc (by decide) (by decide)).trans a10_15e8
  clear a10_15e8 a10_15c8 a10_15a8 a10_14c0 a10_14a0 a10_1480 a10_440 a10_420 a10_2e0 a10_2c0 a10_2a0 q10_440 q10_420 w10_464 w10_460 w10_130 w10_12c w10_128 w10_124 w10_120 w10_11c w10_118 w10_114 w10_110 w10_10c w10_108 w10_104 w10_100 w10_fc w10_f8 w10_f4 w10_f0 w10_ec w10_e8 w10_e4 w10_e0 w10_dc w10_d8 w10_d4 w10_d0 w10_cc w10_c8 w10_c4 w10_c0 w10_bc w10_b8 w10_b4 w10_b0 w10_ac w10_a8 w10_a4 w10_a0 w10_9c w10_98 w10_94 w10_90 w10_8c w10_88 w10_84 w10_80 w10_7c w10_70 w10_6c w10_68 w10_64 w10_60 w10_5c w10_58 w10_54 w10_50 w10_4c w10_48 w10_44 w10_40 w10_3c w10_38 w10_34 w10_30 w10_2c w10_28 w10_24 g10_10 g10_27 g10_26 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 rb10 s10 m10 u10 c10
  have g11_10 : reg n11 a0 = (if Z = 0 then 0 else 1 : Word) := a0_11
  -- 0x1ADC
  obtain ⟨n12, c12, u12⟩ := s11.block svZS1adc E11.self svZS1adc_end
    ⟨trivial, trivial⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have s12 : St n12.mem SV n12 0x1AE0 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have rb12 : ∀ q, reg n12 q = (runBlock svZS1adc (n11.mem, reg n11)).2 q := fun q => by rw [u12.regs]
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
  have g12_8 : reg n12 (8 : Fin 32) = BitVec.ofNat 32 0x3FCC4B78 := by
    rw [rb12, runBlock_reg _ _ _ (8 : Fin 32) s11.zero (by decide), g11_8]
  have g12_18 : reg n12 (18 : Fin 32) = out := by
    rw [rb12, runBlock_reg _ _ _ (18 : Fin 32) s11.zero (by decide), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by
    rw [rb12, runBlock_reg _ _ _ (19 : Fin 32) s11.zero (by decide), g11_19]
  have g12_20 : reg n12 (20 : Fin 32) = BitVec.ofNat 32 0x60 := by
    rw [rb12, runBlock_reg _ _ _ (20 : Fin 32) s11.zero (by decide), g11_20]
  have g12_21 : reg n12 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by
    rw [rb12, runBlock_reg _ _ _ (21 : Fin 32) s11.zero (by decide), g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x15E8 := by
    rw [rb12, runBlock_reg _ _ _ (22 : Fin 32) s11.zero (by decide), g11_22]
  have g12_23 : reg n12 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC4B38 := by
    rw [rb12, runBlock_reg _ _ _ (23 : Fin 32) s11.zero (by decide), g11_23]
  have g12_24 : reg n12 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA60 := by
    rw [rb12, runBlock_reg _ _ _ (24 : Fin 32) s11.zero (by decide), g11_24]
  have g12_26 : reg n12 (26 : Fin 32) = x26 := by
    rw [rb12, runBlock_reg _ _ _ (26 : Fin 32) s11.zero (by decide), g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb12, runBlock_reg _ _ _ (27 : Fin 32) s11.zero (by decide), g11_27]
  have g12_10 : reg n12 a0 = ((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, svZS1adc, upd, ↓reduceIte]; rw [g11_10] <;> rfl
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
  have w12_460 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m12]; exact w11_460
  have w12_464 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m12]; exact w11_464
  have q12_420 : ∀ j, j < 32 → n12.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) := fun j hj => by rw [m12]; exact q11_420 j hj
  have q12_440 : ∀ j, j < 32 → n12.mem (B + 0x21A0 + BitVec.ofNat 32 (0x440 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B78) + BitVec.ofNat 32 j) := fun j hj => by rw [m12]; exact q11_440 j hj
  have a12_2a0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m12]; exact a11_2a0
  have a12_2c0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m12]; exact a11_2c0
  have a12_2e0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m12]; exact a11_2e0
  have a12_420 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := by rw [m12]; exact a11_420
  have a12_440 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := by rw [m12]; exact a11_440
  have a12_1480 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = X := by rw [m12]; exact a11_1480
  have a12_14a0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) 8 = Y := by rw [m12]; exact a11_14a0
  have a12_14c0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x14C0) 8 = Z := by rw [m12]; exact a11_14c0
  have a12_15a8 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := by rw [m12]; exact a11_15a8
  have a12_15c8 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := by rw [m12]; exact a11_15c8
  have a12_15e8 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x15E8) 8 = Z := by rw [m12]; exact a11_15e8
  clear a11_15e8 a11_15c8 a11_15a8 a11_14c0 a11_14a0 a11_1480 a11_440 a11_420 a11_2e0 a11_2c0 a11_2a0 q11_440 q11_420 w11_464 w11_460 w11_130 w11_12c w11_128 w11_124 w11_120 w11_11c w11_118 w11_114 w11_110 w11_10c w11_108 w11_104 w11_100 w11_fc w11_f8 w11_f4 w11_f0 w11_ec w11_e8 w11_e4 w11_e0 w11_dc w11_d8 w11_d4 w11_d0 w11_cc w11_c8 w11_c4 w11_c0 w11_bc w11_b8 w11_b4 w11_b0 w11_ac w11_a8 w11_a4 w11_a0 w11_9c w11_98 w11_94 w11_90 w11_8c w11_88 w11_84 w11_80 w11_7c w11_70 w11_6c w11_68 w11_64 w11_60 w11_5c w11_58 w11_54 w11_50 w11_4c w11_48 w11_44 w11_40 w11_3c w11_38 w11_34 w11_30 w11_2c w11_28 w11_24 g11_2 g11_27 g11_26 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_8 g11_4 g11_3 V11 E11 fR11 t11 fr11 K11 a0_11 rk11 sp11 s11 c11
  -- 0x1AE0: sw
  obtain ⟨n13, d13, s13, fr13, K13, W13, rg13⟩ := sv_sw F E12 s12 sv_at_1ae0 (off' := 0x1AE2) (c := 0x20)
    (by decide) (by rw [g12_2]; sv_addr) (by decide) (by decide)
  have t13 : Steps n0 n13 := t12.trans d13
  have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : SvCode n13.mem := E12.fr F fr13
  have V13 : SvSaves B n13.mem v := V12.keep K13 (by decide)
  have g13_2 : reg n13 sp = B + 0x21A0 := by rw [rg13 sp, g12_2]
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg13 (3 : Fin 32), g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg13 (4 : Fin 32), g12_4]
  have g13_8 : reg n13 (8 : Fin 32) = BitVec.ofNat 32 0x3FCC4B78 := by rw [rg13 (8 : Fin 32), g12_8]
  have g13_10 : reg n13 a0 = ((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF := by rw [rg13 a0, g12_10]
  have g13_18 : reg n13 (18 : Fin 32) = out := by rw [rg13 (18 : Fin 32), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [rg13 (19 : Fin 32), g12_19]
  have g13_20 : reg n13 (20 : Fin 32) = BitVec.ofNat 32 0x60 := by rw [rg13 (20 : Fin 32), g12_20]
  have g13_21 : reg n13 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [rg13 (21 : Fin 32), g12_21]
  have g13_22 : reg n13 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x15E8 := by rw [rg13 (22 : Fin 32), g12_22]
  have g13_23 : reg n13 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC4B38 := by rw [rg13 (23 : Fin 32), g12_23]
  have g13_24 : reg n13 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA60 := by rw [rg13 (24 : Fin 32), g12_24]
  have g13_26 : reg n13 (26 : Fin 32) = x26 := by rw [rg13 (26 : Fin 32), g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg13 (27 : Fin 32), g12_27]
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
  have w13_5c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K13.w32 (by decide) (by decide)).trans w12_5c
  have w13_60 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K13.w32 (by decide) (by decide)).trans w12_60
  have w13_64 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K13.w32 (by decide) (by decide)).trans w12_64
  have w13_68 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K13.w32 (by decide) (by decide)).trans w12_68
  have w13_6c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K13.w32 (by decide) (by decide)).trans w12_6c
  have w13_70 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K13.w32 (by decide) (by decide)).trans w12_70
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
  have w13_460 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := (K13.w32 (by decide) (by decide)).trans w12_460
  have w13_464 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := (K13.w32 (by decide) (by decide)).trans w12_464
  have w13_20 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = ((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF := by rw [W13, g12_10]
  have q13_420 : ∀ j, j < 32 → n13.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) := fun j hj => (K13.range (by decide) (by decide) j hj).trans (q12_420 j hj)
  have q13_440 : ∀ j, j < 32 → n13.mem (B + 0x21A0 + BitVec.ofNat 32 (0x440 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B78) + BitVec.ofNat 32 j) := fun j hj => (K13.range (by decide) (by decide) j hj).trans (q12_440 j hj)
  have a13_2a0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K13.acc (by decide) (by decide)).trans a12_2a0
  have a13_2c0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K13.acc (by decide) (by decide)).trans a12_2c0
  have a13_2e0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K13.acc (by decide) (by decide)).trans a12_2e0
  have a13_420 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := (K13.acc (by decide) (by decide)).trans a12_420
  have a13_440 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := (K13.acc (by decide) (by decide)).trans a12_440
  have a13_1480 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = X := (K13.acc (by decide) (by decide)).trans a12_1480
  have a13_14a0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) 8 = Y := (K13.acc (by decide) (by decide)).trans a12_14a0
  have a13_14c0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x14C0) 8 = Z := (K13.acc (by decide) (by decide)).trans a12_14c0
  have a13_15a8 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := (K13.acc (by decide) (by decide)).trans a12_15a8
  have a13_15c8 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := (K13.acc (by decide) (by decide)).trans a12_15c8
  have a13_15e8 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x15E8) 8 = Z := (K13.acc (by decide) (by decide)).trans a12_15e8
  clear a12_15e8 a12_15c8 a12_15a8 a12_14c0 a12_14a0 a12_1480 a12_440 a12_420 a12_2e0 a12_2c0 a12_2a0 q12_440 q12_420 w12_464 w12_460 w12_130 w12_12c w12_128 w12_124 w12_120 w12_11c w12_118 w12_114 w12_110 w12_10c w12_108 w12_104 w12_100 w12_fc w12_f8 w12_f4 w12_f0 w12_ec w12_e8 w12_e4 w12_e0 w12_dc w12_d8 w12_d4 w12_d0 w12_cc w12_c8 w12_c4 w12_c0 w12_bc w12_b8 w12_b4 w12_b0 w12_ac w12_a8 w12_a4 w12_a0 w12_9c w12_98 w12_94 w12_90 w12_8c w12_88 w12_84 w12_80 w12_7c w12_70 w12_6c w12_68 w12_64 w12_60 w12_5c w12_58 w12_54 w12_50 w12_4c w12_48 w12_44 w12_40 w12_3c w12_38 w12_34 w12_30 w12_2c w12_28 w12_24 g12_10 g12_27 g12_26 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 rb12 s12 m12 u12 c12 g11_10
  -- 0x1AE2
  obtain ⟨n14, c14, u14⟩ := s13.block svZS1ae2 E13.self svZS1ae2_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m14 : n14.mem = n13.mem := u14.mem
  have s14 : St n14.mem SV n14 0x1AEA (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
  have rb14 : ∀ q, reg n14 q = (runBlock svZS1ae2 (n13.mem, reg n13)).2 q := fun q => by rw [u14.regs]
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
  have g14_8 : reg n14 (8 : Fin 32) = BitVec.ofNat 32 0x3FCC4B78 := by
    rw [rb14, runBlock_reg _ _ _ (8 : Fin 32) s13.zero (by decide), g13_8]
  have g14_18 : reg n14 (18 : Fin 32) = out := by
    rw [rb14, runBlock_reg _ _ _ (18 : Fin 32) s13.zero (by decide), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = bp := by
    rw [rb14, runBlock_reg _ _ _ (19 : Fin 32) s13.zero (by decide), g13_19]
  have g14_20 : reg n14 (20 : Fin 32) = BitVec.ofNat 32 0x60 := by
    rw [rb14, runBlock_reg _ _ _ (20 : Fin 32) s13.zero (by decide), g13_20]
  have g14_21 : reg n14 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by
    rw [rb14, runBlock_reg _ _ _ (21 : Fin 32) s13.zero (by decide), g13_21]
  have g14_22 : reg n14 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x15E8 := by
    rw [rb14, runBlock_reg _ _ _ (22 : Fin 32) s13.zero (by decide), g13_22]
  have g14_23 : reg n14 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC4B38 := by
    rw [rb14, runBlock_reg _ _ _ (23 : Fin 32) s13.zero (by decide), g13_23]
  have g14_24 : reg n14 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA60 := by
    rw [rb14, runBlock_reg _ _ _ (24 : Fin 32) s13.zero (by decide), g13_24]
  have g14_26 : reg n14 (26 : Fin 32) = x26 := by
    rw [rb14, runBlock_reg _ _ _ (26 : Fin 32) s13.zero (by decide), g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb14, runBlock_reg _ _ _ (27 : Fin 32) s13.zero (by decide), g13_27]
  have g14_10 : reg n14 a0 = B + 0x21A0 + BitVec.ofNat 32 0x320 := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, svZS1ae2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_8, g13_10, g13_18, g13_19, g13_20, g13_21, g13_22, g13_23, g13_24, g13_26, g13_27, s13.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g14_11 : reg n14 a1 = BitVec.ofNat 32 0x3FCC4B38 := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, svZS1ae2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_8, g13_10, g13_18, g13_19, g13_20, g13_21, g13_22, g13_23, g13_24, g13_26, g13_27, s13.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g14_12 : reg n14 a2 = BitVec.ofNat 32 0x20 := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, svZS1ae2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_8, g13_10, g13_18, g13_19, g13_20, g13_21, g13_22, g13_23, g13_24, g13_26, g13_27, s13.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w14_20 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = ((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF := by rw [m14]; exact w13_20
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
  have w14_5c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m14]; exact w13_5c
  have w14_60 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m14]; exact w13_60
  have w14_64 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m14]; exact w13_64
  have w14_68 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m14]; exact w13_68
  have w14_6c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m14]; exact w13_6c
  have w14_70 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m14]; exact w13_70
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
  have w14_460 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m14]; exact w13_460
  have w14_464 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m14]; exact w13_464
  have q14_420 : ∀ j, j < 32 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) := fun j hj => by rw [m14]; exact q13_420 j hj
  have q14_440 : ∀ j, j < 32 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0x440 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B78) + BitVec.ofNat 32 j) := fun j hj => by rw [m14]; exact q13_440 j hj
  have a14_2a0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m14]; exact a13_2a0
  have a14_2c0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m14]; exact a13_2c0
  have a14_2e0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m14]; exact a13_2e0
  have a14_420 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := by rw [m14]; exact a13_420
  have a14_440 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := by rw [m14]; exact a13_440
  have a14_1480 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = X := by rw [m14]; exact a13_1480
  have a14_14a0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) 8 = Y := by rw [m14]; exact a13_14a0
  have a14_14c0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x14C0) 8 = Z := by rw [m14]; exact a13_14c0
  have a14_15a8 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := by rw [m14]; exact a13_15a8
  have a14_15c8 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := by rw [m14]; exact a13_15c8
  have a14_15e8 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x15E8) 8 = Z := by rw [m14]; exact a13_15e8
  clear a13_15e8 a13_15c8 a13_15a8 a13_14c0 a13_14a0 a13_1480 a13_440 a13_420 a13_2e0 a13_2c0 a13_2a0 q13_440 q13_420 w13_20 w13_464 w13_460 w13_130 w13_12c w13_128 w13_124 w13_120 w13_11c w13_118 w13_114 w13_110 w13_10c w13_108 w13_104 w13_100 w13_fc w13_f8 w13_f4 w13_f0 w13_ec w13_e8 w13_e4 w13_e0 w13_dc w13_d8 w13_d4 w13_d0 w13_cc w13_c8 w13_c4 w13_c0 w13_bc w13_b8 w13_b4 w13_b0 w13_ac w13_a8 w13_a4 w13_a0 w13_9c w13_98 w13_94 w13_90 w13_8c w13_88 w13_84 w13_80 w13_7c w13_70 w13_6c w13_68 w13_64 w13_60 w13_5c w13_58 w13_54 w13_50 w13_4c w13_48 w13_44 w13_40 w13_3c w13_38 w13_34 w13_30 w13_2c w13_28 w13_24 g13_27 g13_26 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_10 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 rg13 W13 K13 fr13 s13 d13
  -- 0x1AEA: memcpy from outside the stack
  obtain ⟨n15, P15, K15, X15⟩ := sv_mcRo2 (c := 0x320) (N := 0x20) F RS E14 s14 sv_at_1aea sv_at_1aee
    (by decide) (by decide) g14_2 g14_10 g14_11 g14_12 (by decide) (Or.inr ⟨by decide, by decide⟩)
  have s15 := P15.st
  have fr15 := P15.fr
  have t15 : Steps n0 n15 := t14.trans P15.steps
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.keep K15 (by decide)
  have g15_2 : reg n15 sp = B + 0x21A0 := by rw [P15.regs sp (by decide), g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P15.regs (3 : Fin 32) (by decide), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P15.regs (4 : Fin 32) (by decide), g14_4]
  have g15_8 : reg n15 (8 : Fin 32) = BitVec.ofNat 32 0x3FCC4B78 := by rw [P15.regs (8 : Fin 32) (by decide), g14_8]
  have g15_18 : reg n15 (18 : Fin 32) = out := by rw [P15.regs (18 : Fin 32) (by decide), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [P15.regs (19 : Fin 32) (by decide), g14_19]
  have g15_20 : reg n15 (20 : Fin 32) = BitVec.ofNat 32 0x60 := by rw [P15.regs (20 : Fin 32) (by decide), g14_20]
  have g15_21 : reg n15 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [P15.regs (21 : Fin 32) (by decide), g14_21]
  have g15_22 : reg n15 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x15E8 := by rw [P15.regs (22 : Fin 32) (by decide), g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC4B38 := by rw [P15.regs (23 : Fin 32) (by decide), g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA60 := by rw [P15.regs (24 : Fin 32) (by decide), g14_24]
  have g15_26 : reg n15 (26 : Fin 32) = x26 := by rw [P15.regs (26 : Fin 32) (by decide), g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P15.regs (27 : Fin 32) (by decide), g14_27]
  have w15_20 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = ((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF := (K15.w32 (by decide) (by decide)).trans w14_20
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
  have w15_5c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K15.w32 (by decide) (by decide)).trans w14_5c
  have w15_60 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K15.w32 (by decide) (by decide)).trans w14_60
  have w15_64 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K15.w32 (by decide) (by decide)).trans w14_64
  have w15_68 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K15.w32 (by decide) (by decide)).trans w14_68
  have w15_6c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K15.w32 (by decide) (by decide)).trans w14_6c
  have w15_70 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K15.w32 (by decide) (by decide)).trans w14_70
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
  have w15_460 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := (K15.w32 (by decide) (by decide)).trans w14_460
  have w15_464 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := (K15.w32 (by decide) (by decide)).trans w14_464
  have q15_420 : ∀ j, j < 32 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) := fun j hj => (K15.range (by decide) (by decide) j hj).trans (q14_420 j hj)
  have q15_440 : ∀ j, j < 32 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0x440 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B78) + BitVec.ofNat 32 j) := fun j hj => (K15.range (by decide) (by decide) j hj).trans (q14_440 j hj)
  have a15_2a0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K15.acc (by decide) (by decide)).trans a14_2a0
  have a15_2c0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K15.acc (by decide) (by decide)).trans a14_2c0
  have a15_2e0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K15.acc (by decide) (by decide)).trans a14_2e0
  have a15_420 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := (K15.acc (by decide) (by decide)).trans a14_420
  have a15_440 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := (K15.acc (by decide) (by decide)).trans a14_440
  have a15_1480 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = X := (K15.acc (by decide) (by decide)).trans a14_1480
  have a15_14a0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) 8 = Y := (K15.acc (by decide) (by decide)).trans a14_14a0
  have a15_14c0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x14C0) 8 = Z := (K15.acc (by decide) (by decide)).trans a14_14c0
  have a15_15a8 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := (K15.acc (by decide) (by decide)).trans a14_15a8
  have a15_15c8 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := (K15.acc (by decide) (by decide)).trans a14_15c8
  have a15_15e8 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x15E8) 8 = Z := (K15.acc (by decide) (by decide)).trans a14_15e8
  have q15_320 : ∀ j, j < 32 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) :=
    fun j hj => (X15 j hj).trans (fR14 _ (SvRo2.r RS (Or.inr ⟨by decide, by decide⟩) hj))
  have a15_320 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := acc_of_frame q15_320
  clear a14_15e8 a14_15c8 a14_15a8 a14_14c0 a14_14a0 a14_1480 a14_440 a14_420 a14_2e0 a14_2c0 a14_2a0 q14_440 q14_420 w14_464 w14_460 w14_130 w14_12c w14_128 w14_124 w14_120 w14_11c w14_118 w14_114 w14_110 w14_10c w14_108 w14_104 w14_100 w14_fc w14_f8 w14_f4 w14_f0 w14_ec w14_e8 w14_e4 w14_e0 w14_dc w14_d8 w14_d4 w14_d0 w14_cc w14_c8 w14_c4 w14_c0 w14_bc w14_b8 w14_b4 w14_b0 w14_ac w14_a8 w14_a4 w14_a0 w14_9c w14_98 w14_94 w14_90 w14_8c w14_88 w14_84 w14_80 w14_7c w14_70 w14_6c w14_68 w14_64 w14_60 w14_5c w14_58 w14_54 w14_50 w14_4c w14_48 w14_44 w14_40 w14_3c w14_38 w14_34 w14_30 w14_2c w14_28 w14_24 w14_20 g14_12 g14_11 g14_10 g14_27 g14_26 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 rb14 s14 m14 u14 c14
  -- 0x1AF2: sb
  obtain ⟨n16, d16, s16, fr16, K16, W16, rg16⟩ := sv_sb F E15 s15 sv_at_1af2 (off' := 0x1AF6) (c := 0x340)
    (by decide) (by rw [g15_2]; sv_addr) (by decide)
  have t16 : Steps n0 n16 := t15.trans d16
  have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : SvCode n16.mem := E15.fr F fr16
  have V16 : SvSaves B n16.mem v := V15.keep K16 (by decide)
  have g16_2 : reg n16 sp = B + 0x21A0 := by rw [rg16 sp, g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg16 (3 : Fin 32), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg16 (4 : Fin 32), g15_4]
  have g16_8 : reg n16 (8 : Fin 32) = BitVec.ofNat 32 0x3FCC4B78 := by rw [rg16 (8 : Fin 32), g15_8]
  have g16_18 : reg n16 (18 : Fin 32) = out := by rw [rg16 (18 : Fin 32), g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [rg16 (19 : Fin 32), g15_19]
  have g16_20 : reg n16 (20 : Fin 32) = BitVec.ofNat 32 0x60 := by rw [rg16 (20 : Fin 32), g15_20]
  have g16_21 : reg n16 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [rg16 (21 : Fin 32), g15_21]
  have g16_22 : reg n16 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x15E8 := by rw [rg16 (22 : Fin 32), g15_22]
  have g16_23 : reg n16 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC4B38 := by rw [rg16 (23 : Fin 32), g15_23]
  have g16_24 : reg n16 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA60 := by rw [rg16 (24 : Fin 32), g15_24]
  have g16_26 : reg n16 (26 : Fin 32) = x26 := by rw [rg16 (26 : Fin 32), g15_26]
  have g16_27 : reg n16 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg16 (27 : Fin 32), g15_27]
  have w16_20 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = ((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF := (K16.w32 (by decide) (by decide)).trans w15_20
  have w16_24 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K16.w32 (by decide) (by decide)).trans w15_24
  have w16_28 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K16.w32 (by decide) (by decide)).trans w15_28
  have w16_2c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K16.w32 (by decide) (by decide)).trans w15_2c
  have w16_30 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K16.w32 (by decide) (by decide)).trans w15_30
  have w16_34 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K16.w32 (by decide) (by decide)).trans w15_34
  have w16_38 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K16.w32 (by decide) (by decide)).trans w15_38
  have w16_3c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K16.w32 (by decide) (by decide)).trans w15_3c
  have w16_40 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K16.w32 (by decide) (by decide)).trans w15_40
  have w16_44 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K16.w32 (by decide) (by decide)).trans w15_44
  have w16_48 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K16.w32 (by decide) (by decide)).trans w15_48
  have w16_4c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K16.w32 (by decide) (by decide)).trans w15_4c
  have w16_50 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K16.w32 (by decide) (by decide)).trans w15_50
  have w16_54 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K16.w32 (by decide) (by decide)).trans w15_54
  have w16_58 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K16.w32 (by decide) (by decide)).trans w15_58
  have w16_5c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K16.w32 (by decide) (by decide)).trans w15_5c
  have w16_60 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K16.w32 (by decide) (by decide)).trans w15_60
  have w16_64 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K16.w32 (by decide) (by decide)).trans w15_64
  have w16_68 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K16.w32 (by decide) (by decide)).trans w15_68
  have w16_6c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K16.w32 (by decide) (by decide)).trans w15_6c
  have w16_70 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K16.w32 (by decide) (by decide)).trans w15_70
  have w16_7c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K16.w32 (by decide) (by decide)).trans w15_7c
  have w16_80 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K16.w32 (by decide) (by decide)).trans w15_80
  have w16_84 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K16.w32 (by decide) (by decide)).trans w15_84
  have w16_88 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K16.w32 (by decide) (by decide)).trans w15_88
  have w16_8c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K16.w32 (by decide) (by decide)).trans w15_8c
  have w16_90 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K16.w32 (by decide) (by decide)).trans w15_90
  have w16_94 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K16.w32 (by decide) (by decide)).trans w15_94
  have w16_98 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K16.w32 (by decide) (by decide)).trans w15_98
  have w16_9c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K16.w32 (by decide) (by decide)).trans w15_9c
  have w16_a0 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K16.w32 (by decide) (by decide)).trans w15_a0
  have w16_a4 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K16.w32 (by decide) (by decide)).trans w15_a4
  have w16_a8 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K16.w32 (by decide) (by decide)).trans w15_a8
  have w16_ac : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K16.w32 (by decide) (by decide)).trans w15_ac
  have w16_b0 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K16.w32 (by decide) (by decide)).trans w15_b0
  have w16_b4 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K16.w32 (by decide) (by decide)).trans w15_b4
  have w16_b8 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K16.w32 (by decide) (by decide)).trans w15_b8
  have w16_bc : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K16.w32 (by decide) (by decide)).trans w15_bc
  have w16_c0 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K16.w32 (by decide) (by decide)).trans w15_c0
  have w16_c4 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K16.w32 (by decide) (by decide)).trans w15_c4
  have w16_c8 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K16.w32 (by decide) (by decide)).trans w15_c8
  have w16_cc : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K16.w32 (by decide) (by decide)).trans w15_cc
  have w16_d0 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K16.w32 (by decide) (by decide)).trans w15_d0
  have w16_d4 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K16.w32 (by decide) (by decide)).trans w15_d4
  have w16_d8 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K16.w32 (by decide) (by decide)).trans w15_d8
  have w16_dc : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K16.w32 (by decide) (by decide)).trans w15_dc
  have w16_e0 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K16.w32 (by decide) (by decide)).trans w15_e0
  have w16_e4 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K16.w32 (by decide) (by decide)).trans w15_e4
  have w16_e8 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K16.w32 (by decide) (by decide)).trans w15_e8
  have w16_ec : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K16.w32 (by decide) (by decide)).trans w15_ec
  have w16_f0 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K16.w32 (by decide) (by decide)).trans w15_f0
  have w16_f4 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K16.w32 (by decide) (by decide)).trans w15_f4
  have w16_f8 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K16.w32 (by decide) (by decide)).trans w15_f8
  have w16_fc : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K16.w32 (by decide) (by decide)).trans w15_fc
  have w16_100 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K16.w32 (by decide) (by decide)).trans w15_100
  have w16_104 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K16.w32 (by decide) (by decide)).trans w15_104
  have w16_108 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K16.w32 (by decide) (by decide)).trans w15_108
  have w16_10c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K16.w32 (by decide) (by decide)).trans w15_10c
  have w16_110 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K16.w32 (by decide) (by decide)).trans w15_110
  have w16_114 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K16.w32 (by decide) (by decide)).trans w15_114
  have w16_118 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K16.w32 (by decide) (by decide)).trans w15_118
  have w16_11c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K16.w32 (by decide) (by decide)).trans w15_11c
  have w16_120 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K16.w32 (by decide) (by decide)).trans w15_120
  have w16_124 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K16.w32 (by decide) (by decide)).trans w15_124
  have w16_128 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K16.w32 (by decide) (by decide)).trans w15_128
  have w16_12c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K16.w32 (by decide) (by decide)).trans w15_12c
  have w16_130 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K16.w32 (by decide) (by decide)).trans w15_130
  have w16_460 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := (K16.w32 (by decide) (by decide)).trans w15_460
  have w16_464 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := (K16.w32 (by decide) (by decide)).trans w15_464
  have b16_340 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [W16, s15.zero]; rfl
  have q16_320 : ∀ j, j < 32 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) := fun j hj => (K16.range (by decide) (by decide) j hj).trans (q15_320 j hj)
  have q16_420 : ∀ j, j < 32 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) := fun j hj => (K16.range (by decide) (by decide) j hj).trans (q15_420 j hj)
  have q16_440 : ∀ j, j < 32 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0x440 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B78) + BitVec.ofNat 32 j) := fun j hj => (K16.range (by decide) (by decide) j hj).trans (q15_440 j hj)
  have a16_2a0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K16.acc (by decide) (by decide)).trans a15_2a0
  have a16_2c0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K16.acc (by decide) (by decide)).trans a15_2c0
  have a16_2e0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K16.acc (by decide) (by decide)).trans a15_2e0
  have a16_320 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := (K16.acc (by decide) (by decide)).trans a15_320
  have a16_420 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := (K16.acc (by decide) (by decide)).trans a15_420
  have a16_440 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := (K16.acc (by decide) (by decide)).trans a15_440
  have a16_1480 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = X := (K16.acc (by decide) (by decide)).trans a15_1480
  have a16_14a0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) 8 = Y := (K16.acc (by decide) (by decide)).trans a15_14a0
  have a16_14c0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x14C0) 8 = Z := (K16.acc (by decide) (by decide)).trans a15_14c0
  have a16_15a8 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := (K16.acc (by decide) (by decide)).trans a15_15a8
  have a16_15c8 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := (K16.acc (by decide) (by decide)).trans a15_15c8
  have a16_15e8 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x15E8) 8 = Z := (K16.acc (by decide) (by decide)).trans a15_15e8
  clear a15_320 q15_320 a15_15e8 a15_15c8 a15_15a8 a15_14c0 a15_14a0 a15_1480 a15_440 a15_420 a15_2e0 a15_2c0 a15_2a0 q15_440 q15_420 w15_464 w15_460 w15_130 w15_12c w15_128 w15_124 w15_120 w15_11c w15_118 w15_114 w15_110 w15_10c w15_108 w15_104 w15_100 w15_fc w15_f8 w15_f4 w15_f0 w15_ec w15_e8 w15_e4 w15_e0 w15_dc w15_d8 w15_d4 w15_d0 w15_cc w15_c8 w15_c4 w15_c0 w15_bc w15_b8 w15_b4 w15_b0 w15_ac w15_a8 w15_a4 w15_a0 w15_9c w15_98 w15_94 w15_90 w15_8c w15_88 w15_84 w15_80 w15_7c w15_70 w15_6c w15_68 w15_64 w15_60 w15_5c w15_58 w15_54 w15_50 w15_4c w15_48 w15_44 w15_40 w15_3c w15_38 w15_34 w15_30 w15_2c w15_28 w15_24 w15_20 g15_27 g15_26 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_8 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 s15 X15 K15 P15
  -- 0x1AF6
  obtain ⟨n17, c17, u17⟩ := s16.block svZS1af6 E16.self svZS1af6_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m17 : n17.mem = n16.mem := u17.mem
  have s17 : St n17.mem SV n17 0x1B04 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
  have rb17 : ∀ q, reg n17 q = (runBlock svZS1af6 (n16.mem, reg n16)).2 q := fun q => by rw [u17.regs]
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
  have g17_8 : reg n17 (8 : Fin 32) = BitVec.ofNat 32 0x3FCC4B78 := by
    rw [rb17, runBlock_reg _ _ _ (8 : Fin 32) s16.zero (by decide), g16_8]
  have g17_18 : reg n17 (18 : Fin 32) = out := by
    rw [rb17, runBlock_reg _ _ _ (18 : Fin 32) s16.zero (by decide), g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = bp := by
    rw [rb17, runBlock_reg _ _ _ (19 : Fin 32) s16.zero (by decide), g16_19]
  have g17_20 : reg n17 (20 : Fin 32) = BitVec.ofNat 32 0x60 := by
    rw [rb17, runBlock_reg _ _ _ (20 : Fin 32) s16.zero (by decide), g16_20]
  have g17_21 : reg n17 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by
    rw [rb17, runBlock_reg _ _ _ (21 : Fin 32) s16.zero (by decide), g16_21]
  have g17_22 : reg n17 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x15E8 := by
    rw [rb17, runBlock_reg _ _ _ (22 : Fin 32) s16.zero (by decide), g16_22]
  have g17_23 : reg n17 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC4B38 := by
    rw [rb17, runBlock_reg _ _ _ (23 : Fin 32) s16.zero (by decide), g16_23]
  have g17_24 : reg n17 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA60 := by
    rw [rb17, runBlock_reg _ _ _ (24 : Fin 32) s16.zero (by decide), g16_24]
  have g17_26 : reg n17 (26 : Fin 32) = x26 := by
    rw [rb17, runBlock_reg _ _ _ (26 : Fin 32) s16.zero (by decide), g16_26]
  have g17_27 : reg n17 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb17, runBlock_reg _ _ _ (27 : Fin 32) s16.zero (by decide), g16_27]
  have g17_10 : reg n17 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1380 := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, svZS1af6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_8, g16_18, g16_19, g16_20, g16_21, g16_22, g16_23, g16_24, g16_26, g16_27, s16.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g17_11 : reg n17 a1 = B + 0x21A0 + BitVec.ofNat 32 0x15E8 := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, svZS1af6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_8, g16_18, g16_19, g16_20, g16_21, g16_22, g16_23, g16_24, g16_26, g16_27, s16.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g17_12 : reg n17 a2 = BitVec.ofNat 32 0x20 := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, svZS1af6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_8, g16_18, g16_19, g16_20, g16_21, g16_22, g16_23, g16_24, g16_26, g16_27, s16.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w17_20 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = ((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF := by rw [m17]; exact w16_20
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
  have w17_460 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m17]; exact w16_460
  have w17_464 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m17]; exact w16_464
  have b17_340 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m17]; exact b16_340
  have q17_320 : ∀ j, j < 32 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) := fun j hj => by rw [m17]; exact q16_320 j hj
  have q17_420 : ∀ j, j < 32 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) := fun j hj => by rw [m17]; exact q16_420 j hj
  have q17_440 : ∀ j, j < 32 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0x440 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B78) + BitVec.ofNat 32 j) := fun j hj => by rw [m17]; exact q16_440 j hj
  have a17_2a0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m17]; exact a16_2a0
  have a17_2c0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m17]; exact a16_2c0
  have a17_2e0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m17]; exact a16_2e0
  have a17_320 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := by rw [m17]; exact a16_320
  have a17_420 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := by rw [m17]; exact a16_420
  have a17_440 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := by rw [m17]; exact a16_440
  have a17_1480 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = X := by rw [m17]; exact a16_1480
  have a17_14a0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) 8 = Y := by rw [m17]; exact a16_14a0
  have a17_14c0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x14C0) 8 = Z := by rw [m17]; exact a16_14c0
  have a17_15a8 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := by rw [m17]; exact a16_15a8
  have a17_15c8 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := by rw [m17]; exact a16_15c8
  have a17_15e8 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x15E8) 8 = Z := by rw [m17]; exact a16_15e8
  clear a16_15e8 a16_15c8 a16_15a8 a16_14c0 a16_14a0 a16_1480 a16_440 a16_420 a16_320 a16_2e0 a16_2c0 a16_2a0 q16_440 q16_420 q16_320 b16_340 w16_464 w16_460 w16_130 w16_12c w16_128 w16_124 w16_120 w16_11c w16_118 w16_114 w16_110 w16_10c w16_108 w16_104 w16_100 w16_fc w16_f8 w16_f4 w16_f0 w16_ec w16_e8 w16_e4 w16_e0 w16_dc w16_d8 w16_d4 w16_d0 w16_cc w16_c8 w16_c4 w16_c0 w16_bc w16_b8 w16_b4 w16_b0 w16_ac w16_a8 w16_a4 w16_a0 w16_9c w16_98 w16_94 w16_90 w16_8c w16_88 w16_84 w16_80 w16_7c w16_70 w16_6c w16_68 w16_64 w16_60 w16_5c w16_58 w16_54 w16_50 w16_4c w16_48 w16_44 w16_40 w16_3c w16_38 w16_34 w16_30 w16_2c w16_28 w16_24 w16_20 g16_27 g16_26 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_8 g16_4 g16_3 g16_2 V16 E16 fR16 t16 rg16 W16 K16 fr16 s16 d16
  -- 0x1B04: memcpy
  obtain ⟨n18, P18, K18, X18⟩ := sv_mc (c := 0x1380) (d := 0x15E8) (N := 0x20) F E17 s17 sv_at_1b04 sv_at_1b08
    (by decide) (by decide) g17_2 g17_10 g17_11 g17_12
    (by decide) (by decide) (by decide)
  have s18 := P18.st
  have fr18 := P18.fr
  have t18 : Steps n0 n18 := t17.trans P18.steps
  have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : SvCode n18.mem := E17.fr F fr18
  have V18 : SvSaves B n18.mem v := V17.keep K18 (by decide)
  have g18_2 : reg n18 sp = B + 0x21A0 := by rw [P18.regs sp (by decide), g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P18.regs (3 : Fin 32) (by decide), g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P18.regs (4 : Fin 32) (by decide), g17_4]
  have g18_8 : reg n18 (8 : Fin 32) = BitVec.ofNat 32 0x3FCC4B78 := by rw [P18.regs (8 : Fin 32) (by decide), g17_8]
  have g18_18 : reg n18 (18 : Fin 32) = out := by rw [P18.regs (18 : Fin 32) (by decide), g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [P18.regs (19 : Fin 32) (by decide), g17_19]
  have g18_20 : reg n18 (20 : Fin 32) = BitVec.ofNat 32 0x60 := by rw [P18.regs (20 : Fin 32) (by decide), g17_20]
  have g18_21 : reg n18 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [P18.regs (21 : Fin 32) (by decide), g17_21]
  have g18_22 : reg n18 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x15E8 := by rw [P18.regs (22 : Fin 32) (by decide), g17_22]
  have g18_23 : reg n18 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC4B38 := by rw [P18.regs (23 : Fin 32) (by decide), g17_23]
  have g18_24 : reg n18 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA60 := by rw [P18.regs (24 : Fin 32) (by decide), g17_24]
  have g18_26 : reg n18 (26 : Fin 32) = x26 := by rw [P18.regs (26 : Fin 32) (by decide), g17_26]
  have g18_27 : reg n18 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P18.regs (27 : Fin 32) (by decide), g17_27]
  have w18_20 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = ((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF := (K18.w32 (by decide) (by decide)).trans w17_20
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
  have w18_460 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := (K18.w32 (by decide) (by decide)).trans w17_460
  have w18_464 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := (K18.w32 (by decide) (by decide)).trans w17_464
  have b18_340 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K18.b8 (by decide) (by decide)).trans b17_340
  have q18_320 : ∀ j, j < 32 → n18.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) := fun j hj => (K18.range (by decide) (by decide) j hj).trans (q17_320 j hj)
  have q18_420 : ∀ j, j < 32 → n18.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) := fun j hj => (K18.range (by decide) (by decide) j hj).trans (q17_420 j hj)
  have q18_440 : ∀ j, j < 32 → n18.mem (B + 0x21A0 + BitVec.ofNat 32 (0x440 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B78) + BitVec.ofNat 32 j) := fun j hj => (K18.range (by decide) (by decide) j hj).trans (q17_440 j hj)
  have a18_2a0 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K18.acc (by decide) (by decide)).trans a17_2a0
  have a18_2c0 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K18.acc (by decide) (by decide)).trans a17_2c0
  have a18_2e0 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K18.acc (by decide) (by decide)).trans a17_2e0
  have a18_320 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := (K18.acc (by decide) (by decide)).trans a17_320
  have a18_420 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := (K18.acc (by decide) (by decide)).trans a17_420
  have a18_440 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := (K18.acc (by decide) (by decide)).trans a17_440
  have a18_1480 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = X := (K18.acc (by decide) (by decide)).trans a17_1480
  have a18_14a0 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) 8 = Y := (K18.acc (by decide) (by decide)).trans a17_14a0
  have a18_14c0 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x14C0) 8 = Z := (K18.acc (by decide) (by decide)).trans a17_14c0
  have a18_15a8 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := (K18.acc (by decide) (by decide)).trans a17_15a8
  have a18_15c8 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := (K18.acc (by decide) (by decide)).trans a17_15c8
  have a18_15e8 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x15E8) 8 = Z := (K18.acc (by decide) (by decide)).trans a17_15e8
  have a18_1380 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = Z := (accV_S 8 fun q hq => by
    rw [show 0x1380 + q = 0x1380 + (0x0 + q) by omega, X18 (0x0 + q) (by omega),
      show 0x15E8 + (0x0 + q) = 0x15E8 + q by omega]).trans a17_15e8
  clear a17_15e8 a17_15c8 a17_15a8 a17_14c0 a17_14a0 a17_1480 a17_440 a17_420 a17_320 a17_2e0 a17_2c0 a17_2a0 q17_440 q17_420 q17_320 b17_340 w17_464 w17_460 w17_130 w17_12c w17_128 w17_124 w17_120 w17_11c w17_118 w17_114 w17_110 w17_10c w17_108 w17_104 w17_100 w17_fc w17_f8 w17_f4 w17_f0 w17_ec w17_e8 w17_e4 w17_e0 w17_dc w17_d8 w17_d4 w17_d0 w17_cc w17_c8 w17_c4 w17_c0 w17_bc w17_b8 w17_b4 w17_b0 w17_ac w17_a8 w17_a4 w17_a0 w17_9c w17_98 w17_94 w17_90 w17_8c w17_88 w17_84 w17_80 w17_7c w17_70 w17_6c w17_68 w17_64 w17_60 w17_5c w17_58 w17_54 w17_50 w17_4c w17_48 w17_44 w17_40 w17_3c w17_38 w17_34 w17_30 w17_2c w17_28 w17_24 w17_20 g17_12 g17_11 g17_10 g17_27 g17_26 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 rb17 s17 m17 u17 c17
  -- 0x1B0C
  obtain ⟨n19, c19, u19⟩ := s18.block svZS1b0c E18.self svZS1b0c_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m19 : n19.mem = n18.mem := u19.mem
  have s19 : St n19.mem SV n19 0x1B14 (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
  have rb19 : ∀ q, reg n19 q = (runBlock svZS1b0c (n18.mem, reg n18)).2 q := fun q => by rw [u19.regs]
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
  have g19_8 : reg n19 (8 : Fin 32) = BitVec.ofNat 32 0x3FCC4B78 := by
    rw [rb19, runBlock_reg _ _ _ (8 : Fin 32) s18.zero (by decide), g18_8]
  have g19_18 : reg n19 (18 : Fin 32) = out := by
    rw [rb19, runBlock_reg _ _ _ (18 : Fin 32) s18.zero (by decide), g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = bp := by
    rw [rb19, runBlock_reg _ _ _ (19 : Fin 32) s18.zero (by decide), g18_19]
  have g19_20 : reg n19 (20 : Fin 32) = BitVec.ofNat 32 0x60 := by
    rw [rb19, runBlock_reg _ _ _ (20 : Fin 32) s18.zero (by decide), g18_20]
  have g19_21 : reg n19 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by
    rw [rb19, runBlock_reg _ _ _ (21 : Fin 32) s18.zero (by decide), g18_21]
  have g19_22 : reg n19 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x15E8 := by
    rw [rb19, runBlock_reg _ _ _ (22 : Fin 32) s18.zero (by decide), g18_22]
  have g19_23 : reg n19 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC4B38 := by
    rw [rb19, runBlock_reg _ _ _ (23 : Fin 32) s18.zero (by decide), g18_23]
  have g19_24 : reg n19 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA60 := by
    rw [rb19, runBlock_reg _ _ _ (24 : Fin 32) s18.zero (by decide), g18_24]
  have g19_26 : reg n19 (26 : Fin 32) = x26 := by
    rw [rb19, runBlock_reg _ _ _ (26 : Fin 32) s18.zero (by decide), g18_26]
  have g19_27 : reg n19 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb19, runBlock_reg _ _ _ (27 : Fin 32) s18.zero (by decide), g18_27]
  have g19_10 : reg n19 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
    rw [rb19]; simp +decide only [runBlock, BInstr.run, svZS1b0c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g18_2, g18_3, g18_4, g18_8, g18_18, g18_19, g18_20, g18_21, g18_22, g18_23, g18_24, g18_26, g18_27, s18.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w19_20 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = ((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF := by rw [m19]; exact w18_20
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
  have w19_460 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m19]; exact w18_460
  have w19_464 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m19]; exact w18_464
  have b19_340 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m19]; exact b18_340
  have q19_320 : ∀ j, j < 32 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) := fun j hj => by rw [m19]; exact q18_320 j hj
  have q19_420 : ∀ j, j < 32 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) := fun j hj => by rw [m19]; exact q18_420 j hj
  have q19_440 : ∀ j, j < 32 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0x440 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B78) + BitVec.ofNat 32 j) := fun j hj => by rw [m19]; exact q18_440 j hj
  have a19_2a0 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m19]; exact a18_2a0
  have a19_2c0 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m19]; exact a18_2c0
  have a19_2e0 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m19]; exact a18_2e0
  have a19_320 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := by rw [m19]; exact a18_320
  have a19_420 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := by rw [m19]; exact a18_420
  have a19_440 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := by rw [m19]; exact a18_440
  have a19_1380 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = Z := by rw [m19]; exact a18_1380
  have a19_1480 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = X := by rw [m19]; exact a18_1480
  have a19_14a0 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) 8 = Y := by rw [m19]; exact a18_14a0
  have a19_14c0 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x14C0) 8 = Z := by rw [m19]; exact a18_14c0
  have a19_15a8 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := by rw [m19]; exact a18_15a8
  have a19_15c8 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := by rw [m19]; exact a18_15c8
  have a19_15e8 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x15E8) 8 = Z := by rw [m19]; exact a18_15e8
  clear a18_1380 a18_15e8 a18_15c8 a18_15a8 a18_14c0 a18_14a0 a18_1480 a18_440 a18_420 a18_320 a18_2e0 a18_2c0 a18_2a0 q18_440 q18_420 q18_320 b18_340 w18_464 w18_460 w18_130 w18_12c w18_128 w18_124 w18_120 w18_11c w18_118 w18_114 w18_110 w18_10c w18_108 w18_104 w18_100 w18_fc w18_f8 w18_f4 w18_f0 w18_ec w18_e8 w18_e4 w18_e0 w18_dc w18_d8 w18_d4 w18_d0 w18_cc w18_c8 w18_c4 w18_c0 w18_bc w18_b8 w18_b4 w18_b0 w18_ac w18_a8 w18_a4 w18_a0 w18_9c w18_98 w18_94 w18_90 w18_8c w18_88 w18_84 w18_80 w18_7c w18_70 w18_6c w18_68 w18_64 w18_60 w18_5c w18_58 w18_54 w18_50 w18_4c w18_48 w18_44 w18_40 w18_3c w18_38 w18_34 w18_30 w18_2c w18_28 w18_24 w18_20 g18_27 g18_26 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 s18 X18 K18 P18
  -- 0x1B14: sb
  obtain ⟨n20, d20, s20, fr20, K20, W20, rg20⟩ := sv_sb F E19 s19 sv_at_1b14 (off' := 0x1B18) (c := 0x13A0)
    (by decide) (by rw [g19_10]; sv_addr) (by decide)
  have t20 : Steps n0 n20 := t19.trans d20
  have fR20 : ∀ x, SvR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
  have E20 : SvCode n20.mem := E19.fr F fr20
  have V20 : SvSaves B n20.mem v := V19.keep K20 (by decide)
  have g20_2 : reg n20 sp = B + 0x21A0 := by rw [rg20 sp, g19_2]
  have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg20 (3 : Fin 32), g19_3]
  have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg20 (4 : Fin 32), g19_4]
  have g20_8 : reg n20 (8 : Fin 32) = BitVec.ofNat 32 0x3FCC4B78 := by rw [rg20 (8 : Fin 32), g19_8]
  have g20_10 : reg n20 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg20 a0, g19_10]
  have g20_18 : reg n20 (18 : Fin 32) = out := by rw [rg20 (18 : Fin 32), g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = bp := by rw [rg20 (19 : Fin 32), g19_19]
  have g20_20 : reg n20 (20 : Fin 32) = BitVec.ofNat 32 0x60 := by rw [rg20 (20 : Fin 32), g19_20]
  have g20_21 : reg n20 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [rg20 (21 : Fin 32), g19_21]
  have g20_22 : reg n20 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x15E8 := by rw [rg20 (22 : Fin 32), g19_22]
  have g20_23 : reg n20 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC4B38 := by rw [rg20 (23 : Fin 32), g19_23]
  have g20_24 : reg n20 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA60 := by rw [rg20 (24 : Fin 32), g19_24]
  have g20_26 : reg n20 (26 : Fin 32) = x26 := by rw [rg20 (26 : Fin 32), g19_26]
  have g20_27 : reg n20 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg20 (27 : Fin 32), g19_27]
  have w20_20 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = ((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF := (K20.w32 (by decide) (by decide)).trans w19_20
  have w20_24 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K20.w32 (by decide) (by decide)).trans w19_24
  have w20_28 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K20.w32 (by decide) (by decide)).trans w19_28
  have w20_2c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K20.w32 (by decide) (by decide)).trans w19_2c
  have w20_30 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K20.w32 (by decide) (by decide)).trans w19_30
  have w20_34 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K20.w32 (by decide) (by decide)).trans w19_34
  have w20_38 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K20.w32 (by decide) (by decide)).trans w19_38
  have w20_3c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K20.w32 (by decide) (by decide)).trans w19_3c
  have w20_40 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K20.w32 (by decide) (by decide)).trans w19_40
  have w20_44 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K20.w32 (by decide) (by decide)).trans w19_44
  have w20_48 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K20.w32 (by decide) (by decide)).trans w19_48
  have w20_4c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K20.w32 (by decide) (by decide)).trans w19_4c
  have w20_50 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K20.w32 (by decide) (by decide)).trans w19_50
  have w20_54 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K20.w32 (by decide) (by decide)).trans w19_54
  have w20_58 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K20.w32 (by decide) (by decide)).trans w19_58
  have w20_5c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K20.w32 (by decide) (by decide)).trans w19_5c
  have w20_60 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K20.w32 (by decide) (by decide)).trans w19_60
  have w20_64 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K20.w32 (by decide) (by decide)).trans w19_64
  have w20_68 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K20.w32 (by decide) (by decide)).trans w19_68
  have w20_6c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K20.w32 (by decide) (by decide)).trans w19_6c
  have w20_70 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K20.w32 (by decide) (by decide)).trans w19_70
  have w20_7c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K20.w32 (by decide) (by decide)).trans w19_7c
  have w20_80 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K20.w32 (by decide) (by decide)).trans w19_80
  have w20_84 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K20.w32 (by decide) (by decide)).trans w19_84
  have w20_88 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K20.w32 (by decide) (by decide)).trans w19_88
  have w20_8c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K20.w32 (by decide) (by decide)).trans w19_8c
  have w20_90 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K20.w32 (by decide) (by decide)).trans w19_90
  have w20_94 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K20.w32 (by decide) (by decide)).trans w19_94
  have w20_98 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K20.w32 (by decide) (by decide)).trans w19_98
  have w20_9c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K20.w32 (by decide) (by decide)).trans w19_9c
  have w20_a0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K20.w32 (by decide) (by decide)).trans w19_a0
  have w20_a4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K20.w32 (by decide) (by decide)).trans w19_a4
  have w20_a8 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K20.w32 (by decide) (by decide)).trans w19_a8
  have w20_ac : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K20.w32 (by decide) (by decide)).trans w19_ac
  have w20_b0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K20.w32 (by decide) (by decide)).trans w19_b0
  have w20_b4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K20.w32 (by decide) (by decide)).trans w19_b4
  have w20_b8 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K20.w32 (by decide) (by decide)).trans w19_b8
  have w20_bc : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K20.w32 (by decide) (by decide)).trans w19_bc
  have w20_c0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K20.w32 (by decide) (by decide)).trans w19_c0
  have w20_c4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K20.w32 (by decide) (by decide)).trans w19_c4
  have w20_c8 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K20.w32 (by decide) (by decide)).trans w19_c8
  have w20_cc : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K20.w32 (by decide) (by decide)).trans w19_cc
  have w20_d0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K20.w32 (by decide) (by decide)).trans w19_d0
  have w20_d4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K20.w32 (by decide) (by decide)).trans w19_d4
  have w20_d8 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K20.w32 (by decide) (by decide)).trans w19_d8
  have w20_dc : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K20.w32 (by decide) (by decide)).trans w19_dc
  have w20_e0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K20.w32 (by decide) (by decide)).trans w19_e0
  have w20_e4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K20.w32 (by decide) (by decide)).trans w19_e4
  have w20_e8 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K20.w32 (by decide) (by decide)).trans w19_e8
  have w20_ec : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K20.w32 (by decide) (by decide)).trans w19_ec
  have w20_f0 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K20.w32 (by decide) (by decide)).trans w19_f0
  have w20_f4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K20.w32 (by decide) (by decide)).trans w19_f4
  have w20_f8 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K20.w32 (by decide) (by decide)).trans w19_f8
  have w20_fc : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K20.w32 (by decide) (by decide)).trans w19_fc
  have w20_100 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K20.w32 (by decide) (by decide)).trans w19_100
  have w20_104 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K20.w32 (by decide) (by decide)).trans w19_104
  have w20_108 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K20.w32 (by decide) (by decide)).trans w19_108
  have w20_10c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K20.w32 (by decide) (by decide)).trans w19_10c
  have w20_110 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K20.w32 (by decide) (by decide)).trans w19_110
  have w20_114 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K20.w32 (by decide) (by decide)).trans w19_114
  have w20_118 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K20.w32 (by decide) (by decide)).trans w19_118
  have w20_11c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K20.w32 (by decide) (by decide)).trans w19_11c
  have w20_120 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K20.w32 (by decide) (by decide)).trans w19_120
  have w20_124 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K20.w32 (by decide) (by decide)).trans w19_124
  have w20_128 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K20.w32 (by decide) (by decide)).trans w19_128
  have w20_12c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K20.w32 (by decide) (by decide)).trans w19_12c
  have w20_130 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K20.w32 (by decide) (by decide)).trans w19_130
  have w20_460 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := (K20.w32 (by decide) (by decide)).trans w19_460
  have w20_464 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := (K20.w32 (by decide) (by decide)).trans w19_464
  have b20_340 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K20.b8 (by decide) (by decide)).trans b19_340
  have b20_13a0 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [W20, s19.zero]; rfl
  have q20_320 : ∀ j, j < 32 → n20.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) := fun j hj => (K20.range (by decide) (by decide) j hj).trans (q19_320 j hj)
  have q20_420 : ∀ j, j < 32 → n20.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) := fun j hj => (K20.range (by decide) (by decide) j hj).trans (q19_420 j hj)
  have q20_440 : ∀ j, j < 32 → n20.mem (B + 0x21A0 + BitVec.ofNat 32 (0x440 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B78) + BitVec.ofNat 32 j) := fun j hj => (K20.range (by decide) (by decide) j hj).trans (q19_440 j hj)
  have a20_2a0 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K20.acc (by decide) (by decide)).trans a19_2a0
  have a20_2c0 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K20.acc (by decide) (by decide)).trans a19_2c0
  have a20_2e0 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K20.acc (by decide) (by decide)).trans a19_2e0
  have a20_320 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := (K20.acc (by decide) (by decide)).trans a19_320
  have a20_420 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := (K20.acc (by decide) (by decide)).trans a19_420
  have a20_440 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := (K20.acc (by decide) (by decide)).trans a19_440
  have a20_1380 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = Z := (K20.acc (by decide) (by decide)).trans a19_1380
  have a20_1480 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = X := (K20.acc (by decide) (by decide)).trans a19_1480
  have a20_14a0 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) 8 = Y := (K20.acc (by decide) (by decide)).trans a19_14a0
  have a20_14c0 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x14C0) 8 = Z := (K20.acc (by decide) (by decide)).trans a19_14c0
  have a20_15a8 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := (K20.acc (by decide) (by decide)).trans a19_15a8
  have a20_15c8 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := (K20.acc (by decide) (by decide)).trans a19_15c8
  have a20_15e8 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x15E8) 8 = Z := (K20.acc (by decide) (by decide)).trans a19_15e8
  clear a19_15e8 a19_15c8 a19_15a8 a19_14c0 a19_14a0 a19_1480 a19_1380 a19_440 a19_420 a19_320 a19_2e0 a19_2c0 a19_2a0 q19_440 q19_420 q19_320 b19_340 w19_464 w19_460 w19_130 w19_12c w19_128 w19_124 w19_120 w19_11c w19_118 w19_114 w19_110 w19_10c w19_108 w19_104 w19_100 w19_fc w19_f8 w19_f4 w19_f0 w19_ec w19_e8 w19_e4 w19_e0 w19_dc w19_d8 w19_d4 w19_d0 w19_cc w19_c8 w19_c4 w19_c0 w19_bc w19_b8 w19_b4 w19_b0 w19_ac w19_a8 w19_a4 w19_a0 w19_9c w19_98 w19_94 w19_90 w19_8c w19_88 w19_84 w19_80 w19_7c w19_70 w19_6c w19_68 w19_64 w19_60 w19_5c w19_58 w19_54 w19_50 w19_4c w19_48 w19_44 w19_40 w19_3c w19_38 w19_34 w19_30 w19_2c w19_28 w19_24 w19_20 g19_10 g19_27 g19_26 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 rb19 s19 m19 u19 c19
  -- 0x1B18
  obtain ⟨n21, c21, u21⟩ := s20.block svZS1b18 E20.self svZS1b18_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m21 : n21.mem = n20.mem := u21.mem
  have s21 : St n21.mem SV n21 0x1B26 (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
  have rb21 : ∀ q, reg n21 q = (runBlock svZS1b18 (n20.mem, reg n20)).2 q := fun q => by rw [u21.regs]
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
  have g21_8 : reg n21 (8 : Fin 32) = BitVec.ofNat 32 0x3FCC4B78 := by
    rw [rb21, runBlock_reg _ _ _ (8 : Fin 32) s20.zero (by decide), g20_8]
  have g21_18 : reg n21 (18 : Fin 32) = out := by
    rw [rb21, runBlock_reg _ _ _ (18 : Fin 32) s20.zero (by decide), g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = bp := by
    rw [rb21, runBlock_reg _ _ _ (19 : Fin 32) s20.zero (by decide), g20_19]
  have g21_20 : reg n21 (20 : Fin 32) = BitVec.ofNat 32 0x60 := by
    rw [rb21, runBlock_reg _ _ _ (20 : Fin 32) s20.zero (by decide), g20_20]
  have g21_21 : reg n21 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by
    rw [rb21, runBlock_reg _ _ _ (21 : Fin 32) s20.zero (by decide), g20_21]
  have g21_22 : reg n21 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x15E8 := by
    rw [rb21, runBlock_reg _ _ _ (22 : Fin 32) s20.zero (by decide), g20_22]
  have g21_23 : reg n21 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC4B38 := by
    rw [rb21, runBlock_reg _ _ _ (23 : Fin 32) s20.zero (by decide), g20_23]
  have g21_24 : reg n21 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA60 := by
    rw [rb21, runBlock_reg _ _ _ (24 : Fin 32) s20.zero (by decide), g20_24]
  have g21_26 : reg n21 (26 : Fin 32) = x26 := by
    rw [rb21, runBlock_reg _ _ _ (26 : Fin 32) s20.zero (by decide), g20_26]
  have g21_27 : reg n21 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb21, runBlock_reg _ _ _ (27 : Fin 32) s20.zero (by decide), g20_27]
  have g21_10 : reg n21 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by
    rw [rb21]; simp +decide only [runBlock, BInstr.run, svZS1b18, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g20_2, g20_3, g20_4, g20_8, g20_10, g20_18, g20_19, g20_20, g20_21, g20_22, g20_23, g20_24, g20_26, g20_27, s20.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g21_11 : reg n21 a1 = BitVec.ofNat 32 0x0 := by
    rw [rb21]; simp +decide only [runBlock, BInstr.run, svZS1b18, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g20_2, g20_3, g20_4, g20_8, g20_10, g20_18, g20_19, g20_20, g20_21, g20_22, g20_23, g20_24, g20_26, g20_27, s20.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g21_12 : reg n21 a2 = BitVec.ofNat 32 0x24 := by
    rw [rb21]; simp +decide only [runBlock, BInstr.run, svZS1b18, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g20_2, g20_3, g20_4, g20_8, g20_10, g20_18, g20_19, g20_20, g20_21, g20_22, g20_23, g20_24, g20_26, g20_27, s20.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w21_20 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = ((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF := by rw [m21]; exact w20_20
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
  have w21_460 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m21]; exact w20_460
  have w21_464 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m21]; exact w20_464
  have b21_340 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m21]; exact b20_340
  have b21_13a0 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m21]; exact b20_13a0
  have q21_320 : ∀ j, j < 32 → n21.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) := fun j hj => by rw [m21]; exact q20_320 j hj
  have q21_420 : ∀ j, j < 32 → n21.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) := fun j hj => by rw [m21]; exact q20_420 j hj
  have q21_440 : ∀ j, j < 32 → n21.mem (B + 0x21A0 + BitVec.ofNat 32 (0x440 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B78) + BitVec.ofNat 32 j) := fun j hj => by rw [m21]; exact q20_440 j hj
  have a21_2a0 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m21]; exact a20_2a0
  have a21_2c0 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m21]; exact a20_2c0
  have a21_2e0 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m21]; exact a20_2e0
  have a21_320 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := by rw [m21]; exact a20_320
  have a21_420 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := by rw [m21]; exact a20_420
  have a21_440 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := by rw [m21]; exact a20_440
  have a21_1380 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = Z := by rw [m21]; exact a20_1380
  have a21_1480 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = X := by rw [m21]; exact a20_1480
  have a21_14a0 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) 8 = Y := by rw [m21]; exact a20_14a0
  have a21_14c0 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x14C0) 8 = Z := by rw [m21]; exact a20_14c0
  have a21_15a8 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := by rw [m21]; exact a20_15a8
  have a21_15c8 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := by rw [m21]; exact a20_15c8
  have a21_15e8 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x15E8) 8 = Z := by rw [m21]; exact a20_15e8
  clear a20_15e8 a20_15c8 a20_15a8 a20_14c0 a20_14a0 a20_1480 a20_1380 a20_440 a20_420 a20_320 a20_2e0 a20_2c0 a20_2a0 q20_440 q20_420 q20_320 b20_13a0 b20_340 w20_464 w20_460 w20_130 w20_12c w20_128 w20_124 w20_120 w20_11c w20_118 w20_114 w20_110 w20_10c w20_108 w20_104 w20_100 w20_fc w20_f8 w20_f4 w20_f0 w20_ec w20_e8 w20_e4 w20_e0 w20_dc w20_d8 w20_d4 w20_d0 w20_cc w20_c8 w20_c4 w20_c0 w20_bc w20_b8 w20_b4 w20_b0 w20_ac w20_a8 w20_a4 w20_a0 w20_9c w20_98 w20_94 w20_90 w20_8c w20_88 w20_84 w20_80 w20_7c w20_70 w20_6c w20_68 w20_64 w20_60 w20_5c w20_58 w20_54 w20_50 w20_4c w20_48 w20_44 w20_40 w20_3c w20_38 w20_34 w20_30 w20_2c w20_28 w20_24 w20_20 g20_27 g20_26 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_10 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 rg20 W20 K20 fr20 s20 d20
  -- 0x1B26: sv_ms3F
  obtain ⟨n22, c22, s22, rk22, K22, fr22, Z22⟩ := sv_ms3F (c := 0x1480) (N := 0x24)
    F E21 s21 sv_at_1b26 sv_at_1b2a (by decide) (by decide)
    g21_10 g21_11 g21_12 (by decide)
  have t22 : Steps n0 n22 := t21.trans c22
  have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
  have E22 : SvCode n22.mem := E21.fr F fr22
  have V22 : SvSaves B n22.mem v := V21.keepL K22 (by decide)
  have g22_2 : reg n22 sp = B + 0x21A0 := by rw [rk22 sp (by decide), g21_2]
  have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk22 (3 : Fin 32) (by decide), g21_3]
  have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk22 (4 : Fin 32) (by decide), g21_4]
  have g22_8 : reg n22 (8 : Fin 32) = BitVec.ofNat 32 0x3FCC4B78 := by rw [rk22 (8 : Fin 32) (by decide), g21_8]
  have g22_18 : reg n22 (18 : Fin 32) = out := by rw [rk22 (18 : Fin 32) (by decide), g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [rk22 (19 : Fin 32) (by decide), g21_19]
  have g22_20 : reg n22 (20 : Fin 32) = BitVec.ofNat 32 0x60 := by rw [rk22 (20 : Fin 32) (by decide), g21_20]
  have g22_21 : reg n22 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [rk22 (21 : Fin 32) (by decide), g21_21]
  have g22_22 : reg n22 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x15E8 := by rw [rk22 (22 : Fin 32) (by decide), g21_22]
  have g22_23 : reg n22 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC4B38 := by rw [rk22 (23 : Fin 32) (by decide), g21_23]
  have g22_24 : reg n22 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA60 := by rw [rk22 (24 : Fin 32) (by decide), g21_24]
  have g22_26 : reg n22 (26 : Fin 32) = x26 := by rw [rk22 (26 : Fin 32) (by decide), g21_26]
  have g22_27 : reg n22 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk22 (27 : Fin 32) (by decide), g21_27]
  have w22_20 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = ((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF := (K22.w32 (by decide) (by decide)).trans w21_20
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
  have w22_460 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := (K22.w32 (by decide) (by decide)).trans w21_460
  have w22_464 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := (K22.w32 (by decide) (by decide)).trans w21_464
  have b22_340 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K22.b8 (by decide) (by decide)).trans b21_340
  have b22_13a0 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K22.b8 (by decide) (by decide)).trans b21_13a0
  have q22_320 : ∀ j, j < 32 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) := fun j hj => (K22.range (by decide) (by decide) j hj).trans (q21_320 j hj)
  have q22_420 : ∀ j, j < 32 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) := fun j hj => (K22.range (by decide) (by decide) j hj).trans (q21_420 j hj)
  have q22_440 : ∀ j, j < 32 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0x440 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B78) + BitVec.ofNat 32 j) := fun j hj => (K22.range (by decide) (by decide) j hj).trans (q21_440 j hj)
  have a22_2a0 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K22.acc (by decide) (by decide)).trans a21_2a0
  have a22_2c0 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K22.acc (by decide) (by decide)).trans a21_2c0
  have a22_2e0 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K22.acc (by decide) (by decide)).trans a21_2e0
  have a22_320 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := (K22.acc (by decide) (by decide)).trans a21_320
  have a22_420 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := (K22.acc (by decide) (by decide)).trans a21_420
  have a22_440 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := (K22.acc (by decide) (by decide)).trans a21_440
  have a22_1380 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = Z := (K22.acc (by decide) (by decide)).trans a21_1380
  have a22_14c0 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x14C0) 8 = Z := (K22.acc (by decide) (by decide)).trans a21_14c0
  have a22_15a8 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := (K22.acc (by decide) (by decide)).trans a21_15a8
  have a22_15c8 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := (K22.acc (by decide) (by decide)).trans a21_15c8
  have a22_15e8 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x15E8) 8 = Z := (K22.acc (by decide) (by decide)).trans a21_15e8
  have a22_1480 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = 0 := acc0_of_fill fun j hj => by rw [show 0x1480 + j = 0x1480 + (0x0 + j) by omega]; exact Z22 _ (by omega)
  have b22_14a0 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = 0 := by rw [show 0x14A0 = 0x1480 + 0x20 from rfl]; exact Z22 _ (by decide)
  clear a21_15e8 a21_15c8 a21_15a8 a21_14c0 a21_14a0 a21_1480 a21_1380 a21_440 a21_420 a21_320 a21_2e0 a21_2c0 a21_2a0 q21_440 q21_420 q21_320 b21_13a0 b21_340 w21_464 w21_460 w21_130 w21_12c w21_128 w21_124 w21_120 w21_11c w21_118 w21_114 w21_110 w21_10c w21_108 w21_104 w21_100 w21_fc w21_f8 w21_f4 w21_f0 w21_ec w21_e8 w21_e4 w21_e0 w21_dc w21_d8 w21_d4 w21_d0 w21_cc w21_c8 w21_c4 w21_c0 w21_bc w21_b8 w21_b4 w21_b0 w21_ac w21_a8 w21_a4 w21_a0 w21_9c w21_98 w21_94 w21_90 w21_8c w21_88 w21_84 w21_80 w21_7c w21_70 w21_6c w21_68 w21_64 w21_60 w21_5c w21_58 w21_54 w21_50 w21_4c w21_48 w21_44 w21_40 w21_3c w21_38 w21_34 w21_30 w21_2c w21_28 w21_24 w21_20 g21_12 g21_11 g21_10 g21_27 g21_26 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_8 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 rb21 s21 m21 u21 c21
  -- 0x1B2E
  obtain ⟨n23, c23, u23⟩ := s22.block svZS1b2e E22.self svZS1b2e_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m23 : n23.mem = n22.mem := u23.mem
  have s23 : St n23.mem SV n23 0x1B3C (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
  have rb23 : ∀ q, reg n23 q = (runBlock svZS1b2e (n22.mem, reg n22)).2 q := fun q => by rw [u23.regs]
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
  have g23_8 : reg n23 (8 : Fin 32) = BitVec.ofNat 32 0x3FCC4B78 := by
    rw [rb23, runBlock_reg _ _ _ (8 : Fin 32) s22.zero (by decide), g22_8]
  have g23_18 : reg n23 (18 : Fin 32) = out := by
    rw [rb23, runBlock_reg _ _ _ (18 : Fin 32) s22.zero (by decide), g22_18]
  have g23_19 : reg n23 (19 : Fin 32) = bp := by
    rw [rb23, runBlock_reg _ _ _ (19 : Fin 32) s22.zero (by decide), g22_19]
  have g23_20 : reg n23 (20 : Fin 32) = BitVec.ofNat 32 0x60 := by
    rw [rb23, runBlock_reg _ _ _ (20 : Fin 32) s22.zero (by decide), g22_20]
  have g23_21 : reg n23 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by
    rw [rb23, runBlock_reg _ _ _ (21 : Fin 32) s22.zero (by decide), g22_21]
  have g23_22 : reg n23 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x15E8 := by
    rw [rb23, runBlock_reg _ _ _ (22 : Fin 32) s22.zero (by decide), g22_22]
  have g23_23 : reg n23 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC4B38 := by
    rw [rb23, runBlock_reg _ _ _ (23 : Fin 32) s22.zero (by decide), g22_23]
  have g23_24 : reg n23 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA60 := by
    rw [rb23, runBlock_reg _ _ _ (24 : Fin 32) s22.zero (by decide), g22_24]
  have g23_26 : reg n23 (26 : Fin 32) = x26 := by
    rw [rb23, runBlock_reg _ _ _ (26 : Fin 32) s22.zero (by decide), g22_26]
  have g23_27 : reg n23 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb23, runBlock_reg _ _ _ (27 : Fin 32) s22.zero (by decide), g22_27]
  have g23_10 : reg n23 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1020 := by
    rw [rb23]; simp +decide only [runBlock, BInstr.run, svZS1b2e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g22_2, g22_3, g22_4, g22_8, g22_18, g22_19, g22_20, g22_21, g22_22, g22_23, g22_24, g22_26, g22_27, s22.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g23_11 : reg n23 a1 = BitVec.ofNat 32 0x3FCC4B78 := by
    rw [rb23]; simp +decide only [runBlock, BInstr.run, svZS1b2e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g22_2, g22_3, g22_4, g22_8, g22_18, g22_19, g22_20, g22_21, g22_22, g22_23, g22_24, g22_26, g22_27, s22.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g23_12 : reg n23 a2 = BitVec.ofNat 32 0x20 := by
    rw [rb23]; simp +decide only [runBlock, BInstr.run, svZS1b2e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g22_2, g22_3, g22_4, g22_8, g22_18, g22_19, g22_20, g22_21, g22_22, g22_23, g22_24, g22_26, g22_27, s22.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w23_20 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = ((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF := by rw [m23]; exact w22_20
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
  have w23_460 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m23]; exact w22_460
  have w23_464 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m23]; exact w22_464
  have b23_340 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m23]; exact b22_340
  have b23_13a0 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m23]; exact b22_13a0
  have b23_14a0 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = 0 := by rw [m23]; exact b22_14a0
  have q23_320 : ∀ j, j < 32 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) := fun j hj => by rw [m23]; exact q22_320 j hj
  have q23_420 : ∀ j, j < 32 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) := fun j hj => by rw [m23]; exact q22_420 j hj
  have q23_440 : ∀ j, j < 32 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0x440 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B78) + BitVec.ofNat 32 j) := fun j hj => by rw [m23]; exact q22_440 j hj
  have a23_2a0 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m23]; exact a22_2a0
  have a23_2c0 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m23]; exact a22_2c0
  have a23_2e0 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m23]; exact a22_2e0
  have a23_320 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := by rw [m23]; exact a22_320
  have a23_420 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := by rw [m23]; exact a22_420
  have a23_440 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := by rw [m23]; exact a22_440
  have a23_1380 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = Z := by rw [m23]; exact a22_1380
  have a23_1480 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = 0 := by rw [m23]; exact a22_1480
  have a23_14c0 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x14C0) 8 = Z := by rw [m23]; exact a22_14c0
  have a23_15a8 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := by rw [m23]; exact a22_15a8
  have a23_15c8 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := by rw [m23]; exact a22_15c8
  have a23_15e8 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x15E8) 8 = Z := by rw [m23]; exact a22_15e8
  clear b22_14a0 a22_1480 a22_15e8 a22_15c8 a22_15a8 a22_14c0 a22_1380 a22_440 a22_420 a22_320 a22_2e0 a22_2c0 a22_2a0 q22_440 q22_420 q22_320 b22_13a0 b22_340 w22_464 w22_460 w22_130 w22_12c w22_128 w22_124 w22_120 w22_11c w22_118 w22_114 w22_110 w22_10c w22_108 w22_104 w22_100 w22_fc w22_f8 w22_f4 w22_f0 w22_ec w22_e8 w22_e4 w22_e0 w22_dc w22_d8 w22_d4 w22_d0 w22_cc w22_c8 w22_c4 w22_c0 w22_bc w22_b8 w22_b4 w22_b0 w22_ac w22_a8 w22_a4 w22_a0 w22_9c w22_98 w22_94 w22_90 w22_8c w22_88 w22_84 w22_80 w22_7c w22_70 w22_6c w22_68 w22_64 w22_60 w22_5c w22_58 w22_54 w22_50 w22_4c w22_48 w22_44 w22_40 w22_3c w22_38 w22_34 w22_30 w22_2c w22_28 w22_24 w22_20 g22_27 g22_26 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 Z22 fr22 K22 rk22 s22 c22
  -- 0x1B3C: memcpy from outside the stack
  obtain ⟨n24, P24, K24, X24⟩ := sv_mcRo2 (c := 0x1020) (N := 0x20) F RS E23 s23 sv_at_1b3c sv_at_1b40
    (by decide) (by decide) g23_2 g23_10 g23_11 g23_12 (by decide) (Or.inr ⟨by decide, by decide⟩)
  have s24 := P24.st
  have fr24 := P24.fr
  have t24 : Steps n0 n24 := t23.trans P24.steps
  have fR24 : ∀ x, SvR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
  have E24 : SvCode n24.mem := E23.fr F fr24
  have V24 : SvSaves B n24.mem v := V23.keep K24 (by decide)
  have g24_2 : reg n24 sp = B + 0x21A0 := by rw [P24.regs sp (by decide), g23_2]
  have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P24.regs (3 : Fin 32) (by decide), g23_3]
  have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P24.regs (4 : Fin 32) (by decide), g23_4]
  have g24_8 : reg n24 (8 : Fin 32) = BitVec.ofNat 32 0x3FCC4B78 := by rw [P24.regs (8 : Fin 32) (by decide), g23_8]
  have g24_18 : reg n24 (18 : Fin 32) = out := by rw [P24.regs (18 : Fin 32) (by decide), g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = bp := by rw [P24.regs (19 : Fin 32) (by decide), g23_19]
  have g24_20 : reg n24 (20 : Fin 32) = BitVec.ofNat 32 0x60 := by rw [P24.regs (20 : Fin 32) (by decide), g23_20]
  have g24_21 : reg n24 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [P24.regs (21 : Fin 32) (by decide), g23_21]
  have g24_22 : reg n24 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x15E8 := by rw [P24.regs (22 : Fin 32) (by decide), g23_22]
  have g24_23 : reg n24 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC4B38 := by rw [P24.regs (23 : Fin 32) (by decide), g23_23]
  have g24_24 : reg n24 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA60 := by rw [P24.regs (24 : Fin 32) (by decide), g23_24]
  have g24_26 : reg n24 (26 : Fin 32) = x26 := by rw [P24.regs (26 : Fin 32) (by decide), g23_26]
  have g24_27 : reg n24 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P24.regs (27 : Fin 32) (by decide), g23_27]
  have w24_20 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = ((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF := (K24.w32 (by decide) (by decide)).trans w23_20
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
  have w24_460 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := (K24.w32 (by decide) (by decide)).trans w23_460
  have w24_464 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := (K24.w32 (by decide) (by decide)).trans w23_464
  have b24_340 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K24.b8 (by decide) (by decide)).trans b23_340
  have b24_13a0 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K24.b8 (by decide) (by decide)).trans b23_13a0
  have b24_14a0 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = 0 := (K24.b8 (by decide) (by decide)).trans b23_14a0
  have q24_320 : ∀ j, j < 32 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) := fun j hj => (K24.range (by decide) (by decide) j hj).trans (q23_320 j hj)
  have q24_420 : ∀ j, j < 32 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) := fun j hj => (K24.range (by decide) (by decide) j hj).trans (q23_420 j hj)
  have q24_440 : ∀ j, j < 32 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0x440 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B78) + BitVec.ofNat 32 j) := fun j hj => (K24.range (by decide) (by decide) j hj).trans (q23_440 j hj)
  have a24_2a0 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K24.acc (by decide) (by decide)).trans a23_2a0
  have a24_2c0 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K24.acc (by decide) (by decide)).trans a23_2c0
  have a24_2e0 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K24.acc (by decide) (by decide)).trans a23_2e0
  have a24_320 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := (K24.acc (by decide) (by decide)).trans a23_320
  have a24_420 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := (K24.acc (by decide) (by decide)).trans a23_420
  have a24_440 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := (K24.acc (by decide) (by decide)).trans a23_440
  have a24_1380 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = Z := (K24.acc (by decide) (by decide)).trans a23_1380
  have a24_1480 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = 0 := (K24.acc (by decide) (by decide)).trans a23_1480
  have a24_14c0 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x14C0) 8 = Z := (K24.acc (by decide) (by decide)).trans a23_14c0
  have a24_15a8 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := (K24.acc (by decide) (by decide)).trans a23_15a8
  have a24_15c8 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := (K24.acc (by decide) (by decide)).trans a23_15c8
  have a24_15e8 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x15E8) 8 = Z := (K24.acc (by decide) (by decide)).trans a23_15e8
  have q24_1020 : ∀ j, j < 32 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1020 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B78) + BitVec.ofNat 32 j) :=
    fun j hj => (X24 j hj).trans (fR23 _ (SvRo2.r RS (Or.inr ⟨by decide, by decide⟩) hj))
  have a24_1020 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := acc_of_frame q24_1020
  clear a23_15e8 a23_15c8 a23_15a8 a23_14c0 a23_1480 a23_1380 a23_440 a23_420 a23_320 a23_2e0 a23_2c0 a23_2a0 q23_440 q23_420 q23_320 b23_14a0 b23_13a0 b23_340 w23_464 w23_460 w23_130 w23_12c w23_128 w23_124 w23_120 w23_11c w23_118 w23_114 w23_110 w23_10c w23_108 w23_104 w23_100 w23_fc w23_f8 w23_f4 w23_f0 w23_ec w23_e8 w23_e4 w23_e0 w23_dc w23_d8 w23_d4 w23_d0 w23_cc w23_c8 w23_c4 w23_c0 w23_bc w23_b8 w23_b4 w23_b0 w23_ac w23_a8 w23_a4 w23_a0 w23_9c w23_98 w23_94 w23_90 w23_8c w23_88 w23_84 w23_80 w23_7c w23_70 w23_6c w23_68 w23_64 w23_60 w23_5c w23_58 w23_54 w23_50 w23_4c w23_48 w23_44 w23_40 w23_3c w23_38 w23_34 w23_30 w23_2c w23_28 w23_24 w23_20 g23_12 g23_11 g23_10 g23_27 g23_26 g23_24 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 rb23 s23 m23 u23 c23
  -- 0x1B44: sw
  obtain ⟨n25, d25, s25, fr25, K25, W25, rg25⟩ := sv_sw F E24 s24 sv_at_1b44 (off' := 0x1B46) (c := 0x38)
    (by decide) (by rw [g24_2]; sv_addr) (by decide) (by decide)
  have t25 : Steps n0 n25 := t24.trans d25
  have fR25 : ∀ x, SvR B x → n25.mem x = M0 x := fun x hx => (fr25 x hx).trans (fR24 x hx)
  have E25 : SvCode n25.mem := E24.fr F fr25
  have V25 : SvSaves B n25.mem v := V24.keep K25 (by decide)
  have g25_2 : reg n25 sp = B + 0x21A0 := by rw [rg25 sp, g24_2]
  have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg25 (3 : Fin 32), g24_3]
  have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg25 (4 : Fin 32), g24_4]
  have g25_8 : reg n25 (8 : Fin 32) = BitVec.ofNat 32 0x3FCC4B78 := by rw [rg25 (8 : Fin 32), g24_8]
  have g25_18 : reg n25 (18 : Fin 32) = out := by rw [rg25 (18 : Fin 32), g24_18]
  have g25_19 : reg n25 (19 : Fin 32) = bp := by rw [rg25 (19 : Fin 32), g24_19]
  have g25_20 : reg n25 (20 : Fin 32) = BitVec.ofNat 32 0x60 := by rw [rg25 (20 : Fin 32), g24_20]
  have g25_21 : reg n25 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [rg25 (21 : Fin 32), g24_21]
  have g25_22 : reg n25 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x15E8 := by rw [rg25 (22 : Fin 32), g24_22]
  have g25_23 : reg n25 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC4B38 := by rw [rg25 (23 : Fin 32), g24_23]
  have g25_24 : reg n25 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA60 := by rw [rg25 (24 : Fin 32), g24_24]
  have g25_26 : reg n25 (26 : Fin 32) = x26 := by rw [rg25 (26 : Fin 32), g24_26]
  have g25_27 : reg n25 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg25 (27 : Fin 32), g24_27]
  have w25_20 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = ((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF := (K25.w32 (by decide) (by decide)).trans w24_20
  have w25_24 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K25.w32 (by decide) (by decide)).trans w24_24
  have w25_28 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K25.w32 (by decide) (by decide)).trans w24_28
  have w25_2c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K25.w32 (by decide) (by decide)).trans w24_2c
  have w25_30 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K25.w32 (by decide) (by decide)).trans w24_30
  have w25_34 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K25.w32 (by decide) (by decide)).trans w24_34
  have w25_3c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K25.w32 (by decide) (by decide)).trans w24_3c
  have w25_40 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K25.w32 (by decide) (by decide)).trans w24_40
  have w25_44 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K25.w32 (by decide) (by decide)).trans w24_44
  have w25_48 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K25.w32 (by decide) (by decide)).trans w24_48
  have w25_4c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K25.w32 (by decide) (by decide)).trans w24_4c
  have w25_50 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K25.w32 (by decide) (by decide)).trans w24_50
  have w25_54 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K25.w32 (by decide) (by decide)).trans w24_54
  have w25_58 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K25.w32 (by decide) (by decide)).trans w24_58
  have w25_5c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K25.w32 (by decide) (by decide)).trans w24_5c
  have w25_60 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K25.w32 (by decide) (by decide)).trans w24_60
  have w25_64 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K25.w32 (by decide) (by decide)).trans w24_64
  have w25_68 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K25.w32 (by decide) (by decide)).trans w24_68
  have w25_6c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K25.w32 (by decide) (by decide)).trans w24_6c
  have w25_70 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K25.w32 (by decide) (by decide)).trans w24_70
  have w25_7c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K25.w32 (by decide) (by decide)).trans w24_7c
  have w25_80 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K25.w32 (by decide) (by decide)).trans w24_80
  have w25_84 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K25.w32 (by decide) (by decide)).trans w24_84
  have w25_88 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K25.w32 (by decide) (by decide)).trans w24_88
  have w25_8c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K25.w32 (by decide) (by decide)).trans w24_8c
  have w25_90 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K25.w32 (by decide) (by decide)).trans w24_90
  have w25_94 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K25.w32 (by decide) (by decide)).trans w24_94
  have w25_98 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K25.w32 (by decide) (by decide)).trans w24_98
  have w25_9c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K25.w32 (by decide) (by decide)).trans w24_9c
  have w25_a0 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K25.w32 (by decide) (by decide)).trans w24_a0
  have w25_a4 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K25.w32 (by decide) (by decide)).trans w24_a4
  have w25_a8 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K25.w32 (by decide) (by decide)).trans w24_a8
  have w25_ac : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K25.w32 (by decide) (by decide)).trans w24_ac
  have w25_b0 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K25.w32 (by decide) (by decide)).trans w24_b0
  have w25_b4 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K25.w32 (by decide) (by decide)).trans w24_b4
  have w25_b8 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K25.w32 (by decide) (by decide)).trans w24_b8
  have w25_bc : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K25.w32 (by decide) (by decide)).trans w24_bc
  have w25_c0 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K25.w32 (by decide) (by decide)).trans w24_c0
  have w25_c4 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K25.w32 (by decide) (by decide)).trans w24_c4
  have w25_c8 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K25.w32 (by decide) (by decide)).trans w24_c8
  have w25_cc : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K25.w32 (by decide) (by decide)).trans w24_cc
  have w25_d0 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K25.w32 (by decide) (by decide)).trans w24_d0
  have w25_d4 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K25.w32 (by decide) (by decide)).trans w24_d4
  have w25_d8 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K25.w32 (by decide) (by decide)).trans w24_d8
  have w25_dc : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K25.w32 (by decide) (by decide)).trans w24_dc
  have w25_e0 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K25.w32 (by decide) (by decide)).trans w24_e0
  have w25_e4 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K25.w32 (by decide) (by decide)).trans w24_e4
  have w25_e8 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K25.w32 (by decide) (by decide)).trans w24_e8
  have w25_ec : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K25.w32 (by decide) (by decide)).trans w24_ec
  have w25_f0 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K25.w32 (by decide) (by decide)).trans w24_f0
  have w25_f4 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K25.w32 (by decide) (by decide)).trans w24_f4
  have w25_f8 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K25.w32 (by decide) (by decide)).trans w24_f8
  have w25_fc : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K25.w32 (by decide) (by decide)).trans w24_fc
  have w25_100 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K25.w32 (by decide) (by decide)).trans w24_100
  have w25_104 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K25.w32 (by decide) (by decide)).trans w24_104
  have w25_108 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K25.w32 (by decide) (by decide)).trans w24_108
  have w25_10c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K25.w32 (by decide) (by decide)).trans w24_10c
  have w25_110 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K25.w32 (by decide) (by decide)).trans w24_110
  have w25_114 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K25.w32 (by decide) (by decide)).trans w24_114
  have w25_118 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K25.w32 (by decide) (by decide)).trans w24_118
  have w25_11c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K25.w32 (by decide) (by decide)).trans w24_11c
  have w25_120 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K25.w32 (by decide) (by decide)).trans w24_120
  have w25_124 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K25.w32 (by decide) (by decide)).trans w24_124
  have w25_128 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K25.w32 (by decide) (by decide)).trans w24_128
  have w25_12c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K25.w32 (by decide) (by decide)).trans w24_12c
  have w25_130 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K25.w32 (by decide) (by decide)).trans w24_130
  have w25_460 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := (K25.w32 (by decide) (by decide)).trans w24_460
  have w25_464 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := (K25.w32 (by decide) (by decide)).trans w24_464
  have b25_340 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K25.b8 (by decide) (by decide)).trans b24_340
  have b25_13a0 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K25.b8 (by decide) (by decide)).trans b24_13a0
  have b25_14a0 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = 0 := (K25.b8 (by decide) (by decide)).trans b24_14a0
  have w25_38 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = BitVec.ofNat 32 0x0 := by rw [W25, s24.zero]; rfl
  have q25_320 : ∀ j, j < 32 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) := fun j hj => (K25.range (by decide) (by decide) j hj).trans (q24_320 j hj)
  have q25_420 : ∀ j, j < 32 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) := fun j hj => (K25.range (by decide) (by decide) j hj).trans (q24_420 j hj)
  have q25_440 : ∀ j, j < 32 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0x440 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B78) + BitVec.ofNat 32 j) := fun j hj => (K25.range (by decide) (by decide) j hj).trans (q24_440 j hj)
  have q25_1020 : ∀ j, j < 32 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1020 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B78) + BitVec.ofNat 32 j) := fun j hj => (K25.range (by decide) (by decide) j hj).trans (q24_1020 j hj)
  have a25_2a0 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K25.acc (by decide) (by decide)).trans a24_2a0
  have a25_2c0 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K25.acc (by decide) (by decide)).trans a24_2c0
  have a25_2e0 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K25.acc (by decide) (by decide)).trans a24_2e0
  have a25_320 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := (K25.acc (by decide) (by decide)).trans a24_320
  have a25_420 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := (K25.acc (by decide) (by decide)).trans a24_420
  have a25_440 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := (K25.acc (by decide) (by decide)).trans a24_440
  have a25_1020 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := (K25.acc (by decide) (by decide)).trans a24_1020
  have a25_1380 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = Z := (K25.acc (by decide) (by decide)).trans a24_1380
  have a25_1480 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = 0 := (K25.acc (by decide) (by decide)).trans a24_1480
  have a25_14c0 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x14C0) 8 = Z := (K25.acc (by decide) (by decide)).trans a24_14c0
  have a25_15a8 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := (K25.acc (by decide) (by decide)).trans a24_15a8
  have a25_15c8 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := (K25.acc (by decide) (by decide)).trans a24_15c8
  have a25_15e8 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x15E8) 8 = Z := (K25.acc (by decide) (by decide)).trans a24_15e8
  clear a24_1020 q24_1020 a24_15e8 a24_15c8 a24_15a8 a24_14c0 a24_1480 a24_1380 a24_440 a24_420 a24_320 a24_2e0 a24_2c0 a24_2a0 q24_440 q24_420 q24_320 b24_14a0 b24_13a0 b24_340 w24_464 w24_460 w24_130 w24_12c w24_128 w24_124 w24_120 w24_11c w24_118 w24_114 w24_110 w24_10c w24_108 w24_104 w24_100 w24_fc w24_f8 w24_f4 w24_f0 w24_ec w24_e8 w24_e4 w24_e0 w24_dc w24_d8 w24_d4 w24_d0 w24_cc w24_c8 w24_c4 w24_c0 w24_bc w24_b8 w24_b4 w24_b0 w24_ac w24_a8 w24_a4 w24_a0 w24_9c w24_98 w24_94 w24_90 w24_8c w24_88 w24_84 w24_80 w24_7c w24_70 w24_6c w24_68 w24_64 w24_60 w24_5c w24_58 w24_54 w24_50 w24_4c w24_48 w24_44 w24_40 w24_3c w24_38 w24_34 w24_30 w24_2c w24_28 w24_24 w24_20 g24_27 g24_26 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 s24 X24 K24 P24
  -- 0x1B46: sb
  obtain ⟨n26, d26, s26, fr26, K26, W26, rg26⟩ := sv_sb F E25 s25 sv_at_1b46 (off' := 0x1B4A) (c := 0x1040)
    (by decide) (by rw [g25_27]; sv_addr) (by decide)
  have t26 : Steps n0 n26 := t25.trans d26
  have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
  have E26 : SvCode n26.mem := E25.fr F fr26
  have V26 : SvSaves B n26.mem v := V25.keep K26 (by decide)
  have g26_2 : reg n26 sp = B + 0x21A0 := by rw [rg26 sp, g25_2]
  have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg26 (3 : Fin 32), g25_3]
  have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg26 (4 : Fin 32), g25_4]
  have g26_8 : reg n26 (8 : Fin 32) = BitVec.ofNat 32 0x3FCC4B78 := by rw [rg26 (8 : Fin 32), g25_8]
  have g26_18 : reg n26 (18 : Fin 32) = out := by rw [rg26 (18 : Fin 32), g25_18]
  have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [rg26 (19 : Fin 32), g25_19]
  have g26_20 : reg n26 (20 : Fin 32) = BitVec.ofNat 32 0x60 := by rw [rg26 (20 : Fin 32), g25_20]
  have g26_21 : reg n26 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [rg26 (21 : Fin 32), g25_21]
  have g26_22 : reg n26 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x15E8 := by rw [rg26 (22 : Fin 32), g25_22]
  have g26_23 : reg n26 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC4B38 := by rw [rg26 (23 : Fin 32), g25_23]
  have g26_24 : reg n26 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA60 := by rw [rg26 (24 : Fin 32), g25_24]
  have g26_26 : reg n26 (26 : Fin 32) = x26 := by rw [rg26 (26 : Fin 32), g25_26]
  have g26_27 : reg n26 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg26 (27 : Fin 32), g25_27]
  have w26_20 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = ((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF := (K26.w32 (by decide) (by decide)).trans w25_20
  have w26_24 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K26.w32 (by decide) (by decide)).trans w25_24
  have w26_28 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K26.w32 (by decide) (by decide)).trans w25_28
  have w26_2c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K26.w32 (by decide) (by decide)).trans w25_2c
  have w26_30 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K26.w32 (by decide) (by decide)).trans w25_30
  have w26_34 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K26.w32 (by decide) (by decide)).trans w25_34
  have w26_38 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = BitVec.ofNat 32 0x0 := (K26.w32 (by decide) (by decide)).trans w25_38
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
  have w26_460 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := (K26.w32 (by decide) (by decide)).trans w25_460
  have w26_464 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := (K26.w32 (by decide) (by decide)).trans w25_464
  have b26_340 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K26.b8 (by decide) (by decide)).trans b25_340
  have b26_13a0 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K26.b8 (by decide) (by decide)).trans b25_13a0
  have b26_14a0 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = 0 := (K26.b8 (by decide) (by decide)).trans b25_14a0
  have b26_1040 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [W26, s25.zero]; rfl
  have q26_320 : ∀ j, j < 32 → n26.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) := fun j hj => (K26.range (by decide) (by decide) j hj).trans (q25_320 j hj)
  have q26_420 : ∀ j, j < 32 → n26.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) := fun j hj => (K26.range (by decide) (by decide) j hj).trans (q25_420 j hj)
  have q26_440 : ∀ j, j < 32 → n26.mem (B + 0x21A0 + BitVec.ofNat 32 (0x440 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B78) + BitVec.ofNat 32 j) := fun j hj => (K26.range (by decide) (by decide) j hj).trans (q25_440 j hj)
  have q26_1020 : ∀ j, j < 32 → n26.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1020 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B78) + BitVec.ofNat 32 j) := fun j hj => (K26.range (by decide) (by decide) j hj).trans (q25_1020 j hj)
  have a26_2a0 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K26.acc (by decide) (by decide)).trans a25_2a0
  have a26_2c0 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K26.acc (by decide) (by decide)).trans a25_2c0
  have a26_2e0 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K26.acc (by decide) (by decide)).trans a25_2e0
  have a26_320 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := (K26.acc (by decide) (by decide)).trans a25_320
  have a26_420 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := (K26.acc (by decide) (by decide)).trans a25_420
  have a26_440 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := (K26.acc (by decide) (by decide)).trans a25_440
  have a26_1020 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := (K26.acc (by decide) (by decide)).trans a25_1020
  have a26_1380 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = Z := (K26.acc (by decide) (by decide)).trans a25_1380
  have a26_1480 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = 0 := (K26.acc (by decide) (by decide)).trans a25_1480
  have a26_14c0 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x14C0) 8 = Z := (K26.acc (by decide) (by decide)).trans a25_14c0
  have a26_15a8 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := (K26.acc (by decide) (by decide)).trans a25_15a8
  have a26_15c8 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := (K26.acc (by decide) (by decide)).trans a25_15c8
  have a26_15e8 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x15E8) 8 = Z := (K26.acc (by decide) (by decide)).trans a25_15e8
  clear a25_15e8 a25_15c8 a25_15a8 a25_14c0 a25_1480 a25_1380 a25_1020 a25_440 a25_420 a25_320 a25_2e0 a25_2c0 a25_2a0 q25_1020 q25_440 q25_420 q25_320 w25_38 b25_14a0 b25_13a0 b25_340 w25_464 w25_460 w25_130 w25_12c w25_128 w25_124 w25_120 w25_11c w25_118 w25_114 w25_110 w25_10c w25_108 w25_104 w25_100 w25_fc w25_f8 w25_f4 w25_f0 w25_ec w25_e8 w25_e4 w25_e0 w25_dc w25_d8 w25_d4 w25_d0 w25_cc w25_c8 w25_c4 w25_c0 w25_bc w25_b8 w25_b4 w25_b0 w25_ac w25_a8 w25_a4 w25_a0 w25_9c w25_98 w25_94 w25_90 w25_8c w25_88 w25_84 w25_80 w25_7c w25_70 w25_6c w25_68 w25_64 w25_60 w25_5c w25_58 w25_54 w25_50 w25_4c w25_48 w25_44 w25_40 w25_3c w25_34 w25_30 w25_2c w25_28 w25_24 w25_20 g25_27 g25_26 g25_24 g25_23 g25_22 g25_21 g25_20 g25_19 g25_18 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 rg25 W25 K25 fr25 s25 d25
  -- 0x1B4A
  obtain ⟨n27, c27, u27⟩ := s26.block svZS1b4a E26.self svZS1b4a_end
    ⟨trivial, trivial⟩
  have m27 : n27.mem = n26.mem := u27.mem
  have s27 : St n27.mem SV n27 0x1B4C (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
  have rb27 : ∀ q, reg n27 q = (runBlock svZS1b4a (n26.mem, reg n26)).2 q := fun q => by rw [u27.regs]
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
  have g27_8 : reg n27 (8 : Fin 32) = BitVec.ofNat 32 0x3FCC4B78 := by
    rw [rb27, runBlock_reg _ _ _ (8 : Fin 32) s26.zero (by decide), g26_8]
  have g27_18 : reg n27 (18 : Fin 32) = out := by
    rw [rb27, runBlock_reg _ _ _ (18 : Fin 32) s26.zero (by decide), g26_18]
  have g27_19 : reg n27 (19 : Fin 32) = bp := by
    rw [rb27, runBlock_reg _ _ _ (19 : Fin 32) s26.zero (by decide), g26_19]
  have g27_20 : reg n27 (20 : Fin 32) = BitVec.ofNat 32 0x60 := by
    rw [rb27, runBlock_reg _ _ _ (20 : Fin 32) s26.zero (by decide), g26_20]
  have g27_21 : reg n27 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by
    rw [rb27, runBlock_reg _ _ _ (21 : Fin 32) s26.zero (by decide), g26_21]
  have g27_22 : reg n27 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x15E8 := by
    rw [rb27, runBlock_reg _ _ _ (22 : Fin 32) s26.zero (by decide), g26_22]
  have g27_23 : reg n27 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC4B38 := by
    rw [rb27, runBlock_reg _ _ _ (23 : Fin 32) s26.zero (by decide), g26_23]
  have g27_24 : reg n27 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA60 := by
    rw [rb27, runBlock_reg _ _ _ (24 : Fin 32) s26.zero (by decide), g26_24]
  have g27_26 : reg n27 (26 : Fin 32) = x26 := by
    rw [rb27, runBlock_reg _ _ _ (26 : Fin 32) s26.zero (by decide), g26_26]
  have g27_27 : reg n27 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb27, runBlock_reg _ _ _ (27 : Fin 32) s26.zero (by decide), g26_27]
  have g27_10 : reg n27 a0 = BitVec.ofNat 32 0x1 := by
    rw [rb27]; simp +decide only [runBlock, BInstr.run, svZS1b4a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g26_2, g26_3, g26_4, g26_8, g26_18, g26_19, g26_20, g26_21, g26_22, g26_23, g26_24, g26_26, g26_27, s26.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w27_20 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = ((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF := by rw [m27]; exact w26_20
  have w27_24 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m27]; exact w26_24
  have w27_28 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m27]; exact w26_28
  have w27_2c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m27]; exact w26_2c
  have w27_30 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m27]; exact w26_30
  have w27_34 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m27]; exact w26_34
  have w27_38 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = BitVec.ofNat 32 0x0 := by rw [m27]; exact w26_38
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
  have w27_460 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m27]; exact w26_460
  have w27_464 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m27]; exact w26_464
  have b27_340 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m27]; exact b26_340
  have b27_1040 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m27]; exact b26_1040
  have b27_13a0 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m27]; exact b26_13a0
  have b27_14a0 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = 0 := by rw [m27]; exact b26_14a0
  have q27_320 : ∀ j, j < 32 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) := fun j hj => by rw [m27]; exact q26_320 j hj
  have q27_420 : ∀ j, j < 32 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) := fun j hj => by rw [m27]; exact q26_420 j hj
  have q27_440 : ∀ j, j < 32 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0x440 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B78) + BitVec.ofNat 32 j) := fun j hj => by rw [m27]; exact q26_440 j hj
  have q27_1020 : ∀ j, j < 32 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1020 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B78) + BitVec.ofNat 32 j) := fun j hj => by rw [m27]; exact q26_1020 j hj
  have a27_2a0 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m27]; exact a26_2a0
  have a27_2c0 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m27]; exact a26_2c0
  have a27_2e0 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m27]; exact a26_2e0
  have a27_320 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := by rw [m27]; exact a26_320
  have a27_420 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := by rw [m27]; exact a26_420
  have a27_440 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := by rw [m27]; exact a26_440
  have a27_1020 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := by rw [m27]; exact a26_1020
  have a27_1380 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = Z := by rw [m27]; exact a26_1380
  have a27_1480 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = 0 := by rw [m27]; exact a26_1480
  have a27_14c0 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x14C0) 8 = Z := by rw [m27]; exact a26_14c0
  have a27_15a8 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := by rw [m27]; exact a26_15a8
  have a27_15c8 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := by rw [m27]; exact a26_15c8
  have a27_15e8 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x15E8) 8 = Z := by rw [m27]; exact a26_15e8
  clear a26_15e8 a26_15c8 a26_15a8 a26_14c0 a26_1480 a26_1380 a26_1020 a26_440 a26_420 a26_320 a26_2e0 a26_2c0 a26_2a0 q26_1020 q26_440 q26_420 q26_320 b26_1040 b26_14a0 b26_13a0 b26_340 w26_464 w26_460 w26_130 w26_12c w26_128 w26_124 w26_120 w26_11c w26_118 w26_114 w26_110 w26_10c w26_108 w26_104 w26_100 w26_fc w26_f8 w26_f4 w26_f0 w26_ec w26_e8 w26_e4 w26_e0 w26_dc w26_d8 w26_d4 w26_d0 w26_cc w26_c8 w26_c4 w26_c0 w26_bc w26_b8 w26_b4 w26_b0 w26_ac w26_a8 w26_a4 w26_a0 w26_9c w26_98 w26_94 w26_90 w26_8c w26_88 w26_84 w26_80 w26_7c w26_70 w26_6c w26_68 w26_64 w26_60 w26_5c w26_58 w26_54 w26_50 w26_4c w26_48 w26_44 w26_40 w26_3c w26_38 w26_34 w26_30 w26_2c w26_28 w26_24 w26_20 g26_27 g26_26 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 rg26 W26 K26 fr26 s26 d26
  -- 0x1B4C: sw
  obtain ⟨n28, d28, s28, fr28, K28, W28, rg28⟩ := sv_sw F E27 s27 sv_at_1b4c (off' := 0x1B4E) (c := 0x34)
    (by decide) (by rw [g27_2]; sv_addr) (by decide) (by decide)
  have t28 : Steps n0 n28 := t27.trans d28
  have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
  have E28 : SvCode n28.mem := E27.fr F fr28
  have V28 : SvSaves B n28.mem v := V27.keep K28 (by decide)
  have g28_2 : reg n28 sp = B + 0x21A0 := by rw [rg28 sp, g27_2]
  have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg28 (3 : Fin 32), g27_3]
  have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg28 (4 : Fin 32), g27_4]
  have g28_8 : reg n28 (8 : Fin 32) = BitVec.ofNat 32 0x3FCC4B78 := by rw [rg28 (8 : Fin 32), g27_8]
  have g28_10 : reg n28 a0 = BitVec.ofNat 32 0x1 := by rw [rg28 a0, g27_10]
  have g28_18 : reg n28 (18 : Fin 32) = out := by rw [rg28 (18 : Fin 32), g27_18]
  have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [rg28 (19 : Fin 32), g27_19]
  have g28_20 : reg n28 (20 : Fin 32) = BitVec.ofNat 32 0x60 := by rw [rg28 (20 : Fin 32), g27_20]
  have g28_21 : reg n28 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [rg28 (21 : Fin 32), g27_21]
  have g28_22 : reg n28 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x15E8 := by rw [rg28 (22 : Fin 32), g27_22]
  have g28_23 : reg n28 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC4B38 := by rw [rg28 (23 : Fin 32), g27_23]
  have g28_24 : reg n28 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA60 := by rw [rg28 (24 : Fin 32), g27_24]
  have g28_26 : reg n28 (26 : Fin 32) = x26 := by rw [rg28 (26 : Fin 32), g27_26]
  have g28_27 : reg n28 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg28 (27 : Fin 32), g27_27]
  have w28_20 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = ((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF := (K28.w32 (by decide) (by decide)).trans w27_20
  have w28_24 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K28.w32 (by decide) (by decide)).trans w27_24
  have w28_28 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K28.w32 (by decide) (by decide)).trans w27_28
  have w28_2c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K28.w32 (by decide) (by decide)).trans w27_2c
  have w28_30 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K28.w32 (by decide) (by decide)).trans w27_30
  have w28_38 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = BitVec.ofNat 32 0x0 := (K28.w32 (by decide) (by decide)).trans w27_38
  have w28_3c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K28.w32 (by decide) (by decide)).trans w27_3c
  have w28_40 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K28.w32 (by decide) (by decide)).trans w27_40
  have w28_44 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K28.w32 (by decide) (by decide)).trans w27_44
  have w28_48 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K28.w32 (by decide) (by decide)).trans w27_48
  have w28_4c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K28.w32 (by decide) (by decide)).trans w27_4c
  have w28_50 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K28.w32 (by decide) (by decide)).trans w27_50
  have w28_54 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K28.w32 (by decide) (by decide)).trans w27_54
  have w28_58 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K28.w32 (by decide) (by decide)).trans w27_58
  have w28_5c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K28.w32 (by decide) (by decide)).trans w27_5c
  have w28_60 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K28.w32 (by decide) (by decide)).trans w27_60
  have w28_64 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K28.w32 (by decide) (by decide)).trans w27_64
  have w28_68 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K28.w32 (by decide) (by decide)).trans w27_68
  have w28_6c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K28.w32 (by decide) (by decide)).trans w27_6c
  have w28_70 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K28.w32 (by decide) (by decide)).trans w27_70
  have w28_7c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K28.w32 (by decide) (by decide)).trans w27_7c
  have w28_80 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K28.w32 (by decide) (by decide)).trans w27_80
  have w28_84 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K28.w32 (by decide) (by decide)).trans w27_84
  have w28_88 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 := (K28.w32 (by decide) (by decide)).trans w27_88
  have w28_8c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c := (K28.w32 (by decide) (by decide)).trans w27_8c
  have w28_90 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 := (K28.w32 (by decide) (by decide)).trans w27_90
  have w28_94 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 := (K28.w32 (by decide) (by decide)).trans w27_94
  have w28_98 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 := (K28.w32 (by decide) (by decide)).trans w27_98
  have w28_9c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c := (K28.w32 (by decide) (by decide)).trans w27_9c
  have w28_a0 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 := (K28.w32 (by decide) (by decide)).trans w27_a0
  have w28_a4 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 := (K28.w32 (by decide) (by decide)).trans w27_a4
  have w28_a8 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 := (K28.w32 (by decide) (by decide)).trans w27_a8
  have w28_ac : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac := (K28.w32 (by decide) (by decide)).trans w27_ac
  have w28_b0 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 := (K28.w32 (by decide) (by decide)).trans w27_b0
  have w28_b4 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 := (K28.w32 (by decide) (by decide)).trans w27_b4
  have w28_b8 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 := (K28.w32 (by decide) (by decide)).trans w27_b8
  have w28_bc : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc := (K28.w32 (by decide) (by decide)).trans w27_bc
  have w28_c0 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 := (K28.w32 (by decide) (by decide)).trans w27_c0
  have w28_c4 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 := (K28.w32 (by decide) (by decide)).trans w27_c4
  have w28_c8 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 := (K28.w32 (by decide) (by decide)).trans w27_c8
  have w28_cc : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc := (K28.w32 (by decide) (by decide)).trans w27_cc
  have w28_d0 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 := (K28.w32 (by decide) (by decide)).trans w27_d0
  have w28_d4 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 := (K28.w32 (by decide) (by decide)).trans w27_d4
  have w28_d8 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 := (K28.w32 (by decide) (by decide)).trans w27_d8
  have w28_dc : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc := (K28.w32 (by decide) (by decide)).trans w27_dc
  have w28_e0 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 := (K28.w32 (by decide) (by decide)).trans w27_e0
  have w28_e4 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 := (K28.w32 (by decide) (by decide)).trans w27_e4
  have w28_e8 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 := (K28.w32 (by decide) (by decide)).trans w27_e8
  have w28_ec : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec := (K28.w32 (by decide) (by decide)).trans w27_ec
  have w28_f0 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 := (K28.w32 (by decide) (by decide)).trans w27_f0
  have w28_f4 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 := (K28.w32 (by decide) (by decide)).trans w27_f4
  have w28_f8 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 := (K28.w32 (by decide) (by decide)).trans w27_f8
  have w28_fc : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc := (K28.w32 (by decide) (by decide)).trans w27_fc
  have w28_100 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 := (K28.w32 (by decide) (by decide)).trans w27_100
  have w28_104 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 := (K28.w32 (by decide) (by decide)).trans w27_104
  have w28_108 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 := (K28.w32 (by decide) (by decide)).trans w27_108
  have w28_10c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c := (K28.w32 (by decide) (by decide)).trans w27_10c
  have w28_110 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 := (K28.w32 (by decide) (by decide)).trans w27_110
  have w28_114 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 := (K28.w32 (by decide) (by decide)).trans w27_114
  have w28_118 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 := (K28.w32 (by decide) (by decide)).trans w27_118
  have w28_11c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c := (K28.w32 (by decide) (by decide)).trans w27_11c
  have w28_120 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 := (K28.w32 (by decide) (by decide)).trans w27_120
  have w28_124 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 := (K28.w32 (by decide) (by decide)).trans w27_124
  have w28_128 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 := (K28.w32 (by decide) (by decide)).trans w27_128
  have w28_12c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c := (K28.w32 (by decide) (by decide)).trans w27_12c
  have w28_130 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 := (K28.w32 (by decide) (by decide)).trans w27_130
  have w28_460 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := (K28.w32 (by decide) (by decide)).trans w27_460
  have w28_464 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := (K28.w32 (by decide) (by decide)).trans w27_464
  have b28_340 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K28.b8 (by decide) (by decide)).trans b27_340
  have b28_1040 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K28.b8 (by decide) (by decide)).trans b27_1040
  have b28_13a0 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K28.b8 (by decide) (by decide)).trans b27_13a0
  have b28_14a0 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = 0 := (K28.b8 (by decide) (by decide)).trans b27_14a0
  have w28_34 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = BitVec.ofNat 32 0x1 := by rw [W28, g27_10]
  have q28_320 : ∀ j, j < 32 → n28.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) := fun j hj => (K28.range (by decide) (by decide) j hj).trans (q27_320 j hj)
  have q28_420 : ∀ j, j < 32 → n28.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) := fun j hj => (K28.range (by decide) (by decide) j hj).trans (q27_420 j hj)
  have q28_440 : ∀ j, j < 32 → n28.mem (B + 0x21A0 + BitVec.ofNat 32 (0x440 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B78) + BitVec.ofNat 32 j) := fun j hj => (K28.range (by decide) (by decide) j hj).trans (q27_440 j hj)
  have q28_1020 : ∀ j, j < 32 → n28.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1020 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B78) + BitVec.ofNat 32 j) := fun j hj => (K28.range (by decide) (by decide) j hj).trans (q27_1020 j hj)
  have a28_2a0 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K28.acc (by decide) (by decide)).trans a27_2a0
  have a28_2c0 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K28.acc (by decide) (by decide)).trans a27_2c0
  have a28_2e0 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K28.acc (by decide) (by decide)).trans a27_2e0
  have a28_320 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := (K28.acc (by decide) (by decide)).trans a27_320
  have a28_420 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := (K28.acc (by decide) (by decide)).trans a27_420
  have a28_440 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := (K28.acc (by decide) (by decide)).trans a27_440
  have a28_1020 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := (K28.acc (by decide) (by decide)).trans a27_1020
  have a28_1380 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = Z := (K28.acc (by decide) (by decide)).trans a27_1380
  have a28_1480 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = 0 := (K28.acc (by decide) (by decide)).trans a27_1480
  have a28_14c0 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x14C0) 8 = Z := (K28.acc (by decide) (by decide)).trans a27_14c0
  have a28_15a8 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := (K28.acc (by decide) (by decide)).trans a27_15a8
  have a28_15c8 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := (K28.acc (by decide) (by decide)).trans a27_15c8
  have a28_15e8 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x15E8) 8 = Z := (K28.acc (by decide) (by decide)).trans a27_15e8
  clear a27_15e8 a27_15c8 a27_15a8 a27_14c0 a27_1480 a27_1380 a27_1020 a27_440 a27_420 a27_320 a27_2e0 a27_2c0 a27_2a0 q27_1020 q27_440 q27_420 q27_320 b27_14a0 b27_13a0 b27_1040 b27_340 w27_464 w27_460 w27_130 w27_12c w27_128 w27_124 w27_120 w27_11c w27_118 w27_114 w27_110 w27_10c w27_108 w27_104 w27_100 w27_fc w27_f8 w27_f4 w27_f0 w27_ec w27_e8 w27_e4 w27_e0 w27_dc w27_d8 w27_d4 w27_d0 w27_cc w27_c8 w27_c4 w27_c0 w27_bc w27_b8 w27_b4 w27_b0 w27_ac w27_a8 w27_a4 w27_a0 w27_9c w27_98 w27_94 w27_90 w27_8c w27_88 w27_84 w27_80 w27_7c w27_70 w27_6c w27_68 w27_64 w27_60 w27_5c w27_58 w27_54 w27_50 w27_4c w27_48 w27_44 w27_40 w27_3c w27_38 w27_34 w27_30 w27_2c w27_28 w27_24 w27_20 g27_10 g27_27 g27_26 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 rb27 s27 m27 u27 c27
  -- 0x1B4E
  obtain ⟨n29, c29, u29⟩ := s28.block svZS1b4e E28.self svZS1b4e_end
    ⟨trivial, trivial⟩
  have m29 : n29.mem = n28.mem := u29.mem
  have s29 : St n29.mem SV n29 0x1B52 (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
  have rb29 : ∀ q, reg n29 q = (runBlock svZS1b4e (n28.mem, reg n28)).2 q := fun q => by rw [u29.regs]
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
  have g29_8 : reg n29 (8 : Fin 32) = BitVec.ofNat 32 0x3FCC4B78 := by
    rw [rb29, runBlock_reg _ _ _ (8 : Fin 32) s28.zero (by decide), g28_8]
  have g29_18 : reg n29 (18 : Fin 32) = out := by
    rw [rb29, runBlock_reg _ _ _ (18 : Fin 32) s28.zero (by decide), g28_18]
  have g29_19 : reg n29 (19 : Fin 32) = bp := by
    rw [rb29, runBlock_reg _ _ _ (19 : Fin 32) s28.zero (by decide), g28_19]
  have g29_20 : reg n29 (20 : Fin 32) = BitVec.ofNat 32 0x60 := by
    rw [rb29, runBlock_reg _ _ _ (20 : Fin 32) s28.zero (by decide), g28_20]
  have g29_21 : reg n29 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by
    rw [rb29, runBlock_reg _ _ _ (21 : Fin 32) s28.zero (by decide), g28_21]
  have g29_22 : reg n29 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x15E8 := by
    rw [rb29, runBlock_reg _ _ _ (22 : Fin 32) s28.zero (by decide), g28_22]
  have g29_23 : reg n29 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC4B38 := by
    rw [rb29, runBlock_reg _ _ _ (23 : Fin 32) s28.zero (by decide), g28_23]
  have g29_24 : reg n29 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA60 := by
    rw [rb29, runBlock_reg _ _ _ (24 : Fin 32) s28.zero (by decide), g28_24]
  have g29_26 : reg n29 (26 : Fin 32) = x26 := by
    rw [rb29, runBlock_reg _ _ _ (26 : Fin 32) s28.zero (by decide), g28_26]
  have g29_27 : reg n29 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb29, runBlock_reg _ _ _ (27 : Fin 32) s28.zero (by decide), g28_27]
  have g29_10 : reg n29 a0 = BitVec.ofNat 32 0x24F := by
    rw [rb29]; simp +decide only [runBlock, BInstr.run, svZS1b4e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g28_2, g28_3, g28_4, g28_8, g28_10, g28_18, g28_19, g28_20, g28_21, g28_22, g28_23, g28_24, g28_26, g28_27, s28.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w29_20 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = ((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF := by rw [m29]; exact w28_20
  have w29_24 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := by rw [m29]; exact w28_24
  have w29_28 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := by rw [m29]; exact w28_28
  have w29_2c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m29]; exact w28_2c
  have w29_30 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m29]; exact w28_30
  have w29_34 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = BitVec.ofNat 32 0x1 := by rw [m29]; exact w28_34
  have w29_38 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = BitVec.ofNat 32 0x0 := by rw [m29]; exact w28_38
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
  have w29_460 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m29]; exact w28_460
  have w29_464 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m29]; exact w28_464
  have b29_340 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m29]; exact b28_340
  have b29_1040 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m29]; exact b28_1040
  have b29_13a0 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := by rw [m29]; exact b28_13a0
  have b29_14a0 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = 0 := by rw [m29]; exact b28_14a0
  have q29_320 : ∀ j, j < 32 → n29.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) := fun j hj => by rw [m29]; exact q28_320 j hj
  have q29_420 : ∀ j, j < 32 → n29.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) := fun j hj => by rw [m29]; exact q28_420 j hj
  have q29_440 : ∀ j, j < 32 → n29.mem (B + 0x21A0 + BitVec.ofNat 32 (0x440 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B78) + BitVec.ofNat 32 j) := fun j hj => by rw [m29]; exact q28_440 j hj
  have q29_1020 : ∀ j, j < 32 → n29.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1020 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B78) + BitVec.ofNat 32 j) := fun j hj => by rw [m29]; exact q28_1020 j hj
  have a29_2a0 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m29]; exact a28_2a0
  have a29_2c0 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m29]; exact a28_2c0
  have a29_2e0 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m29]; exact a28_2e0
  have a29_320 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := by rw [m29]; exact a28_320
  have a29_420 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := by rw [m29]; exact a28_420
  have a29_440 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := by rw [m29]; exact a28_440
  have a29_1020 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := by rw [m29]; exact a28_1020
  have a29_1380 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = Z := by rw [m29]; exact a28_1380
  have a29_1480 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = 0 := by rw [m29]; exact a28_1480
  have a29_14c0 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x14C0) 8 = Z := by rw [m29]; exact a28_14c0
  have a29_15a8 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := by rw [m29]; exact a28_15a8
  have a29_15c8 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := by rw [m29]; exact a28_15c8
  have a29_15e8 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x15E8) 8 = Z := by rw [m29]; exact a28_15e8
  clear a28_15e8 a28_15c8 a28_15a8 a28_14c0 a28_1480 a28_1380 a28_1020 a28_440 a28_420 a28_320 a28_2e0 a28_2c0 a28_2a0 q28_1020 q28_440 q28_420 q28_320 w28_34 b28_14a0 b28_13a0 b28_1040 b28_340 w28_464 w28_460 w28_130 w28_12c w28_128 w28_124 w28_120 w28_11c w28_118 w28_114 w28_110 w28_10c w28_108 w28_104 w28_100 w28_fc w28_f8 w28_f4 w28_f0 w28_ec w28_e8 w28_e4 w28_e0 w28_dc w28_d8 w28_d4 w28_d0 w28_cc w28_c8 w28_c4 w28_c0 w28_bc w28_b8 w28_b4 w28_b0 w28_ac w28_a8 w28_a4 w28_a0 w28_9c w28_98 w28_94 w28_90 w28_8c w28_88 w28_84 w28_80 w28_7c w28_70 w28_6c w28_68 w28_64 w28_60 w28_5c w28_58 w28_54 w28_50 w28_4c w28_48 w28_44 w28_40 w28_3c w28_38 w28_30 w28_2c w28_28 w28_24 w28_20 g28_27 g28_26 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_10 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 rg28 W28 K28 fr28 s28 d28
  -- 0x1B52: sw
  obtain ⟨n30, d30, s30, fr30, K30, W30, rg30⟩ := sv_sw F E29 s29 sv_at_1b52 (off' := 0x1B54) (c := 0x78)
    (by decide) (by rw [g29_2]; sv_addr) (by decide) (by decide)
  have t30 : Steps n0 n30 := t29.trans d30
  have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
  have E30 : SvCode n30.mem := E29.fr F fr30
  have V30 : SvSaves B n30.mem v := V29.keep K30 (by decide)
  have g30_2 : reg n30 sp = B + 0x21A0 := by rw [rg30 sp, g29_2]
  have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg30 (3 : Fin 32), g29_3]
  have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg30 (4 : Fin 32), g29_4]
  have g30_8 : reg n30 (8 : Fin 32) = BitVec.ofNat 32 0x3FCC4B78 := by rw [rg30 (8 : Fin 32), g29_8]
  have g30_10 : reg n30 a0 = BitVec.ofNat 32 0x24F := by rw [rg30 a0, g29_10]
  have g30_18 : reg n30 (18 : Fin 32) = out := by rw [rg30 (18 : Fin 32), g29_18]
  have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [rg30 (19 : Fin 32), g29_19]
  have g30_20 : reg n30 (20 : Fin 32) = BitVec.ofNat 32 0x60 := by rw [rg30 (20 : Fin 32), g29_20]
  have g30_21 : reg n30 (21 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [rg30 (21 : Fin 32), g29_21]
  have g30_22 : reg n30 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x15E8 := by rw [rg30 (22 : Fin 32), g29_22]
  have g30_23 : reg n30 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC4B38 := by rw [rg30 (23 : Fin 32), g29_23]
  have g30_24 : reg n30 (24 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA60 := by rw [rg30 (24 : Fin 32), g29_24]
  have g30_26 : reg n30 (26 : Fin 32) = x26 := by rw [rg30 (26 : Fin 32), g29_26]
  have g30_27 : reg n30 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg30 (27 : Fin 32), g29_27]
  have w30_20 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = ((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF := (K30.w32 (by decide) (by decide)).trans w29_20
  have w30_24 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 := (K30.w32 (by decide) (by decide)).trans w29_24
  have w30_28 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 := (K30.w32 (by decide) (by decide)).trans w29_28
  have w30_2c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K30.w32 (by decide) (by decide)).trans w29_2c
  have w30_30 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K30.w32 (by decide) (by decide)).trans w29_30
  have w30_34 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = BitVec.ofNat 32 0x1 := (K30.w32 (by decide) (by decide)).trans w29_34
  have w30_38 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = BitVec.ofNat 32 0x0 := (K30.w32 (by decide) (by decide)).trans w29_38
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
  have w30_460 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := (K30.w32 (by decide) (by decide)).trans w29_460
  have w30_464 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := (K30.w32 (by decide) (by decide)).trans w29_464
  have b30_340 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K30.b8 (by decide) (by decide)).trans b29_340
  have b30_1040 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K30.b8 (by decide) (by decide)).trans b29_1040
  have b30_13a0 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = (BitVec.ofNat 32 0x0).extractLsb' 0 8 := (K30.b8 (by decide) (by decide)).trans b29_13a0
  have b30_14a0 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = 0 := (K30.b8 (by decide) (by decide)).trans b29_14a0
  have w30_78 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 0x24F := by rw [W30, g29_10]
  have q30_320 : ∀ j, j < 32 → n30.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) := fun j hj => (K30.range (by decide) (by decide) j hj).trans (q29_320 j hj)
  have q30_420 : ∀ j, j < 32 → n30.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B38) + BitVec.ofNat 32 j) := fun j hj => (K30.range (by decide) (by decide) j hj).trans (q29_420 j hj)
  have q30_440 : ∀ j, j < 32 → n30.mem (B + 0x21A0 + BitVec.ofNat 32 (0x440 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B78) + BitVec.ofNat 32 j) := fun j hj => (K30.range (by decide) (by decide) j hj).trans (q29_440 j hj)
  have q30_1020 : ∀ j, j < 32 → n30.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1020 + j)) = M0 ((BitVec.ofNat 32 0x3FCC4B78) + BitVec.ofNat 32 j) := fun j hj => (K30.range (by decide) (by decide) j hj).trans (q29_1020 j hj)
  have a30_2a0 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K30.acc (by decide) (by decide)).trans a29_2a0
  have a30_2c0 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K30.acc (by decide) (by decide)).trans a29_2c0
  have a30_2e0 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K30.acc (by decide) (by decide)).trans a29_2e0
  have a30_320 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := (K30.acc (by decide) (by decide)).trans a29_320
  have a30_420 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := (K30.acc (by decide) (by decide)).trans a29_420
  have a30_440 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := (K30.acc (by decide) (by decide)).trans a29_440
  have a30_1020 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := (K30.acc (by decide) (by decide)).trans a29_1020
  have a30_1380 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = Z := (K30.acc (by decide) (by decide)).trans a29_1380
  have a30_1480 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = 0 := (K30.acc (by decide) (by decide)).trans a29_1480
  have a30_14c0 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x14C0) 8 = Z := (K30.acc (by decide) (by decide)).trans a29_14c0
  have a30_15a8 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := (K30.acc (by decide) (by decide)).trans a29_15a8
  have a30_15c8 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := (K30.acc (by decide) (by decide)).trans a29_15c8
  have a30_15e8 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x15E8) 8 = Z := (K30.acc (by decide) (by decide)).trans a29_15e8
  clear a29_15e8 a29_15c8 a29_15a8 a29_14c0 a29_1480 a29_1380 a29_1020 a29_440 a29_420 a29_320 a29_2e0 a29_2c0 a29_2a0 q29_1020 q29_440 q29_420 q29_320 b29_14a0 b29_13a0 b29_1040 b29_340 w29_464 w29_460 w29_130 w29_12c w29_128 w29_124 w29_120 w29_11c w29_118 w29_114 w29_110 w29_10c w29_108 w29_104 w29_100 w29_fc w29_f8 w29_f4 w29_f0 w29_ec w29_e8 w29_e4 w29_e0 w29_dc w29_d8 w29_d4 w29_d0 w29_cc w29_c8 w29_c4 w29_c0 w29_bc w29_b8 w29_b4 w29_b0 w29_ac w29_a8 w29_a4 w29_a0 w29_9c w29_98 w29_94 w29_90 w29_8c w29_88 w29_84 w29_80 w29_7c w29_70 w29_6c w29_68 w29_64 w29_60 w29_5c w29_58 w29_54 w29_50 w29_4c w29_48 w29_44 w29_40 w29_3c w29_38 w29_34 w29_30 w29_2c w29_28 w29_24 w29_20 g29_10 g29_27 g29_26 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 rb29 s29 m29 u29 c29
  exact .inr ⟨n30, t30, s30, E30, V30, fR30, g30_2, g30_3, g30_4, g30_18, g30_19, g30_20, g30_21, g30_22, g30_23, g30_24, g30_26, g30_27, w30_20, w30_24, w30_28, w30_2c, w30_30, w30_34, w30_38, w30_3c, w30_40, w30_44, w30_48, w30_4c, w30_50, w30_54, w30_58, w30_5c, w30_60, w30_64, w30_68, w30_6c, w30_70, w30_78, w30_7c, w30_80, w30_84, w30_88, w30_8c, w30_90, w30_94, w30_98, w30_9c, w30_a0, w30_a4, w30_a8, w30_ac, w30_b0, w30_b4, w30_b8, w30_bc, w30_c0, w30_c4, w30_c8, w30_cc, w30_d0, w30_d4, w30_d8, w30_dc, w30_e0, w30_e4, w30_e8, w30_ec, w30_f0, w30_f4, w30_f8, w30_fc, w30_100, w30_104, w30_108, w30_10c, w30_110, w30_114, w30_118, w30_11c, w30_120, w30_124, w30_128, w30_12c, w30_130, w30_460, w30_464, b30_340, b30_1040, b30_13a0, b30_14a0, q30_320, q30_420, q30_440, q30_1020, a30_2a0, a30_2c0, a30_2e0, a30_320, a30_420, a30_440, a30_1020, a30_1380, a30_1480, a30_14c0, a30_15a8, a30_15c8, a30_15e8⟩

end C3.RV32.Sv
