import C3BootProofs.Proofs.SvZLib

/-!
# `sigstore::verify`: the end of a batch of the inversion of `Z`

From the divstep loop's exit at 0x1D62 back to the head at 0x1B54: the batch's matrix is stored at 0x1320, `update_fg` applies it to `f` and `g` and `update_de` to `d` and `e` modulo the field's modulus at 0x420, and the steps left drop by the batch's size.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svZB1d62 : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x320, .alu .add a0 a0 sp]
theorem svZB1d62_end : blockEnd sigstoreVerifyCode 0x1D62 svZB1d62 = some 0x1D6A := by
  simp only [svZB1d62]
  rw [blockEnd, sv_at_1d62]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d64]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d68]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svZB1d8a : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x221, .aluImm .add a1 sp 0x320, .lui a2 0x1000, .aluImm .add a2 a2 0x380, .alu .add a2 a2 sp, .lui a3 0x1000, .aluImm .add a3 a3 0x320, .alu .add a3 a3 sp]
theorem svZB1d8a_end : blockEnd sigstoreVerifyCode 0x1D8A svZB1d8a = some 0x1DA4 := by
  simp only [svZB1d8a]
  rw [blockEnd, sv_at_1d8a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d8e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d92]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d94]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d96]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d9a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d9c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d9e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1da2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svZB1da6 : List BInstr :=
  [.alu .add a4 x0 (8 : Fin 32)]
theorem svZB1da6_end : blockEnd sigstoreVerifyCode 0x1DA6 svZB1da6 = some 0x1DA8 := by
  simp only [svZB1da6]
  rw [blockEnd, sv_at_1da6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svZB1db0 : List BInstr :=
  [.aluImm .add a0 sp 0x320, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x221, .aluImm .add a2 x0 0x24]
theorem svZB1db0_end : blockEnd sigstoreVerifyCode 0x1DB0 svZB1db0 = some 0x1DBE := by
  simp only [svZB1db0]
  rw [blockEnd, sv_at_1db0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1db2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1db6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1dba]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svZB1dc6 : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x380, .alu .add a0 a0 sp, .aluImm .add a2 x0 0x24, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x245]
theorem svZB1dc6_end : blockEnd sigstoreVerifyCode 0x1DC6 svZB1dc6 = some 0x1DDA := by
  simp only [svZB1dc6]
  rw [blockEnd, sv_at_1dc6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1dc8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1dcc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1dce]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1dd2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1dd6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svZB1de2 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x221, .lui a1 0x1000, .aluImm .add a1 a1 0x480, .alu .add a1 a1 sp, .lui a2 0x1000, .aluImm .add a2 a2 0x20, .alu .add a2 a2 sp, .aluImm .add a3 sp 0x420, .aluImm .add a4 x0 0xFFFFFFFF, .aluImm .add a5 x0 0xFFFFFFFF, .lui a6 0x1000, .aluImm .add a6 a6 0x320, .alu .add a6 a6 sp, .alu .add (17 : Fin 32) x0 (8 : Fin 32)]
theorem svZB1de2_end : blockEnd sigstoreVerifyCode 0x1DE2 svZB1de2 = some 0x1E0C := by
  simp only [svZB1de2]
  rw [blockEnd, sv_at_1de2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1de6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1dea]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1dec]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1df0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1df2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1df4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1df8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1dfa]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1dfe]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1e00]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1e02]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1e04]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1e08]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1e0a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svZB1e14 : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x480, .alu .add a0 a0 sp, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x221, .aluImm .add a2 x0 0x24]
theorem svZB1e14_end : blockEnd sigstoreVerifyCode 0x1E14 svZB1e14 = some 0x1E28 := by
  simp only [svZB1e14]
  rw [blockEnd, sv_at_1e14]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1e16]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1e1a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1e1c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1e20]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1e24]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svZB1e30 : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x20, .alu .add a0 a0 sp, .aluImm .add a2 x0 0x24, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x245]
theorem svZB1e30_end : blockEnd sigstoreVerifyCode 0x1E30 svZB1e30 = some 0x1E44 := by
  simp only [svZB1e30]
  rw [blockEnd, sv_at_1e30]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1e32]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1e36]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1e38]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1e3c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1e40]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svZB1e4e : List BInstr :=
  [.alu .sub a0 a0 (8 : Fin 32)]
theorem svZB1e4e_end : blockEnd sigstoreVerifyCode 0x1E4E svZB1e4e = some 0x1E50 := by
  simp only [svZB1e4e]
  rw [blockEnd, sv_at_1e4e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_zb {B out bp x26 dlo dhi rem nzw ulo uhi vlo vhi qlo qhi rlo rhi : Word} {ns : Nat} {fs gs ds es : BitVec 8} {rv sv zv X Y fv gv dv ev : Nat} {w4c w50 w54 w58 w64 w68 w6c w7c w80 w84 w88 w8c w90 w94 w98 w9c wa0 wa4 wa8 wac wb0 wb4 wb8 wbc wc0 wc4 wc8 wcc wd0 wd4 wd8 wdc we0 we4 we8 wec wf0 wf4 wf8 wfc w100 w104 w108 w10c w110 w114 w118 w11c w120 w124 w128 w12c w130 : Word} {v : Nat → Word} {n0 : Machine}
    (F : Fr B 0x3830) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x1D62 (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_26 : reg n0 (26 : Fin 32) = x26)
    (g0_27 : reg n0 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20)
    (w0_20 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = nzw)
    (w0_34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = dlo)
    (w0_38 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = dhi)
    (w0_4c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c)
    (w0_50 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50)
    (w0_54 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54)
    (w0_58 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58)
    (w0_64 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64)
    (w0_68 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68)
    (w0_6c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c)
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
    (w0_460 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF)
    (w0_464 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF)
    (a0_2a0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv)
    (a0_2c0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv)
    (a0_2e0 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv)
    (a0_320 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = fv)
    (a0_420 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)
    (a0_440 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8)
    (a0_1020 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = ev)
    (a0_1380 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = gv)
    (a0_1480 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = dv)
    (a0_15a8 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X)
    (a0_15c8 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y)
    (b0_340 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = fs)
    (b0_1040 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = es)
    (b0_13a0 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = gs)
    (b0_14a0 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = ds)
    (IC0 : SvIvCode M0)
    (EC0 : SvEcCode M0)
    (g0_24 : reg n0 (24 : Fin 32) = ulo)
    (w0_3c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = uhi)
    (w0_44 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = vlo)
    (w0_40 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = vhi)
    (w0_70 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = qlo)
    (w0_60 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = qhi)
    (w0_5c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rlo)
    (w0_74 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = rhi)
    (w0_1c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 ns)
    (hns1 : 1 ≤ ns)
    (hns2 : ns ≤ 62)
    (UC0 : SvUpCode M0)
    (hfs : fs.toNat ≤ 1)
    (hgs : gs.toNat ≤ 1)
    (hds : ds.toNat ≤ 1)
    (hes : es.toNat ≤ 1) :
    (¬ (∃ σ20a A20a, sgnVal σ20a A20a = sgnVal (fs).toNat (fv) * i64Val ((ulo).toNat + 2 ^ 32 * (uhi).toNat) + sgnVal (gs).toNat (gv) * i64Val ((vlo).toNat + 2 ^ 32 * (vhi).toNat) ∧ (σ20a ≤ 1) ∧ ∃ σ20b A20b, sgnVal σ20b A20b = sgnVal (fs).toNat (fv) * i64Val ((qlo).toNat + 2 ^ 32 * (qhi).toNat) + sgnVal (gs).toNat (gv) * i64Val ((rlo).toNat + 2 ^ 32 * (rhi).toNat) ∧ (σ20b ≤ 1) ∧ ∃ σ26a A26a, sgnVal σ26a A26a = sgnVal (ds).toNat (dv) * i64Val ((ulo).toNat + 2 ^ 32 * (uhi).toNat) + sgnVal (es).toNat (ev) * i64Val ((vlo).toNat + 2 ^ 32 * (vhi).toNat) ∧ (σ26a ≤ 1) ∧ ∃ σ26b A26b, sgnVal σ26b A26b = sgnVal (ds).toNat (dv) * i64Val ((qlo).toNat + 2 ^ 32 * (qhi).toNat) + sgnVal (es).toNat (ev) * i64Val ((rlo).toNat + 2 ^ 32 * (rhi).toNat) ∧ (σ26b ≤ 1) ∧ True) ∧ SvErrRet B out v n0) ∨
    (∃ σ20a A20a, sgnVal σ20a A20a = sgnVal (fs).toNat (fv) * i64Val ((ulo).toNat + 2 ^ 32 * (uhi).toNat) + sgnVal (gs).toNat (gv) * i64Val ((vlo).toNat + 2 ^ 32 * (vhi).toNat) ∧
    (σ20a ≤ 1) ∧
    ∃ σ20b A20b, sgnVal σ20b A20b = sgnVal (fs).toNat (fv) * i64Val ((qlo).toNat + 2 ^ 32 * (qhi).toNat) + sgnVal (gs).toNat (gv) * i64Val ((rlo).toNat + 2 ^ 32 * (rhi).toNat) ∧
    (σ20b ≤ 1) ∧
    ∃ σ26a A26a, sgnVal σ26a A26a = sgnVal (ds).toNat (dv) * i64Val ((ulo).toNat + 2 ^ 32 * (uhi).toNat) + sgnVal (es).toNat (ev) * i64Val ((vlo).toNat + 2 ^ 32 * (vhi).toNat) ∧
    (σ26a ≤ 1) ∧
    ∃ σ26b A26b, sgnVal σ26b A26b = sgnVal (ds).toNat (dv) * i64Val ((qlo).toNat + 2 ^ 32 * (qhi).toNat) + sgnVal (es).toNat (ev) * i64Val ((rlo).toNat + 2 ^ 32 * (rhi).toNat) ∧
    (σ26b ≤ 1) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x1B54 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 ns ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = nzw ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = dlo ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = dhi ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = uhi ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = vhi ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = vlo ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rlo ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = qhi ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = qlo ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = rhi ∧
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
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = ulo ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = uhi ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = vlo ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = vhi ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = qlo ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = qhi ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) = rlo ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x133C) = rhi ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = BitVec.ofNat 8 σ20a ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 8 (lrsm8 σ26a A26a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).1 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA64) = BitVec.ofNat 8 (lrsm8 σ26b A26b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).1 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = BitVec.ofNat 8 (lrsm8 σ26b A26b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).1 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = BitVec.ofNat 8 σ20b ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = BitVec.ofNat 8 (lrsm8 σ26a A26a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).1 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = A20a / 2 ^ ns % 2 ^ 256 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 8 = (lrsm8 σ26a A26a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).2 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) 8 = (lrsm8 σ26b A26b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).2 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = (lrsm8 σ26b A26b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).2 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = A20b / 2 ^ ns % 2 ^ 256 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = (lrsm8 σ26a A26a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).2 ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X ∧
        accV n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y ∧
        SvKeepL B n0.mem n'.mem [(0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4), (0x1338, 0x4), (0x133C, 0x4), (0xA20, 0x45), (0x320, 0x24), (0x1380, 0x24), (0xA20, 0x45), (0x1480, 0x24), (0x1020, 0x24), (0x78, 0x4)]) := by
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x1D62
  obtain ⟨n1, c1, u1⟩ := s0.block svZB1d62 E0.self svZB1d62_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have s1 : St n1.mem SV n1 0x1D6A (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have rb1 : ∀ q, reg n1 q = (runBlock svZB1d62 (n0.mem, reg n0)).2 q := fun q => by rw [u1.regs]
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
  have g1_24 : reg n1 (24 : Fin 32) = ulo := by
    rw [rb1, runBlock_reg _ _ _ (24 : Fin 32) s0.zero (by decide), g0_24]
  have g1_26 : reg n1 (26 : Fin 32) = x26 := by
    rw [rb1, runBlock_reg _ _ _ (26 : Fin 32) s0.zero (by decide), g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb1, runBlock_reg _ _ _ (27 : Fin 32) s0.zero (by decide), g0_27]
  have g1_10 : reg n1 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svZB1d62, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_18, g0_19, g0_24, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk1 : SvKeepL B n0.mem n1.mem [] := by rw [m1]; exact (SvKeepL.refl : SvKeepL B n0.mem n0.mem [])
  have w1_1c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 ns := by rw [m1]; exact w0_1c
  have w1_20 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = nzw := by rw [m1]; exact w0_20
  have w1_34 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = dlo := by rw [m1]; exact w0_34
  have w1_38 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = dhi := by rw [m1]; exact w0_38
  have w1_3c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = uhi := by rw [m1]; exact w0_3c
  have w1_40 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = vhi := by rw [m1]; exact w0_40
  have w1_44 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = vlo := by rw [m1]; exact w0_44
  have w1_4c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m1]; exact w0_4c
  have w1_50 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m1]; exact w0_50
  have w1_54 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m1]; exact w0_54
  have w1_58 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m1]; exact w0_58
  have w1_5c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rlo := by rw [m1]; exact w0_5c
  have w1_60 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = qhi := by rw [m1]; exact w0_60
  have w1_64 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m1]; exact w0_64
  have w1_68 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m1]; exact w0_68
  have w1_6c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m1]; exact w0_6c
  have w1_70 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = qlo := by rw [m1]; exact w0_70
  have w1_74 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = rhi := by rw [m1]; exact w0_74
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
  have w1_460 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m1]; exact w0_460
  have w1_464 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m1]; exact w0_464
  have b1_340 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = fs := by rw [m1]; exact b0_340
  have b1_1040 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = es := by rw [m1]; exact b0_1040
  have b1_13a0 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = gs := by rw [m1]; exact b0_13a0
  have b1_14a0 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = ds := by rw [m1]; exact b0_14a0
  have a1_2a0 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m1]; exact a0_2a0
  have a1_2c0 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m1]; exact a0_2c0
  have a1_2e0 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m1]; exact a0_2e0
  have a1_320 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = fv := by rw [m1]; exact a0_320
  have a1_420 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := by rw [m1]; exact a0_420
  have a1_440 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := by rw [m1]; exact a0_440
  have a1_1020 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = ev := by rw [m1]; exact a0_1020
  have a1_1380 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = gv := by rw [m1]; exact a0_1380
  have a1_1480 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = dv := by rw [m1]; exact a0_1480
  have a1_15a8 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := by rw [m1]; exact a0_15a8
  have a1_15c8 : accV n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := by rw [m1]; exact a0_15c8
  -- 0x1D6A: sw
  obtain ⟨n2, d2, s2, fr2, K2, W2, rg2⟩ := sv_sw F E1 s1 sv_at_1d6a (off' := 0x1D6E) (c := 0x1320)
    (by decide) (by rw [g1_10]; sv_addr) (by decide) (by decide)
  have t2 : Steps n0 n2 := t1.trans d2
  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.keep K2 (by decide)
  have g2_2 : reg n2 sp = B + 0x21A0 := by rw [rg2 sp, g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg2 (3 : Fin 32), g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg2 (4 : Fin 32), g1_4]
  have g2_10 : reg n2 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg2 a0, g1_10]
  have g2_18 : reg n2 (18 : Fin 32) = out := by rw [rg2 (18 : Fin 32), g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [rg2 (19 : Fin 32), g1_19]
  have g2_24 : reg n2 (24 : Fin 32) = ulo := by rw [rg2 (24 : Fin 32), g1_24]
  have g2_26 : reg n2 (26 : Fin 32) = x26 := by rw [rg2 (26 : Fin 32), g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg2 (27 : Fin 32), g1_27]
  have keep_kk2 : SvKeepL B n0.mem n2.mem [(0x1320, 0x4)] := keep_kk1.trans K2.toL
  clear keep_kk1
  have w2_1c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 ns := (K2.w32 (by decide) (by decide)).trans w1_1c
  have w2_20 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = nzw := (K2.w32 (by decide) (by decide)).trans w1_20
  have w2_34 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = dlo := (K2.w32 (by decide) (by decide)).trans w1_34
  have w2_38 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = dhi := (K2.w32 (by decide) (by decide)).trans w1_38
  have w2_3c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = uhi := (K2.w32 (by decide) (by decide)).trans w1_3c
  have w2_40 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = vhi := (K2.w32 (by decide) (by decide)).trans w1_40
  have w2_44 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = vlo := (K2.w32 (by decide) (by decide)).trans w1_44
  have w2_4c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K2.w32 (by decide) (by decide)).trans w1_4c
  have w2_50 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K2.w32 (by decide) (by decide)).trans w1_50
  have w2_54 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K2.w32 (by decide) (by decide)).trans w1_54
  have w2_58 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K2.w32 (by decide) (by decide)).trans w1_58
  have w2_5c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rlo := (K2.w32 (by decide) (by decide)).trans w1_5c
  have w2_60 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = qhi := (K2.w32 (by decide) (by decide)).trans w1_60
  have w2_64 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K2.w32 (by decide) (by decide)).trans w1_64
  have w2_68 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K2.w32 (by decide) (by decide)).trans w1_68
  have w2_6c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K2.w32 (by decide) (by decide)).trans w1_6c
  have w2_70 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = qlo := (K2.w32 (by decide) (by decide)).trans w1_70
  have w2_74 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = rhi := (K2.w32 (by decide) (by decide)).trans w1_74
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
  have w2_460 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := (K2.w32 (by decide) (by decide)).trans w1_460
  have w2_464 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := (K2.w32 (by decide) (by decide)).trans w1_464
  have b2_340 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = fs := (K2.b8 (by decide) (by decide)).trans b1_340
  have b2_1040 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = es := (K2.b8 (by decide) (by decide)).trans b1_1040
  have b2_13a0 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = gs := (K2.b8 (by decide) (by decide)).trans b1_13a0
  have b2_14a0 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = ds := (K2.b8 (by decide) (by decide)).trans b1_14a0
  have w2_1320 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = ulo := by rw [W2, g1_24]
  have a2_2a0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K2.acc (by decide) (by decide)).trans a1_2a0
  have a2_2c0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K2.acc (by decide) (by decide)).trans a1_2c0
  have a2_2e0 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K2.acc (by decide) (by decide)).trans a1_2e0
  have a2_320 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = fv := (K2.acc (by decide) (by decide)).trans a1_320
  have a2_420 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := (K2.acc (by decide) (by decide)).trans a1_420
  have a2_440 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := (K2.acc (by decide) (by decide)).trans a1_440
  have a2_1020 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = ev := (K2.acc (by decide) (by decide)).trans a1_1020
  have a2_1380 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = gv := (K2.acc (by decide) (by decide)).trans a1_1380
  have a2_1480 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = dv := (K2.acc (by decide) (by decide)).trans a1_1480
  have a2_15a8 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := (K2.acc (by decide) (by decide)).trans a1_15a8
  have a2_15c8 : accV n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := (K2.acc (by decide) (by decide)).trans a1_15c8
  clear a1_15c8 a1_15a8 a1_1480 a1_1380 a1_1020 a1_440 a1_420 a1_320 a1_2e0 a1_2c0 a1_2a0 b1_14a0 b1_13a0 b1_1040 b1_340 w1_464 w1_460 w1_130 w1_12c w1_128 w1_124 w1_120 w1_11c w1_118 w1_114 w1_110 w1_10c w1_108 w1_104 w1_100 w1_fc w1_f8 w1_f4 w1_f0 w1_ec w1_e8 w1_e4 w1_e0 w1_dc w1_d8 w1_d4 w1_d0 w1_cc w1_c8 w1_c4 w1_c0 w1_bc w1_b8 w1_b4 w1_b0 w1_ac w1_a8 w1_a4 w1_a0 w1_9c w1_98 w1_94 w1_90 w1_8c w1_88 w1_84 w1_80 w1_7c w1_78 w1_74 w1_70 w1_6c w1_68 w1_64 w1_60 w1_5c w1_58 w1_54 w1_50 w1_4c w1_44 w1_40 w1_3c w1_38 w1_34 w1_20 w1_1c g1_10 g1_27 g1_26 g1_24 g1_19 g1_18 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
  -- 0x1D6E: lw
  obtain ⟨n3, d3, u3⟩ := s2.lw E2.self sv_at_1d6e (off' := 0x1D70) (by decide)
    (by rw [g2_2, show B + 0x21A0 + 0x3C = B + 0x21A0 + BitVec.ofNat 32 0x3C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s3 : St n3.mem SV n3 0x1D70 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
  have t3 : Steps n0 n3 := t2.trans (.single d3)
  have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : SvCode n3.mem := E2.fr F fr3
  have V3 : SvSaves B n3.mem v := V2.same m3
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_4]
  have g3_10 : reg n3 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_10]
  have g3_18 : reg n3 (18 : Fin 32) = out := by rw [u3.regs, upd_ne (by decide) (by decide), g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_19]
  have g3_24 : reg n3 (24 : Fin 32) = ulo := by rw [u3.regs, upd_ne (by decide) (by decide), g2_24]
  have g3_26 : reg n3 (26 : Fin 32) = x26 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_27]
  have g3_11 : reg n3 a1 = uhi := by
    rw [u3.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g2_2, show B + 0x21A0 + 0x3C = B + 0x21A0 + BitVec.ofNat 32 0x3C by sv_addr, w2_3c]
  have keep_kk3 : SvKeepL B n0.mem n3.mem [(0x1320, 0x4)] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have w3_1c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 ns := by rw [m3]; exact w2_1c
  have w3_20 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = nzw := by rw [m3]; exact w2_20
  have w3_34 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = dlo := by rw [m3]; exact w2_34
  have w3_38 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = dhi := by rw [m3]; exact w2_38
  have w3_3c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = uhi := by rw [m3]; exact w2_3c
  have w3_40 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = vhi := by rw [m3]; exact w2_40
  have w3_44 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = vlo := by rw [m3]; exact w2_44
  have w3_4c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m3]; exact w2_4c
  have w3_50 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m3]; exact w2_50
  have w3_54 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m3]; exact w2_54
  have w3_58 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m3]; exact w2_58
  have w3_5c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rlo := by rw [m3]; exact w2_5c
  have w3_60 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = qhi := by rw [m3]; exact w2_60
  have w3_64 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m3]; exact w2_64
  have w3_68 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m3]; exact w2_68
  have w3_6c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m3]; exact w2_6c
  have w3_70 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = qlo := by rw [m3]; exact w2_70
  have w3_74 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = rhi := by rw [m3]; exact w2_74
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
  have w3_460 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m3]; exact w2_460
  have w3_464 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m3]; exact w2_464
  have w3_1320 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = ulo := by rw [m3]; exact w2_1320
  have b3_340 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = fs := by rw [m3]; exact b2_340
  have b3_1040 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = es := by rw [m3]; exact b2_1040
  have b3_13a0 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = gs := by rw [m3]; exact b2_13a0
  have b3_14a0 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = ds := by rw [m3]; exact b2_14a0
  have a3_2a0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m3]; exact a2_2a0
  have a3_2c0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m3]; exact a2_2c0
  have a3_2e0 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m3]; exact a2_2e0
  have a3_320 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = fv := by rw [m3]; exact a2_320
  have a3_420 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := by rw [m3]; exact a2_420
  have a3_440 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := by rw [m3]; exact a2_440
  have a3_1020 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = ev := by rw [m3]; exact a2_1020
  have a3_1380 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = gv := by rw [m3]; exact a2_1380
  have a3_1480 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = dv := by rw [m3]; exact a2_1480
  have a3_15a8 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := by rw [m3]; exact a2_15a8
  have a3_15c8 : accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := by rw [m3]; exact a2_15c8
  clear a2_15c8 a2_15a8 a2_1480 a2_1380 a2_1020 a2_440 a2_420 a2_320 a2_2e0 a2_2c0 a2_2a0 w2_1320 b2_14a0 b2_13a0 b2_1040 b2_340 w2_464 w2_460 w2_130 w2_12c w2_128 w2_124 w2_120 w2_11c w2_118 w2_114 w2_110 w2_10c w2_108 w2_104 w2_100 w2_fc w2_f8 w2_f4 w2_f0 w2_ec w2_e8 w2_e4 w2_e0 w2_dc w2_d8 w2_d4 w2_d0 w2_cc w2_c8 w2_c4 w2_c0 w2_bc w2_b8 w2_b4 w2_b0 w2_ac w2_a8 w2_a4 w2_a0 w2_9c w2_98 w2_94 w2_90 w2_8c w2_88 w2_84 w2_80 w2_7c w2_78 w2_74 w2_70 w2_6c w2_68 w2_64 w2_60 w2_5c w2_58 w2_54 w2_50 w2_4c w2_44 w2_40 w2_3c w2_38 w2_34 w2_20 w2_1c g2_27 g2_26 g2_24 g2_19 g2_18 g2_10 g2_4 g2_3 g2_2 V2 E2 fR2 t2 rg2 W2 K2 fr2 s2 d2
  -- 0x1D70: sw
  obtain ⟨n4, d4, s4, fr4, K4, W4, rg4⟩ := sv_sw F E3 s3 sv_at_1d70 (off' := 0x1D72) (c := 0x1324)
    (by decide) (by rw [g3_10]; sv_addr) (by decide) (by decide)
  have t4 : Steps n0 n4 := t3.trans d4
  have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : SvCode n4.mem := E3.fr F fr4
  have V4 : SvSaves B n4.mem v := V3.keep K4 (by decide)
  have g4_2 : reg n4 sp = B + 0x21A0 := by rw [rg4 sp, g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg4 (3 : Fin 32), g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg4 (4 : Fin 32), g3_4]
  have g4_10 : reg n4 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg4 a0, g3_10]
  have g4_11 : reg n4 a1 = uhi := by rw [rg4 a1, g3_11]
  have g4_18 : reg n4 (18 : Fin 32) = out := by rw [rg4 (18 : Fin 32), g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [rg4 (19 : Fin 32), g3_19]
  have g4_24 : reg n4 (24 : Fin 32) = ulo := by rw [rg4 (24 : Fin 32), g3_24]
  have g4_26 : reg n4 (26 : Fin 32) = x26 := by rw [rg4 (26 : Fin 32), g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg4 (27 : Fin 32), g3_27]
  have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x1320, 0x4), (0x1324, 0x4)] := keep_kk3.trans K4.toL
  clear keep_kk3
  have w4_1c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 ns := (K4.w32 (by decide) (by decide)).trans w3_1c
  have w4_20 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = nzw := (K4.w32 (by decide) (by decide)).trans w3_20
  have w4_34 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = dlo := (K4.w32 (by decide) (by decide)).trans w3_34
  have w4_38 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = dhi := (K4.w32 (by decide) (by decide)).trans w3_38
  have w4_3c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = uhi := (K4.w32 (by decide) (by decide)).trans w3_3c
  have w4_40 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = vhi := (K4.w32 (by decide) (by decide)).trans w3_40
  have w4_44 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = vlo := (K4.w32 (by decide) (by decide)).trans w3_44
  have w4_4c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K4.w32 (by decide) (by decide)).trans w3_4c
  have w4_50 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K4.w32 (by decide) (by decide)).trans w3_50
  have w4_54 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K4.w32 (by decide) (by decide)).trans w3_54
  have w4_58 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K4.w32 (by decide) (by decide)).trans w3_58
  have w4_5c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rlo := (K4.w32 (by decide) (by decide)).trans w3_5c
  have w4_60 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = qhi := (K4.w32 (by decide) (by decide)).trans w3_60
  have w4_64 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K4.w32 (by decide) (by decide)).trans w3_64
  have w4_68 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K4.w32 (by decide) (by decide)).trans w3_68
  have w4_6c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K4.w32 (by decide) (by decide)).trans w3_6c
  have w4_70 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = qlo := (K4.w32 (by decide) (by decide)).trans w3_70
  have w4_74 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = rhi := (K4.w32 (by decide) (by decide)).trans w3_74
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
  have w4_460 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := (K4.w32 (by decide) (by decide)).trans w3_460
  have w4_464 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := (K4.w32 (by decide) (by decide)).trans w3_464
  have w4_1320 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = ulo := (K4.w32 (by decide) (by decide)).trans w3_1320
  have b4_340 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = fs := (K4.b8 (by decide) (by decide)).trans b3_340
  have b4_1040 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = es := (K4.b8 (by decide) (by decide)).trans b3_1040
  have b4_13a0 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = gs := (K4.b8 (by decide) (by decide)).trans b3_13a0
  have b4_14a0 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = ds := (K4.b8 (by decide) (by decide)).trans b3_14a0
  have w4_1324 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = uhi := by rw [W4, g3_11]
  have a4_2a0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K4.acc (by decide) (by decide)).trans a3_2a0
  have a4_2c0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K4.acc (by decide) (by decide)).trans a3_2c0
  have a4_2e0 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K4.acc (by decide) (by decide)).trans a3_2e0
  have a4_320 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = fv := (K4.acc (by decide) (by decide)).trans a3_320
  have a4_420 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := (K4.acc (by decide) (by decide)).trans a3_420
  have a4_440 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := (K4.acc (by decide) (by decide)).trans a3_440
  have a4_1020 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = ev := (K4.acc (by decide) (by decide)).trans a3_1020
  have a4_1380 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = gv := (K4.acc (by decide) (by decide)).trans a3_1380
  have a4_1480 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = dv := (K4.acc (by decide) (by decide)).trans a3_1480
  have a4_15a8 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := (K4.acc (by decide) (by decide)).trans a3_15a8
  have a4_15c8 : accV n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := (K4.acc (by decide) (by decide)).trans a3_15c8
  clear a3_15c8 a3_15a8 a3_1480 a3_1380 a3_1020 a3_440 a3_420 a3_320 a3_2e0 a3_2c0 a3_2a0 b3_14a0 b3_13a0 b3_1040 b3_340 w3_1320 w3_464 w3_460 w3_130 w3_12c w3_128 w3_124 w3_120 w3_11c w3_118 w3_114 w3_110 w3_10c w3_108 w3_104 w3_100 w3_fc w3_f8 w3_f4 w3_f0 w3_ec w3_e8 w3_e4 w3_e0 w3_dc w3_d8 w3_d4 w3_d0 w3_cc w3_c8 w3_c4 w3_c0 w3_bc w3_b8 w3_b4 w3_b0 w3_ac w3_a8 w3_a4 w3_a0 w3_9c w3_98 w3_94 w3_90 w3_8c w3_88 w3_84 w3_80 w3_7c w3_78 w3_74 w3_70 w3_6c w3_68 w3_64 w3_60 w3_5c w3_58 w3_54 w3_50 w3_4c w3_44 w3_40 w3_3c w3_38 w3_34 w3_20 w3_1c g3_11 g3_27 g3_26 g3_24 g3_19 g3_18 g3_10 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
  -- 0x1D72: lw
  obtain ⟨n5, d5, u5⟩ := s4.lw E4.self sv_at_1d72 (off' := 0x1D74) (by decide)
    (by rw [g4_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s5 : St n5.mem SV n5 0x1D74 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have fr5 : ∀ x, SvR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
  have t5 : Steps n0 n5 := t4.trans (.single d5)
  have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : SvCode n5.mem := E4.fr F fr5
  have V5 : SvSaves B n5.mem v := V4.same m5
  have g5_2 : reg n5 sp = B + 0x21A0 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u5.regs, upd_ne (by decide) (by decide), g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u5.regs, upd_ne (by decide) (by decide), g4_4]
  have g5_10 : reg n5 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_10]
  have g5_18 : reg n5 (18 : Fin 32) = out := by rw [u5.regs, upd_ne (by decide) (by decide), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_19]
  have g5_24 : reg n5 (24 : Fin 32) = ulo := by rw [u5.regs, upd_ne (by decide) (by decide), g4_24]
  have g5_26 : reg n5 (26 : Fin 32) = x26 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_27]
  have g5_11 : reg n5 a1 = vlo := by
    rw [u5.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g4_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr, w4_44]
  have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x1320, 0x4), (0x1324, 0x4)] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have w5_1c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 ns := by rw [m5]; exact w4_1c
  have w5_20 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = nzw := by rw [m5]; exact w4_20
  have w5_34 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = dlo := by rw [m5]; exact w4_34
  have w5_38 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = dhi := by rw [m5]; exact w4_38
  have w5_3c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = uhi := by rw [m5]; exact w4_3c
  have w5_40 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = vhi := by rw [m5]; exact w4_40
  have w5_44 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = vlo := by rw [m5]; exact w4_44
  have w5_4c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m5]; exact w4_4c
  have w5_50 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m5]; exact w4_50
  have w5_54 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m5]; exact w4_54
  have w5_58 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m5]; exact w4_58
  have w5_5c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rlo := by rw [m5]; exact w4_5c
  have w5_60 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = qhi := by rw [m5]; exact w4_60
  have w5_64 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m5]; exact w4_64
  have w5_68 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m5]; exact w4_68
  have w5_6c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m5]; exact w4_6c
  have w5_70 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = qlo := by rw [m5]; exact w4_70
  have w5_74 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = rhi := by rw [m5]; exact w4_74
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
  have w5_460 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m5]; exact w4_460
  have w5_464 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m5]; exact w4_464
  have w5_1320 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = ulo := by rw [m5]; exact w4_1320
  have w5_1324 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = uhi := by rw [m5]; exact w4_1324
  have b5_340 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = fs := by rw [m5]; exact b4_340
  have b5_1040 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = es := by rw [m5]; exact b4_1040
  have b5_13a0 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = gs := by rw [m5]; exact b4_13a0
  have b5_14a0 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = ds := by rw [m5]; exact b4_14a0
  have a5_2a0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m5]; exact a4_2a0
  have a5_2c0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m5]; exact a4_2c0
  have a5_2e0 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m5]; exact a4_2e0
  have a5_320 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = fv := by rw [m5]; exact a4_320
  have a5_420 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := by rw [m5]; exact a4_420
  have a5_440 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := by rw [m5]; exact a4_440
  have a5_1020 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = ev := by rw [m5]; exact a4_1020
  have a5_1380 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = gv := by rw [m5]; exact a4_1380
  have a5_1480 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = dv := by rw [m5]; exact a4_1480
  have a5_15a8 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := by rw [m5]; exact a4_15a8
  have a5_15c8 : accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := by rw [m5]; exact a4_15c8
  clear a4_15c8 a4_15a8 a4_1480 a4_1380 a4_1020 a4_440 a4_420 a4_320 a4_2e0 a4_2c0 a4_2a0 w4_1324 b4_14a0 b4_13a0 b4_1040 b4_340 w4_1320 w4_464 w4_460 w4_130 w4_12c w4_128 w4_124 w4_120 w4_11c w4_118 w4_114 w4_110 w4_10c w4_108 w4_104 w4_100 w4_fc w4_f8 w4_f4 w4_f0 w4_ec w4_e8 w4_e4 w4_e0 w4_dc w4_d8 w4_d4 w4_d0 w4_cc w4_c8 w4_c4 w4_c0 w4_bc w4_b8 w4_b4 w4_b0 w4_ac w4_a8 w4_a4 w4_a0 w4_9c w4_98 w4_94 w4_90 w4_8c w4_88 w4_84 w4_80 w4_7c w4_78 w4_74 w4_70 w4_6c w4_68 w4_64 w4_60 w4_5c w4_58 w4_54 w4_50 w4_4c w4_44 w4_40 w4_3c w4_38 w4_34 w4_20 w4_1c g4_27 g4_26 g4_24 g4_19 g4_18 g4_11 g4_10 g4_4 g4_3 g4_2 V4 E4 fR4 t4 rg4 W4 K4 fr4 s4 d4
  -- 0x1D74: sw
  obtain ⟨n6, d6, s6, fr6, K6, W6, rg6⟩ := sv_sw F E5 s5 sv_at_1d74 (off' := 0x1D76) (c := 0x1328)
    (by decide) (by rw [g5_10]; sv_addr) (by decide) (by decide)
  have t6 : Steps n0 n6 := t5.trans d6
  have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : SvCode n6.mem := E5.fr F fr6
  have V6 : SvSaves B n6.mem v := V5.keep K6 (by decide)
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [rg6 sp, g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg6 (3 : Fin 32), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg6 (4 : Fin 32), g5_4]
  have g6_10 : reg n6 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg6 a0, g5_10]
  have g6_11 : reg n6 a1 = vlo := by rw [rg6 a1, g5_11]
  have g6_18 : reg n6 (18 : Fin 32) = out := by rw [rg6 (18 : Fin 32), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [rg6 (19 : Fin 32), g5_19]
  have g6_24 : reg n6 (24 : Fin 32) = ulo := by rw [rg6 (24 : Fin 32), g5_24]
  have g6_26 : reg n6 (26 : Fin 32) = x26 := by rw [rg6 (26 : Fin 32), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg6 (27 : Fin 32), g5_27]
  have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4)] := keep_kk5.trans K6.toL
  clear keep_kk5
  have w6_1c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 ns := (K6.w32 (by decide) (by decide)).trans w5_1c
  have w6_20 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = nzw := (K6.w32 (by decide) (by decide)).trans w5_20
  have w6_34 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = dlo := (K6.w32 (by decide) (by decide)).trans w5_34
  have w6_38 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = dhi := (K6.w32 (by decide) (by decide)).trans w5_38
  have w6_3c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = uhi := (K6.w32 (by decide) (by decide)).trans w5_3c
  have w6_40 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = vhi := (K6.w32 (by decide) (by decide)).trans w5_40
  have w6_44 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = vlo := (K6.w32 (by decide) (by decide)).trans w5_44
  have w6_4c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K6.w32 (by decide) (by decide)).trans w5_4c
  have w6_50 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K6.w32 (by decide) (by decide)).trans w5_50
  have w6_54 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K6.w32 (by decide) (by decide)).trans w5_54
  have w6_58 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K6.w32 (by decide) (by decide)).trans w5_58
  have w6_5c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rlo := (K6.w32 (by decide) (by decide)).trans w5_5c
  have w6_60 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = qhi := (K6.w32 (by decide) (by decide)).trans w5_60
  have w6_64 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K6.w32 (by decide) (by decide)).trans w5_64
  have w6_68 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K6.w32 (by decide) (by decide)).trans w5_68
  have w6_6c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K6.w32 (by decide) (by decide)).trans w5_6c
  have w6_70 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = qlo := (K6.w32 (by decide) (by decide)).trans w5_70
  have w6_74 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = rhi := (K6.w32 (by decide) (by decide)).trans w5_74
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
  have w6_460 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := (K6.w32 (by decide) (by decide)).trans w5_460
  have w6_464 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := (K6.w32 (by decide) (by decide)).trans w5_464
  have w6_1320 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = ulo := (K6.w32 (by decide) (by decide)).trans w5_1320
  have w6_1324 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = uhi := (K6.w32 (by decide) (by decide)).trans w5_1324
  have b6_340 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = fs := (K6.b8 (by decide) (by decide)).trans b5_340
  have b6_1040 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = es := (K6.b8 (by decide) (by decide)).trans b5_1040
  have b6_13a0 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = gs := (K6.b8 (by decide) (by decide)).trans b5_13a0
  have b6_14a0 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = ds := (K6.b8 (by decide) (by decide)).trans b5_14a0
  have w6_1328 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = vlo := by rw [W6, g5_11]
  have a6_2a0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K6.acc (by decide) (by decide)).trans a5_2a0
  have a6_2c0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K6.acc (by decide) (by decide)).trans a5_2c0
  have a6_2e0 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K6.acc (by decide) (by decide)).trans a5_2e0
  have a6_320 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = fv := (K6.acc (by decide) (by decide)).trans a5_320
  have a6_420 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := (K6.acc (by decide) (by decide)).trans a5_420
  have a6_440 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := (K6.acc (by decide) (by decide)).trans a5_440
  have a6_1020 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = ev := (K6.acc (by decide) (by decide)).trans a5_1020
  have a6_1380 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = gv := (K6.acc (by decide) (by decide)).trans a5_1380
  have a6_1480 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = dv := (K6.acc (by decide) (by decide)).trans a5_1480
  have a6_15a8 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := (K6.acc (by decide) (by decide)).trans a5_15a8
  have a6_15c8 : accV n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := (K6.acc (by decide) (by decide)).trans a5_15c8
  clear a5_15c8 a5_15a8 a5_1480 a5_1380 a5_1020 a5_440 a5_420 a5_320 a5_2e0 a5_2c0 a5_2a0 b5_14a0 b5_13a0 b5_1040 b5_340 w5_1324 w5_1320 w5_464 w5_460 w5_130 w5_12c w5_128 w5_124 w5_120 w5_11c w5_118 w5_114 w5_110 w5_10c w5_108 w5_104 w5_100 w5_fc w5_f8 w5_f4 w5_f0 w5_ec w5_e8 w5_e4 w5_e0 w5_dc w5_d8 w5_d4 w5_d0 w5_cc w5_c8 w5_c4 w5_c0 w5_bc w5_b8 w5_b4 w5_b0 w5_ac w5_a8 w5_a4 w5_a0 w5_9c w5_98 w5_94 w5_90 w5_8c w5_88 w5_84 w5_80 w5_7c w5_78 w5_74 w5_70 w5_6c w5_68 w5_64 w5_60 w5_5c w5_58 w5_54 w5_50 w5_4c w5_44 w5_40 w5_3c w5_38 w5_34 w5_20 w5_1c g5_11 g5_27 g5_26 g5_24 g5_19 g5_18 g5_10 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5
  -- 0x1D76: lw
  obtain ⟨n7, d7, u7⟩ := s6.lw E6.self sv_at_1d76 (off' := 0x1D78) (by decide)
    (by rw [g6_2, show B + 0x21A0 + 0x40 = B + 0x21A0 + BitVec.ofNat 32 0x40 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s7 : St n7.mem SV n7 0x1D78 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have fr7 : ∀ x, SvR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
  have t7 : Steps n0 n7 := t6.trans (.single d7)
  have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : SvCode n7.mem := E6.fr F fr7
  have V7 : SvSaves B n7.mem v := V6.same m7
  have g7_2 : reg n7 sp = B + 0x21A0 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_4]
  have g7_10 : reg n7 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_10]
  have g7_18 : reg n7 (18 : Fin 32) = out := by rw [u7.regs, upd_ne (by decide) (by decide), g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [u7.regs, upd_ne (by decide) (by decide), g6_19]
  have g7_24 : reg n7 (24 : Fin 32) = ulo := by rw [u7.regs, upd_ne (by decide) (by decide), g6_24]
  have g7_26 : reg n7 (26 : Fin 32) = x26 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_27]
  have g7_11 : reg n7 a1 = vhi := by
    rw [u7.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g6_2, show B + 0x21A0 + 0x40 = B + 0x21A0 + BitVec.ofNat 32 0x40 by sv_addr, w6_40]
  have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4)] := by rw [m7]; exact keep_kk6
  clear keep_kk6
  have w7_1c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 ns := by rw [m7]; exact w6_1c
  have w7_20 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = nzw := by rw [m7]; exact w6_20
  have w7_34 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = dlo := by rw [m7]; exact w6_34
  have w7_38 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = dhi := by rw [m7]; exact w6_38
  have w7_3c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = uhi := by rw [m7]; exact w6_3c
  have w7_40 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = vhi := by rw [m7]; exact w6_40
  have w7_44 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = vlo := by rw [m7]; exact w6_44
  have w7_4c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m7]; exact w6_4c
  have w7_50 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m7]; exact w6_50
  have w7_54 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m7]; exact w6_54
  have w7_58 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m7]; exact w6_58
  have w7_5c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rlo := by rw [m7]; exact w6_5c
  have w7_60 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = qhi := by rw [m7]; exact w6_60
  have w7_64 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m7]; exact w6_64
  have w7_68 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m7]; exact w6_68
  have w7_6c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m7]; exact w6_6c
  have w7_70 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = qlo := by rw [m7]; exact w6_70
  have w7_74 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = rhi := by rw [m7]; exact w6_74
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
  have w7_460 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m7]; exact w6_460
  have w7_464 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m7]; exact w6_464
  have w7_1320 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = ulo := by rw [m7]; exact w6_1320
  have w7_1324 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = uhi := by rw [m7]; exact w6_1324
  have w7_1328 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = vlo := by rw [m7]; exact w6_1328
  have b7_340 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = fs := by rw [m7]; exact b6_340
  have b7_1040 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = es := by rw [m7]; exact b6_1040
  have b7_13a0 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = gs := by rw [m7]; exact b6_13a0
  have b7_14a0 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = ds := by rw [m7]; exact b6_14a0
  have a7_2a0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m7]; exact a6_2a0
  have a7_2c0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m7]; exact a6_2c0
  have a7_2e0 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m7]; exact a6_2e0
  have a7_320 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = fv := by rw [m7]; exact a6_320
  have a7_420 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := by rw [m7]; exact a6_420
  have a7_440 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := by rw [m7]; exact a6_440
  have a7_1020 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = ev := by rw [m7]; exact a6_1020
  have a7_1380 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = gv := by rw [m7]; exact a6_1380
  have a7_1480 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = dv := by rw [m7]; exact a6_1480
  have a7_15a8 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := by rw [m7]; exact a6_15a8
  have a7_15c8 : accV n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := by rw [m7]; exact a6_15c8
  clear a6_15c8 a6_15a8 a6_1480 a6_1380 a6_1020 a6_440 a6_420 a6_320 a6_2e0 a6_2c0 a6_2a0 w6_1328 b6_14a0 b6_13a0 b6_1040 b6_340 w6_1324 w6_1320 w6_464 w6_460 w6_130 w6_12c w6_128 w6_124 w6_120 w6_11c w6_118 w6_114 w6_110 w6_10c w6_108 w6_104 w6_100 w6_fc w6_f8 w6_f4 w6_f0 w6_ec w6_e8 w6_e4 w6_e0 w6_dc w6_d8 w6_d4 w6_d0 w6_cc w6_c8 w6_c4 w6_c0 w6_bc w6_b8 w6_b4 w6_b0 w6_ac w6_a8 w6_a4 w6_a0 w6_9c w6_98 w6_94 w6_90 w6_8c w6_88 w6_84 w6_80 w6_7c w6_78 w6_74 w6_70 w6_6c w6_68 w6_64 w6_60 w6_5c w6_58 w6_54 w6_50 w6_4c w6_44 w6_40 w6_3c w6_38 w6_34 w6_20 w6_1c g6_27 g6_26 g6_24 g6_19 g6_18 g6_11 g6_10 g6_4 g6_3 g6_2 V6 E6 fR6 t6 rg6 W6 K6 fr6 s6 d6
  -- 0x1D78: sw
  obtain ⟨n8, d8, s8, fr8, K8, W8, rg8⟩ := sv_sw F E7 s7 sv_at_1d78 (off' := 0x1D7A) (c := 0x132C)
    (by decide) (by rw [g7_10]; sv_addr) (by decide) (by decide)
  have t8 : Steps n0 n8 := t7.trans d8
  have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : SvCode n8.mem := E7.fr F fr8
  have V8 : SvSaves B n8.mem v := V7.keep K8 (by decide)
  have g8_2 : reg n8 sp = B + 0x21A0 := by rw [rg8 sp, g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg8 (3 : Fin 32), g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg8 (4 : Fin 32), g7_4]
  have g8_10 : reg n8 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg8 a0, g7_10]
  have g8_11 : reg n8 a1 = vhi := by rw [rg8 a1, g7_11]
  have g8_18 : reg n8 (18 : Fin 32) = out := by rw [rg8 (18 : Fin 32), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [rg8 (19 : Fin 32), g7_19]
  have g8_24 : reg n8 (24 : Fin 32) = ulo := by rw [rg8 (24 : Fin 32), g7_24]
  have g8_26 : reg n8 (26 : Fin 32) = x26 := by rw [rg8 (26 : Fin 32), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg8 (27 : Fin 32), g7_27]
  have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4)] := keep_kk7.trans K8.toL
  clear keep_kk7
  have w8_1c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 ns := (K8.w32 (by decide) (by decide)).trans w7_1c
  have w8_20 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = nzw := (K8.w32 (by decide) (by decide)).trans w7_20
  have w8_34 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = dlo := (K8.w32 (by decide) (by decide)).trans w7_34
  have w8_38 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = dhi := (K8.w32 (by decide) (by decide)).trans w7_38
  have w8_3c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = uhi := (K8.w32 (by decide) (by decide)).trans w7_3c
  have w8_40 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = vhi := (K8.w32 (by decide) (by decide)).trans w7_40
  have w8_44 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = vlo := (K8.w32 (by decide) (by decide)).trans w7_44
  have w8_4c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K8.w32 (by decide) (by decide)).trans w7_4c
  have w8_50 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K8.w32 (by decide) (by decide)).trans w7_50
  have w8_54 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K8.w32 (by decide) (by decide)).trans w7_54
  have w8_58 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K8.w32 (by decide) (by decide)).trans w7_58
  have w8_5c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rlo := (K8.w32 (by decide) (by decide)).trans w7_5c
  have w8_60 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = qhi := (K8.w32 (by decide) (by decide)).trans w7_60
  have w8_64 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K8.w32 (by decide) (by decide)).trans w7_64
  have w8_68 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K8.w32 (by decide) (by decide)).trans w7_68
  have w8_6c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K8.w32 (by decide) (by decide)).trans w7_6c
  have w8_70 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = qlo := (K8.w32 (by decide) (by decide)).trans w7_70
  have w8_74 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = rhi := (K8.w32 (by decide) (by decide)).trans w7_74
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
  have w8_460 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := (K8.w32 (by decide) (by decide)).trans w7_460
  have w8_464 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := (K8.w32 (by decide) (by decide)).trans w7_464
  have w8_1320 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = ulo := (K8.w32 (by decide) (by decide)).trans w7_1320
  have w8_1324 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = uhi := (K8.w32 (by decide) (by decide)).trans w7_1324
  have w8_1328 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = vlo := (K8.w32 (by decide) (by decide)).trans w7_1328
  have b8_340 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = fs := (K8.b8 (by decide) (by decide)).trans b7_340
  have b8_1040 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = es := (K8.b8 (by decide) (by decide)).trans b7_1040
  have b8_13a0 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = gs := (K8.b8 (by decide) (by decide)).trans b7_13a0
  have b8_14a0 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = ds := (K8.b8 (by decide) (by decide)).trans b7_14a0
  have w8_132c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = vhi := by rw [W8, g7_11]
  have a8_2a0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K8.acc (by decide) (by decide)).trans a7_2a0
  have a8_2c0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K8.acc (by decide) (by decide)).trans a7_2c0
  have a8_2e0 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K8.acc (by decide) (by decide)).trans a7_2e0
  have a8_320 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = fv := (K8.acc (by decide) (by decide)).trans a7_320
  have a8_420 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := (K8.acc (by decide) (by decide)).trans a7_420
  have a8_440 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := (K8.acc (by decide) (by decide)).trans a7_440
  have a8_1020 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = ev := (K8.acc (by decide) (by decide)).trans a7_1020
  have a8_1380 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = gv := (K8.acc (by decide) (by decide)).trans a7_1380
  have a8_1480 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = dv := (K8.acc (by decide) (by decide)).trans a7_1480
  have a8_15a8 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := (K8.acc (by decide) (by decide)).trans a7_15a8
  have a8_15c8 : accV n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := (K8.acc (by decide) (by decide)).trans a7_15c8
  clear a7_15c8 a7_15a8 a7_1480 a7_1380 a7_1020 a7_440 a7_420 a7_320 a7_2e0 a7_2c0 a7_2a0 b7_14a0 b7_13a0 b7_1040 b7_340 w7_1328 w7_1324 w7_1320 w7_464 w7_460 w7_130 w7_12c w7_128 w7_124 w7_120 w7_11c w7_118 w7_114 w7_110 w7_10c w7_108 w7_104 w7_100 w7_fc w7_f8 w7_f4 w7_f0 w7_ec w7_e8 w7_e4 w7_e0 w7_dc w7_d8 w7_d4 w7_d0 w7_cc w7_c8 w7_c4 w7_c0 w7_bc w7_b8 w7_b4 w7_b0 w7_ac w7_a8 w7_a4 w7_a0 w7_9c w7_98 w7_94 w7_90 w7_8c w7_88 w7_84 w7_80 w7_7c w7_78 w7_74 w7_70 w7_6c w7_68 w7_64 w7_60 w7_5c w7_58 w7_54 w7_50 w7_4c w7_44 w7_40 w7_3c w7_38 w7_34 w7_20 w7_1c g7_11 g7_27 g7_26 g7_24 g7_19 g7_18 g7_10 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 m7 s7 u7 d7
  -- 0x1D7A: lw
  obtain ⟨n9, d9, u9⟩ := s8.lw E8.self sv_at_1d7a (off' := 0x1D7C) (by decide)
    (by rw [g8_2, show B + 0x21A0 + 0x70 = B + 0x21A0 + BitVec.ofNat 32 0x70 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s9 : St n9.mem SV n9 0x1D7C (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have m9 : n9.mem = n8.mem := u9.mem
  have fr9 : ∀ x, SvR B x → n9.mem x = n8.mem x := fun x _ => by rw [m9]
  have t9 : Steps n0 n9 := t8.trans (.single d9)
  have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : SvCode n9.mem := E8.fr F fr9
  have V9 : SvSaves B n9.mem v := V8.same m9
  have g9_2 : reg n9 sp = B + 0x21A0 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u9.regs, upd_ne (by decide) (by decide), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u9.regs, upd_ne (by decide) (by decide), g8_4]
  have g9_10 : reg n9 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_10]
  have g9_18 : reg n9 (18 : Fin 32) = out := by rw [u9.regs, upd_ne (by decide) (by decide), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_19]
  have g9_24 : reg n9 (24 : Fin 32) = ulo := by rw [u9.regs, upd_ne (by decide) (by decide), g8_24]
  have g9_26 : reg n9 (26 : Fin 32) = x26 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_27]
  have g9_11 : reg n9 a1 = qlo := by
    rw [u9.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g8_2, show B + 0x21A0 + 0x70 = B + 0x21A0 + BitVec.ofNat 32 0x70 by sv_addr, w8_70]
  have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4)] := by rw [m9]; exact keep_kk8
  clear keep_kk8
  have w9_1c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 ns := by rw [m9]; exact w8_1c
  have w9_20 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = nzw := by rw [m9]; exact w8_20
  have w9_34 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = dlo := by rw [m9]; exact w8_34
  have w9_38 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = dhi := by rw [m9]; exact w8_38
  have w9_3c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = uhi := by rw [m9]; exact w8_3c
  have w9_40 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = vhi := by rw [m9]; exact w8_40
  have w9_44 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = vlo := by rw [m9]; exact w8_44
  have w9_4c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m9]; exact w8_4c
  have w9_50 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m9]; exact w8_50
  have w9_54 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m9]; exact w8_54
  have w9_58 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m9]; exact w8_58
  have w9_5c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rlo := by rw [m9]; exact w8_5c
  have w9_60 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = qhi := by rw [m9]; exact w8_60
  have w9_64 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m9]; exact w8_64
  have w9_68 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m9]; exact w8_68
  have w9_6c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m9]; exact w8_6c
  have w9_70 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = qlo := by rw [m9]; exact w8_70
  have w9_74 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = rhi := by rw [m9]; exact w8_74
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
  have w9_460 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m9]; exact w8_460
  have w9_464 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m9]; exact w8_464
  have w9_1320 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = ulo := by rw [m9]; exact w8_1320
  have w9_1324 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = uhi := by rw [m9]; exact w8_1324
  have w9_1328 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = vlo := by rw [m9]; exact w8_1328
  have w9_132c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = vhi := by rw [m9]; exact w8_132c
  have b9_340 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = fs := by rw [m9]; exact b8_340
  have b9_1040 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = es := by rw [m9]; exact b8_1040
  have b9_13a0 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = gs := by rw [m9]; exact b8_13a0
  have b9_14a0 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = ds := by rw [m9]; exact b8_14a0
  have a9_2a0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m9]; exact a8_2a0
  have a9_2c0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m9]; exact a8_2c0
  have a9_2e0 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m9]; exact a8_2e0
  have a9_320 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = fv := by rw [m9]; exact a8_320
  have a9_420 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := by rw [m9]; exact a8_420
  have a9_440 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := by rw [m9]; exact a8_440
  have a9_1020 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = ev := by rw [m9]; exact a8_1020
  have a9_1380 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = gv := by rw [m9]; exact a8_1380
  have a9_1480 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = dv := by rw [m9]; exact a8_1480
  have a9_15a8 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := by rw [m9]; exact a8_15a8
  have a9_15c8 : accV n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := by rw [m9]; exact a8_15c8
  clear a8_15c8 a8_15a8 a8_1480 a8_1380 a8_1020 a8_440 a8_420 a8_320 a8_2e0 a8_2c0 a8_2a0 w8_132c b8_14a0 b8_13a0 b8_1040 b8_340 w8_1328 w8_1324 w8_1320 w8_464 w8_460 w8_130 w8_12c w8_128 w8_124 w8_120 w8_11c w8_118 w8_114 w8_110 w8_10c w8_108 w8_104 w8_100 w8_fc w8_f8 w8_f4 w8_f0 w8_ec w8_e8 w8_e4 w8_e0 w8_dc w8_d8 w8_d4 w8_d0 w8_cc w8_c8 w8_c4 w8_c0 w8_bc w8_b8 w8_b4 w8_b0 w8_ac w8_a8 w8_a4 w8_a0 w8_9c w8_98 w8_94 w8_90 w8_8c w8_88 w8_84 w8_80 w8_7c w8_78 w8_74 w8_70 w8_6c w8_68 w8_64 w8_60 w8_5c w8_58 w8_54 w8_50 w8_4c w8_44 w8_40 w8_3c w8_38 w8_34 w8_20 w8_1c g8_27 g8_26 g8_24 g8_19 g8_18 g8_11 g8_10 g8_4 g8_3 g8_2 V8 E8 fR8 t8 rg8 W8 K8 fr8 s8 d8
  -- 0x1D7C: sw
  obtain ⟨n10, d10, s10, fr10, K10, W10, rg10⟩ := sv_sw F E9 s9 sv_at_1d7c (off' := 0x1D7E) (c := 0x1330)
    (by decide) (by rw [g9_10]; sv_addr) (by decide) (by decide)
  have t10 : Steps n0 n10 := t9.trans d10
  have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : SvCode n10.mem := E9.fr F fr10
  have V10 : SvSaves B n10.mem v := V9.keep K10 (by decide)
  have g10_2 : reg n10 sp = B + 0x21A0 := by rw [rg10 sp, g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg10 (3 : Fin 32), g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg10 (4 : Fin 32), g9_4]
  have g10_10 : reg n10 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg10 a0, g9_10]
  have g10_11 : reg n10 a1 = qlo := by rw [rg10 a1, g9_11]
  have g10_18 : reg n10 (18 : Fin 32) = out := by rw [rg10 (18 : Fin 32), g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [rg10 (19 : Fin 32), g9_19]
  have g10_24 : reg n10 (24 : Fin 32) = ulo := by rw [rg10 (24 : Fin 32), g9_24]
  have g10_26 : reg n10 (26 : Fin 32) = x26 := by rw [rg10 (26 : Fin 32), g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg10 (27 : Fin 32), g9_27]
  have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4)] := keep_kk9.trans K10.toL
  clear keep_kk9
  have w10_1c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 ns := (K10.w32 (by decide) (by decide)).trans w9_1c
  have w10_20 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = nzw := (K10.w32 (by decide) (by decide)).trans w9_20
  have w10_34 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = dlo := (K10.w32 (by decide) (by decide)).trans w9_34
  have w10_38 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = dhi := (K10.w32 (by decide) (by decide)).trans w9_38
  have w10_3c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = uhi := (K10.w32 (by decide) (by decide)).trans w9_3c
  have w10_40 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = vhi := (K10.w32 (by decide) (by decide)).trans w9_40
  have w10_44 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = vlo := (K10.w32 (by decide) (by decide)).trans w9_44
  have w10_4c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K10.w32 (by decide) (by decide)).trans w9_4c
  have w10_50 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K10.w32 (by decide) (by decide)).trans w9_50
  have w10_54 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K10.w32 (by decide) (by decide)).trans w9_54
  have w10_58 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K10.w32 (by decide) (by decide)).trans w9_58
  have w10_5c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rlo := (K10.w32 (by decide) (by decide)).trans w9_5c
  have w10_60 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = qhi := (K10.w32 (by decide) (by decide)).trans w9_60
  have w10_64 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K10.w32 (by decide) (by decide)).trans w9_64
  have w10_68 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K10.w32 (by decide) (by decide)).trans w9_68
  have w10_6c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K10.w32 (by decide) (by decide)).trans w9_6c
  have w10_70 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = qlo := (K10.w32 (by decide) (by decide)).trans w9_70
  have w10_74 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = rhi := (K10.w32 (by decide) (by decide)).trans w9_74
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
  have w10_460 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := (K10.w32 (by decide) (by decide)).trans w9_460
  have w10_464 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := (K10.w32 (by decide) (by decide)).trans w9_464
  have w10_1320 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = ulo := (K10.w32 (by decide) (by decide)).trans w9_1320
  have w10_1324 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = uhi := (K10.w32 (by decide) (by decide)).trans w9_1324
  have w10_1328 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = vlo := (K10.w32 (by decide) (by decide)).trans w9_1328
  have w10_132c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = vhi := (K10.w32 (by decide) (by decide)).trans w9_132c
  have b10_340 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = fs := (K10.b8 (by decide) (by decide)).trans b9_340
  have b10_1040 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = es := (K10.b8 (by decide) (by decide)).trans b9_1040
  have b10_13a0 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = gs := (K10.b8 (by decide) (by decide)).trans b9_13a0
  have b10_14a0 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = ds := (K10.b8 (by decide) (by decide)).trans b9_14a0
  have w10_1330 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = qlo := by rw [W10, g9_11]
  have a10_2a0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K10.acc (by decide) (by decide)).trans a9_2a0
  have a10_2c0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K10.acc (by decide) (by decide)).trans a9_2c0
  have a10_2e0 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K10.acc (by decide) (by decide)).trans a9_2e0
  have a10_320 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = fv := (K10.acc (by decide) (by decide)).trans a9_320
  have a10_420 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := (K10.acc (by decide) (by decide)).trans a9_420
  have a10_440 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := (K10.acc (by decide) (by decide)).trans a9_440
  have a10_1020 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = ev := (K10.acc (by decide) (by decide)).trans a9_1020
  have a10_1380 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = gv := (K10.acc (by decide) (by decide)).trans a9_1380
  have a10_1480 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = dv := (K10.acc (by decide) (by decide)).trans a9_1480
  have a10_15a8 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := (K10.acc (by decide) (by decide)).trans a9_15a8
  have a10_15c8 : accV n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := (K10.acc (by decide) (by decide)).trans a9_15c8
  clear a9_15c8 a9_15a8 a9_1480 a9_1380 a9_1020 a9_440 a9_420 a9_320 a9_2e0 a9_2c0 a9_2a0 b9_14a0 b9_13a0 b9_1040 b9_340 w9_132c w9_1328 w9_1324 w9_1320 w9_464 w9_460 w9_130 w9_12c w9_128 w9_124 w9_120 w9_11c w9_118 w9_114 w9_110 w9_10c w9_108 w9_104 w9_100 w9_fc w9_f8 w9_f4 w9_f0 w9_ec w9_e8 w9_e4 w9_e0 w9_dc w9_d8 w9_d4 w9_d0 w9_cc w9_c8 w9_c4 w9_c0 w9_bc w9_b8 w9_b4 w9_b0 w9_ac w9_a8 w9_a4 w9_a0 w9_9c w9_98 w9_94 w9_90 w9_8c w9_88 w9_84 w9_80 w9_7c w9_78 w9_74 w9_70 w9_6c w9_68 w9_64 w9_60 w9_5c w9_58 w9_54 w9_50 w9_4c w9_44 w9_40 w9_3c w9_38 w9_34 w9_20 w9_1c g9_11 g9_27 g9_26 g9_24 g9_19 g9_18 g9_10 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 m9 s9 u9 d9
  -- 0x1D7E: lw
  obtain ⟨n11, d11, u11⟩ := s10.lw E10.self sv_at_1d7e (off' := 0x1D80) (by decide)
    (by rw [g10_2, show B + 0x21A0 + 0x60 = B + 0x21A0 + BitVec.ofNat 32 0x60 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s11 : St n11.mem SV n11 0x1D80 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
  have t11 : Steps n0 n11 := t10.trans (.single d11)
  have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : SvCode n11.mem := E10.fr F fr11
  have V11 : SvSaves B n11.mem v := V10.same m11
  have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, upd_ne (by decide) (by decide), g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, upd_ne (by decide) (by decide), g10_4]
  have g11_10 : reg n11 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_10]
  have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, upd_ne (by decide) (by decide), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_19]
  have g11_24 : reg n11 (24 : Fin 32) = ulo := by rw [u11.regs, upd_ne (by decide) (by decide), g10_24]
  have g11_26 : reg n11 (26 : Fin 32) = x26 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_27]
  have g11_11 : reg n11 a1 = qhi := by
    rw [u11.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g10_2, show B + 0x21A0 + 0x60 = B + 0x21A0 + BitVec.ofNat 32 0x60 by sv_addr, w10_60]
  have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4)] := by rw [m11]; exact keep_kk10
  clear keep_kk10
  have w11_1c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 ns := by rw [m11]; exact w10_1c
  have w11_20 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = nzw := by rw [m11]; exact w10_20
  have w11_34 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = dlo := by rw [m11]; exact w10_34
  have w11_38 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = dhi := by rw [m11]; exact w10_38
  have w11_3c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = uhi := by rw [m11]; exact w10_3c
  have w11_40 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = vhi := by rw [m11]; exact w10_40
  have w11_44 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = vlo := by rw [m11]; exact w10_44
  have w11_4c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m11]; exact w10_4c
  have w11_50 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m11]; exact w10_50
  have w11_54 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m11]; exact w10_54
  have w11_58 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m11]; exact w10_58
  have w11_5c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rlo := by rw [m11]; exact w10_5c
  have w11_60 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = qhi := by rw [m11]; exact w10_60
  have w11_64 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m11]; exact w10_64
  have w11_68 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m11]; exact w10_68
  have w11_6c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m11]; exact w10_6c
  have w11_70 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = qlo := by rw [m11]; exact w10_70
  have w11_74 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = rhi := by rw [m11]; exact w10_74
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
  have w11_460 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m11]; exact w10_460
  have w11_464 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m11]; exact w10_464
  have w11_1320 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = ulo := by rw [m11]; exact w10_1320
  have w11_1324 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = uhi := by rw [m11]; exact w10_1324
  have w11_1328 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = vlo := by rw [m11]; exact w10_1328
  have w11_132c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = vhi := by rw [m11]; exact w10_132c
  have w11_1330 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = qlo := by rw [m11]; exact w10_1330
  have b11_340 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = fs := by rw [m11]; exact b10_340
  have b11_1040 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = es := by rw [m11]; exact b10_1040
  have b11_13a0 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = gs := by rw [m11]; exact b10_13a0
  have b11_14a0 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = ds := by rw [m11]; exact b10_14a0
  have a11_2a0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m11]; exact a10_2a0
  have a11_2c0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m11]; exact a10_2c0
  have a11_2e0 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m11]; exact a10_2e0
  have a11_320 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = fv := by rw [m11]; exact a10_320
  have a11_420 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := by rw [m11]; exact a10_420
  have a11_440 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := by rw [m11]; exact a10_440
  have a11_1020 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = ev := by rw [m11]; exact a10_1020
  have a11_1380 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = gv := by rw [m11]; exact a10_1380
  have a11_1480 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = dv := by rw [m11]; exact a10_1480
  have a11_15a8 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := by rw [m11]; exact a10_15a8
  have a11_15c8 : accV n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := by rw [m11]; exact a10_15c8
  clear a10_15c8 a10_15a8 a10_1480 a10_1380 a10_1020 a10_440 a10_420 a10_320 a10_2e0 a10_2c0 a10_2a0 w10_1330 b10_14a0 b10_13a0 b10_1040 b10_340 w10_132c w10_1328 w10_1324 w10_1320 w10_464 w10_460 w10_130 w10_12c w10_128 w10_124 w10_120 w10_11c w10_118 w10_114 w10_110 w10_10c w10_108 w10_104 w10_100 w10_fc w10_f8 w10_f4 w10_f0 w10_ec w10_e8 w10_e4 w10_e0 w10_dc w10_d8 w10_d4 w10_d0 w10_cc w10_c8 w10_c4 w10_c0 w10_bc w10_b8 w10_b4 w10_b0 w10_ac w10_a8 w10_a4 w10_a0 w10_9c w10_98 w10_94 w10_90 w10_8c w10_88 w10_84 w10_80 w10_7c w10_78 w10_74 w10_70 w10_6c w10_68 w10_64 w10_60 w10_5c w10_58 w10_54 w10_50 w10_4c w10_44 w10_40 w10_3c w10_38 w10_34 w10_20 w10_1c g10_27 g10_26 g10_24 g10_19 g10_18 g10_11 g10_10 g10_4 g10_3 g10_2 V10 E10 fR10 t10 rg10 W10 K10 fr10 s10 d10
  -- 0x1D80: sw
  obtain ⟨n12, d12, s12, fr12, K12, W12, rg12⟩ := sv_sw F E11 s11 sv_at_1d80 (off' := 0x1D82) (c := 0x1334)
    (by decide) (by rw [g11_10]; sv_addr) (by decide) (by decide)
  have t12 : Steps n0 n12 := t11.trans d12
  have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : SvCode n12.mem := E11.fr F fr12
  have V12 : SvSaves B n12.mem v := V11.keep K12 (by decide)
  have g12_2 : reg n12 sp = B + 0x21A0 := by rw [rg12 sp, g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg12 (3 : Fin 32), g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg12 (4 : Fin 32), g11_4]
  have g12_10 : reg n12 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg12 a0, g11_10]
  have g12_11 : reg n12 a1 = qhi := by rw [rg12 a1, g11_11]
  have g12_18 : reg n12 (18 : Fin 32) = out := by rw [rg12 (18 : Fin 32), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [rg12 (19 : Fin 32), g11_19]
  have g12_24 : reg n12 (24 : Fin 32) = ulo := by rw [rg12 (24 : Fin 32), g11_24]
  have g12_26 : reg n12 (26 : Fin 32) = x26 := by rw [rg12 (26 : Fin 32), g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg12 (27 : Fin 32), g11_27]
  have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4)] := keep_kk11.trans K12.toL
  clear keep_kk11
  have w12_1c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 ns := (K12.w32 (by decide) (by decide)).trans w11_1c
  have w12_20 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = nzw := (K12.w32 (by decide) (by decide)).trans w11_20
  have w12_34 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = dlo := (K12.w32 (by decide) (by decide)).trans w11_34
  have w12_38 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = dhi := (K12.w32 (by decide) (by decide)).trans w11_38
  have w12_3c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = uhi := (K12.w32 (by decide) (by decide)).trans w11_3c
  have w12_40 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = vhi := (K12.w32 (by decide) (by decide)).trans w11_40
  have w12_44 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = vlo := (K12.w32 (by decide) (by decide)).trans w11_44
  have w12_4c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K12.w32 (by decide) (by decide)).trans w11_4c
  have w12_50 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K12.w32 (by decide) (by decide)).trans w11_50
  have w12_54 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K12.w32 (by decide) (by decide)).trans w11_54
  have w12_58 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K12.w32 (by decide) (by decide)).trans w11_58
  have w12_5c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rlo := (K12.w32 (by decide) (by decide)).trans w11_5c
  have w12_60 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = qhi := (K12.w32 (by decide) (by decide)).trans w11_60
  have w12_64 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K12.w32 (by decide) (by decide)).trans w11_64
  have w12_68 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K12.w32 (by decide) (by decide)).trans w11_68
  have w12_6c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K12.w32 (by decide) (by decide)).trans w11_6c
  have w12_70 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = qlo := (K12.w32 (by decide) (by decide)).trans w11_70
  have w12_74 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = rhi := (K12.w32 (by decide) (by decide)).trans w11_74
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
  have w12_460 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := (K12.w32 (by decide) (by decide)).trans w11_460
  have w12_464 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := (K12.w32 (by decide) (by decide)).trans w11_464
  have w12_1320 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = ulo := (K12.w32 (by decide) (by decide)).trans w11_1320
  have w12_1324 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = uhi := (K12.w32 (by decide) (by decide)).trans w11_1324
  have w12_1328 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = vlo := (K12.w32 (by decide) (by decide)).trans w11_1328
  have w12_132c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = vhi := (K12.w32 (by decide) (by decide)).trans w11_132c
  have w12_1330 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = qlo := (K12.w32 (by decide) (by decide)).trans w11_1330
  have b12_340 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = fs := (K12.b8 (by decide) (by decide)).trans b11_340
  have b12_1040 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = es := (K12.b8 (by decide) (by decide)).trans b11_1040
  have b12_13a0 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = gs := (K12.b8 (by decide) (by decide)).trans b11_13a0
  have b12_14a0 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = ds := (K12.b8 (by decide) (by decide)).trans b11_14a0
  have w12_1334 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = qhi := by rw [W12, g11_11]
  have a12_2a0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K12.acc (by decide) (by decide)).trans a11_2a0
  have a12_2c0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K12.acc (by decide) (by decide)).trans a11_2c0
  have a12_2e0 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K12.acc (by decide) (by decide)).trans a11_2e0
  have a12_320 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = fv := (K12.acc (by decide) (by decide)).trans a11_320
  have a12_420 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := (K12.acc (by decide) (by decide)).trans a11_420
  have a12_440 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := (K12.acc (by decide) (by decide)).trans a11_440
  have a12_1020 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = ev := (K12.acc (by decide) (by decide)).trans a11_1020
  have a12_1380 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = gv := (K12.acc (by decide) (by decide)).trans a11_1380
  have a12_1480 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = dv := (K12.acc (by decide) (by decide)).trans a11_1480
  have a12_15a8 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := (K12.acc (by decide) (by decide)).trans a11_15a8
  have a12_15c8 : accV n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := (K12.acc (by decide) (by decide)).trans a11_15c8
  clear a11_15c8 a11_15a8 a11_1480 a11_1380 a11_1020 a11_440 a11_420 a11_320 a11_2e0 a11_2c0 a11_2a0 b11_14a0 b11_13a0 b11_1040 b11_340 w11_1330 w11_132c w11_1328 w11_1324 w11_1320 w11_464 w11_460 w11_130 w11_12c w11_128 w11_124 w11_120 w11_11c w11_118 w11_114 w11_110 w11_10c w11_108 w11_104 w11_100 w11_fc w11_f8 w11_f4 w11_f0 w11_ec w11_e8 w11_e4 w11_e0 w11_dc w11_d8 w11_d4 w11_d0 w11_cc w11_c8 w11_c4 w11_c0 w11_bc w11_b8 w11_b4 w11_b0 w11_ac w11_a8 w11_a4 w11_a0 w11_9c w11_98 w11_94 w11_90 w11_8c w11_88 w11_84 w11_80 w11_7c w11_78 w11_74 w11_70 w11_6c w11_68 w11_64 w11_60 w11_5c w11_58 w11_54 w11_50 w11_4c w11_44 w11_40 w11_3c w11_38 w11_34 w11_20 w11_1c g11_11 g11_27 g11_26 g11_24 g11_19 g11_18 g11_10 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 m11 s11 u11 d11
  -- 0x1D82: lw
  obtain ⟨n13, d13, u13⟩ := s12.lw E12.self sv_at_1d82 (off' := 0x1D84) (by decide)
    (by rw [g12_2, show B + 0x21A0 + 0x5C = B + 0x21A0 + BitVec.ofNat 32 0x5C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s13 : St n13.mem SV n13 0x1D84 (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
  have m13 : n13.mem = n12.mem := u13.mem
  have fr13 : ∀ x, SvR B x → n13.mem x = n12.mem x := fun x _ => by rw [m13]
  have t13 : Steps n0 n13 := t12.trans (.single d13)
  have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : SvCode n13.mem := E12.fr F fr13
  have V13 : SvSaves B n13.mem v := V12.same m13
  have g13_2 : reg n13 sp = B + 0x21A0 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_2]
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u13.regs, upd_ne (by decide) (by decide), g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u13.regs, upd_ne (by decide) (by decide), g12_4]
  have g13_10 : reg n13 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_10]
  have g13_18 : reg n13 (18 : Fin 32) = out := by rw [u13.regs, upd_ne (by decide) (by decide), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [u13.regs, upd_ne (by decide) (by decide), g12_19]
  have g13_24 : reg n13 (24 : Fin 32) = ulo := by rw [u13.regs, upd_ne (by decide) (by decide), g12_24]
  have g13_26 : reg n13 (26 : Fin 32) = x26 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_27]
  have g13_11 : reg n13 a1 = rlo := by
    rw [u13.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g12_2, show B + 0x21A0 + 0x5C = B + 0x21A0 + BitVec.ofNat 32 0x5C by sv_addr, w12_5c]
  have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4)] := by rw [m13]; exact keep_kk12
  clear keep_kk12
  have w13_1c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 ns := by rw [m13]; exact w12_1c
  have w13_20 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = nzw := by rw [m13]; exact w12_20
  have w13_34 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = dlo := by rw [m13]; exact w12_34
  have w13_38 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = dhi := by rw [m13]; exact w12_38
  have w13_3c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = uhi := by rw [m13]; exact w12_3c
  have w13_40 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = vhi := by rw [m13]; exact w12_40
  have w13_44 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = vlo := by rw [m13]; exact w12_44
  have w13_4c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m13]; exact w12_4c
  have w13_50 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m13]; exact w12_50
  have w13_54 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m13]; exact w12_54
  have w13_58 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m13]; exact w12_58
  have w13_5c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rlo := by rw [m13]; exact w12_5c
  have w13_60 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = qhi := by rw [m13]; exact w12_60
  have w13_64 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m13]; exact w12_64
  have w13_68 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m13]; exact w12_68
  have w13_6c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m13]; exact w12_6c
  have w13_70 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = qlo := by rw [m13]; exact w12_70
  have w13_74 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = rhi := by rw [m13]; exact w12_74
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
  have w13_460 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m13]; exact w12_460
  have w13_464 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m13]; exact w12_464
  have w13_1320 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = ulo := by rw [m13]; exact w12_1320
  have w13_1324 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = uhi := by rw [m13]; exact w12_1324
  have w13_1328 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = vlo := by rw [m13]; exact w12_1328
  have w13_132c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = vhi := by rw [m13]; exact w12_132c
  have w13_1330 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = qlo := by rw [m13]; exact w12_1330
  have w13_1334 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = qhi := by rw [m13]; exact w12_1334
  have b13_340 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = fs := by rw [m13]; exact b12_340
  have b13_1040 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = es := by rw [m13]; exact b12_1040
  have b13_13a0 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = gs := by rw [m13]; exact b12_13a0
  have b13_14a0 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = ds := by rw [m13]; exact b12_14a0
  have a13_2a0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m13]; exact a12_2a0
  have a13_2c0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m13]; exact a12_2c0
  have a13_2e0 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m13]; exact a12_2e0
  have a13_320 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = fv := by rw [m13]; exact a12_320
  have a13_420 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := by rw [m13]; exact a12_420
  have a13_440 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := by rw [m13]; exact a12_440
  have a13_1020 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = ev := by rw [m13]; exact a12_1020
  have a13_1380 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = gv := by rw [m13]; exact a12_1380
  have a13_1480 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = dv := by rw [m13]; exact a12_1480
  have a13_15a8 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := by rw [m13]; exact a12_15a8
  have a13_15c8 : accV n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := by rw [m13]; exact a12_15c8
  clear a12_15c8 a12_15a8 a12_1480 a12_1380 a12_1020 a12_440 a12_420 a12_320 a12_2e0 a12_2c0 a12_2a0 w12_1334 b12_14a0 b12_13a0 b12_1040 b12_340 w12_1330 w12_132c w12_1328 w12_1324 w12_1320 w12_464 w12_460 w12_130 w12_12c w12_128 w12_124 w12_120 w12_11c w12_118 w12_114 w12_110 w12_10c w12_108 w12_104 w12_100 w12_fc w12_f8 w12_f4 w12_f0 w12_ec w12_e8 w12_e4 w12_e0 w12_dc w12_d8 w12_d4 w12_d0 w12_cc w12_c8 w12_c4 w12_c0 w12_bc w12_b8 w12_b4 w12_b0 w12_ac w12_a8 w12_a4 w12_a0 w12_9c w12_98 w12_94 w12_90 w12_8c w12_88 w12_84 w12_80 w12_7c w12_78 w12_74 w12_70 w12_6c w12_68 w12_64 w12_60 w12_5c w12_58 w12_54 w12_50 w12_4c w12_44 w12_40 w12_3c w12_38 w12_34 w12_20 w12_1c g12_27 g12_26 g12_24 g12_19 g12_18 g12_11 g12_10 g12_4 g12_3 g12_2 V12 E12 fR12 t12 rg12 W12 K12 fr12 s12 d12
  -- 0x1D84: sw
  obtain ⟨n14, d14, s14, fr14, K14, W14, rg14⟩ := sv_sw F E13 s13 sv_at_1d84 (off' := 0x1D86) (c := 0x1338)
    (by decide) (by rw [g13_10]; sv_addr) (by decide) (by decide)
  have t14 : Steps n0 n14 := t13.trans d14
  have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : SvCode n14.mem := E13.fr F fr14
  have V14 : SvSaves B n14.mem v := V13.keep K14 (by decide)
  have g14_2 : reg n14 sp = B + 0x21A0 := by rw [rg14 sp, g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg14 (3 : Fin 32), g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg14 (4 : Fin 32), g13_4]
  have g14_10 : reg n14 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg14 a0, g13_10]
  have g14_11 : reg n14 a1 = rlo := by rw [rg14 a1, g13_11]
  have g14_18 : reg n14 (18 : Fin 32) = out := by rw [rg14 (18 : Fin 32), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [rg14 (19 : Fin 32), g13_19]
  have g14_24 : reg n14 (24 : Fin 32) = ulo := by rw [rg14 (24 : Fin 32), g13_24]
  have g14_26 : reg n14 (26 : Fin 32) = x26 := by rw [rg14 (26 : Fin 32), g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg14 (27 : Fin 32), g13_27]
  have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4), (0x1338, 0x4)] := keep_kk13.trans K14.toL
  clear keep_kk13
  have w14_1c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 ns := (K14.w32 (by decide) (by decide)).trans w13_1c
  have w14_20 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = nzw := (K14.w32 (by decide) (by decide)).trans w13_20
  have w14_34 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = dlo := (K14.w32 (by decide) (by decide)).trans w13_34
  have w14_38 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = dhi := (K14.w32 (by decide) (by decide)).trans w13_38
  have w14_3c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = uhi := (K14.w32 (by decide) (by decide)).trans w13_3c
  have w14_40 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = vhi := (K14.w32 (by decide) (by decide)).trans w13_40
  have w14_44 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = vlo := (K14.w32 (by decide) (by decide)).trans w13_44
  have w14_4c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K14.w32 (by decide) (by decide)).trans w13_4c
  have w14_50 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K14.w32 (by decide) (by decide)).trans w13_50
  have w14_54 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K14.w32 (by decide) (by decide)).trans w13_54
  have w14_58 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K14.w32 (by decide) (by decide)).trans w13_58
  have w14_5c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rlo := (K14.w32 (by decide) (by decide)).trans w13_5c
  have w14_60 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = qhi := (K14.w32 (by decide) (by decide)).trans w13_60
  have w14_64 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K14.w32 (by decide) (by decide)).trans w13_64
  have w14_68 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K14.w32 (by decide) (by decide)).trans w13_68
  have w14_6c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K14.w32 (by decide) (by decide)).trans w13_6c
  have w14_70 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = qlo := (K14.w32 (by decide) (by decide)).trans w13_70
  have w14_74 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = rhi := (K14.w32 (by decide) (by decide)).trans w13_74
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
  have w14_460 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := (K14.w32 (by decide) (by decide)).trans w13_460
  have w14_464 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := (K14.w32 (by decide) (by decide)).trans w13_464
  have w14_1320 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = ulo := (K14.w32 (by decide) (by decide)).trans w13_1320
  have w14_1324 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = uhi := (K14.w32 (by decide) (by decide)).trans w13_1324
  have w14_1328 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = vlo := (K14.w32 (by decide) (by decide)).trans w13_1328
  have w14_132c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = vhi := (K14.w32 (by decide) (by decide)).trans w13_132c
  have w14_1330 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = qlo := (K14.w32 (by decide) (by decide)).trans w13_1330
  have w14_1334 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = qhi := (K14.w32 (by decide) (by decide)).trans w13_1334
  have b14_340 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = fs := (K14.b8 (by decide) (by decide)).trans b13_340
  have b14_1040 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = es := (K14.b8 (by decide) (by decide)).trans b13_1040
  have b14_13a0 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = gs := (K14.b8 (by decide) (by decide)).trans b13_13a0
  have b14_14a0 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = ds := (K14.b8 (by decide) (by decide)).trans b13_14a0
  have w14_1338 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) = rlo := by rw [W14, g13_11]
  have a14_2a0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K14.acc (by decide) (by decide)).trans a13_2a0
  have a14_2c0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K14.acc (by decide) (by decide)).trans a13_2c0
  have a14_2e0 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K14.acc (by decide) (by decide)).trans a13_2e0
  have a14_320 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = fv := (K14.acc (by decide) (by decide)).trans a13_320
  have a14_420 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := (K14.acc (by decide) (by decide)).trans a13_420
  have a14_440 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := (K14.acc (by decide) (by decide)).trans a13_440
  have a14_1020 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = ev := (K14.acc (by decide) (by decide)).trans a13_1020
  have a14_1380 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = gv := (K14.acc (by decide) (by decide)).trans a13_1380
  have a14_1480 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = dv := (K14.acc (by decide) (by decide)).trans a13_1480
  have a14_15a8 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := (K14.acc (by decide) (by decide)).trans a13_15a8
  have a14_15c8 : accV n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := (K14.acc (by decide) (by decide)).trans a13_15c8
  clear a13_15c8 a13_15a8 a13_1480 a13_1380 a13_1020 a13_440 a13_420 a13_320 a13_2e0 a13_2c0 a13_2a0 b13_14a0 b13_13a0 b13_1040 b13_340 w13_1334 w13_1330 w13_132c w13_1328 w13_1324 w13_1320 w13_464 w13_460 w13_130 w13_12c w13_128 w13_124 w13_120 w13_11c w13_118 w13_114 w13_110 w13_10c w13_108 w13_104 w13_100 w13_fc w13_f8 w13_f4 w13_f0 w13_ec w13_e8 w13_e4 w13_e0 w13_dc w13_d8 w13_d4 w13_d0 w13_cc w13_c8 w13_c4 w13_c0 w13_bc w13_b8 w13_b4 w13_b0 w13_ac w13_a8 w13_a4 w13_a0 w13_9c w13_98 w13_94 w13_90 w13_8c w13_88 w13_84 w13_80 w13_7c w13_78 w13_74 w13_70 w13_6c w13_68 w13_64 w13_60 w13_5c w13_58 w13_54 w13_50 w13_4c w13_44 w13_40 w13_3c w13_38 w13_34 w13_20 w13_1c g13_11 g13_27 g13_26 g13_24 g13_19 g13_18 g13_10 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 m13 s13 u13 d13
  -- 0x1D86: lw
  obtain ⟨n15, d15, u15⟩ := s14.lw E14.self sv_at_1d86 (off' := 0x1D88) (by decide)
    (by rw [g14_2, show B + 0x21A0 + 0x74 = B + 0x21A0 + BitVec.ofNat 32 0x74 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s15 : St n15.mem SV n15 0x1D88 (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
  have m15 : n15.mem = n14.mem := u15.mem
  have fr15 : ∀ x, SvR B x → n15.mem x = n14.mem x := fun x _ => by rw [m15]
  have t15 : Steps n0 n15 := t14.trans (.single d15)
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.same m15
  have g15_2 : reg n15 sp = B + 0x21A0 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u15.regs, upd_ne (by decide) (by decide), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u15.regs, upd_ne (by decide) (by decide), g14_4]
  have g15_10 : reg n15 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_10]
  have g15_18 : reg n15 (18 : Fin 32) = out := by rw [u15.regs, upd_ne (by decide) (by decide), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [u15.regs, upd_ne (by decide) (by decide), g14_19]
  have g15_24 : reg n15 (24 : Fin 32) = ulo := by rw [u15.regs, upd_ne (by decide) (by decide), g14_24]
  have g15_26 : reg n15 (26 : Fin 32) = x26 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_27]
  have g15_11 : reg n15 a1 = rhi := by
    rw [u15.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g14_2, show B + 0x21A0 + 0x74 = B + 0x21A0 + BitVec.ofNat 32 0x74 by sv_addr, w14_74]
  have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4), (0x1338, 0x4)] := by rw [m15]; exact keep_kk14
  clear keep_kk14
  have w15_1c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 ns := by rw [m15]; exact w14_1c
  have w15_20 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = nzw := by rw [m15]; exact w14_20
  have w15_34 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = dlo := by rw [m15]; exact w14_34
  have w15_38 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = dhi := by rw [m15]; exact w14_38
  have w15_3c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = uhi := by rw [m15]; exact w14_3c
  have w15_40 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = vhi := by rw [m15]; exact w14_40
  have w15_44 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = vlo := by rw [m15]; exact w14_44
  have w15_4c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m15]; exact w14_4c
  have w15_50 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m15]; exact w14_50
  have w15_54 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m15]; exact w14_54
  have w15_58 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m15]; exact w14_58
  have w15_5c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rlo := by rw [m15]; exact w14_5c
  have w15_60 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = qhi := by rw [m15]; exact w14_60
  have w15_64 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m15]; exact w14_64
  have w15_68 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m15]; exact w14_68
  have w15_6c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m15]; exact w14_6c
  have w15_70 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = qlo := by rw [m15]; exact w14_70
  have w15_74 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = rhi := by rw [m15]; exact w14_74
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
  have w15_460 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m15]; exact w14_460
  have w15_464 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m15]; exact w14_464
  have w15_1320 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = ulo := by rw [m15]; exact w14_1320
  have w15_1324 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = uhi := by rw [m15]; exact w14_1324
  have w15_1328 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = vlo := by rw [m15]; exact w14_1328
  have w15_132c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = vhi := by rw [m15]; exact w14_132c
  have w15_1330 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = qlo := by rw [m15]; exact w14_1330
  have w15_1334 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = qhi := by rw [m15]; exact w14_1334
  have w15_1338 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) = rlo := by rw [m15]; exact w14_1338
  have b15_340 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = fs := by rw [m15]; exact b14_340
  have b15_1040 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = es := by rw [m15]; exact b14_1040
  have b15_13a0 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = gs := by rw [m15]; exact b14_13a0
  have b15_14a0 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = ds := by rw [m15]; exact b14_14a0
  have a15_2a0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m15]; exact a14_2a0
  have a15_2c0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m15]; exact a14_2c0
  have a15_2e0 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m15]; exact a14_2e0
  have a15_320 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = fv := by rw [m15]; exact a14_320
  have a15_420 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := by rw [m15]; exact a14_420
  have a15_440 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := by rw [m15]; exact a14_440
  have a15_1020 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = ev := by rw [m15]; exact a14_1020
  have a15_1380 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = gv := by rw [m15]; exact a14_1380
  have a15_1480 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = dv := by rw [m15]; exact a14_1480
  have a15_15a8 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := by rw [m15]; exact a14_15a8
  have a15_15c8 : accV n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := by rw [m15]; exact a14_15c8
  clear a14_15c8 a14_15a8 a14_1480 a14_1380 a14_1020 a14_440 a14_420 a14_320 a14_2e0 a14_2c0 a14_2a0 w14_1338 b14_14a0 b14_13a0 b14_1040 b14_340 w14_1334 w14_1330 w14_132c w14_1328 w14_1324 w14_1320 w14_464 w14_460 w14_130 w14_12c w14_128 w14_124 w14_120 w14_11c w14_118 w14_114 w14_110 w14_10c w14_108 w14_104 w14_100 w14_fc w14_f8 w14_f4 w14_f0 w14_ec w14_e8 w14_e4 w14_e0 w14_dc w14_d8 w14_d4 w14_d0 w14_cc w14_c8 w14_c4 w14_c0 w14_bc w14_b8 w14_b4 w14_b0 w14_ac w14_a8 w14_a4 w14_a0 w14_9c w14_98 w14_94 w14_90 w14_8c w14_88 w14_84 w14_80 w14_7c w14_78 w14_74 w14_70 w14_6c w14_68 w14_64 w14_60 w14_5c w14_58 w14_54 w14_50 w14_4c w14_44 w14_40 w14_3c w14_38 w14_34 w14_20 w14_1c g14_27 g14_26 g14_24 g14_19 g14_18 g14_11 g14_10 g14_4 g14_3 g14_2 V14 E14 fR14 t14 rg14 W14 K14 fr14 s14 d14
  -- 0x1D88: sw
  obtain ⟨n16, d16, s16, fr16, K16, W16, rg16⟩ := sv_sw F E15 s15 sv_at_1d88 (off' := 0x1D8A) (c := 0x133C)
    (by decide) (by rw [g15_10]; sv_addr) (by decide) (by decide)
  have t16 : Steps n0 n16 := t15.trans d16
  have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : SvCode n16.mem := E15.fr F fr16
  have V16 : SvSaves B n16.mem v := V15.keep K16 (by decide)
  have g16_2 : reg n16 sp = B + 0x21A0 := by rw [rg16 sp, g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg16 (3 : Fin 32), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg16 (4 : Fin 32), g15_4]
  have g16_10 : reg n16 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg16 a0, g15_10]
  have g16_11 : reg n16 a1 = rhi := by rw [rg16 a1, g15_11]
  have g16_18 : reg n16 (18 : Fin 32) = out := by rw [rg16 (18 : Fin 32), g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [rg16 (19 : Fin 32), g15_19]
  have g16_24 : reg n16 (24 : Fin 32) = ulo := by rw [rg16 (24 : Fin 32), g15_24]
  have g16_26 : reg n16 (26 : Fin 32) = x26 := by rw [rg16 (26 : Fin 32), g15_26]
  have g16_27 : reg n16 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg16 (27 : Fin 32), g15_27]
  have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4), (0x1338, 0x4), (0x133C, 0x4)] := keep_kk15.trans K16.toL
  clear keep_kk15
  have w16_1c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 ns := (K16.w32 (by decide) (by decide)).trans w15_1c
  have w16_20 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = nzw := (K16.w32 (by decide) (by decide)).trans w15_20
  have w16_34 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = dlo := (K16.w32 (by decide) (by decide)).trans w15_34
  have w16_38 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = dhi := (K16.w32 (by decide) (by decide)).trans w15_38
  have w16_3c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = uhi := (K16.w32 (by decide) (by decide)).trans w15_3c
  have w16_40 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = vhi := (K16.w32 (by decide) (by decide)).trans w15_40
  have w16_44 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = vlo := (K16.w32 (by decide) (by decide)).trans w15_44
  have w16_4c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K16.w32 (by decide) (by decide)).trans w15_4c
  have w16_50 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K16.w32 (by decide) (by decide)).trans w15_50
  have w16_54 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K16.w32 (by decide) (by decide)).trans w15_54
  have w16_58 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K16.w32 (by decide) (by decide)).trans w15_58
  have w16_5c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rlo := (K16.w32 (by decide) (by decide)).trans w15_5c
  have w16_60 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = qhi := (K16.w32 (by decide) (by decide)).trans w15_60
  have w16_64 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K16.w32 (by decide) (by decide)).trans w15_64
  have w16_68 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K16.w32 (by decide) (by decide)).trans w15_68
  have w16_6c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K16.w32 (by decide) (by decide)).trans w15_6c
  have w16_70 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = qlo := (K16.w32 (by decide) (by decide)).trans w15_70
  have w16_74 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = rhi := (K16.w32 (by decide) (by decide)).trans w15_74
  have w16_78 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := (K16.w32 (by decide) (by decide)).trans w15_78
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
  have w16_1320 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = ulo := (K16.w32 (by decide) (by decide)).trans w15_1320
  have w16_1324 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = uhi := (K16.w32 (by decide) (by decide)).trans w15_1324
  have w16_1328 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = vlo := (K16.w32 (by decide) (by decide)).trans w15_1328
  have w16_132c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = vhi := (K16.w32 (by decide) (by decide)).trans w15_132c
  have w16_1330 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = qlo := (K16.w32 (by decide) (by decide)).trans w15_1330
  have w16_1334 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = qhi := (K16.w32 (by decide) (by decide)).trans w15_1334
  have w16_1338 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) = rlo := (K16.w32 (by decide) (by decide)).trans w15_1338
  have b16_340 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = fs := (K16.b8 (by decide) (by decide)).trans b15_340
  have b16_1040 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = es := (K16.b8 (by decide) (by decide)).trans b15_1040
  have b16_13a0 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = gs := (K16.b8 (by decide) (by decide)).trans b15_13a0
  have b16_14a0 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = ds := (K16.b8 (by decide) (by decide)).trans b15_14a0
  have w16_133c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x133C) = rhi := by rw [W16, g15_11]
  have a16_2a0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K16.acc (by decide) (by decide)).trans a15_2a0
  have a16_2c0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K16.acc (by decide) (by decide)).trans a15_2c0
  have a16_2e0 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K16.acc (by decide) (by decide)).trans a15_2e0
  have a16_320 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = fv := (K16.acc (by decide) (by decide)).trans a15_320
  have a16_420 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := (K16.acc (by decide) (by decide)).trans a15_420
  have a16_440 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := (K16.acc (by decide) (by decide)).trans a15_440
  have a16_1020 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = ev := (K16.acc (by decide) (by decide)).trans a15_1020
  have a16_1380 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = gv := (K16.acc (by decide) (by decide)).trans a15_1380
  have a16_1480 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = dv := (K16.acc (by decide) (by decide)).trans a15_1480
  have a16_15a8 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := (K16.acc (by decide) (by decide)).trans a15_15a8
  have a16_15c8 : accV n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := (K16.acc (by decide) (by decide)).trans a15_15c8
  clear a15_15c8 a15_15a8 a15_1480 a15_1380 a15_1020 a15_440 a15_420 a15_320 a15_2e0 a15_2c0 a15_2a0 b15_14a0 b15_13a0 b15_1040 b15_340 w15_1338 w15_1334 w15_1330 w15_132c w15_1328 w15_1324 w15_1320 w15_464 w15_460 w15_130 w15_12c w15_128 w15_124 w15_120 w15_11c w15_118 w15_114 w15_110 w15_10c w15_108 w15_104 w15_100 w15_fc w15_f8 w15_f4 w15_f0 w15_ec w15_e8 w15_e4 w15_e0 w15_dc w15_d8 w15_d4 w15_d0 w15_cc w15_c8 w15_c4 w15_c0 w15_bc w15_b8 w15_b4 w15_b0 w15_ac w15_a8 w15_a4 w15_a0 w15_9c w15_98 w15_94 w15_90 w15_8c w15_88 w15_84 w15_80 w15_7c w15_78 w15_74 w15_70 w15_6c w15_68 w15_64 w15_60 w15_5c w15_58 w15_54 w15_50 w15_4c w15_44 w15_40 w15_3c w15_38 w15_34 w15_20 w15_1c g15_11 g15_27 g15_26 g15_24 g15_19 g15_18 g15_10 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 m15 s15 u15 d15
  -- 0x1D8A
  obtain ⟨n17, c17, u17⟩ := s16.block svZB1d8a E16.self svZB1d8a_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m17 : n17.mem = n16.mem := u17.mem
  have s17 : St n17.mem SV n17 0x1DA4 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
  have rb17 : ∀ q, reg n17 q = (runBlock svZB1d8a (n16.mem, reg n16)).2 q := fun q => by rw [u17.regs]
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
  have g17_18 : reg n17 (18 : Fin 32) = out := by
    rw [rb17, runBlock_reg _ _ _ (18 : Fin 32) s16.zero (by decide), g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = bp := by
    rw [rb17, runBlock_reg _ _ _ (19 : Fin 32) s16.zero (by decide), g16_19]
  have g17_24 : reg n17 (24 : Fin 32) = ulo := by
    rw [rb17, runBlock_reg _ _ _ (24 : Fin 32) s16.zero (by decide), g16_24]
  have g17_26 : reg n17 (26 : Fin 32) = x26 := by
    rw [rb17, runBlock_reg _ _ _ (26 : Fin 32) s16.zero (by decide), g16_26]
  have g17_27 : reg n17 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb17, runBlock_reg _ _ _ (27 : Fin 32) s16.zero (by decide), g16_27]
  have g17_10 : reg n17 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, svZB1d8a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_10, g16_11, g16_18, g16_19, g16_24, g16_26, g16_27, s16.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g17_11 : reg n17 a1 = B + 0x21A0 + BitVec.ofNat 32 0x320 := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, svZB1d8a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_10, g16_11, g16_18, g16_19, g16_24, g16_26, g16_27, s16.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g17_12 : reg n17 a2 = B + 0x21A0 + BitVec.ofNat 32 0x1380 := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, svZB1d8a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_10, g16_11, g16_18, g16_19, g16_24, g16_26, g16_27, s16.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g17_13 : reg n17 a3 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, svZB1d8a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_10, g16_11, g16_18, g16_19, g16_24, g16_26, g16_27, s16.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4), (0x1338, 0x4), (0x133C, 0x4)] := by rw [m17]; exact keep_kk16
  clear keep_kk16
  have w17_1c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 ns := by rw [m17]; exact w16_1c
  have w17_20 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = nzw := by rw [m17]; exact w16_20
  have w17_34 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = dlo := by rw [m17]; exact w16_34
  have w17_38 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = dhi := by rw [m17]; exact w16_38
  have w17_3c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = uhi := by rw [m17]; exact w16_3c
  have w17_40 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = vhi := by rw [m17]; exact w16_40
  have w17_44 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = vlo := by rw [m17]; exact w16_44
  have w17_4c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m17]; exact w16_4c
  have w17_50 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m17]; exact w16_50
  have w17_54 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m17]; exact w16_54
  have w17_58 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m17]; exact w16_58
  have w17_5c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rlo := by rw [m17]; exact w16_5c
  have w17_60 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = qhi := by rw [m17]; exact w16_60
  have w17_64 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m17]; exact w16_64
  have w17_68 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m17]; exact w16_68
  have w17_6c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m17]; exact w16_6c
  have w17_70 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = qlo := by rw [m17]; exact w16_70
  have w17_74 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = rhi := by rw [m17]; exact w16_74
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
  have w17_460 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m17]; exact w16_460
  have w17_464 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m17]; exact w16_464
  have w17_1320 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = ulo := by rw [m17]; exact w16_1320
  have w17_1324 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = uhi := by rw [m17]; exact w16_1324
  have w17_1328 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = vlo := by rw [m17]; exact w16_1328
  have w17_132c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = vhi := by rw [m17]; exact w16_132c
  have w17_1330 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = qlo := by rw [m17]; exact w16_1330
  have w17_1334 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = qhi := by rw [m17]; exact w16_1334
  have w17_1338 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) = rlo := by rw [m17]; exact w16_1338
  have w17_133c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x133C) = rhi := by rw [m17]; exact w16_133c
  have b17_340 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = fs := by rw [m17]; exact b16_340
  have b17_1040 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = es := by rw [m17]; exact b16_1040
  have b17_13a0 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = gs := by rw [m17]; exact b16_13a0
  have b17_14a0 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = ds := by rw [m17]; exact b16_14a0
  have a17_2a0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m17]; exact a16_2a0
  have a17_2c0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m17]; exact a16_2c0
  have a17_2e0 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m17]; exact a16_2e0
  have a17_320 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = fv := by rw [m17]; exact a16_320
  have a17_420 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := by rw [m17]; exact a16_420
  have a17_440 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := by rw [m17]; exact a16_440
  have a17_1020 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = ev := by rw [m17]; exact a16_1020
  have a17_1380 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = gv := by rw [m17]; exact a16_1380
  have a17_1480 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = dv := by rw [m17]; exact a16_1480
  have a17_15a8 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := by rw [m17]; exact a16_15a8
  have a17_15c8 : accV n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := by rw [m17]; exact a16_15c8
  clear a16_15c8 a16_15a8 a16_1480 a16_1380 a16_1020 a16_440 a16_420 a16_320 a16_2e0 a16_2c0 a16_2a0 w16_133c b16_14a0 b16_13a0 b16_1040 b16_340 w16_1338 w16_1334 w16_1330 w16_132c w16_1328 w16_1324 w16_1320 w16_464 w16_460 w16_130 w16_12c w16_128 w16_124 w16_120 w16_11c w16_118 w16_114 w16_110 w16_10c w16_108 w16_104 w16_100 w16_fc w16_f8 w16_f4 w16_f0 w16_ec w16_e8 w16_e4 w16_e0 w16_dc w16_d8 w16_d4 w16_d0 w16_cc w16_c8 w16_c4 w16_c0 w16_bc w16_b8 w16_b4 w16_b0 w16_ac w16_a8 w16_a4 w16_a0 w16_9c w16_98 w16_94 w16_90 w16_8c w16_88 w16_84 w16_80 w16_7c w16_78 w16_74 w16_70 w16_6c w16_68 w16_64 w16_60 w16_5c w16_58 w16_54 w16_50 w16_4c w16_44 w16_40 w16_3c w16_38 w16_34 w16_20 w16_1c g16_27 g16_26 g16_24 g16_19 g16_18 g16_11 g16_10 g16_4 g16_3 g16_2 V16 E16 fR16 t16 rg16 W16 K16 fr16 s16 d16
  -- 0x1DA4: lw
  obtain ⟨n18, d18, u18⟩ := s17.lw E17.self sv_at_1da4 (off' := 0x1DA6) (by decide)
    (by rw [g17_2, show B + 0x21A0 + 0x1C = B + 0x21A0 + BitVec.ofNat 32 0x1C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s18 : St n18.mem SV n18 0x1DA6 (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
  have m18 : n18.mem = n17.mem := u18.mem
  have fr18 : ∀ x, SvR B x → n18.mem x = n17.mem x := fun x _ => by rw [m18]
  have t18 : Steps n0 n18 := t17.trans (.single d18)
  have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : SvCode n18.mem := E17.fr F fr18
  have V18 : SvSaves B n18.mem v := V17.same m18
  have g18_2 : reg n18 sp = B + 0x21A0 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u18.regs, upd_ne (by decide) (by decide), g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u18.regs, upd_ne (by decide) (by decide), g17_4]
  have g18_10 : reg n18 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_10]
  have g18_11 : reg n18 a1 = B + 0x21A0 + BitVec.ofNat 32 0x320 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_11]
  have g18_12 : reg n18 a2 = B + 0x21A0 + BitVec.ofNat 32 0x1380 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_12]
  have g18_13 : reg n18 a3 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_13]
  have g18_18 : reg n18 (18 : Fin 32) = out := by rw [u18.regs, upd_ne (by decide) (by decide), g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_19]
  have g18_24 : reg n18 (24 : Fin 32) = ulo := by rw [u18.regs, upd_ne (by decide) (by decide), g17_24]
  have g18_26 : reg n18 (26 : Fin 32) = x26 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_26]
  have g18_27 : reg n18 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_27]
  have g18_8 : reg n18 (8 : Fin 32) = BitVec.ofNat 32 ns := by
    rw [u18.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g17_2, show B + 0x21A0 + 0x1C = B + 0x21A0 + BitVec.ofNat 32 0x1C by sv_addr, w17_1c]
  have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4), (0x1338, 0x4), (0x133C, 0x4)] := by rw [m18]; exact keep_kk17
  clear keep_kk17
  have w18_1c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 ns := by rw [m18]; exact w17_1c
  have w18_20 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = nzw := by rw [m18]; exact w17_20
  have w18_34 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = dlo := by rw [m18]; exact w17_34
  have w18_38 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = dhi := by rw [m18]; exact w17_38
  have w18_3c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = uhi := by rw [m18]; exact w17_3c
  have w18_40 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = vhi := by rw [m18]; exact w17_40
  have w18_44 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = vlo := by rw [m18]; exact w17_44
  have w18_4c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m18]; exact w17_4c
  have w18_50 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m18]; exact w17_50
  have w18_54 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m18]; exact w17_54
  have w18_58 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m18]; exact w17_58
  have w18_5c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rlo := by rw [m18]; exact w17_5c
  have w18_60 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = qhi := by rw [m18]; exact w17_60
  have w18_64 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m18]; exact w17_64
  have w18_68 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m18]; exact w17_68
  have w18_6c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m18]; exact w17_6c
  have w18_70 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = qlo := by rw [m18]; exact w17_70
  have w18_74 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = rhi := by rw [m18]; exact w17_74
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
  have w18_460 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m18]; exact w17_460
  have w18_464 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m18]; exact w17_464
  have w18_1320 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = ulo := by rw [m18]; exact w17_1320
  have w18_1324 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = uhi := by rw [m18]; exact w17_1324
  have w18_1328 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = vlo := by rw [m18]; exact w17_1328
  have w18_132c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = vhi := by rw [m18]; exact w17_132c
  have w18_1330 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = qlo := by rw [m18]; exact w17_1330
  have w18_1334 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = qhi := by rw [m18]; exact w17_1334
  have w18_1338 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) = rlo := by rw [m18]; exact w17_1338
  have w18_133c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x133C) = rhi := by rw [m18]; exact w17_133c
  have b18_340 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = fs := by rw [m18]; exact b17_340
  have b18_1040 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = es := by rw [m18]; exact b17_1040
  have b18_13a0 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = gs := by rw [m18]; exact b17_13a0
  have b18_14a0 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = ds := by rw [m18]; exact b17_14a0
  have a18_2a0 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m18]; exact a17_2a0
  have a18_2c0 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m18]; exact a17_2c0
  have a18_2e0 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m18]; exact a17_2e0
  have a18_320 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = fv := by rw [m18]; exact a17_320
  have a18_420 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := by rw [m18]; exact a17_420
  have a18_440 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := by rw [m18]; exact a17_440
  have a18_1020 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = ev := by rw [m18]; exact a17_1020
  have a18_1380 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = gv := by rw [m18]; exact a17_1380
  have a18_1480 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = dv := by rw [m18]; exact a17_1480
  have a18_15a8 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := by rw [m18]; exact a17_15a8
  have a18_15c8 : accV n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := by rw [m18]; exact a17_15c8
  clear a17_15c8 a17_15a8 a17_1480 a17_1380 a17_1020 a17_440 a17_420 a17_320 a17_2e0 a17_2c0 a17_2a0 b17_14a0 b17_13a0 b17_1040 b17_340 w17_133c w17_1338 w17_1334 w17_1330 w17_132c w17_1328 w17_1324 w17_1320 w17_464 w17_460 w17_130 w17_12c w17_128 w17_124 w17_120 w17_11c w17_118 w17_114 w17_110 w17_10c w17_108 w17_104 w17_100 w17_fc w17_f8 w17_f4 w17_f0 w17_ec w17_e8 w17_e4 w17_e0 w17_dc w17_d8 w17_d4 w17_d0 w17_cc w17_c8 w17_c4 w17_c0 w17_bc w17_b8 w17_b4 w17_b0 w17_ac w17_a8 w17_a4 w17_a0 w17_9c w17_98 w17_94 w17_90 w17_8c w17_88 w17_84 w17_80 w17_7c w17_78 w17_74 w17_70 w17_6c w17_68 w17_64 w17_60 w17_5c w17_58 w17_54 w17_50 w17_4c w17_44 w17_40 w17_3c w17_38 w17_34 w17_20 w17_1c g17_13 g17_12 g17_11 g17_10 g17_27 g17_26 g17_24 g17_19 g17_18 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 rb17 s17 m17 u17 c17
  -- 0x1DA6
  obtain ⟨n19, c19, u19⟩ := s18.block svZB1da6 E18.self svZB1da6_end
    ⟨trivial, trivial⟩
  have m19 : n19.mem = n18.mem := u19.mem
  have s19 : St n19.mem SV n19 0x1DA8 (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
  have rb19 : ∀ q, reg n19 q = (runBlock svZB1da6 (n18.mem, reg n18)).2 q := fun q => by rw [u19.regs]
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
  have g19_8 : reg n19 (8 : Fin 32) = BitVec.ofNat 32 ns := by
    rw [rb19, runBlock_reg _ _ _ (8 : Fin 32) s18.zero (by decide), g18_8]
  have g19_10 : reg n19 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb19, runBlock_reg _ _ _ a0 s18.zero (by decide), g18_10]
  have g19_11 : reg n19 a1 = B + 0x21A0 + BitVec.ofNat 32 0x320 := by
    rw [rb19, runBlock_reg _ _ _ a1 s18.zero (by decide), g18_11]
  have g19_12 : reg n19 a2 = B + 0x21A0 + BitVec.ofNat 32 0x1380 := by
    rw [rb19, runBlock_reg _ _ _ a2 s18.zero (by decide), g18_12]
  have g19_13 : reg n19 a3 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
    rw [rb19, runBlock_reg _ _ _ a3 s18.zero (by decide), g18_13]
  have g19_18 : reg n19 (18 : Fin 32) = out := by
    rw [rb19, runBlock_reg _ _ _ (18 : Fin 32) s18.zero (by decide), g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = bp := by
    rw [rb19, runBlock_reg _ _ _ (19 : Fin 32) s18.zero (by decide), g18_19]
  have g19_24 : reg n19 (24 : Fin 32) = ulo := by
    rw [rb19, runBlock_reg _ _ _ (24 : Fin 32) s18.zero (by decide), g18_24]
  have g19_26 : reg n19 (26 : Fin 32) = x26 := by
    rw [rb19, runBlock_reg _ _ _ (26 : Fin 32) s18.zero (by decide), g18_26]
  have g19_27 : reg n19 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb19, runBlock_reg _ _ _ (27 : Fin 32) s18.zero (by decide), g18_27]
  have g19_14 : reg n19 a4 = BitVec.ofNat 32 ns := by
    rw [rb19]; simp +decide only [runBlock, BInstr.run, svZB1da6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g18_2, g18_3, g18_4, g18_8, g18_10, g18_11, g18_12, g18_13, g18_18, g18_19, g18_24, g18_26, g18_27, s18.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4), (0x1338, 0x4), (0x133C, 0x4)] := by rw [m19]; exact keep_kk18
  clear keep_kk18
  have w19_1c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 ns := by rw [m19]; exact w18_1c
  have w19_20 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = nzw := by rw [m19]; exact w18_20
  have w19_34 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = dlo := by rw [m19]; exact w18_34
  have w19_38 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = dhi := by rw [m19]; exact w18_38
  have w19_3c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = uhi := by rw [m19]; exact w18_3c
  have w19_40 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = vhi := by rw [m19]; exact w18_40
  have w19_44 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = vlo := by rw [m19]; exact w18_44
  have w19_4c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m19]; exact w18_4c
  have w19_50 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m19]; exact w18_50
  have w19_54 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m19]; exact w18_54
  have w19_58 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m19]; exact w18_58
  have w19_5c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rlo := by rw [m19]; exact w18_5c
  have w19_60 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = qhi := by rw [m19]; exact w18_60
  have w19_64 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m19]; exact w18_64
  have w19_68 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m19]; exact w18_68
  have w19_6c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m19]; exact w18_6c
  have w19_70 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = qlo := by rw [m19]; exact w18_70
  have w19_74 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = rhi := by rw [m19]; exact w18_74
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
  have w19_460 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m19]; exact w18_460
  have w19_464 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m19]; exact w18_464
  have w19_1320 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = ulo := by rw [m19]; exact w18_1320
  have w19_1324 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = uhi := by rw [m19]; exact w18_1324
  have w19_1328 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = vlo := by rw [m19]; exact w18_1328
  have w19_132c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = vhi := by rw [m19]; exact w18_132c
  have w19_1330 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = qlo := by rw [m19]; exact w18_1330
  have w19_1334 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = qhi := by rw [m19]; exact w18_1334
  have w19_1338 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) = rlo := by rw [m19]; exact w18_1338
  have w19_133c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x133C) = rhi := by rw [m19]; exact w18_133c
  have b19_340 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = fs := by rw [m19]; exact b18_340
  have b19_1040 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = es := by rw [m19]; exact b18_1040
  have b19_13a0 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = gs := by rw [m19]; exact b18_13a0
  have b19_14a0 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = ds := by rw [m19]; exact b18_14a0
  have a19_2a0 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m19]; exact a18_2a0
  have a19_2c0 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m19]; exact a18_2c0
  have a19_2e0 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m19]; exact a18_2e0
  have a19_320 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = fv := by rw [m19]; exact a18_320
  have a19_420 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := by rw [m19]; exact a18_420
  have a19_440 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := by rw [m19]; exact a18_440
  have a19_1020 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = ev := by rw [m19]; exact a18_1020
  have a19_1380 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = gv := by rw [m19]; exact a18_1380
  have a19_1480 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = dv := by rw [m19]; exact a18_1480
  have a19_15a8 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := by rw [m19]; exact a18_15a8
  have a19_15c8 : accV n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := by rw [m19]; exact a18_15c8
  clear a18_15c8 a18_15a8 a18_1480 a18_1380 a18_1020 a18_440 a18_420 a18_320 a18_2e0 a18_2c0 a18_2a0 b18_14a0 b18_13a0 b18_1040 b18_340 w18_133c w18_1338 w18_1334 w18_1330 w18_132c w18_1328 w18_1324 w18_1320 w18_464 w18_460 w18_130 w18_12c w18_128 w18_124 w18_120 w18_11c w18_118 w18_114 w18_110 w18_10c w18_108 w18_104 w18_100 w18_fc w18_f8 w18_f4 w18_f0 w18_ec w18_e8 w18_e4 w18_e0 w18_dc w18_d8 w18_d4 w18_d0 w18_cc w18_c8 w18_c4 w18_c0 w18_bc w18_b8 w18_b4 w18_b0 w18_ac w18_a8 w18_a4 w18_a0 w18_9c w18_98 w18_94 w18_90 w18_8c w18_88 w18_84 w18_80 w18_7c w18_78 w18_74 w18_70 w18_6c w18_68 w18_64 w18_60 w18_5c w18_58 w18_54 w18_50 w18_4c w18_44 w18_40 w18_3c w18_38 w18_34 w18_20 w18_1c g18_8 g18_27 g18_26 g18_24 g18_19 g18_18 g18_13 g18_12 g18_11 g18_10 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 m18 s18 u18 d18
  -- 0x1DA8: sv_ufg8F
  obtain ⟨n20, c20, s20, sp20, rk20, R1_20, R2_20, K20, fr20⟩ := sv_ufg8F (co := 0xA20) (ca := 0x320) (cb := 0x1380) (ct := 0x1320) (s := ns)
    F E19 (UC0.sv F fR19) s19 sv_at_1da8 sv_at_1dac (by decide) (by decide) g19_2
    g19_10 g19_11 g19_12 g19_13 g19_14 hns1 (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) 
    (by rw [show 0x320 + 0x20 = 0x340 from rfl, b19_340]; exact hfs)
    (by rw [show 0x1380 + 0x20 = 0x13A0 from rfl, b19_13a0]; exact hgs)
  obtain ⟨σ20a, A20a, hσ0_20, e0_20, bb0_20, vv0_20⟩ := R1_20
  simp only [svI, svM, show 0x320 + 0x20 = 0x340 from rfl, show 0x1380 + 0x20 = 0x13A0 from rfl,
    show 0x1320 + 0x0 = 0x1320 from rfl, show 0x1320 + 0x8 = 0x1328 from rfl] at e0_20
  rw [b19_340, a19_320, b19_13a0, a19_1380,
    acc2_frame w19_1320 w19_1324, acc2_frame w19_1328 w19_132c] at e0_20
  obtain ⟨σ20b, A20b, hσ1_20, e1_20, bb1_20, vv1_20⟩ := R2_20
  simp only [svI, svM, show 0x320 + 0x20 = 0x340 from rfl, show 0x1380 + 0x20 = 0x13A0 from rfl,
    show 0x1320 + 0x10 = 0x1330 from rfl, show 0x1320 + 0x18 = 0x1338 from rfl] at e1_20
  rw [b19_340, a19_320, b19_13a0, a19_1380,
    acc2_frame w19_1330 w19_1334, acc2_frame w19_1338 w19_133c] at e1_20
  have t20 : Steps n0 n20 := t19.trans c20
  have fR20 : ∀ x, SvR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
  have E20 : SvCode n20.mem := E19.fr F fr20
  have V20 : SvSaves B n20.mem v := V19.keepL K20 (by decide)
  have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk20 (3 : Fin 32) (by decide), g19_3]
  have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk20 (4 : Fin 32) (by decide), g19_4]
  have g20_8 : reg n20 (8 : Fin 32) = BitVec.ofNat 32 ns := by rw [rk20 (8 : Fin 32) (by decide), g19_8]
  have g20_18 : reg n20 (18 : Fin 32) = out := by rw [rk20 (18 : Fin 32) (by decide), g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = bp := by rw [rk20 (19 : Fin 32) (by decide), g19_19]
  have g20_24 : reg n20 (24 : Fin 32) = ulo := by rw [rk20 (24 : Fin 32) (by decide), g19_24]
  have g20_26 : reg n20 (26 : Fin 32) = x26 := by rw [rk20 (26 : Fin 32) (by decide), g19_26]
  have g20_27 : reg n20 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk20 (27 : Fin 32) (by decide), g19_27]
  have g20_2 : reg n20 sp = B + 0x21A0 := sp20
  have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4), (0x1338, 0x4), (0x133C, 0x4), (0xA20, 0x45)] := keep_kk19.trans K20
  clear keep_kk19
  have w20_1c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 ns := (K20.w32 (by decide) (by decide)).trans w19_1c
  have w20_20 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = nzw := (K20.w32 (by decide) (by decide)).trans w19_20
  have w20_34 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = dlo := (K20.w32 (by decide) (by decide)).trans w19_34
  have w20_38 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = dhi := (K20.w32 (by decide) (by decide)).trans w19_38
  have w20_3c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = uhi := (K20.w32 (by decide) (by decide)).trans w19_3c
  have w20_40 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = vhi := (K20.w32 (by decide) (by decide)).trans w19_40
  have w20_44 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = vlo := (K20.w32 (by decide) (by decide)).trans w19_44
  have w20_4c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K20.w32 (by decide) (by decide)).trans w19_4c
  have w20_50 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K20.w32 (by decide) (by decide)).trans w19_50
  have w20_54 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K20.w32 (by decide) (by decide)).trans w19_54
  have w20_58 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K20.w32 (by decide) (by decide)).trans w19_58
  have w20_5c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rlo := (K20.w32 (by decide) (by decide)).trans w19_5c
  have w20_60 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = qhi := (K20.w32 (by decide) (by decide)).trans w19_60
  have w20_64 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K20.w32 (by decide) (by decide)).trans w19_64
  have w20_68 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K20.w32 (by decide) (by decide)).trans w19_68
  have w20_6c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K20.w32 (by decide) (by decide)).trans w19_6c
  have w20_70 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = qlo := (K20.w32 (by decide) (by decide)).trans w19_70
  have w20_74 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = rhi := (K20.w32 (by decide) (by decide)).trans w19_74
  have w20_78 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := (K20.w32 (by decide) (by decide)).trans w19_78
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
  have w20_1320 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = ulo := (K20.w32 (by decide) (by decide)).trans w19_1320
  have w20_1324 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = uhi := (K20.w32 (by decide) (by decide)).trans w19_1324
  have w20_1328 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = vlo := (K20.w32 (by decide) (by decide)).trans w19_1328
  have w20_132c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = vhi := (K20.w32 (by decide) (by decide)).trans w19_132c
  have w20_1330 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = qlo := (K20.w32 (by decide) (by decide)).trans w19_1330
  have w20_1334 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = qhi := (K20.w32 (by decide) (by decide)).trans w19_1334
  have w20_1338 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) = rlo := (K20.w32 (by decide) (by decide)).trans w19_1338
  have w20_133c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x133C) = rhi := (K20.w32 (by decide) (by decide)).trans w19_133c
  have b20_340 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = fs := (K20.b8 (by decide) (by decide)).trans b19_340
  have b20_1040 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = es := (K20.b8 (by decide) (by decide)).trans b19_1040
  have b20_13a0 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = gs := (K20.b8 (by decide) (by decide)).trans b19_13a0
  have b20_14a0 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = ds := (K20.b8 (by decide) (by decide)).trans b19_14a0
  have a20_2a0 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K20.acc (by decide) (by decide)).trans a19_2a0
  have a20_2c0 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K20.acc (by decide) (by decide)).trans a19_2c0
  have a20_2e0 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K20.acc (by decide) (by decide)).trans a19_2e0
  have a20_320 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = fv := (K20.acc (by decide) (by decide)).trans a19_320
  have a20_420 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := (K20.acc (by decide) (by decide)).trans a19_420
  have a20_440 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := (K20.acc (by decide) (by decide)).trans a19_440
  have a20_1020 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = ev := (K20.acc (by decide) (by decide)).trans a19_1020
  have a20_1380 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = gv := (K20.acc (by decide) (by decide)).trans a19_1380
  have a20_1480 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = dv := (K20.acc (by decide) (by decide)).trans a19_1480
  have a20_15a8 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := (K20.acc (by decide) (by decide)).trans a19_15a8
  have a20_15c8 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := (K20.acc (by decide) (by decide)).trans a19_15c8
  have a20_a20 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 8 = A20a / 2 ^ ns % 2 ^ 256 := vv0_20
  have a20_a44 : accV n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) 8 = A20b / 2 ^ ns % 2 ^ 256 := vv1_20
  have b20_a40 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 8 σ20a := byte_of_toNat bb0_20
  have b20_a64 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA64) = BitVec.ofNat 8 σ20b := byte_of_toNat bb1_20
  clear a19_15c8 a19_15a8 a19_1480 a19_1380 a19_1020 a19_440 a19_420 a19_320 a19_2e0 a19_2c0 a19_2a0 b19_14a0 b19_13a0 b19_1040 b19_340 w19_133c w19_1338 w19_1334 w19_1330 w19_132c w19_1328 w19_1324 w19_1320 w19_464 w19_460 w19_130 w19_12c w19_128 w19_124 w19_120 w19_11c w19_118 w19_114 w19_110 w19_10c w19_108 w19_104 w19_100 w19_fc w19_f8 w19_f4 w19_f0 w19_ec w19_e8 w19_e4 w19_e0 w19_dc w19_d8 w19_d4 w19_d0 w19_cc w19_c8 w19_c4 w19_c0 w19_bc w19_b8 w19_b4 w19_b0 w19_ac w19_a8 w19_a4 w19_a0 w19_9c w19_98 w19_94 w19_90 w19_8c w19_88 w19_84 w19_80 w19_7c w19_78 w19_74 w19_70 w19_6c w19_68 w19_64 w19_60 w19_5c w19_58 w19_54 w19_50 w19_4c w19_44 w19_40 w19_3c w19_38 w19_34 w19_20 w19_1c g19_14 g19_27 g19_26 g19_24 g19_19 g19_18 g19_13 g19_12 g19_11 g19_10 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 rb19 s19 m19 u19 c19
  -- 0x1DB0
  obtain ⟨n21, c21, u21⟩ := s20.block svZB1db0 E20.self svZB1db0_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m21 : n21.mem = n20.mem := u21.mem
  have s21 : St n21.mem SV n21 0x1DBE (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
  have rb21 : ∀ q, reg n21 q = (runBlock svZB1db0 (n20.mem, reg n20)).2 q := fun q => by rw [u21.regs]
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
  have g21_18 : reg n21 (18 : Fin 32) = out := by
    rw [rb21, runBlock_reg _ _ _ (18 : Fin 32) s20.zero (by decide), g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = bp := by
    rw [rb21, runBlock_reg _ _ _ (19 : Fin 32) s20.zero (by decide), g20_19]
  have g21_24 : reg n21 (24 : Fin 32) = ulo := by
    rw [rb21, runBlock_reg _ _ _ (24 : Fin 32) s20.zero (by decide), g20_24]
  have g21_26 : reg n21 (26 : Fin 32) = x26 := by
    rw [rb21, runBlock_reg _ _ _ (26 : Fin 32) s20.zero (by decide), g20_26]
  have g21_27 : reg n21 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb21, runBlock_reg _ _ _ (27 : Fin 32) s20.zero (by decide), g20_27]
  have g21_10 : reg n21 a0 = B + 0x21A0 + BitVec.ofNat 32 0x320 := by
    rw [rb21]; simp +decide only [runBlock, BInstr.run, svZB1db0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g20_2, g20_3, g20_4, g20_8, g20_18, g20_19, g20_24, g20_26, g20_27, s20.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g21_11 : reg n21 a1 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb21]; simp +decide only [runBlock, BInstr.run, svZB1db0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g20_2, g20_3, g20_4, g20_8, g20_18, g20_19, g20_24, g20_26, g20_27, s20.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g21_12 : reg n21 a2 = BitVec.ofNat 32 0x24 := by
    rw [rb21]; simp +decide only [runBlock, BInstr.run, svZB1db0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g20_2, g20_3, g20_4, g20_8, g20_18, g20_19, g20_24, g20_26, g20_27, s20.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4), (0x1338, 0x4), (0x133C, 0x4), (0xA20, 0x45)] := by rw [m21]; exact keep_kk20
  clear keep_kk20
  have w21_1c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 ns := by rw [m21]; exact w20_1c
  have w21_20 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = nzw := by rw [m21]; exact w20_20
  have w21_34 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = dlo := by rw [m21]; exact w20_34
  have w21_38 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = dhi := by rw [m21]; exact w20_38
  have w21_3c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = uhi := by rw [m21]; exact w20_3c
  have w21_40 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = vhi := by rw [m21]; exact w20_40
  have w21_44 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = vlo := by rw [m21]; exact w20_44
  have w21_4c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m21]; exact w20_4c
  have w21_50 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m21]; exact w20_50
  have w21_54 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m21]; exact w20_54
  have w21_58 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m21]; exact w20_58
  have w21_5c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rlo := by rw [m21]; exact w20_5c
  have w21_60 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = qhi := by rw [m21]; exact w20_60
  have w21_64 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m21]; exact w20_64
  have w21_68 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m21]; exact w20_68
  have w21_6c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m21]; exact w20_6c
  have w21_70 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = qlo := by rw [m21]; exact w20_70
  have w21_74 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = rhi := by rw [m21]; exact w20_74
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
  have w21_460 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m21]; exact w20_460
  have w21_464 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m21]; exact w20_464
  have w21_1320 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = ulo := by rw [m21]; exact w20_1320
  have w21_1324 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = uhi := by rw [m21]; exact w20_1324
  have w21_1328 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = vlo := by rw [m21]; exact w20_1328
  have w21_132c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = vhi := by rw [m21]; exact w20_132c
  have w21_1330 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = qlo := by rw [m21]; exact w20_1330
  have w21_1334 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = qhi := by rw [m21]; exact w20_1334
  have w21_1338 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) = rlo := by rw [m21]; exact w20_1338
  have w21_133c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x133C) = rhi := by rw [m21]; exact w20_133c
  have b21_340 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = fs := by rw [m21]; exact b20_340
  have b21_a40 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 8 σ20a := by rw [m21]; exact b20_a40
  have b21_a64 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA64) = BitVec.ofNat 8 σ20b := by rw [m21]; exact b20_a64
  have b21_1040 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = es := by rw [m21]; exact b20_1040
  have b21_13a0 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = gs := by rw [m21]; exact b20_13a0
  have b21_14a0 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = ds := by rw [m21]; exact b20_14a0
  have a21_2a0 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m21]; exact a20_2a0
  have a21_2c0 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m21]; exact a20_2c0
  have a21_2e0 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m21]; exact a20_2e0
  have a21_320 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = fv := by rw [m21]; exact a20_320
  have a21_420 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := by rw [m21]; exact a20_420
  have a21_440 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := by rw [m21]; exact a20_440
  have a21_a20 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 8 = A20a / 2 ^ ns % 2 ^ 256 := by rw [m21]; exact a20_a20
  have a21_a44 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) 8 = A20b / 2 ^ ns % 2 ^ 256 := by rw [m21]; exact a20_a44
  have a21_1020 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = ev := by rw [m21]; exact a20_1020
  have a21_1380 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = gv := by rw [m21]; exact a20_1380
  have a21_1480 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = dv := by rw [m21]; exact a20_1480
  have a21_15a8 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := by rw [m21]; exact a20_15a8
  have a21_15c8 : accV n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := by rw [m21]; exact a20_15c8
  clear b20_a64 b20_a40 a20_a44 a20_a20 a20_15c8 a20_15a8 a20_1480 a20_1380 a20_1020 a20_440 a20_420 a20_320 a20_2e0 a20_2c0 a20_2a0 b20_14a0 b20_13a0 b20_1040 b20_340 w20_133c w20_1338 w20_1334 w20_1330 w20_132c w20_1328 w20_1324 w20_1320 w20_464 w20_460 w20_130 w20_12c w20_128 w20_124 w20_120 w20_11c w20_118 w20_114 w20_110 w20_10c w20_108 w20_104 w20_100 w20_fc w20_f8 w20_f4 w20_f0 w20_ec w20_e8 w20_e4 w20_e0 w20_dc w20_d8 w20_d4 w20_d0 w20_cc w20_c8 w20_c4 w20_c0 w20_bc w20_b8 w20_b4 w20_b0 w20_ac w20_a8 w20_a4 w20_a0 w20_9c w20_98 w20_94 w20_90 w20_8c w20_88 w20_84 w20_80 w20_7c w20_78 w20_74 w20_70 w20_6c w20_68 w20_64 w20_60 w20_5c w20_58 w20_54 w20_50 w20_4c w20_44 w20_40 w20_3c w20_38 w20_34 w20_20 w20_1c g20_2 g20_27 g20_26 g20_24 g20_19 g20_18 g20_8 g20_4 g20_3 V20 E20 fR20 t20 vv1_20 bb1_20 vv0_20 bb0_20 fr20 K20 rk20 sp20 s20 c20
  -- 0x1DBE: memcpy
  obtain ⟨n22, P22, K22, X22⟩ := sv_mc (c := 0x320) (d := 0xA20) (N := 0x24) F E21 s21 sv_at_1dbe sv_at_1dc2
    (by decide) (by decide) g21_2 g21_10 g21_11 g21_12
    (by decide) (by decide) (by decide)
  have s22 := P22.st
  have fr22 := P22.fr
  have t22 : Steps n0 n22 := t21.trans P22.steps
  have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
  have E22 : SvCode n22.mem := E21.fr F fr22
  have V22 : SvSaves B n22.mem v := V21.keep K22 (by decide)
  have g22_2 : reg n22 sp = B + 0x21A0 := by rw [P22.regs sp (by decide), g21_2]
  have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P22.regs (3 : Fin 32) (by decide), g21_3]
  have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P22.regs (4 : Fin 32) (by decide), g21_4]
  have g22_8 : reg n22 (8 : Fin 32) = BitVec.ofNat 32 ns := by rw [P22.regs (8 : Fin 32) (by decide), g21_8]
  have g22_18 : reg n22 (18 : Fin 32) = out := by rw [P22.regs (18 : Fin 32) (by decide), g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [P22.regs (19 : Fin 32) (by decide), g21_19]
  have g22_24 : reg n22 (24 : Fin 32) = ulo := by rw [P22.regs (24 : Fin 32) (by decide), g21_24]
  have g22_26 : reg n22 (26 : Fin 32) = x26 := by rw [P22.regs (26 : Fin 32) (by decide), g21_26]
  have g22_27 : reg n22 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P22.regs (27 : Fin 32) (by decide), g21_27]
  have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4), (0x1338, 0x4), (0x133C, 0x4), (0xA20, 0x45), (0x320, 0x24)] := keep_kk21.trans K22.toL
  clear keep_kk21
  have w22_1c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 ns := (K22.w32 (by decide) (by decide)).trans w21_1c
  have w22_20 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = nzw := (K22.w32 (by decide) (by decide)).trans w21_20
  have w22_34 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = dlo := (K22.w32 (by decide) (by decide)).trans w21_34
  have w22_38 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = dhi := (K22.w32 (by decide) (by decide)).trans w21_38
  have w22_3c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = uhi := (K22.w32 (by decide) (by decide)).trans w21_3c
  have w22_40 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = vhi := (K22.w32 (by decide) (by decide)).trans w21_40
  have w22_44 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = vlo := (K22.w32 (by decide) (by decide)).trans w21_44
  have w22_4c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K22.w32 (by decide) (by decide)).trans w21_4c
  have w22_50 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K22.w32 (by decide) (by decide)).trans w21_50
  have w22_54 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K22.w32 (by decide) (by decide)).trans w21_54
  have w22_58 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K22.w32 (by decide) (by decide)).trans w21_58
  have w22_5c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rlo := (K22.w32 (by decide) (by decide)).trans w21_5c
  have w22_60 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = qhi := (K22.w32 (by decide) (by decide)).trans w21_60
  have w22_64 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K22.w32 (by decide) (by decide)).trans w21_64
  have w22_68 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K22.w32 (by decide) (by decide)).trans w21_68
  have w22_6c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K22.w32 (by decide) (by decide)).trans w21_6c
  have w22_70 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = qlo := (K22.w32 (by decide) (by decide)).trans w21_70
  have w22_74 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = rhi := (K22.w32 (by decide) (by decide)).trans w21_74
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
  have w22_460 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := (K22.w32 (by decide) (by decide)).trans w21_460
  have w22_464 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := (K22.w32 (by decide) (by decide)).trans w21_464
  have w22_1320 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = ulo := (K22.w32 (by decide) (by decide)).trans w21_1320
  have w22_1324 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = uhi := (K22.w32 (by decide) (by decide)).trans w21_1324
  have w22_1328 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = vlo := (K22.w32 (by decide) (by decide)).trans w21_1328
  have w22_132c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = vhi := (K22.w32 (by decide) (by decide)).trans w21_132c
  have w22_1330 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = qlo := (K22.w32 (by decide) (by decide)).trans w21_1330
  have w22_1334 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = qhi := (K22.w32 (by decide) (by decide)).trans w21_1334
  have w22_1338 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) = rlo := (K22.w32 (by decide) (by decide)).trans w21_1338
  have w22_133c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x133C) = rhi := (K22.w32 (by decide) (by decide)).trans w21_133c
  have b22_a40 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 8 σ20a := (K22.b8 (by decide) (by decide)).trans b21_a40
  have b22_a64 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA64) = BitVec.ofNat 8 σ20b := (K22.b8 (by decide) (by decide)).trans b21_a64
  have b22_1040 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = es := (K22.b8 (by decide) (by decide)).trans b21_1040
  have b22_13a0 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = gs := (K22.b8 (by decide) (by decide)).trans b21_13a0
  have b22_14a0 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = ds := (K22.b8 (by decide) (by decide)).trans b21_14a0
  have b22_340 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = BitVec.ofNat 8 σ20a := by rw [show 0x340 = 0x320 + 0x20 from rfl, X22 0x20 (by decide)]; exact b21_a40
  have a22_2a0 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K22.acc (by decide) (by decide)).trans a21_2a0
  have a22_2c0 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K22.acc (by decide) (by decide)).trans a21_2c0
  have a22_2e0 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K22.acc (by decide) (by decide)).trans a21_2e0
  have a22_420 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := (K22.acc (by decide) (by decide)).trans a21_420
  have a22_440 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := (K22.acc (by decide) (by decide)).trans a21_440
  have a22_a20 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 8 = A20a / 2 ^ ns % 2 ^ 256 := (K22.acc (by decide) (by decide)).trans a21_a20
  have a22_a44 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) 8 = A20b / 2 ^ ns % 2 ^ 256 := (K22.acc (by decide) (by decide)).trans a21_a44
  have a22_1020 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = ev := (K22.acc (by decide) (by decide)).trans a21_1020
  have a22_1380 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = gv := (K22.acc (by decide) (by decide)).trans a21_1380
  have a22_1480 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = dv := (K22.acc (by decide) (by decide)).trans a21_1480
  have a22_15a8 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := (K22.acc (by decide) (by decide)).trans a21_15a8
  have a22_15c8 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := (K22.acc (by decide) (by decide)).trans a21_15c8
  have a22_320 : accV n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = A20a / 2 ^ ns % 2 ^ 256 := (accV_S 8 fun q hq => by
    rw [show 0x320 + q = 0x320 + (0x0 + q) by omega, X22 (0x0 + q) (by omega),
      show 0xA20 + (0x0 + q) = 0xA20 + q by omega]).trans a21_a20
  clear a21_15c8 a21_15a8 a21_1480 a21_1380 a21_1020 a21_a44 a21_a20 a21_440 a21_420 a21_320 a21_2e0 a21_2c0 a21_2a0 b21_14a0 b21_13a0 b21_1040 b21_a64 b21_a40 b21_340 w21_133c w21_1338 w21_1334 w21_1330 w21_132c w21_1328 w21_1324 w21_1320 w21_464 w21_460 w21_130 w21_12c w21_128 w21_124 w21_120 w21_11c w21_118 w21_114 w21_110 w21_10c w21_108 w21_104 w21_100 w21_fc w21_f8 w21_f4 w21_f0 w21_ec w21_e8 w21_e4 w21_e0 w21_dc w21_d8 w21_d4 w21_d0 w21_cc w21_c8 w21_c4 w21_c0 w21_bc w21_b8 w21_b4 w21_b0 w21_ac w21_a8 w21_a4 w21_a0 w21_9c w21_98 w21_94 w21_90 w21_8c w21_88 w21_84 w21_80 w21_7c w21_78 w21_74 w21_70 w21_6c w21_68 w21_64 w21_60 w21_5c w21_58 w21_54 w21_50 w21_4c w21_44 w21_40 w21_3c w21_38 w21_34 w21_20 w21_1c g21_12 g21_11 g21_10 g21_27 g21_26 g21_24 g21_19 g21_18 g21_8 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 rb21 s21 m21 u21 c21
  -- 0x1DC6
  obtain ⟨n23, c23, u23⟩ := s22.block svZB1dc6 E22.self svZB1dc6_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m23 : n23.mem = n22.mem := u23.mem
  have s23 : St n23.mem SV n23 0x1DDA (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
  have rb23 : ∀ q, reg n23 q = (runBlock svZB1dc6 (n22.mem, reg n22)).2 q := fun q => by rw [u23.regs]
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
  have g23_24 : reg n23 (24 : Fin 32) = ulo := by
    rw [rb23, runBlock_reg _ _ _ (24 : Fin 32) s22.zero (by decide), g22_24]
  have g23_26 : reg n23 (26 : Fin 32) = x26 := by
    rw [rb23, runBlock_reg _ _ _ (26 : Fin 32) s22.zero (by decide), g22_26]
  have g23_27 : reg n23 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb23, runBlock_reg _ _ _ (27 : Fin 32) s22.zero (by decide), g22_27]
  have g23_10 : reg n23 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1380 := by
    rw [rb23]; simp +decide only [runBlock, BInstr.run, svZB1dc6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g22_2, g22_3, g22_4, g22_8, g22_18, g22_19, g22_24, g22_26, g22_27, s22.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g23_11 : reg n23 a1 = B + 0x21A0 + BitVec.ofNat 32 0xA44 := by
    rw [rb23]; simp +decide only [runBlock, BInstr.run, svZB1dc6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g22_2, g22_3, g22_4, g22_8, g22_18, g22_19, g22_24, g22_26, g22_27, s22.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g23_12 : reg n23 a2 = BitVec.ofNat 32 0x24 := by
    rw [rb23]; simp +decide only [runBlock, BInstr.run, svZB1dc6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g22_2, g22_3, g22_4, g22_8, g22_18, g22_19, g22_24, g22_26, g22_27, s22.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4), (0x1338, 0x4), (0x133C, 0x4), (0xA20, 0x45), (0x320, 0x24)] := by rw [m23]; exact keep_kk22
  clear keep_kk22
  have w23_1c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 ns := by rw [m23]; exact w22_1c
  have w23_20 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = nzw := by rw [m23]; exact w22_20
  have w23_34 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = dlo := by rw [m23]; exact w22_34
  have w23_38 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = dhi := by rw [m23]; exact w22_38
  have w23_3c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = uhi := by rw [m23]; exact w22_3c
  have w23_40 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = vhi := by rw [m23]; exact w22_40
  have w23_44 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = vlo := by rw [m23]; exact w22_44
  have w23_4c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m23]; exact w22_4c
  have w23_50 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m23]; exact w22_50
  have w23_54 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m23]; exact w22_54
  have w23_58 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m23]; exact w22_58
  have w23_5c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rlo := by rw [m23]; exact w22_5c
  have w23_60 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = qhi := by rw [m23]; exact w22_60
  have w23_64 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m23]; exact w22_64
  have w23_68 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m23]; exact w22_68
  have w23_6c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m23]; exact w22_6c
  have w23_70 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = qlo := by rw [m23]; exact w22_70
  have w23_74 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = rhi := by rw [m23]; exact w22_74
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
  have w23_460 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m23]; exact w22_460
  have w23_464 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m23]; exact w22_464
  have w23_1320 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = ulo := by rw [m23]; exact w22_1320
  have w23_1324 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = uhi := by rw [m23]; exact w22_1324
  have w23_1328 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = vlo := by rw [m23]; exact w22_1328
  have w23_132c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = vhi := by rw [m23]; exact w22_132c
  have w23_1330 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = qlo := by rw [m23]; exact w22_1330
  have w23_1334 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = qhi := by rw [m23]; exact w22_1334
  have w23_1338 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) = rlo := by rw [m23]; exact w22_1338
  have w23_133c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x133C) = rhi := by rw [m23]; exact w22_133c
  have b23_340 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = BitVec.ofNat 8 σ20a := by rw [m23]; exact b22_340
  have b23_a40 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 8 σ20a := by rw [m23]; exact b22_a40
  have b23_a64 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA64) = BitVec.ofNat 8 σ20b := by rw [m23]; exact b22_a64
  have b23_1040 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = es := by rw [m23]; exact b22_1040
  have b23_13a0 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = gs := by rw [m23]; exact b22_13a0
  have b23_14a0 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = ds := by rw [m23]; exact b22_14a0
  have a23_2a0 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m23]; exact a22_2a0
  have a23_2c0 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m23]; exact a22_2c0
  have a23_2e0 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m23]; exact a22_2e0
  have a23_320 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = A20a / 2 ^ ns % 2 ^ 256 := by rw [m23]; exact a22_320
  have a23_420 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := by rw [m23]; exact a22_420
  have a23_440 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := by rw [m23]; exact a22_440
  have a23_a20 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 8 = A20a / 2 ^ ns % 2 ^ 256 := by rw [m23]; exact a22_a20
  have a23_a44 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) 8 = A20b / 2 ^ ns % 2 ^ 256 := by rw [m23]; exact a22_a44
  have a23_1020 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = ev := by rw [m23]; exact a22_1020
  have a23_1380 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = gv := by rw [m23]; exact a22_1380
  have a23_1480 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = dv := by rw [m23]; exact a22_1480
  have a23_15a8 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := by rw [m23]; exact a22_15a8
  have a23_15c8 : accV n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := by rw [m23]; exact a22_15c8
  clear a22_320 a22_15c8 a22_15a8 a22_1480 a22_1380 a22_1020 a22_a44 a22_a20 a22_440 a22_420 a22_2e0 a22_2c0 a22_2a0 b22_340 b22_14a0 b22_13a0 b22_1040 b22_a64 b22_a40 w22_133c w22_1338 w22_1334 w22_1330 w22_132c w22_1328 w22_1324 w22_1320 w22_464 w22_460 w22_130 w22_12c w22_128 w22_124 w22_120 w22_11c w22_118 w22_114 w22_110 w22_10c w22_108 w22_104 w22_100 w22_fc w22_f8 w22_f4 w22_f0 w22_ec w22_e8 w22_e4 w22_e0 w22_dc w22_d8 w22_d4 w22_d0 w22_cc w22_c8 w22_c4 w22_c0 w22_bc w22_b8 w22_b4 w22_b0 w22_ac w22_a8 w22_a4 w22_a0 w22_9c w22_98 w22_94 w22_90 w22_8c w22_88 w22_84 w22_80 w22_7c w22_78 w22_74 w22_70 w22_6c w22_68 w22_64 w22_60 w22_5c w22_58 w22_54 w22_50 w22_4c w22_44 w22_40 w22_3c w22_38 w22_34 w22_20 w22_1c g22_27 g22_26 g22_24 g22_19 g22_18 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 s22 X22 K22 P22
  -- 0x1DDA: memcpy
  obtain ⟨n24, P24, K24, X24⟩ := sv_mc (c := 0x1380) (d := 0xA44) (N := 0x24) F E23 s23 sv_at_1dda sv_at_1dde
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
  have g24_24 : reg n24 (24 : Fin 32) = ulo := by rw [P24.regs (24 : Fin 32) (by decide), g23_24]
  have g24_26 : reg n24 (26 : Fin 32) = x26 := by rw [P24.regs (26 : Fin 32) (by decide), g23_26]
  have g24_27 : reg n24 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P24.regs (27 : Fin 32) (by decide), g23_27]
  have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4), (0x1338, 0x4), (0x133C, 0x4), (0xA20, 0x45), (0x320, 0x24), (0x1380, 0x24)] := keep_kk23.trans K24.toL
  clear keep_kk23
  have w24_1c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 ns := (K24.w32 (by decide) (by decide)).trans w23_1c
  have w24_20 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = nzw := (K24.w32 (by decide) (by decide)).trans w23_20
  have w24_34 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = dlo := (K24.w32 (by decide) (by decide)).trans w23_34
  have w24_38 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = dhi := (K24.w32 (by decide) (by decide)).trans w23_38
  have w24_3c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = uhi := (K24.w32 (by decide) (by decide)).trans w23_3c
  have w24_40 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = vhi := (K24.w32 (by decide) (by decide)).trans w23_40
  have w24_44 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = vlo := (K24.w32 (by decide) (by decide)).trans w23_44
  have w24_4c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K24.w32 (by decide) (by decide)).trans w23_4c
  have w24_50 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K24.w32 (by decide) (by decide)).trans w23_50
  have w24_54 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K24.w32 (by decide) (by decide)).trans w23_54
  have w24_58 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K24.w32 (by decide) (by decide)).trans w23_58
  have w24_5c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rlo := (K24.w32 (by decide) (by decide)).trans w23_5c
  have w24_60 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = qhi := (K24.w32 (by decide) (by decide)).trans w23_60
  have w24_64 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K24.w32 (by decide) (by decide)).trans w23_64
  have w24_68 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K24.w32 (by decide) (by decide)).trans w23_68
  have w24_6c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K24.w32 (by decide) (by decide)).trans w23_6c
  have w24_70 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = qlo := (K24.w32 (by decide) (by decide)).trans w23_70
  have w24_74 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = rhi := (K24.w32 (by decide) (by decide)).trans w23_74
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
  have w24_460 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := (K24.w32 (by decide) (by decide)).trans w23_460
  have w24_464 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := (K24.w32 (by decide) (by decide)).trans w23_464
  have w24_1320 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = ulo := (K24.w32 (by decide) (by decide)).trans w23_1320
  have w24_1324 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = uhi := (K24.w32 (by decide) (by decide)).trans w23_1324
  have w24_1328 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = vlo := (K24.w32 (by decide) (by decide)).trans w23_1328
  have w24_132c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = vhi := (K24.w32 (by decide) (by decide)).trans w23_132c
  have w24_1330 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = qlo := (K24.w32 (by decide) (by decide)).trans w23_1330
  have w24_1334 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = qhi := (K24.w32 (by decide) (by decide)).trans w23_1334
  have w24_1338 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) = rlo := (K24.w32 (by decide) (by decide)).trans w23_1338
  have w24_133c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x133C) = rhi := (K24.w32 (by decide) (by decide)).trans w23_133c
  have b24_340 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = BitVec.ofNat 8 σ20a := (K24.b8 (by decide) (by decide)).trans b23_340
  have b24_a40 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 8 σ20a := (K24.b8 (by decide) (by decide)).trans b23_a40
  have b24_a64 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA64) = BitVec.ofNat 8 σ20b := (K24.b8 (by decide) (by decide)).trans b23_a64
  have b24_1040 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = es := (K24.b8 (by decide) (by decide)).trans b23_1040
  have b24_14a0 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = ds := (K24.b8 (by decide) (by decide)).trans b23_14a0
  have b24_13a0 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = BitVec.ofNat 8 σ20b := by rw [show 0x13A0 = 0x1380 + 0x20 from rfl, X24 0x20 (by decide)]; exact b23_a64
  have a24_2a0 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K24.acc (by decide) (by decide)).trans a23_2a0
  have a24_2c0 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K24.acc (by decide) (by decide)).trans a23_2c0
  have a24_2e0 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K24.acc (by decide) (by decide)).trans a23_2e0
  have a24_320 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = A20a / 2 ^ ns % 2 ^ 256 := (K24.acc (by decide) (by decide)).trans a23_320
  have a24_420 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := (K24.acc (by decide) (by decide)).trans a23_420
  have a24_440 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := (K24.acc (by decide) (by decide)).trans a23_440
  have a24_a20 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 8 = A20a / 2 ^ ns % 2 ^ 256 := (K24.acc (by decide) (by decide)).trans a23_a20
  have a24_a44 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) 8 = A20b / 2 ^ ns % 2 ^ 256 := (K24.acc (by decide) (by decide)).trans a23_a44
  have a24_1020 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = ev := (K24.acc (by decide) (by decide)).trans a23_1020
  have a24_1480 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = dv := (K24.acc (by decide) (by decide)).trans a23_1480
  have a24_15a8 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := (K24.acc (by decide) (by decide)).trans a23_15a8
  have a24_15c8 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := (K24.acc (by decide) (by decide)).trans a23_15c8
  have a24_1380 : accV n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = A20b / 2 ^ ns % 2 ^ 256 := (accV_S 8 fun q hq => by
    rw [show 0x1380 + q = 0x1380 + (0x0 + q) by omega, X24 (0x0 + q) (by omega),
      show 0xA44 + (0x0 + q) = 0xA44 + q by omega]).trans a23_a44
  clear a23_15c8 a23_15a8 a23_1480 a23_1380 a23_1020 a23_a44 a23_a20 a23_440 a23_420 a23_320 a23_2e0 a23_2c0 a23_2a0 b23_14a0 b23_13a0 b23_1040 b23_a64 b23_a40 b23_340 w23_133c w23_1338 w23_1334 w23_1330 w23_132c w23_1328 w23_1324 w23_1320 w23_464 w23_460 w23_130 w23_12c w23_128 w23_124 w23_120 w23_11c w23_118 w23_114 w23_110 w23_10c w23_108 w23_104 w23_100 w23_fc w23_f8 w23_f4 w23_f0 w23_ec w23_e8 w23_e4 w23_e0 w23_dc w23_d8 w23_d4 w23_d0 w23_cc w23_c8 w23_c4 w23_c0 w23_bc w23_b8 w23_b4 w23_b0 w23_ac w23_a8 w23_a4 w23_a0 w23_9c w23_98 w23_94 w23_90 w23_8c w23_88 w23_84 w23_80 w23_7c w23_78 w23_74 w23_70 w23_6c w23_68 w23_64 w23_60 w23_5c w23_58 w23_54 w23_50 w23_4c w23_44 w23_40 w23_3c w23_38 w23_34 w23_20 w23_1c g23_12 g23_11 g23_10 g23_27 g23_26 g23_24 g23_19 g23_18 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 rb23 s23 m23 u23 c23
  -- 0x1DE2
  obtain ⟨n25, c25, u25⟩ := s24.block svZB1de2 E24.self svZB1de2_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m25 : n25.mem = n24.mem := u25.mem
  have s25 : St n25.mem SV n25 0x1E0C (reg n25) := ⟨u25.pc, rfl, fun _ => rfl⟩
  have rb25 : ∀ q, reg n25 q = (runBlock svZB1de2 (n24.mem, reg n24)).2 q := fun q => by rw [u25.regs]
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
  have g25_24 : reg n25 (24 : Fin 32) = ulo := by
    rw [rb25, runBlock_reg _ _ _ (24 : Fin 32) s24.zero (by decide), g24_24]
  have g25_26 : reg n25 (26 : Fin 32) = x26 := by
    rw [rb25, runBlock_reg _ _ _ (26 : Fin 32) s24.zero (by decide), g24_26]
  have g25_27 : reg n25 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb25, runBlock_reg _ _ _ (27 : Fin 32) s24.zero (by decide), g24_27]
  have g25_10 : reg n25 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb25]; simp +decide only [runBlock, BInstr.run, svZB1de2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_18, g24_19, g24_24, g24_26, g24_27, s24.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g25_11 : reg n25 a1 = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by
    rw [rb25]; simp +decide only [runBlock, BInstr.run, svZB1de2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_18, g24_19, g24_24, g24_26, g24_27, s24.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g25_12 : reg n25 a2 = B + 0x21A0 + BitVec.ofNat 32 0x1020 := by
    rw [rb25]; simp +decide only [runBlock, BInstr.run, svZB1de2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_18, g24_19, g24_24, g24_26, g24_27, s24.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g25_13 : reg n25 a3 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb25]; simp +decide only [runBlock, BInstr.run, svZB1de2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_18, g24_19, g24_24, g24_26, g24_27, s24.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g25_14 : reg n25 a4 = BitVec.ofNat 32 0xFFFFFFFF := by
    rw [rb25]; simp +decide only [runBlock, BInstr.run, svZB1de2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_18, g24_19, g24_24, g24_26, g24_27, s24.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g25_15 : reg n25 a5 = BitVec.ofNat 32 0xFFFFFFFF := by
    rw [rb25]; simp +decide only [runBlock, BInstr.run, svZB1de2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_18, g24_19, g24_24, g24_26, g24_27, s24.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g25_16 : reg n25 a6 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
    rw [rb25]; simp +decide only [runBlock, BInstr.run, svZB1de2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_18, g24_19, g24_24, g24_26, g24_27, s24.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g25_17 : reg n25 a7 = BitVec.ofNat 32 ns := by
    rw [rb25]; simp +decide only [runBlock, BInstr.run, svZB1de2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_18, g24_19, g24_24, g24_26, g24_27, s24.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk25 : SvKeepL B n0.mem n25.mem [(0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4), (0x1338, 0x4), (0x133C, 0x4), (0xA20, 0x45), (0x320, 0x24), (0x1380, 0x24)] := by rw [m25]; exact keep_kk24
  clear keep_kk24
  have w25_1c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 ns := by rw [m25]; exact w24_1c
  have w25_20 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = nzw := by rw [m25]; exact w24_20
  have w25_34 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = dlo := by rw [m25]; exact w24_34
  have w25_38 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = dhi := by rw [m25]; exact w24_38
  have w25_3c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = uhi := by rw [m25]; exact w24_3c
  have w25_40 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = vhi := by rw [m25]; exact w24_40
  have w25_44 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = vlo := by rw [m25]; exact w24_44
  have w25_4c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m25]; exact w24_4c
  have w25_50 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m25]; exact w24_50
  have w25_54 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m25]; exact w24_54
  have w25_58 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m25]; exact w24_58
  have w25_5c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rlo := by rw [m25]; exact w24_5c
  have w25_60 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = qhi := by rw [m25]; exact w24_60
  have w25_64 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m25]; exact w24_64
  have w25_68 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m25]; exact w24_68
  have w25_6c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m25]; exact w24_6c
  have w25_70 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = qlo := by rw [m25]; exact w24_70
  have w25_74 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = rhi := by rw [m25]; exact w24_74
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
  have w25_460 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m25]; exact w24_460
  have w25_464 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m25]; exact w24_464
  have w25_1320 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = ulo := by rw [m25]; exact w24_1320
  have w25_1324 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = uhi := by rw [m25]; exact w24_1324
  have w25_1328 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = vlo := by rw [m25]; exact w24_1328
  have w25_132c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = vhi := by rw [m25]; exact w24_132c
  have w25_1330 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = qlo := by rw [m25]; exact w24_1330
  have w25_1334 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = qhi := by rw [m25]; exact w24_1334
  have w25_1338 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) = rlo := by rw [m25]; exact w24_1338
  have w25_133c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x133C) = rhi := by rw [m25]; exact w24_133c
  have b25_340 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = BitVec.ofNat 8 σ20a := by rw [m25]; exact b24_340
  have b25_a40 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 8 σ20a := by rw [m25]; exact b24_a40
  have b25_a64 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA64) = BitVec.ofNat 8 σ20b := by rw [m25]; exact b24_a64
  have b25_1040 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = es := by rw [m25]; exact b24_1040
  have b25_13a0 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = BitVec.ofNat 8 σ20b := by rw [m25]; exact b24_13a0
  have b25_14a0 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = ds := by rw [m25]; exact b24_14a0
  have a25_2a0 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m25]; exact a24_2a0
  have a25_2c0 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m25]; exact a24_2c0
  have a25_2e0 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m25]; exact a24_2e0
  have a25_320 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = A20a / 2 ^ ns % 2 ^ 256 := by rw [m25]; exact a24_320
  have a25_420 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := by rw [m25]; exact a24_420
  have a25_440 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := by rw [m25]; exact a24_440
  have a25_a20 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 8 = A20a / 2 ^ ns % 2 ^ 256 := by rw [m25]; exact a24_a20
  have a25_a44 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) 8 = A20b / 2 ^ ns % 2 ^ 256 := by rw [m25]; exact a24_a44
  have a25_1020 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = ev := by rw [m25]; exact a24_1020
  have a25_1380 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = A20b / 2 ^ ns % 2 ^ 256 := by rw [m25]; exact a24_1380
  have a25_1480 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = dv := by rw [m25]; exact a24_1480
  have a25_15a8 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := by rw [m25]; exact a24_15a8
  have a25_15c8 : accV n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := by rw [m25]; exact a24_15c8
  clear a24_1380 a24_15c8 a24_15a8 a24_1480 a24_1020 a24_a44 a24_a20 a24_440 a24_420 a24_320 a24_2e0 a24_2c0 a24_2a0 b24_13a0 b24_14a0 b24_1040 b24_a64 b24_a40 b24_340 w24_133c w24_1338 w24_1334 w24_1330 w24_132c w24_1328 w24_1324 w24_1320 w24_464 w24_460 w24_130 w24_12c w24_128 w24_124 w24_120 w24_11c w24_118 w24_114 w24_110 w24_10c w24_108 w24_104 w24_100 w24_fc w24_f8 w24_f4 w24_f0 w24_ec w24_e8 w24_e4 w24_e0 w24_dc w24_d8 w24_d4 w24_d0 w24_cc w24_c8 w24_c4 w24_c0 w24_bc w24_b8 w24_b4 w24_b0 w24_ac w24_a8 w24_a4 w24_a0 w24_9c w24_98 w24_94 w24_90 w24_8c w24_88 w24_84 w24_80 w24_7c w24_78 w24_74 w24_70 w24_6c w24_68 w24_64 w24_60 w24_5c w24_58 w24_54 w24_50 w24_4c w24_44 w24_40 w24_3c w24_38 w24_34 w24_20 w24_1c g24_27 g24_26 g24_24 g24_19 g24_18 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 s24 X24 K24 P24
  -- 0x1E0C: sv_ude8Fs
  obtain ⟨n26, c26, s26, sp26, rk26, R1_26, R2_26, K26, fr26⟩ := sv_ude8Fs (co := 0xA20) (ca := 0x1480) (cb := 0x1020) (ct := 0x1320) (s := ns)
    F E25 (UC0.sv F fR25) s25 sv_at_1e0c sv_at_1e10 (by decide) (by decide) g25_2
    g25_10 g25_11 g25_12 g25_13 g25_14 g25_15 g25_16 g25_17 hns1 (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [show 0x1480 + 0x20 = 0x14A0 from rfl, b25_14a0]; exact hds)
    (by rw [show 0x1020 + 0x20 = 0x1040 from rfl, b25_1040]; exact hes)
  obtain ⟨σ26a, A26a, hσ0_26, e0_26, bb0_26, vv0_26⟩ := R1_26
  simp only [svI, svM, show 0x1480 + 0x20 = 0x14A0 from rfl, show 0x1020 + 0x20 = 0x1040 from rfl,
    show 0x1320 + 0x0 = 0x1320 from rfl, show 0x1320 + 0x8 = 0x1328 from rfl] at e0_26
  rw [b25_14a0, a25_1480, b25_1040, a25_1020,
    acc2_frame w25_1320 w25_1324, acc2_frame w25_1328 w25_132c] at e0_26
  obtain ⟨σ26b, A26b, hσ1_26, e1_26, bb1_26, vv1_26⟩ := R2_26
  simp only [svI, svM, show 0x1480 + 0x20 = 0x14A0 from rfl, show 0x1020 + 0x20 = 0x1040 from rfl,
    show 0x1320 + 0x10 = 0x1330 from rfl, show 0x1320 + 0x18 = 0x1338 from rfl] at e1_26
  rw [b25_14a0, a25_1480, b25_1040, a25_1020,
    acc2_frame w25_1330 w25_1334, acc2_frame w25_1338 w25_133c] at e1_26
  rw [a25_420] at bb0_26 vv0_26 bb1_26 vv1_26
  have t26 : Steps n0 n26 := t25.trans c26
  have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
  have E26 : SvCode n26.mem := E25.fr F fr26
  have V26 : SvSaves B n26.mem v := V25.keepL K26 (by decide)
  have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk26 (3 : Fin 32) (by decide), g25_3]
  have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk26 (4 : Fin 32) (by decide), g25_4]
  have g26_8 : reg n26 (8 : Fin 32) = BitVec.ofNat 32 ns := by rw [rk26 (8 : Fin 32) (by decide), g25_8]
  have g26_18 : reg n26 (18 : Fin 32) = out := by rw [rk26 (18 : Fin 32) (by decide), g25_18]
  have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [rk26 (19 : Fin 32) (by decide), g25_19]
  have g26_24 : reg n26 (24 : Fin 32) = ulo := by rw [rk26 (24 : Fin 32) (by decide), g25_24]
  have g26_26 : reg n26 (26 : Fin 32) = x26 := by rw [rk26 (26 : Fin 32) (by decide), g25_26]
  have g26_27 : reg n26 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk26 (27 : Fin 32) (by decide), g25_27]
  have g26_2 : reg n26 sp = B + 0x21A0 := sp26
  have keep_kk26 : SvKeepL B n0.mem n26.mem [(0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4), (0x1338, 0x4), (0x133C, 0x4), (0xA20, 0x45), (0x320, 0x24), (0x1380, 0x24), (0xA20, 0x45)] := keep_kk25.trans K26
  clear keep_kk25
  have w26_1c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 ns := (K26.w32 (by decide) (by decide)).trans w25_1c
  have w26_20 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = nzw := (K26.w32 (by decide) (by decide)).trans w25_20
  have w26_34 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = dlo := (K26.w32 (by decide) (by decide)).trans w25_34
  have w26_38 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = dhi := (K26.w32 (by decide) (by decide)).trans w25_38
  have w26_3c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = uhi := (K26.w32 (by decide) (by decide)).trans w25_3c
  have w26_40 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = vhi := (K26.w32 (by decide) (by decide)).trans w25_40
  have w26_44 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = vlo := (K26.w32 (by decide) (by decide)).trans w25_44
  have w26_4c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K26.w32 (by decide) (by decide)).trans w25_4c
  have w26_50 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K26.w32 (by decide) (by decide)).trans w25_50
  have w26_54 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K26.w32 (by decide) (by decide)).trans w25_54
  have w26_58 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K26.w32 (by decide) (by decide)).trans w25_58
  have w26_5c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rlo := (K26.w32 (by decide) (by decide)).trans w25_5c
  have w26_60 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = qhi := (K26.w32 (by decide) (by decide)).trans w25_60
  have w26_64 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K26.w32 (by decide) (by decide)).trans w25_64
  have w26_68 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K26.w32 (by decide) (by decide)).trans w25_68
  have w26_6c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K26.w32 (by decide) (by decide)).trans w25_6c
  have w26_70 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = qlo := (K26.w32 (by decide) (by decide)).trans w25_70
  have w26_74 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = rhi := (K26.w32 (by decide) (by decide)).trans w25_74
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
  have w26_460 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := (K26.w32 (by decide) (by decide)).trans w25_460
  have w26_464 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := (K26.w32 (by decide) (by decide)).trans w25_464
  have w26_1320 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = ulo := (K26.w32 (by decide) (by decide)).trans w25_1320
  have w26_1324 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = uhi := (K26.w32 (by decide) (by decide)).trans w25_1324
  have w26_1328 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = vlo := (K26.w32 (by decide) (by decide)).trans w25_1328
  have w26_132c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = vhi := (K26.w32 (by decide) (by decide)).trans w25_132c
  have w26_1330 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = qlo := (K26.w32 (by decide) (by decide)).trans w25_1330
  have w26_1334 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = qhi := (K26.w32 (by decide) (by decide)).trans w25_1334
  have w26_1338 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) = rlo := (K26.w32 (by decide) (by decide)).trans w25_1338
  have w26_133c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x133C) = rhi := (K26.w32 (by decide) (by decide)).trans w25_133c
  have b26_340 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = BitVec.ofNat 8 σ20a := (K26.b8 (by decide) (by decide)).trans b25_340
  have b26_1040 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = es := (K26.b8 (by decide) (by decide)).trans b25_1040
  have b26_13a0 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = BitVec.ofNat 8 σ20b := (K26.b8 (by decide) (by decide)).trans b25_13a0
  have b26_14a0 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = ds := (K26.b8 (by decide) (by decide)).trans b25_14a0
  have a26_2a0 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K26.acc (by decide) (by decide)).trans a25_2a0
  have a26_2c0 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K26.acc (by decide) (by decide)).trans a25_2c0
  have a26_2e0 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K26.acc (by decide) (by decide)).trans a25_2e0
  have a26_320 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = A20a / 2 ^ ns % 2 ^ 256 := (K26.acc (by decide) (by decide)).trans a25_320
  have a26_420 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := (K26.acc (by decide) (by decide)).trans a25_420
  have a26_440 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := (K26.acc (by decide) (by decide)).trans a25_440
  have a26_1020 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = ev := (K26.acc (by decide) (by decide)).trans a25_1020
  have a26_1380 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = A20b / 2 ^ ns % 2 ^ 256 := (K26.acc (by decide) (by decide)).trans a25_1380
  have a26_1480 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = dv := (K26.acc (by decide) (by decide)).trans a25_1480
  have a26_15a8 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := (K26.acc (by decide) (by decide)).trans a25_15a8
  have a26_15c8 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := (K26.acc (by decide) (by decide)).trans a25_15c8
  have a26_a20 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 8 = (lrsm8 σ26a A26a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).2 := vv0_26
  have a26_a44 : accV n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) 8 = (lrsm8 σ26b A26b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).2 := vv1_26
  have b26_a40 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 8 (lrsm8 σ26a A26a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).1 := byte_of_toNat bb0_26
  have b26_a64 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA64) = BitVec.ofNat 8 (lrsm8 σ26b A26b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).1 := byte_of_toNat bb1_26
  clear a25_15c8 a25_15a8 a25_1480 a25_1380 a25_1020 a25_a44 a25_a20 a25_440 a25_420 a25_320 a25_2e0 a25_2c0 a25_2a0 b25_14a0 b25_13a0 b25_1040 b25_a64 b25_a40 b25_340 w25_133c w25_1338 w25_1334 w25_1330 w25_132c w25_1328 w25_1324 w25_1320 w25_464 w25_460 w25_130 w25_12c w25_128 w25_124 w25_120 w25_11c w25_118 w25_114 w25_110 w25_10c w25_108 w25_104 w25_100 w25_fc w25_f8 w25_f4 w25_f0 w25_ec w25_e8 w25_e4 w25_e0 w25_dc w25_d8 w25_d4 w25_d0 w25_cc w25_c8 w25_c4 w25_c0 w25_bc w25_b8 w25_b4 w25_b0 w25_ac w25_a8 w25_a4 w25_a0 w25_9c w25_98 w25_94 w25_90 w25_8c w25_88 w25_84 w25_80 w25_7c w25_78 w25_74 w25_70 w25_6c w25_68 w25_64 w25_60 w25_5c w25_58 w25_54 w25_50 w25_4c w25_44 w25_40 w25_3c w25_38 w25_34 w25_20 w25_1c g25_17 g25_16 g25_15 g25_14 g25_13 g25_12 g25_11 g25_10 g25_27 g25_26 g25_24 g25_19 g25_18 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 fr25 rb25 s25 m25 u25 c25
  -- 0x1E14
  obtain ⟨n27, c27, u27⟩ := s26.block svZB1e14 E26.self svZB1e14_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m27 : n27.mem = n26.mem := u27.mem
  have s27 : St n27.mem SV n27 0x1E28 (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
  have rb27 : ∀ q, reg n27 q = (runBlock svZB1e14 (n26.mem, reg n26)).2 q := fun q => by rw [u27.regs]
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
  have g27_8 : reg n27 (8 : Fin 32) = BitVec.ofNat 32 ns := by
    rw [rb27, runBlock_reg _ _ _ (8 : Fin 32) s26.zero (by decide), g26_8]
  have g27_18 : reg n27 (18 : Fin 32) = out := by
    rw [rb27, runBlock_reg _ _ _ (18 : Fin 32) s26.zero (by decide), g26_18]
  have g27_19 : reg n27 (19 : Fin 32) = bp := by
    rw [rb27, runBlock_reg _ _ _ (19 : Fin 32) s26.zero (by decide), g26_19]
  have g27_24 : reg n27 (24 : Fin 32) = ulo := by
    rw [rb27, runBlock_reg _ _ _ (24 : Fin 32) s26.zero (by decide), g26_24]
  have g27_26 : reg n27 (26 : Fin 32) = x26 := by
    rw [rb27, runBlock_reg _ _ _ (26 : Fin 32) s26.zero (by decide), g26_26]
  have g27_27 : reg n27 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb27, runBlock_reg _ _ _ (27 : Fin 32) s26.zero (by decide), g26_27]
  have g27_10 : reg n27 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by
    rw [rb27]; simp +decide only [runBlock, BInstr.run, svZB1e14, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g26_2, g26_3, g26_4, g26_8, g26_18, g26_19, g26_24, g26_26, g26_27, s26.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g27_11 : reg n27 a1 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb27]; simp +decide only [runBlock, BInstr.run, svZB1e14, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g26_2, g26_3, g26_4, g26_8, g26_18, g26_19, g26_24, g26_26, g26_27, s26.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g27_12 : reg n27 a2 = BitVec.ofNat 32 0x24 := by
    rw [rb27]; simp +decide only [runBlock, BInstr.run, svZB1e14, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g26_2, g26_3, g26_4, g26_8, g26_18, g26_19, g26_24, g26_26, g26_27, s26.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk27 : SvKeepL B n0.mem n27.mem [(0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4), (0x1338, 0x4), (0x133C, 0x4), (0xA20, 0x45), (0x320, 0x24), (0x1380, 0x24), (0xA20, 0x45)] := by rw [m27]; exact keep_kk26
  clear keep_kk26
  have w27_1c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 ns := by rw [m27]; exact w26_1c
  have w27_20 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = nzw := by rw [m27]; exact w26_20
  have w27_34 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = dlo := by rw [m27]; exact w26_34
  have w27_38 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = dhi := by rw [m27]; exact w26_38
  have w27_3c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = uhi := by rw [m27]; exact w26_3c
  have w27_40 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = vhi := by rw [m27]; exact w26_40
  have w27_44 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = vlo := by rw [m27]; exact w26_44
  have w27_4c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m27]; exact w26_4c
  have w27_50 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m27]; exact w26_50
  have w27_54 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m27]; exact w26_54
  have w27_58 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m27]; exact w26_58
  have w27_5c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rlo := by rw [m27]; exact w26_5c
  have w27_60 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = qhi := by rw [m27]; exact w26_60
  have w27_64 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m27]; exact w26_64
  have w27_68 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m27]; exact w26_68
  have w27_6c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m27]; exact w26_6c
  have w27_70 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = qlo := by rw [m27]; exact w26_70
  have w27_74 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = rhi := by rw [m27]; exact w26_74
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
  have w27_460 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m27]; exact w26_460
  have w27_464 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m27]; exact w26_464
  have w27_1320 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = ulo := by rw [m27]; exact w26_1320
  have w27_1324 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = uhi := by rw [m27]; exact w26_1324
  have w27_1328 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = vlo := by rw [m27]; exact w26_1328
  have w27_132c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = vhi := by rw [m27]; exact w26_132c
  have w27_1330 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = qlo := by rw [m27]; exact w26_1330
  have w27_1334 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = qhi := by rw [m27]; exact w26_1334
  have w27_1338 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) = rlo := by rw [m27]; exact w26_1338
  have w27_133c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x133C) = rhi := by rw [m27]; exact w26_133c
  have b27_340 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = BitVec.ofNat 8 σ20a := by rw [m27]; exact b26_340
  have b27_a40 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 8 (lrsm8 σ26a A26a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).1 := by rw [m27]; exact b26_a40
  have b27_a64 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA64) = BitVec.ofNat 8 (lrsm8 σ26b A26b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).1 := by rw [m27]; exact b26_a64
  have b27_1040 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = es := by rw [m27]; exact b26_1040
  have b27_13a0 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = BitVec.ofNat 8 σ20b := by rw [m27]; exact b26_13a0
  have b27_14a0 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = ds := by rw [m27]; exact b26_14a0
  have a27_2a0 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m27]; exact a26_2a0
  have a27_2c0 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m27]; exact a26_2c0
  have a27_2e0 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m27]; exact a26_2e0
  have a27_320 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = A20a / 2 ^ ns % 2 ^ 256 := by rw [m27]; exact a26_320
  have a27_420 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := by rw [m27]; exact a26_420
  have a27_440 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := by rw [m27]; exact a26_440
  have a27_a20 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 8 = (lrsm8 σ26a A26a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).2 := by rw [m27]; exact a26_a20
  have a27_a44 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) 8 = (lrsm8 σ26b A26b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).2 := by rw [m27]; exact a26_a44
  have a27_1020 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = ev := by rw [m27]; exact a26_1020
  have a27_1380 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = A20b / 2 ^ ns % 2 ^ 256 := by rw [m27]; exact a26_1380
  have a27_1480 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = dv := by rw [m27]; exact a26_1480
  have a27_15a8 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := by rw [m27]; exact a26_15a8
  have a27_15c8 : accV n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := by rw [m27]; exact a26_15c8
  clear b26_a64 b26_a40 a26_a44 a26_a20 a26_15c8 a26_15a8 a26_1480 a26_1380 a26_1020 a26_440 a26_420 a26_320 a26_2e0 a26_2c0 a26_2a0 b26_14a0 b26_13a0 b26_1040 b26_340 w26_133c w26_1338 w26_1334 w26_1330 w26_132c w26_1328 w26_1324 w26_1320 w26_464 w26_460 w26_130 w26_12c w26_128 w26_124 w26_120 w26_11c w26_118 w26_114 w26_110 w26_10c w26_108 w26_104 w26_100 w26_fc w26_f8 w26_f4 w26_f0 w26_ec w26_e8 w26_e4 w26_e0 w26_dc w26_d8 w26_d4 w26_d0 w26_cc w26_c8 w26_c4 w26_c0 w26_bc w26_b8 w26_b4 w26_b0 w26_ac w26_a8 w26_a4 w26_a0 w26_9c w26_98 w26_94 w26_90 w26_8c w26_88 w26_84 w26_80 w26_7c w26_78 w26_74 w26_70 w26_6c w26_68 w26_64 w26_60 w26_5c w26_58 w26_54 w26_50 w26_4c w26_44 w26_40 w26_3c w26_38 w26_34 w26_20 w26_1c g26_2 g26_27 g26_26 g26_24 g26_19 g26_18 g26_8 g26_4 g26_3 V26 E26 fR26 t26 vv1_26 bb1_26 vv0_26 bb0_26 fr26 K26 rk26 sp26 s26 c26
  -- 0x1E28: memcpy
  obtain ⟨n28, P28, K28, X28⟩ := sv_mc (c := 0x1480) (d := 0xA20) (N := 0x24) F E27 s27 sv_at_1e28 sv_at_1e2c
    (by decide) (by decide) g27_2 g27_10 g27_11 g27_12
    (by decide) (by decide) (by decide)
  have s28 := P28.st
  have fr28 := P28.fr
  have t28 : Steps n0 n28 := t27.trans P28.steps
  have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
  have E28 : SvCode n28.mem := E27.fr F fr28
  have V28 : SvSaves B n28.mem v := V27.keep K28 (by decide)
  have g28_2 : reg n28 sp = B + 0x21A0 := by rw [P28.regs sp (by decide), g27_2]
  have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P28.regs (3 : Fin 32) (by decide), g27_3]
  have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P28.regs (4 : Fin 32) (by decide), g27_4]
  have g28_8 : reg n28 (8 : Fin 32) = BitVec.ofNat 32 ns := by rw [P28.regs (8 : Fin 32) (by decide), g27_8]
  have g28_18 : reg n28 (18 : Fin 32) = out := by rw [P28.regs (18 : Fin 32) (by decide), g27_18]
  have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [P28.regs (19 : Fin 32) (by decide), g27_19]
  have g28_24 : reg n28 (24 : Fin 32) = ulo := by rw [P28.regs (24 : Fin 32) (by decide), g27_24]
  have g28_26 : reg n28 (26 : Fin 32) = x26 := by rw [P28.regs (26 : Fin 32) (by decide), g27_26]
  have g28_27 : reg n28 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P28.regs (27 : Fin 32) (by decide), g27_27]
  have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4), (0x1338, 0x4), (0x133C, 0x4), (0xA20, 0x45), (0x320, 0x24), (0x1380, 0x24), (0xA20, 0x45), (0x1480, 0x24)] := keep_kk27.trans K28.toL
  clear keep_kk27
  have w28_1c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 ns := (K28.w32 (by decide) (by decide)).trans w27_1c
  have w28_20 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = nzw := (K28.w32 (by decide) (by decide)).trans w27_20
  have w28_34 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = dlo := (K28.w32 (by decide) (by decide)).trans w27_34
  have w28_38 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = dhi := (K28.w32 (by decide) (by decide)).trans w27_38
  have w28_3c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = uhi := (K28.w32 (by decide) (by decide)).trans w27_3c
  have w28_40 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = vhi := (K28.w32 (by decide) (by decide)).trans w27_40
  have w28_44 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = vlo := (K28.w32 (by decide) (by decide)).trans w27_44
  have w28_4c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K28.w32 (by decide) (by decide)).trans w27_4c
  have w28_50 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K28.w32 (by decide) (by decide)).trans w27_50
  have w28_54 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K28.w32 (by decide) (by decide)).trans w27_54
  have w28_58 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K28.w32 (by decide) (by decide)).trans w27_58
  have w28_5c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rlo := (K28.w32 (by decide) (by decide)).trans w27_5c
  have w28_60 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = qhi := (K28.w32 (by decide) (by decide)).trans w27_60
  have w28_64 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K28.w32 (by decide) (by decide)).trans w27_64
  have w28_68 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K28.w32 (by decide) (by decide)).trans w27_68
  have w28_6c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K28.w32 (by decide) (by decide)).trans w27_6c
  have w28_70 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = qlo := (K28.w32 (by decide) (by decide)).trans w27_70
  have w28_74 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = rhi := (K28.w32 (by decide) (by decide)).trans w27_74
  have w28_78 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = rem := (K28.w32 (by decide) (by decide)).trans w27_78
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
  have w28_1320 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = ulo := (K28.w32 (by decide) (by decide)).trans w27_1320
  have w28_1324 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = uhi := (K28.w32 (by decide) (by decide)).trans w27_1324
  have w28_1328 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = vlo := (K28.w32 (by decide) (by decide)).trans w27_1328
  have w28_132c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = vhi := (K28.w32 (by decide) (by decide)).trans w27_132c
  have w28_1330 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = qlo := (K28.w32 (by decide) (by decide)).trans w27_1330
  have w28_1334 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = qhi := (K28.w32 (by decide) (by decide)).trans w27_1334
  have w28_1338 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) = rlo := (K28.w32 (by decide) (by decide)).trans w27_1338
  have w28_133c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x133C) = rhi := (K28.w32 (by decide) (by decide)).trans w27_133c
  have b28_340 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = BitVec.ofNat 8 σ20a := (K28.b8 (by decide) (by decide)).trans b27_340
  have b28_a40 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 8 (lrsm8 σ26a A26a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).1 := (K28.b8 (by decide) (by decide)).trans b27_a40
  have b28_a64 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA64) = BitVec.ofNat 8 (lrsm8 σ26b A26b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).1 := (K28.b8 (by decide) (by decide)).trans b27_a64
  have b28_1040 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = es := (K28.b8 (by decide) (by decide)).trans b27_1040
  have b28_13a0 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = BitVec.ofNat 8 σ20b := (K28.b8 (by decide) (by decide)).trans b27_13a0
  have b28_14a0 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = BitVec.ofNat 8 (lrsm8 σ26a A26a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).1 := by rw [show 0x14A0 = 0x1480 + 0x20 from rfl, X28 0x20 (by decide)]; exact b27_a40
  have a28_2a0 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K28.acc (by decide) (by decide)).trans a27_2a0
  have a28_2c0 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K28.acc (by decide) (by decide)).trans a27_2c0
  have a28_2e0 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K28.acc (by decide) (by decide)).trans a27_2e0
  have a28_320 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = A20a / 2 ^ ns % 2 ^ 256 := (K28.acc (by decide) (by decide)).trans a27_320
  have a28_420 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := (K28.acc (by decide) (by decide)).trans a27_420
  have a28_440 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := (K28.acc (by decide) (by decide)).trans a27_440
  have a28_a20 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 8 = (lrsm8 σ26a A26a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).2 := (K28.acc (by decide) (by decide)).trans a27_a20
  have a28_a44 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) 8 = (lrsm8 σ26b A26b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).2 := (K28.acc (by decide) (by decide)).trans a27_a44
  have a28_1020 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = ev := (K28.acc (by decide) (by decide)).trans a27_1020
  have a28_1380 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = A20b / 2 ^ ns % 2 ^ 256 := (K28.acc (by decide) (by decide)).trans a27_1380
  have a28_15a8 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := (K28.acc (by decide) (by decide)).trans a27_15a8
  have a28_15c8 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := (K28.acc (by decide) (by decide)).trans a27_15c8
  have a28_1480 : accV n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = (lrsm8 σ26a A26a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).2 := (accV_S 8 fun q hq => by
    rw [show 0x1480 + q = 0x1480 + (0x0 + q) by omega, X28 (0x0 + q) (by omega),
      show 0xA20 + (0x0 + q) = 0xA20 + q by omega]).trans a27_a20
  clear a27_15c8 a27_15a8 a27_1480 a27_1380 a27_1020 a27_a44 a27_a20 a27_440 a27_420 a27_320 a27_2e0 a27_2c0 a27_2a0 b27_14a0 b27_13a0 b27_1040 b27_a64 b27_a40 b27_340 w27_133c w27_1338 w27_1334 w27_1330 w27_132c w27_1328 w27_1324 w27_1320 w27_464 w27_460 w27_130 w27_12c w27_128 w27_124 w27_120 w27_11c w27_118 w27_114 w27_110 w27_10c w27_108 w27_104 w27_100 w27_fc w27_f8 w27_f4 w27_f0 w27_ec w27_e8 w27_e4 w27_e0 w27_dc w27_d8 w27_d4 w27_d0 w27_cc w27_c8 w27_c4 w27_c0 w27_bc w27_b8 w27_b4 w27_b0 w27_ac w27_a8 w27_a4 w27_a0 w27_9c w27_98 w27_94 w27_90 w27_8c w27_88 w27_84 w27_80 w27_7c w27_78 w27_74 w27_70 w27_6c w27_68 w27_64 w27_60 w27_5c w27_58 w27_54 w27_50 w27_4c w27_44 w27_40 w27_3c w27_38 w27_34 w27_20 w27_1c g27_12 g27_11 g27_10 g27_27 g27_26 g27_24 g27_19 g27_18 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 rb27 s27 m27 u27 c27
  -- 0x1E30
  obtain ⟨n29, c29, u29⟩ := s28.block svZB1e30 E28.self svZB1e30_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m29 : n29.mem = n28.mem := u29.mem
  have s29 : St n29.mem SV n29 0x1E44 (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
  have rb29 : ∀ q, reg n29 q = (runBlock svZB1e30 (n28.mem, reg n28)).2 q := fun q => by rw [u29.regs]
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
  have g29_8 : reg n29 (8 : Fin 32) = BitVec.ofNat 32 ns := by
    rw [rb29, runBlock_reg _ _ _ (8 : Fin 32) s28.zero (by decide), g28_8]
  have g29_18 : reg n29 (18 : Fin 32) = out := by
    rw [rb29, runBlock_reg _ _ _ (18 : Fin 32) s28.zero (by decide), g28_18]
  have g29_19 : reg n29 (19 : Fin 32) = bp := by
    rw [rb29, runBlock_reg _ _ _ (19 : Fin 32) s28.zero (by decide), g28_19]
  have g29_24 : reg n29 (24 : Fin 32) = ulo := by
    rw [rb29, runBlock_reg _ _ _ (24 : Fin 32) s28.zero (by decide), g28_24]
  have g29_26 : reg n29 (26 : Fin 32) = x26 := by
    rw [rb29, runBlock_reg _ _ _ (26 : Fin 32) s28.zero (by decide), g28_26]
  have g29_27 : reg n29 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb29, runBlock_reg _ _ _ (27 : Fin 32) s28.zero (by decide), g28_27]
  have g29_10 : reg n29 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1020 := by
    rw [rb29]; simp +decide only [runBlock, BInstr.run, svZB1e30, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g28_2, g28_3, g28_4, g28_8, g28_18, g28_19, g28_24, g28_26, g28_27, s28.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g29_11 : reg n29 a1 = B + 0x21A0 + BitVec.ofNat 32 0xA44 := by
    rw [rb29]; simp +decide only [runBlock, BInstr.run, svZB1e30, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g28_2, g28_3, g28_4, g28_8, g28_18, g28_19, g28_24, g28_26, g28_27, s28.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g29_12 : reg n29 a2 = BitVec.ofNat 32 0x24 := by
    rw [rb29]; simp +decide only [runBlock, BInstr.run, svZB1e30, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g28_2, g28_3, g28_4, g28_8, g28_18, g28_19, g28_24, g28_26, g28_27, s28.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4), (0x1338, 0x4), (0x133C, 0x4), (0xA20, 0x45), (0x320, 0x24), (0x1380, 0x24), (0xA20, 0x45), (0x1480, 0x24)] := by rw [m29]; exact keep_kk28
  clear keep_kk28
  have w29_1c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 ns := by rw [m29]; exact w28_1c
  have w29_20 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = nzw := by rw [m29]; exact w28_20
  have w29_34 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = dlo := by rw [m29]; exact w28_34
  have w29_38 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = dhi := by rw [m29]; exact w28_38
  have w29_3c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = uhi := by rw [m29]; exact w28_3c
  have w29_40 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = vhi := by rw [m29]; exact w28_40
  have w29_44 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = vlo := by rw [m29]; exact w28_44
  have w29_4c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m29]; exact w28_4c
  have w29_50 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m29]; exact w28_50
  have w29_54 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m29]; exact w28_54
  have w29_58 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m29]; exact w28_58
  have w29_5c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rlo := by rw [m29]; exact w28_5c
  have w29_60 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = qhi := by rw [m29]; exact w28_60
  have w29_64 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m29]; exact w28_64
  have w29_68 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m29]; exact w28_68
  have w29_6c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m29]; exact w28_6c
  have w29_70 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = qlo := by rw [m29]; exact w28_70
  have w29_74 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = rhi := by rw [m29]; exact w28_74
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
  have w29_460 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m29]; exact w28_460
  have w29_464 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m29]; exact w28_464
  have w29_1320 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = ulo := by rw [m29]; exact w28_1320
  have w29_1324 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = uhi := by rw [m29]; exact w28_1324
  have w29_1328 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = vlo := by rw [m29]; exact w28_1328
  have w29_132c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = vhi := by rw [m29]; exact w28_132c
  have w29_1330 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = qlo := by rw [m29]; exact w28_1330
  have w29_1334 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = qhi := by rw [m29]; exact w28_1334
  have w29_1338 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) = rlo := by rw [m29]; exact w28_1338
  have w29_133c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x133C) = rhi := by rw [m29]; exact w28_133c
  have b29_340 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = BitVec.ofNat 8 σ20a := by rw [m29]; exact b28_340
  have b29_a40 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 8 (lrsm8 σ26a A26a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).1 := by rw [m29]; exact b28_a40
  have b29_a64 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA64) = BitVec.ofNat 8 (lrsm8 σ26b A26b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).1 := by rw [m29]; exact b28_a64
  have b29_1040 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = es := by rw [m29]; exact b28_1040
  have b29_13a0 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = BitVec.ofNat 8 σ20b := by rw [m29]; exact b28_13a0
  have b29_14a0 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = BitVec.ofNat 8 (lrsm8 σ26a A26a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).1 := by rw [m29]; exact b28_14a0
  have a29_2a0 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m29]; exact a28_2a0
  have a29_2c0 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m29]; exact a28_2c0
  have a29_2e0 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m29]; exact a28_2e0
  have a29_320 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = A20a / 2 ^ ns % 2 ^ 256 := by rw [m29]; exact a28_320
  have a29_420 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := by rw [m29]; exact a28_420
  have a29_440 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := by rw [m29]; exact a28_440
  have a29_a20 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 8 = (lrsm8 σ26a A26a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).2 := by rw [m29]; exact a28_a20
  have a29_a44 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) 8 = (lrsm8 σ26b A26b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).2 := by rw [m29]; exact a28_a44
  have a29_1020 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = ev := by rw [m29]; exact a28_1020
  have a29_1380 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = A20b / 2 ^ ns % 2 ^ 256 := by rw [m29]; exact a28_1380
  have a29_1480 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = (lrsm8 σ26a A26a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).2 := by rw [m29]; exact a28_1480
  have a29_15a8 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := by rw [m29]; exact a28_15a8
  have a29_15c8 : accV n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := by rw [m29]; exact a28_15c8
  clear a28_1480 a28_15c8 a28_15a8 a28_1380 a28_1020 a28_a44 a28_a20 a28_440 a28_420 a28_320 a28_2e0 a28_2c0 a28_2a0 b28_14a0 b28_13a0 b28_1040 b28_a64 b28_a40 b28_340 w28_133c w28_1338 w28_1334 w28_1330 w28_132c w28_1328 w28_1324 w28_1320 w28_464 w28_460 w28_130 w28_12c w28_128 w28_124 w28_120 w28_11c w28_118 w28_114 w28_110 w28_10c w28_108 w28_104 w28_100 w28_fc w28_f8 w28_f4 w28_f0 w28_ec w28_e8 w28_e4 w28_e0 w28_dc w28_d8 w28_d4 w28_d0 w28_cc w28_c8 w28_c4 w28_c0 w28_bc w28_b8 w28_b4 w28_b0 w28_ac w28_a8 w28_a4 w28_a0 w28_9c w28_98 w28_94 w28_90 w28_8c w28_88 w28_84 w28_80 w28_7c w28_78 w28_74 w28_70 w28_6c w28_68 w28_64 w28_60 w28_5c w28_58 w28_54 w28_50 w28_4c w28_44 w28_40 w28_3c w28_38 w28_34 w28_20 w28_1c g28_27 g28_26 g28_24 g28_19 g28_18 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 s28 X28 K28 P28
  -- 0x1E44: memcpy
  obtain ⟨n30, P30, K30, X30⟩ := sv_mc (c := 0x1020) (d := 0xA44) (N := 0x24) F E29 s29 sv_at_1e44 sv_at_1e48
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
  have g30_8 : reg n30 (8 : Fin 32) = BitVec.ofNat 32 ns := by rw [P30.regs (8 : Fin 32) (by decide), g29_8]
  have g30_18 : reg n30 (18 : Fin 32) = out := by rw [P30.regs (18 : Fin 32) (by decide), g29_18]
  have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [P30.regs (19 : Fin 32) (by decide), g29_19]
  have g30_24 : reg n30 (24 : Fin 32) = ulo := by rw [P30.regs (24 : Fin 32) (by decide), g29_24]
  have g30_26 : reg n30 (26 : Fin 32) = x26 := by rw [P30.regs (26 : Fin 32) (by decide), g29_26]
  have g30_27 : reg n30 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P30.regs (27 : Fin 32) (by decide), g29_27]
  have keep_kk30 : SvKeepL B n0.mem n30.mem [(0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4), (0x1338, 0x4), (0x133C, 0x4), (0xA20, 0x45), (0x320, 0x24), (0x1380, 0x24), (0xA20, 0x45), (0x1480, 0x24), (0x1020, 0x24)] := keep_kk29.trans K30.toL
  clear keep_kk29
  have w30_1c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 ns := (K30.w32 (by decide) (by decide)).trans w29_1c
  have w30_20 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = nzw := (K30.w32 (by decide) (by decide)).trans w29_20
  have w30_34 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = dlo := (K30.w32 (by decide) (by decide)).trans w29_34
  have w30_38 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = dhi := (K30.w32 (by decide) (by decide)).trans w29_38
  have w30_3c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = uhi := (K30.w32 (by decide) (by decide)).trans w29_3c
  have w30_40 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = vhi := (K30.w32 (by decide) (by decide)).trans w29_40
  have w30_44 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = vlo := (K30.w32 (by decide) (by decide)).trans w29_44
  have w30_4c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K30.w32 (by decide) (by decide)).trans w29_4c
  have w30_50 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K30.w32 (by decide) (by decide)).trans w29_50
  have w30_54 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K30.w32 (by decide) (by decide)).trans w29_54
  have w30_58 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K30.w32 (by decide) (by decide)).trans w29_58
  have w30_5c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rlo := (K30.w32 (by decide) (by decide)).trans w29_5c
  have w30_60 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = qhi := (K30.w32 (by decide) (by decide)).trans w29_60
  have w30_64 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K30.w32 (by decide) (by decide)).trans w29_64
  have w30_68 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K30.w32 (by decide) (by decide)).trans w29_68
  have w30_6c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K30.w32 (by decide) (by decide)).trans w29_6c
  have w30_70 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = qlo := (K30.w32 (by decide) (by decide)).trans w29_70
  have w30_74 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = rhi := (K30.w32 (by decide) (by decide)).trans w29_74
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
  have w30_460 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := (K30.w32 (by decide) (by decide)).trans w29_460
  have w30_464 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := (K30.w32 (by decide) (by decide)).trans w29_464
  have w30_1320 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = ulo := (K30.w32 (by decide) (by decide)).trans w29_1320
  have w30_1324 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = uhi := (K30.w32 (by decide) (by decide)).trans w29_1324
  have w30_1328 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = vlo := (K30.w32 (by decide) (by decide)).trans w29_1328
  have w30_132c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = vhi := (K30.w32 (by decide) (by decide)).trans w29_132c
  have w30_1330 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = qlo := (K30.w32 (by decide) (by decide)).trans w29_1330
  have w30_1334 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = qhi := (K30.w32 (by decide) (by decide)).trans w29_1334
  have w30_1338 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) = rlo := (K30.w32 (by decide) (by decide)).trans w29_1338
  have w30_133c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x133C) = rhi := (K30.w32 (by decide) (by decide)).trans w29_133c
  have b30_340 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = BitVec.ofNat 8 σ20a := (K30.b8 (by decide) (by decide)).trans b29_340
  have b30_a40 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 8 (lrsm8 σ26a A26a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).1 := (K30.b8 (by decide) (by decide)).trans b29_a40
  have b30_a64 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA64) = BitVec.ofNat 8 (lrsm8 σ26b A26b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).1 := (K30.b8 (by decide) (by decide)).trans b29_a64
  have b30_13a0 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = BitVec.ofNat 8 σ20b := (K30.b8 (by decide) (by decide)).trans b29_13a0
  have b30_14a0 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = BitVec.ofNat 8 (lrsm8 σ26a A26a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).1 := (K30.b8 (by decide) (by decide)).trans b29_14a0
  have b30_1040 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = BitVec.ofNat 8 (lrsm8 σ26b A26b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).1 := by rw [show 0x1040 = 0x1020 + 0x20 from rfl, X30 0x20 (by decide)]; exact b29_a64
  have a30_2a0 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K30.acc (by decide) (by decide)).trans a29_2a0
  have a30_2c0 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K30.acc (by decide) (by decide)).trans a29_2c0
  have a30_2e0 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K30.acc (by decide) (by decide)).trans a29_2e0
  have a30_320 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = A20a / 2 ^ ns % 2 ^ 256 := (K30.acc (by decide) (by decide)).trans a29_320
  have a30_420 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := (K30.acc (by decide) (by decide)).trans a29_420
  have a30_440 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := (K30.acc (by decide) (by decide)).trans a29_440
  have a30_a20 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 8 = (lrsm8 σ26a A26a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).2 := (K30.acc (by decide) (by decide)).trans a29_a20
  have a30_a44 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) 8 = (lrsm8 σ26b A26b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).2 := (K30.acc (by decide) (by decide)).trans a29_a44
  have a30_1380 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = A20b / 2 ^ ns % 2 ^ 256 := (K30.acc (by decide) (by decide)).trans a29_1380
  have a30_1480 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = (lrsm8 σ26a A26a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).2 := (K30.acc (by decide) (by decide)).trans a29_1480
  have a30_15a8 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := (K30.acc (by decide) (by decide)).trans a29_15a8
  have a30_15c8 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := (K30.acc (by decide) (by decide)).trans a29_15c8
  have a30_1020 : accV n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = (lrsm8 σ26b A26b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).2 := (accV_S 8 fun q hq => by
    rw [show 0x1020 + q = 0x1020 + (0x0 + q) by omega, X30 (0x0 + q) (by omega),
      show 0xA44 + (0x0 + q) = 0xA44 + q by omega]).trans a29_a44
  clear a29_15c8 a29_15a8 a29_1480 a29_1380 a29_1020 a29_a44 a29_a20 a29_440 a29_420 a29_320 a29_2e0 a29_2c0 a29_2a0 b29_14a0 b29_13a0 b29_1040 b29_a64 b29_a40 b29_340 w29_133c w29_1338 w29_1334 w29_1330 w29_132c w29_1328 w29_1324 w29_1320 w29_464 w29_460 w29_130 w29_12c w29_128 w29_124 w29_120 w29_11c w29_118 w29_114 w29_110 w29_10c w29_108 w29_104 w29_100 w29_fc w29_f8 w29_f4 w29_f0 w29_ec w29_e8 w29_e4 w29_e0 w29_dc w29_d8 w29_d4 w29_d0 w29_cc w29_c8 w29_c4 w29_c0 w29_bc w29_b8 w29_b4 w29_b0 w29_ac w29_a8 w29_a4 w29_a0 w29_9c w29_98 w29_94 w29_90 w29_8c w29_88 w29_84 w29_80 w29_7c w29_78 w29_74 w29_70 w29_6c w29_68 w29_64 w29_60 w29_5c w29_58 w29_54 w29_50 w29_4c w29_44 w29_40 w29_3c w29_38 w29_34 w29_20 w29_1c g29_12 g29_11 g29_10 g29_27 g29_26 g29_24 g29_19 g29_18 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 rb29 s29 m29 u29 c29
  -- 0x1E4C: lw
  obtain ⟨n31, d31, u31⟩ := s30.lw E30.self sv_at_1e4c (off' := 0x1E4E) (by decide)
    (by rw [g30_2, show B + 0x21A0 + 0x78 = B + 0x21A0 + BitVec.ofNat 32 0x78 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s31 : St n31.mem SV n31 0x1E4E (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
  have m31 : n31.mem = n30.mem := u31.mem
  have fr31 : ∀ x, SvR B x → n31.mem x = n30.mem x := fun x _ => by rw [m31]
  have t31 : Steps n0 n31 := t30.trans (.single d31)
  have fR31 : ∀ x, SvR B x → n31.mem x = M0 x := fun x hx => (fr31 x hx).trans (fR30 x hx)
  have E31 : SvCode n31.mem := E30.fr F fr31
  have V31 : SvSaves B n31.mem v := V30.same m31
  have g31_2 : reg n31 sp = B + 0x21A0 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_2]
  have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_3]
  have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_4]
  have g31_8 : reg n31 (8 : Fin 32) = BitVec.ofNat 32 ns := by rw [u31.regs, upd_ne (by decide) (by decide), g30_8]
  have g31_18 : reg n31 (18 : Fin 32) = out := by rw [u31.regs, upd_ne (by decide) (by decide), g30_18]
  have g31_19 : reg n31 (19 : Fin 32) = bp := by rw [u31.regs, upd_ne (by decide) (by decide), g30_19]
  have g31_24 : reg n31 (24 : Fin 32) = ulo := by rw [u31.regs, upd_ne (by decide) (by decide), g30_24]
  have g31_26 : reg n31 (26 : Fin 32) = x26 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_26]
  have g31_27 : reg n31 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_27]
  have g31_10 : reg n31 a0 = rem := by
    rw [u31.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g30_2, show B + 0x21A0 + 0x78 = B + 0x21A0 + BitVec.ofNat 32 0x78 by sv_addr, w30_78]
  have keep_kk31 : SvKeepL B n0.mem n31.mem [(0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4), (0x1338, 0x4), (0x133C, 0x4), (0xA20, 0x45), (0x320, 0x24), (0x1380, 0x24), (0xA20, 0x45), (0x1480, 0x24), (0x1020, 0x24)] := by rw [m31]; exact keep_kk30
  clear keep_kk30
  have w31_1c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 ns := by rw [m31]; exact w30_1c
  have w31_20 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = nzw := by rw [m31]; exact w30_20
  have w31_34 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = dlo := by rw [m31]; exact w30_34
  have w31_38 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = dhi := by rw [m31]; exact w30_38
  have w31_3c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = uhi := by rw [m31]; exact w30_3c
  have w31_40 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = vhi := by rw [m31]; exact w30_40
  have w31_44 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = vlo := by rw [m31]; exact w30_44
  have w31_4c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m31]; exact w30_4c
  have w31_50 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m31]; exact w30_50
  have w31_54 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m31]; exact w30_54
  have w31_58 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m31]; exact w30_58
  have w31_5c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rlo := by rw [m31]; exact w30_5c
  have w31_60 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = qhi := by rw [m31]; exact w30_60
  have w31_64 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m31]; exact w30_64
  have w31_68 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m31]; exact w30_68
  have w31_6c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m31]; exact w30_6c
  have w31_70 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = qlo := by rw [m31]; exact w30_70
  have w31_74 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = rhi := by rw [m31]; exact w30_74
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
  have w31_460 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m31]; exact w30_460
  have w31_464 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m31]; exact w30_464
  have w31_1320 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = ulo := by rw [m31]; exact w30_1320
  have w31_1324 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = uhi := by rw [m31]; exact w30_1324
  have w31_1328 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = vlo := by rw [m31]; exact w30_1328
  have w31_132c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = vhi := by rw [m31]; exact w30_132c
  have w31_1330 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = qlo := by rw [m31]; exact w30_1330
  have w31_1334 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = qhi := by rw [m31]; exact w30_1334
  have w31_1338 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) = rlo := by rw [m31]; exact w30_1338
  have w31_133c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x133C) = rhi := by rw [m31]; exact w30_133c
  have b31_340 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = BitVec.ofNat 8 σ20a := by rw [m31]; exact b30_340
  have b31_a40 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 8 (lrsm8 σ26a A26a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).1 := by rw [m31]; exact b30_a40
  have b31_a64 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA64) = BitVec.ofNat 8 (lrsm8 σ26b A26b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).1 := by rw [m31]; exact b30_a64
  have b31_1040 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = BitVec.ofNat 8 (lrsm8 σ26b A26b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).1 := by rw [m31]; exact b30_1040
  have b31_13a0 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = BitVec.ofNat 8 σ20b := by rw [m31]; exact b30_13a0
  have b31_14a0 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = BitVec.ofNat 8 (lrsm8 σ26a A26a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).1 := by rw [m31]; exact b30_14a0
  have a31_2a0 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m31]; exact a30_2a0
  have a31_2c0 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m31]; exact a30_2c0
  have a31_2e0 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m31]; exact a30_2e0
  have a31_320 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = A20a / 2 ^ ns % 2 ^ 256 := by rw [m31]; exact a30_320
  have a31_420 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := by rw [m31]; exact a30_420
  have a31_440 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := by rw [m31]; exact a30_440
  have a31_a20 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 8 = (lrsm8 σ26a A26a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).2 := by rw [m31]; exact a30_a20
  have a31_a44 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) 8 = (lrsm8 σ26b A26b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).2 := by rw [m31]; exact a30_a44
  have a31_1020 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = (lrsm8 σ26b A26b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).2 := by rw [m31]; exact a30_1020
  have a31_1380 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = A20b / 2 ^ ns % 2 ^ 256 := by rw [m31]; exact a30_1380
  have a31_1480 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = (lrsm8 σ26a A26a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).2 := by rw [m31]; exact a30_1480
  have a31_15a8 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := by rw [m31]; exact a30_15a8
  have a31_15c8 : accV n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := by rw [m31]; exact a30_15c8
  clear a30_1020 a30_15c8 a30_15a8 a30_1480 a30_1380 a30_a44 a30_a20 a30_440 a30_420 a30_320 a30_2e0 a30_2c0 a30_2a0 b30_1040 b30_14a0 b30_13a0 b30_a64 b30_a40 b30_340 w30_133c w30_1338 w30_1334 w30_1330 w30_132c w30_1328 w30_1324 w30_1320 w30_464 w30_460 w30_130 w30_12c w30_128 w30_124 w30_120 w30_11c w30_118 w30_114 w30_110 w30_10c w30_108 w30_104 w30_100 w30_fc w30_f8 w30_f4 w30_f0 w30_ec w30_e8 w30_e4 w30_e0 w30_dc w30_d8 w30_d4 w30_d0 w30_cc w30_c8 w30_c4 w30_c0 w30_bc w30_b8 w30_b4 w30_b0 w30_ac w30_a8 w30_a4 w30_a0 w30_9c w30_98 w30_94 w30_90 w30_8c w30_88 w30_84 w30_80 w30_7c w30_78 w30_74 w30_70 w30_6c w30_68 w30_64 w30_60 w30_5c w30_58 w30_54 w30_50 w30_4c w30_44 w30_40 w30_3c w30_38 w30_34 w30_20 w30_1c g30_27 g30_26 g30_24 g30_19 g30_18 g30_8 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 s30 X30 K30 P30
  -- 0x1E4E
  obtain ⟨n32, c32, u32⟩ := s31.block svZB1e4e E31.self svZB1e4e_end
    ⟨trivial, trivial⟩
  have m32 : n32.mem = n31.mem := u32.mem
  have s32 : St n32.mem SV n32 0x1E50 (reg n32) := ⟨u32.pc, rfl, fun _ => rfl⟩
  have rb32 : ∀ q, reg n32 q = (runBlock svZB1e4e (n31.mem, reg n31)).2 q := fun q => by rw [u32.regs]
  have fr32 : ∀ x, SvR B x → n32.mem x = n31.mem x := fun x _ => by rw [m32]
  have t32 : Steps n0 n32 := t31.trans c32
  have fR32 : ∀ x, SvR B x → n32.mem x = M0 x := fun x hx => (fr32 x hx).trans (fR31 x hx)
  have E32 : SvCode n32.mem := E31.fr F fr32
  have V32 : SvSaves B n32.mem v := V31.same m32
  have g32_2 : reg n32 sp = B + 0x21A0 := by
    rw [rb32, runBlock_reg _ _ _ sp s31.zero (by decide), g31_2]
  have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb32, runBlock_reg _ _ _ (3 : Fin 32) s31.zero (by decide), g31_3]
  have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb32, runBlock_reg _ _ _ (4 : Fin 32) s31.zero (by decide), g31_4]
  have g32_8 : reg n32 (8 : Fin 32) = BitVec.ofNat 32 ns := by
    rw [rb32, runBlock_reg _ _ _ (8 : Fin 32) s31.zero (by decide), g31_8]
  have g32_18 : reg n32 (18 : Fin 32) = out := by
    rw [rb32, runBlock_reg _ _ _ (18 : Fin 32) s31.zero (by decide), g31_18]
  have g32_19 : reg n32 (19 : Fin 32) = bp := by
    rw [rb32, runBlock_reg _ _ _ (19 : Fin 32) s31.zero (by decide), g31_19]
  have g32_24 : reg n32 (24 : Fin 32) = ulo := by
    rw [rb32, runBlock_reg _ _ _ (24 : Fin 32) s31.zero (by decide), g31_24]
  have g32_26 : reg n32 (26 : Fin 32) = x26 := by
    rw [rb32, runBlock_reg _ _ _ (26 : Fin 32) s31.zero (by decide), g31_26]
  have g32_27 : reg n32 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb32, runBlock_reg _ _ _ (27 : Fin 32) s31.zero (by decide), g31_27]
  have g32_10 : reg n32 a0 = (rem) - (BitVec.ofNat 32 ns) := by
    rw [rb32]; simp +decide only [runBlock, BInstr.run, svZB1e4e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g31_2, g31_3, g31_4, g31_8, g31_10, g31_18, g31_19, g31_24, g31_26, g31_27, s31.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk32 : SvKeepL B n0.mem n32.mem [(0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4), (0x1338, 0x4), (0x133C, 0x4), (0xA20, 0x45), (0x320, 0x24), (0x1380, 0x24), (0xA20, 0x45), (0x1480, 0x24), (0x1020, 0x24)] := by rw [m32]; exact keep_kk31
  clear keep_kk31
  have w32_1c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 ns := by rw [m32]; exact w31_1c
  have w32_20 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = nzw := by rw [m32]; exact w31_20
  have w32_34 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = dlo := by rw [m32]; exact w31_34
  have w32_38 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = dhi := by rw [m32]; exact w31_38
  have w32_3c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = uhi := by rw [m32]; exact w31_3c
  have w32_40 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = vhi := by rw [m32]; exact w31_40
  have w32_44 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = vlo := by rw [m32]; exact w31_44
  have w32_4c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m32]; exact w31_4c
  have w32_50 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m32]; exact w31_50
  have w32_54 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m32]; exact w31_54
  have w32_58 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m32]; exact w31_58
  have w32_5c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rlo := by rw [m32]; exact w31_5c
  have w32_60 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = qhi := by rw [m32]; exact w31_60
  have w32_64 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m32]; exact w31_64
  have w32_68 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m32]; exact w31_68
  have w32_6c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m32]; exact w31_6c
  have w32_70 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = qlo := by rw [m32]; exact w31_70
  have w32_74 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = rhi := by rw [m32]; exact w31_74
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
  have w32_460 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m32]; exact w31_460
  have w32_464 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m32]; exact w31_464
  have w32_1320 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = ulo := by rw [m32]; exact w31_1320
  have w32_1324 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = uhi := by rw [m32]; exact w31_1324
  have w32_1328 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = vlo := by rw [m32]; exact w31_1328
  have w32_132c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = vhi := by rw [m32]; exact w31_132c
  have w32_1330 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = qlo := by rw [m32]; exact w31_1330
  have w32_1334 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = qhi := by rw [m32]; exact w31_1334
  have w32_1338 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) = rlo := by rw [m32]; exact w31_1338
  have w32_133c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x133C) = rhi := by rw [m32]; exact w31_133c
  have b32_340 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = BitVec.ofNat 8 σ20a := by rw [m32]; exact b31_340
  have b32_a40 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 8 (lrsm8 σ26a A26a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).1 := by rw [m32]; exact b31_a40
  have b32_a64 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA64) = BitVec.ofNat 8 (lrsm8 σ26b A26b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).1 := by rw [m32]; exact b31_a64
  have b32_1040 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = BitVec.ofNat 8 (lrsm8 σ26b A26b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).1 := by rw [m32]; exact b31_1040
  have b32_13a0 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = BitVec.ofNat 8 σ20b := by rw [m32]; exact b31_13a0
  have b32_14a0 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = BitVec.ofNat 8 (lrsm8 σ26a A26a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).1 := by rw [m32]; exact b31_14a0
  have a32_2a0 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m32]; exact a31_2a0
  have a32_2c0 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m32]; exact a31_2c0
  have a32_2e0 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m32]; exact a31_2e0
  have a32_320 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = A20a / 2 ^ ns % 2 ^ 256 := by rw [m32]; exact a31_320
  have a32_420 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := by rw [m32]; exact a31_420
  have a32_440 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := by rw [m32]; exact a31_440
  have a32_a20 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 8 = (lrsm8 σ26a A26a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).2 := by rw [m32]; exact a31_a20
  have a32_a44 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) 8 = (lrsm8 σ26b A26b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).2 := by rw [m32]; exact a31_a44
  have a32_1020 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = (lrsm8 σ26b A26b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).2 := by rw [m32]; exact a31_1020
  have a32_1380 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = A20b / 2 ^ ns % 2 ^ 256 := by rw [m32]; exact a31_1380
  have a32_1480 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = (lrsm8 σ26a A26a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).2 := by rw [m32]; exact a31_1480
  have a32_15a8 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := by rw [m32]; exact a31_15a8
  have a32_15c8 : accV n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := by rw [m32]; exact a31_15c8
  clear a31_15c8 a31_15a8 a31_1480 a31_1380 a31_1020 a31_a44 a31_a20 a31_440 a31_420 a31_320 a31_2e0 a31_2c0 a31_2a0 b31_14a0 b31_13a0 b31_1040 b31_a64 b31_a40 b31_340 w31_133c w31_1338 w31_1334 w31_1330 w31_132c w31_1328 w31_1324 w31_1320 w31_464 w31_460 w31_130 w31_12c w31_128 w31_124 w31_120 w31_11c w31_118 w31_114 w31_110 w31_10c w31_108 w31_104 w31_100 w31_fc w31_f8 w31_f4 w31_f0 w31_ec w31_e8 w31_e4 w31_e0 w31_dc w31_d8 w31_d4 w31_d0 w31_cc w31_c8 w31_c4 w31_c0 w31_bc w31_b8 w31_b4 w31_b0 w31_ac w31_a8 w31_a4 w31_a0 w31_9c w31_98 w31_94 w31_90 w31_8c w31_88 w31_84 w31_80 w31_7c w31_78 w31_74 w31_70 w31_6c w31_68 w31_64 w31_60 w31_5c w31_58 w31_54 w31_50 w31_4c w31_44 w31_40 w31_3c w31_38 w31_34 w31_20 w31_1c g31_10 g31_27 g31_26 g31_24 g31_19 g31_18 g31_8 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 m31 s31 u31 d31
  -- 0x1E50: j
  obtain ⟨n33, d33, u33⟩ := s32.jump E32.self sv_at_1e50 (off' := 0x1B52) (by decide)
    (by rw [s32.pc]; decide)
  have s33 : St n33.mem SV n33 0x1B52 (reg n33) := ⟨u33.pc, rfl, fun _ => rfl⟩
  have m33 : n33.mem = n32.mem := u33.mem
  have fr33 : ∀ x, SvR B x → n33.mem x = n32.mem x := fun x _ => by rw [m33]
  have t33 : Steps n0 n33 := t32.trans (.single d33)
  have fR33 : ∀ x, SvR B x → n33.mem x = M0 x := fun x hx => (fr33 x hx).trans (fR32 x hx)
  have E33 : SvCode n33.mem := E32.fr F fr33
  have V33 : SvSaves B n33.mem v := V32.same m33
  have g33_2 : reg n33 sp = B + 0x21A0 := by rw [u33.regs, g32_2]
  have g33_3 : reg n33 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u33.regs, g32_3]
  have g33_4 : reg n33 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u33.regs, g32_4]
  have g33_8 : reg n33 (8 : Fin 32) = BitVec.ofNat 32 ns := by rw [u33.regs, g32_8]
  have g33_10 : reg n33 a0 = (rem) - (BitVec.ofNat 32 ns) := by rw [u33.regs, g32_10]
  have g33_18 : reg n33 (18 : Fin 32) = out := by rw [u33.regs, g32_18]
  have g33_19 : reg n33 (19 : Fin 32) = bp := by rw [u33.regs, g32_19]
  have g33_24 : reg n33 (24 : Fin 32) = ulo := by rw [u33.regs, g32_24]
  have g33_26 : reg n33 (26 : Fin 32) = x26 := by rw [u33.regs, g32_26]
  have g33_27 : reg n33 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u33.regs, g32_27]
  have keep_kk33 : SvKeepL B n0.mem n33.mem [(0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4), (0x1338, 0x4), (0x133C, 0x4), (0xA20, 0x45), (0x320, 0x24), (0x1380, 0x24), (0xA20, 0x45), (0x1480, 0x24), (0x1020, 0x24)] := by rw [m33]; exact keep_kk32
  clear keep_kk32
  have w33_1c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 ns := by rw [m33]; exact w32_1c
  have w33_20 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = nzw := by rw [m33]; exact w32_20
  have w33_34 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = dlo := by rw [m33]; exact w32_34
  have w33_38 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = dhi := by rw [m33]; exact w32_38
  have w33_3c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = uhi := by rw [m33]; exact w32_3c
  have w33_40 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = vhi := by rw [m33]; exact w32_40
  have w33_44 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = vlo := by rw [m33]; exact w32_44
  have w33_4c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m33]; exact w32_4c
  have w33_50 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m33]; exact w32_50
  have w33_54 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m33]; exact w32_54
  have w33_58 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m33]; exact w32_58
  have w33_5c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rlo := by rw [m33]; exact w32_5c
  have w33_60 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = qhi := by rw [m33]; exact w32_60
  have w33_64 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m33]; exact w32_64
  have w33_68 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m33]; exact w32_68
  have w33_6c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m33]; exact w32_6c
  have w33_70 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = qlo := by rw [m33]; exact w32_70
  have w33_74 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = rhi := by rw [m33]; exact w32_74
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
  have w33_460 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m33]; exact w32_460
  have w33_464 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := by rw [m33]; exact w32_464
  have w33_1320 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = ulo := by rw [m33]; exact w32_1320
  have w33_1324 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = uhi := by rw [m33]; exact w32_1324
  have w33_1328 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = vlo := by rw [m33]; exact w32_1328
  have w33_132c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = vhi := by rw [m33]; exact w32_132c
  have w33_1330 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = qlo := by rw [m33]; exact w32_1330
  have w33_1334 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = qhi := by rw [m33]; exact w32_1334
  have w33_1338 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) = rlo := by rw [m33]; exact w32_1338
  have w33_133c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x133C) = rhi := by rw [m33]; exact w32_133c
  have b33_340 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = BitVec.ofNat 8 σ20a := by rw [m33]; exact b32_340
  have b33_a40 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 8 (lrsm8 σ26a A26a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).1 := by rw [m33]; exact b32_a40
  have b33_a64 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA64) = BitVec.ofNat 8 (lrsm8 σ26b A26b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).1 := by rw [m33]; exact b32_a64
  have b33_1040 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = BitVec.ofNat 8 (lrsm8 σ26b A26b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).1 := by rw [m33]; exact b32_1040
  have b33_13a0 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = BitVec.ofNat 8 σ20b := by rw [m33]; exact b32_13a0
  have b33_14a0 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = BitVec.ofNat 8 (lrsm8 σ26a A26a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).1 := by rw [m33]; exact b32_14a0
  have a33_2a0 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := by rw [m33]; exact a32_2a0
  have a33_2c0 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := by rw [m33]; exact a32_2c0
  have a33_2e0 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := by rw [m33]; exact a32_2e0
  have a33_320 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = A20a / 2 ^ ns % 2 ^ 256 := by rw [m33]; exact a32_320
  have a33_420 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := by rw [m33]; exact a32_420
  have a33_440 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := by rw [m33]; exact a32_440
  have a33_a20 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 8 = (lrsm8 σ26a A26a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).2 := by rw [m33]; exact a32_a20
  have a33_a44 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) 8 = (lrsm8 σ26b A26b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).2 := by rw [m33]; exact a32_a44
  have a33_1020 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = (lrsm8 σ26b A26b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).2 := by rw [m33]; exact a32_1020
  have a33_1380 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = A20b / 2 ^ ns % 2 ^ 256 := by rw [m33]; exact a32_1380
  have a33_1480 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = (lrsm8 σ26a A26a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).2 := by rw [m33]; exact a32_1480
  have a33_15a8 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := by rw [m33]; exact a32_15a8
  have a33_15c8 : accV n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := by rw [m33]; exact a32_15c8
  clear a32_15c8 a32_15a8 a32_1480 a32_1380 a32_1020 a32_a44 a32_a20 a32_440 a32_420 a32_320 a32_2e0 a32_2c0 a32_2a0 b32_14a0 b32_13a0 b32_1040 b32_a64 b32_a40 b32_340 w32_133c w32_1338 w32_1334 w32_1330 w32_132c w32_1328 w32_1324 w32_1320 w32_464 w32_460 w32_130 w32_12c w32_128 w32_124 w32_120 w32_11c w32_118 w32_114 w32_110 w32_10c w32_108 w32_104 w32_100 w32_fc w32_f8 w32_f4 w32_f0 w32_ec w32_e8 w32_e4 w32_e0 w32_dc w32_d8 w32_d4 w32_d0 w32_cc w32_c8 w32_c4 w32_c0 w32_bc w32_b8 w32_b4 w32_b0 w32_ac w32_a8 w32_a4 w32_a0 w32_9c w32_98 w32_94 w32_90 w32_8c w32_88 w32_84 w32_80 w32_7c w32_78 w32_74 w32_70 w32_6c w32_68 w32_64 w32_60 w32_5c w32_58 w32_54 w32_50 w32_4c w32_44 w32_40 w32_3c w32_38 w32_34 w32_20 w32_1c g32_10 g32_27 g32_26 g32_24 g32_19 g32_18 g32_8 g32_4 g32_3 g32_2 V32 E32 fR32 t32 fr32 rb32 s32 m32 u32 c32
  -- 0x1B52: sw
  obtain ⟨n34, d34, s34, fr34, K34, W34, rg34⟩ := sv_sw F E33 s33 sv_at_1b52 (off' := 0x1B54) (c := 0x78)
    (by decide) (by rw [g33_2]; sv_addr) (by decide) (by decide)
  have t34 : Steps n0 n34 := t33.trans d34
  have fR34 : ∀ x, SvR B x → n34.mem x = M0 x := fun x hx => (fr34 x hx).trans (fR33 x hx)
  have E34 : SvCode n34.mem := E33.fr F fr34
  have V34 : SvSaves B n34.mem v := V33.keep K34 (by decide)
  have g34_2 : reg n34 sp = B + 0x21A0 := by rw [rg34 sp, g33_2]
  have g34_3 : reg n34 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg34 (3 : Fin 32), g33_3]
  have g34_4 : reg n34 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg34 (4 : Fin 32), g33_4]
  have g34_8 : reg n34 (8 : Fin 32) = BitVec.ofNat 32 ns := by rw [rg34 (8 : Fin 32), g33_8]
  have g34_10 : reg n34 a0 = (rem) - (BitVec.ofNat 32 ns) := by rw [rg34 a0, g33_10]
  have g34_18 : reg n34 (18 : Fin 32) = out := by rw [rg34 (18 : Fin 32), g33_18]
  have g34_19 : reg n34 (19 : Fin 32) = bp := by rw [rg34 (19 : Fin 32), g33_19]
  have g34_24 : reg n34 (24 : Fin 32) = ulo := by rw [rg34 (24 : Fin 32), g33_24]
  have g34_26 : reg n34 (26 : Fin 32) = x26 := by rw [rg34 (26 : Fin 32), g33_26]
  have g34_27 : reg n34 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg34 (27 : Fin 32), g33_27]
  have keep_kk34 : SvKeepL B n0.mem n34.mem [(0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1330, 0x4), (0x1334, 0x4), (0x1338, 0x4), (0x133C, 0x4), (0xA20, 0x45), (0x320, 0x24), (0x1380, 0x24), (0xA20, 0x45), (0x1480, 0x24), (0x1020, 0x24), (0x78, 0x4)] := keep_kk33.trans K34.toL
  clear keep_kk33
  have w34_1c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = BitVec.ofNat 32 ns := (K34.w32 (by decide) (by decide)).trans w33_1c
  have w34_20 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = nzw := (K34.w32 (by decide) (by decide)).trans w33_20
  have w34_34 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = dlo := (K34.w32 (by decide) (by decide)).trans w33_34
  have w34_38 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = dhi := (K34.w32 (by decide) (by decide)).trans w33_38
  have w34_3c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = uhi := (K34.w32 (by decide) (by decide)).trans w33_3c
  have w34_40 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = vhi := (K34.w32 (by decide) (by decide)).trans w33_40
  have w34_44 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = vlo := (K34.w32 (by decide) (by decide)).trans w33_44
  have w34_4c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K34.w32 (by decide) (by decide)).trans w33_4c
  have w34_50 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K34.w32 (by decide) (by decide)).trans w33_50
  have w34_54 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K34.w32 (by decide) (by decide)).trans w33_54
  have w34_58 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K34.w32 (by decide) (by decide)).trans w33_58
  have w34_5c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rlo := (K34.w32 (by decide) (by decide)).trans w33_5c
  have w34_60 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = qhi := (K34.w32 (by decide) (by decide)).trans w33_60
  have w34_64 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K34.w32 (by decide) (by decide)).trans w33_64
  have w34_68 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K34.w32 (by decide) (by decide)).trans w33_68
  have w34_6c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K34.w32 (by decide) (by decide)).trans w33_6c
  have w34_70 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = qlo := (K34.w32 (by decide) (by decide)).trans w33_70
  have w34_74 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = rhi := (K34.w32 (by decide) (by decide)).trans w33_74
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
  have w34_460 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x460) = BitVec.ofNat 32 0xFFFFFFFF := (K34.w32 (by decide) (by decide)).trans w33_460
  have w34_464 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x464) = BitVec.ofNat 32 0xFFFFFFFF := (K34.w32 (by decide) (by decide)).trans w33_464
  have w34_1320 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = ulo := (K34.w32 (by decide) (by decide)).trans w33_1320
  have w34_1324 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = uhi := (K34.w32 (by decide) (by decide)).trans w33_1324
  have w34_1328 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = vlo := (K34.w32 (by decide) (by decide)).trans w33_1328
  have w34_132c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = vhi := (K34.w32 (by decide) (by decide)).trans w33_132c
  have w34_1330 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x1330) = qlo := (K34.w32 (by decide) (by decide)).trans w33_1330
  have w34_1334 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x1334) = qhi := (K34.w32 (by decide) (by decide)).trans w33_1334
  have w34_1338 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x1338) = rlo := (K34.w32 (by decide) (by decide)).trans w33_1338
  have w34_133c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x133C) = rhi := (K34.w32 (by decide) (by decide)).trans w33_133c
  have b34_340 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x340) = BitVec.ofNat 8 σ20a := (K34.b8 (by decide) (by decide)).trans b33_340
  have b34_a40 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 8 (lrsm8 σ26a A26a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).1 := (K34.b8 (by decide) (by decide)).trans b33_a40
  have b34_a64 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA64) = BitVec.ofNat 8 (lrsm8 σ26b A26b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).1 := (K34.b8 (by decide) (by decide)).trans b33_a64
  have b34_1040 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = BitVec.ofNat 8 (lrsm8 σ26b A26b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).1 := (K34.b8 (by decide) (by decide)).trans b33_1040
  have b34_13a0 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x13A0) = BitVec.ofNat 8 σ20b := (K34.b8 (by decide) (by decide)).trans b33_13a0
  have b34_14a0 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x14A0) = BitVec.ofNat 8 (lrsm8 σ26a A26a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).1 := (K34.b8 (by decide) (by decide)).trans b33_14a0
  have w34_78 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = (rem) - (BitVec.ofNat 32 ns) := by rw [W34, g33_10]
  have a34_2a0 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) 8 = rv := (K34.acc (by decide) (by decide)).trans a33_2a0
  have a34_2c0 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) 8 = sv := (K34.acc (by decide) (by decide)).trans a33_2c0
  have a34_2e0 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8 = zv := (K34.acc (by decide) (by decide)).trans a33_2e0
  have a34_320 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) 8 = A20a / 2 ^ ns % 2 ^ 256 := (K34.acc (by decide) (by decide)).trans a33_320
  have a34_420 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8 := (K34.acc (by decide) (by decide)).trans a33_420
  have a34_440 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x440) 8 = accV M0 (BitVec.ofNat 32 0x3FCC4B78) 8 := (K34.acc (by decide) (by decide)).trans a33_440
  have a34_a20 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 8 = (lrsm8 σ26a A26a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).2 := (K34.acc (by decide) (by decide)).trans a33_a20
  have a34_a44 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) 8 = (lrsm8 σ26b A26b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).2 := (K34.acc (by decide) (by decide)).trans a33_a44
  have a34_1020 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 8 = (lrsm8 σ26b A26b ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).2 := (K34.acc (by decide) (by decide)).trans a33_1020
  have a34_1380 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 8 = A20b / 2 ^ ns % 2 ^ 256 := (K34.acc (by decide) (by decide)).trans a33_1380
  have a34_1480 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) 8 = (lrsm8 σ26a A26a ((BitVec.ofNat 32 0xFFFFFFFF).toNat + 2 ^ 32 * (BitVec.ofNat 32 0xFFFFFFFF).toNat) ns (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8)).2 := (K34.acc (by decide) (by decide)).trans a33_1480
  have a34_15a8 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x15A8) 8 = X := (K34.acc (by decide) (by decide)).trans a33_15a8
  have a34_15c8 : accV n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C8) 8 = Y := (K34.acc (by decide) (by decide)).trans a33_15c8
  clear a33_15c8 a33_15a8 a33_1480 a33_1380 a33_1020 a33_a44 a33_a20 a33_440 a33_420 a33_320 a33_2e0 a33_2c0 a33_2a0 b33_14a0 b33_13a0 b33_1040 b33_a64 b33_a40 b33_340 w33_133c w33_1338 w33_1334 w33_1330 w33_132c w33_1328 w33_1324 w33_1320 w33_464 w33_460 w33_130 w33_12c w33_128 w33_124 w33_120 w33_11c w33_118 w33_114 w33_110 w33_10c w33_108 w33_104 w33_100 w33_fc w33_f8 w33_f4 w33_f0 w33_ec w33_e8 w33_e4 w33_e0 w33_dc w33_d8 w33_d4 w33_d0 w33_cc w33_c8 w33_c4 w33_c0 w33_bc w33_b8 w33_b4 w33_b0 w33_ac w33_a8 w33_a4 w33_a0 w33_9c w33_98 w33_94 w33_90 w33_8c w33_88 w33_84 w33_80 w33_7c w33_78 w33_74 w33_70 w33_6c w33_68 w33_64 w33_60 w33_5c w33_58 w33_54 w33_50 w33_4c w33_44 w33_40 w33_3c w33_38 w33_34 w33_20 w33_1c g33_27 g33_26 g33_24 g33_19 g33_18 g33_10 g33_8 g33_4 g33_3 g33_2 V33 E33 fR33 t33 fr33 m33 s33 u33 d33
  exact .inr ⟨σ20a, A20a, e0_20, hσ0_20, σ20b, A20b, e1_20, hσ1_20, σ26a, A26a, e0_26, hσ0_26, σ26b, A26b, e1_26, hσ1_26, n34, t34, s34, E34, V34, fR34, g34_2, g34_3, g34_4, g34_18, g34_19, g34_26, g34_27, w34_1c, w34_20, w34_34, w34_38, w34_3c, w34_40, w34_44, w34_4c, w34_50, w34_54, w34_58, w34_5c, w34_60, w34_64, w34_68, w34_6c, w34_70, w34_74, w34_78, w34_7c, w34_80, w34_84, w34_88, w34_8c, w34_90, w34_94, w34_98, w34_9c, w34_a0, w34_a4, w34_a8, w34_ac, w34_b0, w34_b4, w34_b8, w34_bc, w34_c0, w34_c4, w34_c8, w34_cc, w34_d0, w34_d4, w34_d8, w34_dc, w34_e0, w34_e4, w34_e8, w34_ec, w34_f0, w34_f4, w34_f8, w34_fc, w34_100, w34_104, w34_108, w34_10c, w34_110, w34_114, w34_118, w34_11c, w34_120, w34_124, w34_128, w34_12c, w34_130, w34_460, w34_464, w34_1320, w34_1324, w34_1328, w34_132c, w34_1330, w34_1334, w34_1338, w34_133c, b34_340, b34_a40, b34_a64, b34_1040, b34_13a0, b34_14a0, a34_2a0, a34_2c0, a34_2e0, a34_320, a34_420, a34_440, a34_a20, a34_a44, a34_1020, a34_1380, a34_1480, a34_15a8, a34_15c8, keep_kk34.mono (by decide)⟩

end C3.RV32.Sv
