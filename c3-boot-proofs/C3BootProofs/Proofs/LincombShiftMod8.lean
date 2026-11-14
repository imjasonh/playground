import C3BootProofs.Proofs.LincombShiftMod12
import C3BootProofs.Proofs.Norm8
import C3BootProofs.Proofs.LincombInt8
import C3BootProofs.Proofs.WideMul8x2
import C3BootProofs.Proofs.CondNeg8
import C3BootProofs.Proofs.ShrWide8Main
import C3BootProofs.Proofs.UintSelect8

/-!
# `SignedInt<8>::lincomb_int_reduce_shift_mod::<2>`

The step of Bernstein-Yang inversion that updates `d` and `e`: the linear
combination `a·c + b·d` through the proved `lincomb_int`, plus the multiple
`m·mf` of the modulus that clears its low `shift` bits (`mf` is the low 64
bits times `mi`, masked to `shift` bits), shifted right by `shift`, and
reduced below `m` with one conditional subtraction. The compiled function
inlines the 64-bit multiplication, the mask, and three subtraction loops,
and calls the proved `to_uint_resize`, `leading_mut`, `trailing`,
`widening_mul_fixed::<8, 2>`, `borrowing_sub`,
`conditional_negate_in_place_wide`, `shr_in_place_wide`, `Uint<8>::select`,
`memset`, and `memcpy`.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem lsm8_at_0 : fetchRel lincombShiftMod8Code 0x0 = some (.aluImm .add sp sp 0xFFFFFF00, 2) := by decide
theorem lsm8_at_2 : fetchRel lincombShiftMod8Code 0x2 = some (.store .sw sp ra 0xFC, 2) := by decide
theorem lsm8_at_4 : fetchRel lincombShiftMod8Code 0x4 = some (.store .sw sp (8 : Fin 32) 0xF8, 2) := by decide
theorem lsm8_at_6 : fetchRel lincombShiftMod8Code 0x6 = some (.store .sw sp (9 : Fin 32) 0xF4, 2) := by decide
theorem lsm8_at_8 : fetchRel lincombShiftMod8Code 0x8 = some (.store .sw sp (18 : Fin 32) 0xF0, 2) := by decide
theorem lsm8_at_a : fetchRel lincombShiftMod8Code 0xA = some (.store .sw sp (19 : Fin 32) 0xEC, 2) := by decide
theorem lsm8_at_c : fetchRel lincombShiftMod8Code 0xC = some (.store .sw sp (20 : Fin 32) 0xE8, 2) := by decide
theorem lsm8_at_e : fetchRel lincombShiftMod8Code 0xE = some (.store .sw sp (21 : Fin 32) 0xE4, 2) := by decide
theorem lsm8_at_10 : fetchRel lincombShiftMod8Code 0x10 = some (.store .sw sp (22 : Fin 32) 0xE0, 2) := by decide
theorem lsm8_at_12 : fetchRel lincombShiftMod8Code 0x12 = some (.store .sw sp (23 : Fin 32) 0xDC, 2) := by decide
theorem lsm8_at_14 : fetchRel lincombShiftMod8Code 0x14 = some (.store .sw sp (24 : Fin 32) 0xD8, 2) := by decide
theorem lsm8_at_16 : fetchRel lincombShiftMod8Code 0x16 = some (.store .sw sp (25 : Fin 32) 0xD4, 2) := by decide
theorem lsm8_at_18 : fetchRel lincombShiftMod8Code 0x18 = some (.alu .add (21 : Fin 32) x0 (17 : Fin 32), 2) := by decide
theorem lsm8_at_1a : fetchRel lincombShiftMod8Code 0x1A = some (.alu .add (23 : Fin 32) x0 a6, 2) := by decide
theorem lsm8_at_1c : fetchRel lincombShiftMod8Code 0x1C = some (.alu .add (19 : Fin 32) x0 a5, 2) := by decide
theorem lsm8_at_1e : fetchRel lincombShiftMod8Code 0x1E = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem lsm8_at_20 : fetchRel lincombShiftMod8Code 0x20 = some (.aluImm .add a0 sp 0x28, 2) := by decide
theorem lsm8_at_22 : fetchRel lincombShiftMod8Code 0x22 = some (.aluImm .add (20 : Fin 32) sp 0x28, 4) := by decide
theorem lsm8_at_26 : fetchRel lincombShiftMod8Code 0x26 = some (.auipc ra 0x0, 4) := by decide
theorem lsm8_at_2a : fetchRel lincombShiftMod8Code 0x2A = some (.jalr ra ra 0xFFFFFA4A, 4) := by decide
theorem lsm8_at_2e : fetchRel lincombShiftMod8Code 0x2E = some (.alu .add a0 x0 sp, 2) := by decide
theorem lsm8_at_30 : fetchRel lincombShiftMod8Code 0x30 = some (.aluImm .add a1 sp 0x28, 2) := by decide
theorem lsm8_at_32 : fetchRel lincombShiftMod8Code 0x32 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem lsm8_at_36 : fetchRel lincombShiftMod8Code 0x36 = some (.auipc ra 0x3000, 4) := by decide
theorem lsm8_at_3a : fetchRel lincombShiftMod8Code 0x3A = some (.jalr ra ra 0x4E6, 4) := by decide
theorem lsm8_at_3e : fetchRel lincombShiftMod8Code 0x3E = some (.load .lw a0 sp 0x48, 2) := by decide
theorem lsm8_at_40 : fetchRel lincombShiftMod8Code 0x40 = some (.load .lw a1 sp 0x4C, 2) := by decide
theorem lsm8_at_42 : fetchRel lincombShiftMod8Code 0x42 = some (.load .lbu (22 : Fin 32) sp 0x50, 4) := by decide
theorem lsm8_at_46 : fetchRel lincombShiftMod8Code 0x46 = some (.store .sw sp a0 0x20, 2) := by decide
theorem lsm8_at_48 : fetchRel lincombShiftMod8Code 0x48 = some (.store .sw sp a1 0x24, 2) := by decide
theorem lsm8_at_4a : fetchRel lincombShiftMod8Code 0x4A = some (.aluImm .add a0 sp 0x28, 2) := by decide
theorem lsm8_at_4c : fetchRel lincombShiftMod8Code 0x4C = some (.alu .add a1 x0 sp, 2) := by decide
theorem lsm8_at_4e : fetchRel lincombShiftMod8Code 0x4E = some (.auipc ra 0xFFFFC000, 4) := by decide
theorem lsm8_at_52 : fetchRel lincombShiftMod8Code 0x52 = some (.jalr ra ra 0xFFFFFF68, 4) := by decide
theorem lsm8_at_56 : fetchRel lincombShiftMod8Code 0x56 = some (.aluImm .add (6 : Fin 32) x0 0x0, 2) := by decide
theorem lsm8_at_58 : fetchRel lincombShiftMod8Code 0x58 = some (.store .sw sp x0 0xC8, 2) := by decide
theorem lsm8_at_5a : fetchRel lincombShiftMod8Code 0x5A = some (.store .sw sp x0 0xCC, 2) := by decide
theorem lsm8_at_5c : fetchRel lincombShiftMod8Code 0x5C = some (.aluImm .add (17 : Fin 32) sp 0xC8, 4) := by decide
theorem lsm8_at_60 : fetchRel lincombShiftMod8Code 0x60 = some (.aluImm .add a6 x0 0x2, 2) := by decide
theorem lsm8_at_62 : fetchRel lincombShiftMod8Code 0x62 = some (.aluImm .add (5 : Fin 32) x0 0x2, 2) := by decide
theorem lsm8_at_64 : fetchRel lincombShiftMod8Code 0x64 = some (.branch .beq a6 x0 0x48, 4) := by decide
theorem lsm8_at_68 : fetchRel lincombShiftMod8Code 0x68 = some (.aluImm .add (9 : Fin 32) x0 0x0, 2) := by decide
theorem lsm8_at_6a : fetchRel lincombShiftMod8Code 0x6A = some (.aluImm .sll a1 (6 : Fin 32) 0x2, 4) := by decide
theorem lsm8_at_6e : fetchRel lincombShiftMod8Code 0x6E = some (.alu .add a1 a1 (20 : Fin 32), 2) := by decide
theorem lsm8_at_70 : fetchRel lincombShiftMod8Code 0x70 = some (.load .lw a4 a1 0x0, 2) := by decide
theorem lsm8_at_72 : fetchRel lincombShiftMod8Code 0x72 = some (.alu .add a5 x0 (5 : Fin 32), 2) := by decide
theorem lsm8_at_74 : fetchRel lincombShiftMod8Code 0x74 = some (.alu .add a1 x0 (17 : Fin 32), 2) := by decide
theorem lsm8_at_76 : fetchRel lincombShiftMod8Code 0x76 = some (.alu .add (8 : Fin 32) x0 (21 : Fin 32), 2) := by decide
theorem lsm8_at_78 : fetchRel lincombShiftMod8Code 0x78 = some (.branch .beq (5 : Fin 32) x0 0x2A, 4) := by decide
theorem lsm8_at_7c : fetchRel lincombShiftMod8Code 0x7C = some (.load .lw a2 (8 : Fin 32) 0x0, 2) := by decide
theorem lsm8_at_7e : fetchRel lincombShiftMod8Code 0x7E = some (.alu .mul a3 a2 a4, 4) := by decide
theorem lsm8_at_82 : fetchRel lincombShiftMod8Code 0x82 = some (.load .lw a0 a1 0x0, 2) := by decide
theorem lsm8_at_84 : fetchRel lincombShiftMod8Code 0x84 = some (.alu .mulhu a2 a2 a4, 4) := by decide
theorem lsm8_at_88 : fetchRel lincombShiftMod8Code 0x88 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, 2) := by decide
theorem lsm8_at_8a : fetchRel lincombShiftMod8Code 0x8A = some (.alu .add (9 : Fin 32) (9 : Fin 32) a0, 2) := by decide
theorem lsm8_at_8c : fetchRel lincombShiftMod8Code 0x8C = some (.alu .sltu a0 (9 : Fin 32) a0, 4) := by decide
theorem lsm8_at_90 : fetchRel lincombShiftMod8Code 0x90 = some (.alu .add a3 a3 (9 : Fin 32), 2) := by decide
theorem lsm8_at_92 : fetchRel lincombShiftMod8Code 0x92 = some (.alu .add a0 a0 a2, 2) := by decide
theorem lsm8_at_94 : fetchRel lincombShiftMod8Code 0x94 = some (.alu .sltu (9 : Fin 32) a3 (9 : Fin 32), 4) := by decide
theorem lsm8_at_98 : fetchRel lincombShiftMod8Code 0x98 = some (.store .sw a1 a3 0x0, 2) := by decide
theorem lsm8_at_9a : fetchRel lincombShiftMod8Code 0x9A = some (.alu .add (9 : Fin 32) (9 : Fin 32) a0, 2) := by decide
theorem lsm8_at_9c : fetchRel lincombShiftMod8Code 0x9C = some (.aluImm .add a1 a1 0x4, 2) := by decide
theorem lsm8_at_9e : fetchRel lincombShiftMod8Code 0x9E = some (.aluImm .add a5 a5 0xFFFFFFFF, 2) := by decide
theorem lsm8_at_a0 : fetchRel lincombShiftMod8Code 0xA0 = some (.branch .bne a5 x0 0xFFFFFFDC, 2) := by decide
theorem lsm8_at_a2 : fetchRel lincombShiftMod8Code 0xA2 = some (.aluImm .add (6 : Fin 32) (6 : Fin 32) 0x1, 2) := by decide
theorem lsm8_at_a4 : fetchRel lincombShiftMod8Code 0xA4 = some (.aluImm .add (17 : Fin 32) (17 : Fin 32) 0x4, 2) := by decide
theorem lsm8_at_a6 : fetchRel lincombShiftMod8Code 0xA6 = some (.aluImm .add (5 : Fin 32) (5 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem lsm8_at_a8 : fetchRel lincombShiftMod8Code 0xA8 = some (.branch .bne (6 : Fin 32) a6 0xFFFFFFC0, 4) := by decide
theorem lsm8_at_ac : fetchRel lincombShiftMod8Code 0xAC = some (.aluImm .add a0 x0 0x40, 4) := by decide
theorem lsm8_at_b0 : fetchRel lincombShiftMod8Code 0xB0 = some (.alu .sub (24 : Fin 32) a0 (19 : Fin 32), 4) := by decide
theorem lsm8_at_b4 : fetchRel lincombShiftMod8Code 0xB4 = some (.branch .bgeu (24 : Fin 32) a0 0x220, 4) := by decide
theorem lsm8_at_b8 : fetchRel lincombShiftMod8Code 0xB8 = some (.aluImm .srl (21 : Fin 32) (24 : Fin 32) 0x5, 4) := by decide
theorem lsm8_at_bc : fetchRel lincombShiftMod8Code 0xBC = some (.aluImm .add a0 x0 0x2, 2) := by decide
theorem lsm8_at_be : fetchRel lincombShiftMod8Code 0xBE = some (.store .sw sp x0 0x28, 2) := by decide
theorem lsm8_at_c0 : fetchRel lincombShiftMod8Code 0xC0 = some (.store .sw sp x0 0x2C, 2) := by decide
theorem lsm8_at_c2 : fetchRel lincombShiftMod8Code 0xC2 = some (.alu .sub a2 a0 (21 : Fin 32), 4) := by decide
theorem lsm8_at_c6 : fetchRel lincombShiftMod8Code 0xC6 = some (.aluImm .add a0 sp 0x28, 2) := by decide
theorem lsm8_at_c8 : fetchRel lincombShiftMod8Code 0xC8 = some (.aluImm .add a1 x0 0x2, 2) := by decide
theorem lsm8_at_ca : fetchRel lincombShiftMod8Code 0xCA = some (.auipc ra 0x0, 4) := by decide
theorem lsm8_at_ce : fetchRel lincombShiftMod8Code 0xCE = some (.jalr ra ra 0xFFFFFD18, 4) := by decide
theorem lsm8_at_d2 : fetchRel lincombShiftMod8Code 0xD2 = some (.alu .add (20 : Fin 32) x0 a0, 2) := by decide
theorem lsm8_at_d4 : fetchRel lincombShiftMod8Code 0xD4 = some (.alu .add (8 : Fin 32) x0 a1, 2) := by decide
theorem lsm8_at_d6 : fetchRel lincombShiftMod8Code 0xD6 = some (.lui a0 0x3FCC5000, 4) := by decide
theorem lsm8_at_da : fetchRel lincombShiftMod8Code 0xDA = some (.aluImm .add a0 a0 0xFFFFF838, 4) := by decide
theorem lsm8_at_de : fetchRel lincombShiftMod8Code 0xDE = some (.aluImm .add a1 x0 0x2, 2) := by decide
theorem lsm8_at_e0 : fetchRel lincombShiftMod8Code 0xE0 = some (.alu .add a2 x0 (21 : Fin 32), 2) := by decide
theorem lsm8_at_e2 : fetchRel lincombShiftMod8Code 0xE2 = some (.auipc ra 0x0, 4) := by decide
theorem lsm8_at_e6 : fetchRel lincombShiftMod8Code 0xE6 = some (.jalr ra ra 0xFFFFFD10, 4) := by decide
theorem lsm8_at_ea : fetchRel lincombShiftMod8Code 0xEA = some (.branch .bne (8 : Fin 32) a1 0x1E2, 4) := by decide
theorem lsm8_at_ee : fetchRel lincombShiftMod8Code 0xEE = some (.aluImm .add (21 : Fin 32) sp 0x80, 4) := by decide
theorem lsm8_at_f2 : fetchRel lincombShiftMod8Code 0xF2 = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem lsm8_at_f4 : fetchRel lincombShiftMod8Code 0xF4 = some (.alu .add a2 x0 (20 : Fin 32), 2) := by decide
theorem lsm8_at_f6 : fetchRel lincombShiftMod8Code 0xF6 = some (.branch .beq (8 : Fin 32) x0 0xE, 2) := by decide
theorem lsm8_at_f8 : fetchRel lincombShiftMod8Code 0xF8 = some (.load .lw a3 a0 0x0, 2) := by decide
theorem lsm8_at_fa : fetchRel lincombShiftMod8Code 0xFA = some (.aluImm .add a0 a0 0x4, 2) := by decide
theorem lsm8_at_fc : fetchRel lincombShiftMod8Code 0xFC = some (.store .sw a2 a3 0x0, 2) := by decide
theorem lsm8_at_fe : fetchRel lincombShiftMod8Code 0xFE = some (.aluImm .add a2 a2 0x4, 2) := by decide
theorem lsm8_at_100 : fetchRel lincombShiftMod8Code 0x100 = some (.aluImm .add a1 a1 0xFFFFFFFF, 2) := by decide
theorem lsm8_at_102 : fetchRel lincombShiftMod8Code 0x102 = some (.branch .bne a1 x0 0xFFFFFFF6, 2) := by decide
theorem lsm8_at_104 : fetchRel lincombShiftMod8Code 0x104 = some (.aluImm .and a0 (24 : Fin 32) 0x1F, 4) := by decide
theorem lsm8_at_108 : fetchRel lincombShiftMod8Code 0x108 = some (.branch .beq a0 x0 0x28, 2) := by decide
theorem lsm8_at_10a : fetchRel lincombShiftMod8Code 0x10A = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem lsm8_at_10c : fetchRel lincombShiftMod8Code 0x10C = some (.aluImm .sll a2 (8 : Fin 32) 0x2, 4) := by decide
theorem lsm8_at_110 : fetchRel lincombShiftMod8Code 0x110 = some (.alu .add a3 a2 (20 : Fin 32), 4) := by decide
theorem lsm8_at_114 : fetchRel lincombShiftMod8Code 0x114 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem lsm8_at_118 : fetchRel lincombShiftMod8Code 0x118 = some (.alu .sub a2 a2 a0, 2) := by decide
theorem lsm8_at_11a : fetchRel lincombShiftMod8Code 0x11A = some (.aluImm .add a3 a3 0xFFFFFFFC, 2) := by decide
theorem lsm8_at_11c : fetchRel lincombShiftMod8Code 0x11C = some (.branch .beq (8 : Fin 32) x0 0x14, 2) := by decide
theorem lsm8_at_11e : fetchRel lincombShiftMod8Code 0x11E = some (.load .lw a4 a3 0x0, 2) := by decide
theorem lsm8_at_120 : fetchRel lincombShiftMod8Code 0x120 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem lsm8_at_122 : fetchRel lincombShiftMod8Code 0x122 = some (.alu .srl a5 a4 a0, 4) := by decide
theorem lsm8_at_126 : fetchRel lincombShiftMod8Code 0x126 = some (.alu .or a5 a5 a1, 2) := by decide
theorem lsm8_at_128 : fetchRel lincombShiftMod8Code 0x128 = some (.alu .sll a1 a4 a2, 4) := by decide
theorem lsm8_at_12c : fetchRel lincombShiftMod8Code 0x12C = some (.store .sw a3 a5 0x0, 2) := by decide
theorem lsm8_at_12e : fetchRel lincombShiftMod8Code 0x12E = some (.jal x0 0xFFFFFFEC, 2) := by decide
theorem lsm8_at_130 : fetchRel lincombShiftMod8Code 0x130 = some (.load .lw a2 sp 0x28, 2) := by decide
theorem lsm8_at_132 : fetchRel lincombShiftMod8Code 0x132 = some (.load .lw a3 sp 0x2C, 2) := by decide
theorem lsm8_at_134 : fetchRel lincombShiftMod8Code 0x134 = some (.store .sw sp x0 0x28, 2) := by decide
theorem lsm8_at_136 : fetchRel lincombShiftMod8Code 0x136 = some (.store .sw sp x0 0x2C, 2) := by decide
theorem lsm8_at_138 : fetchRel lincombShiftMod8Code 0x138 = some (.aluImm .add a0 sp 0xC8, 2) := by decide
theorem lsm8_at_13a : fetchRel lincombShiftMod8Code 0x13A = some (.aluImm .add a1 sp 0x58, 2) := by decide
theorem lsm8_at_13c : fetchRel lincombShiftMod8Code 0x13C = some (.store .sw sp a2 0x58, 2) := by decide
theorem lsm8_at_13e : fetchRel lincombShiftMod8Code 0x13E = some (.store .sw sp a3 0x5C, 2) := by decide
theorem lsm8_at_140 : fetchRel lincombShiftMod8Code 0x140 = some (.aluImm .add a2 sp 0x28, 2) := by decide
theorem lsm8_at_142 : fetchRel lincombShiftMod8Code 0x142 = some (.aluImm .add a3 x0 0x2, 2) := by decide
theorem lsm8_at_144 : fetchRel lincombShiftMod8Code 0x144 = some (.branch .beq a3 x0 0x14, 2) := by decide
theorem lsm8_at_146 : fetchRel lincombShiftMod8Code 0x146 = some (.load .lw a4 a0 0x0, 2) := by decide
theorem lsm8_at_148 : fetchRel lincombShiftMod8Code 0x148 = some (.load .lw a5 a1 0x0, 2) := by decide
theorem lsm8_at_14a : fetchRel lincombShiftMod8Code 0x14A = some (.aluImm .add a0 a0 0x4, 2) := by decide
theorem lsm8_at_14c : fetchRel lincombShiftMod8Code 0x14C = some (.alu .and a4 a4 a5, 2) := by decide
theorem lsm8_at_14e : fetchRel lincombShiftMod8Code 0x14E = some (.aluImm .add a1 a1 0x4, 2) := by decide
theorem lsm8_at_150 : fetchRel lincombShiftMod8Code 0x150 = some (.store .sw a2 a4 0x0, 2) := by decide
theorem lsm8_at_152 : fetchRel lincombShiftMod8Code 0x152 = some (.aluImm .add a2 a2 0x4, 2) := by decide
theorem lsm8_at_154 : fetchRel lincombShiftMod8Code 0x154 = some (.aluImm .add a3 a3 0xFFFFFFFF, 2) := by decide
theorem lsm8_at_156 : fetchRel lincombShiftMod8Code 0x156 = some (.branch .bne a3 x0 0xFFFFFFF0, 2) := by decide
theorem lsm8_at_158 : fetchRel lincombShiftMod8Code 0x158 = some (.load .lw a0 sp 0x28, 2) := by decide
theorem lsm8_at_15a : fetchRel lincombShiftMod8Code 0x15A = some (.load .lw a1 sp 0x2C, 2) := by decide
theorem lsm8_at_15c : fetchRel lincombShiftMod8Code 0x15C = some (.store .sw sp a0 0xC8, 2) := by decide
theorem lsm8_at_15e : fetchRel lincombShiftMod8Code 0x15E = some (.store .sw sp a1 0xCC, 2) := by decide
theorem lsm8_at_160 : fetchRel lincombShiftMod8Code 0x160 = some (.aluImm .add a0 sp 0x60, 2) := by decide
theorem lsm8_at_162 : fetchRel lincombShiftMod8Code 0x162 = some (.aluImm .add a2 sp 0xC8, 2) := by decide
theorem lsm8_at_164 : fetchRel lincombShiftMod8Code 0x164 = some (.alu .add a1 x0 (23 : Fin 32), 2) := by decide
theorem lsm8_at_166 : fetchRel lincombShiftMod8Code 0x166 = some (.aluImm .add (24 : Fin 32) sp 0x60, 4) := by decide
theorem lsm8_at_16a : fetchRel lincombShiftMod8Code 0x16A = some (.auipc ra 0x0, 4) := by decide
theorem lsm8_at_16e : fetchRel lincombShiftMod8Code 0x16E = some (.jalr ra ra 0xFFFFFC9E, 4) := by decide
theorem lsm8_at_172 : fetchRel lincombShiftMod8Code 0x172 = some (.aluImm .add a0 sp 0x88, 2) := by decide
theorem lsm8_at_174 : fetchRel lincombShiftMod8Code 0x174 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem lsm8_at_178 : fetchRel lincombShiftMod8Code 0x178 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem lsm8_at_17a : fetchRel lincombShiftMod8Code 0x17A = some (.aluImm .add (25 : Fin 32) sp 0x88, 4) := by decide
theorem lsm8_at_17e : fetchRel lincombShiftMod8Code 0x17E = some (.auipc ra 0x3000, 4) := by decide
theorem lsm8_at_182 : fetchRel lincombShiftMod8Code 0x182 = some (.jalr ra ra 0x336, 4) := by decide
theorem lsm8_at_186 : fetchRel lincombShiftMod8Code 0x186 = some (.aluImm .add (20 : Fin 32) x0 0x0, 2) := by decide
theorem lsm8_at_188 : fetchRel lincombShiftMod8Code 0x188 = some (.alu .add (9 : Fin 32) x0 sp, 2) := by decide
theorem lsm8_at_18a : fetchRel lincombShiftMod8Code 0x18A = some (.aluImm .add (8 : Fin 32) x0 0x8, 2) := by decide
theorem lsm8_at_18c : fetchRel lincombShiftMod8Code 0x18C = some (.branch .beq (8 : Fin 32) x0 0x22, 2) := by decide
theorem lsm8_at_18e : fetchRel lincombShiftMod8Code 0x18E = some (.load .lw a0 (9 : Fin 32) 0x0, 2) := by decide
theorem lsm8_at_190 : fetchRel lincombShiftMod8Code 0x190 = some (.load .lw a1 (24 : Fin 32) 0x0, 4) := by decide
theorem lsm8_at_194 : fetchRel lincombShiftMod8Code 0x194 = some (.alu .add a2 x0 (20 : Fin 32), 2) := by decide
theorem lsm8_at_196 : fetchRel lincombShiftMod8Code 0x196 = some (.auipc ra 0xFFFF1000, 4) := by decide
theorem lsm8_at_19a : fetchRel lincombShiftMod8Code 0x19A = some (.jalr ra ra 0xFFFFFE58, 4) := by decide
theorem lsm8_at_19e : fetchRel lincombShiftMod8Code 0x19E = some (.alu .add (20 : Fin 32) x0 a1, 2) := by decide
theorem lsm8_at_1a0 : fetchRel lincombShiftMod8Code 0x1A0 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x4, 2) := by decide
theorem lsm8_at_1a2 : fetchRel lincombShiftMod8Code 0x1A2 = some (.store .sw (25 : Fin 32) a0 0x0, 4) := by decide
theorem lsm8_at_1a6 : fetchRel lincombShiftMod8Code 0x1A6 = some (.aluImm .add (24 : Fin 32) (24 : Fin 32) 0x4, 2) := by decide
theorem lsm8_at_1a8 : fetchRel lincombShiftMod8Code 0x1A8 = some (.aluImm .add (25 : Fin 32) (25 : Fin 32) 0x4, 2) := by decide
theorem lsm8_at_1aa : fetchRel lincombShiftMod8Code 0x1AA = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem lsm8_at_1ac : fetchRel lincombShiftMod8Code 0x1AC = some (.branch .bne (8 : Fin 32) x0 0xFFFFFFE2, 2) := by decide
theorem lsm8_at_1ae : fetchRel lincombShiftMod8Code 0x1AE = some (.alu .add a0 x0 sp, 2) := by decide
theorem lsm8_at_1b0 : fetchRel lincombShiftMod8Code 0x1B0 = some (.aluImm .add a1 sp 0x88, 2) := by decide
theorem lsm8_at_1b2 : fetchRel lincombShiftMod8Code 0x1B2 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem lsm8_at_1b6 : fetchRel lincombShiftMod8Code 0x1B6 = some (.auipc ra 0x3000, 4) := by decide
theorem lsm8_at_1ba : fetchRel lincombShiftMod8Code 0x1BA = some (.jalr ra ra 0x366, 4) := by decide
theorem lsm8_at_1be : fetchRel lincombShiftMod8Code 0x1BE = some (.store .sw sp x0 0x28, 2) := by decide
theorem lsm8_at_1c0 : fetchRel lincombShiftMod8Code 0x1C0 = some (.store .sw sp x0 0x2C, 2) := by decide
theorem lsm8_at_1c2 : fetchRel lincombShiftMod8Code 0x1C2 = some (.aluImm .add (24 : Fin 32) sp 0x20, 4) := by decide
theorem lsm8_at_1c6 : fetchRel lincombShiftMod8Code 0x1C6 = some (.aluImm .add (9 : Fin 32) sp 0x28, 2) := by decide
theorem lsm8_at_1c8 : fetchRel lincombShiftMod8Code 0x1C8 = some (.aluImm .add (8 : Fin 32) x0 0x2, 2) := by decide
theorem lsm8_at_1ca : fetchRel lincombShiftMod8Code 0x1CA = some (.branch .beq (8 : Fin 32) x0 0x22, 2) := by decide
theorem lsm8_at_1cc : fetchRel lincombShiftMod8Code 0x1CC = some (.load .lw a0 (24 : Fin 32) 0x0, 4) := by decide
theorem lsm8_at_1d0 : fetchRel lincombShiftMod8Code 0x1D0 = some (.load .lw a1 (21 : Fin 32) 0x0, 4) := by decide
theorem lsm8_at_1d4 : fetchRel lincombShiftMod8Code 0x1D4 = some (.alu .add a2 x0 (20 : Fin 32), 2) := by decide
theorem lsm8_at_1d6 : fetchRel lincombShiftMod8Code 0x1D6 = some (.auipc ra 0xFFFF1000, 4) := by decide
theorem lsm8_at_1da : fetchRel lincombShiftMod8Code 0x1DA = some (.jalr ra ra 0xFFFFFE18, 4) := by decide
theorem lsm8_at_1de : fetchRel lincombShiftMod8Code 0x1DE = some (.alu .add (20 : Fin 32) x0 a1, 2) := by decide
theorem lsm8_at_1e0 : fetchRel lincombShiftMod8Code 0x1E0 = some (.aluImm .add (24 : Fin 32) (24 : Fin 32) 0x4, 2) := by decide
theorem lsm8_at_1e2 : fetchRel lincombShiftMod8Code 0x1E2 = some (.store .sw (9 : Fin 32) a0 0x0, 2) := by decide
theorem lsm8_at_1e4 : fetchRel lincombShiftMod8Code 0x1E4 = some (.aluImm .add (21 : Fin 32) (21 : Fin 32) 0x4, 2) := by decide
theorem lsm8_at_1e6 : fetchRel lincombShiftMod8Code 0x1E6 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x4, 2) := by decide
theorem lsm8_at_1e8 : fetchRel lincombShiftMod8Code 0x1E8 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem lsm8_at_1ea : fetchRel lincombShiftMod8Code 0x1EA = some (.branch .bne (8 : Fin 32) x0 0xFFFFFFE2, 2) := by decide
theorem lsm8_at_1ec : fetchRel lincombShiftMod8Code 0x1EC = some (.load .lw a0 sp 0x28, 2) := by decide
theorem lsm8_at_1ee : fetchRel lincombShiftMod8Code 0x1EE = some (.load .lw a1 sp 0x2C, 2) := by decide
theorem lsm8_at_1f0 : fetchRel lincombShiftMod8Code 0x1F0 = some (.store .sw sp a0 0x20, 2) := by decide
theorem lsm8_at_1f2 : fetchRel lincombShiftMod8Code 0x1F2 = some (.store .sw sp a1 0x24, 2) := by decide
theorem lsm8_at_1f4 : fetchRel lincombShiftMod8Code 0x1F4 = some (.store .sw sp (20 : Fin 32) 0x28, 2) := by decide
theorem lsm8_at_1f6 : fetchRel lincombShiftMod8Code 0x1F6 = some (.aluImm .add a0 sp 0x28, 2) := by decide
theorem lsm8_at_1f8 : fetchRel lincombShiftMod8Code 0x1F8 = some (.load .lw a0 sp 0x28, 2) := by decide
theorem lsm8_at_1fa : fetchRel lincombShiftMod8Code 0x1FA = some (.alu .sltu (20 : Fin 32) x0 a0, 4) := by decide
theorem lsm8_at_1fe : fetchRel lincombShiftMod8Code 0x1FE = some (.alu .add a0 x0 sp, 2) := by decide
theorem lsm8_at_200 : fetchRel lincombShiftMod8Code 0x200 = some (.aluImm .add a1 sp 0x20, 2) := by decide
theorem lsm8_at_202 : fetchRel lincombShiftMod8Code 0x202 = some (.alu .add a2 x0 (20 : Fin 32), 2) := by decide
theorem lsm8_at_204 : fetchRel lincombShiftMod8Code 0x204 = some (.alu .add (21 : Fin 32) x0 sp, 2) := by decide
theorem lsm8_at_206 : fetchRel lincombShiftMod8Code 0x206 = some (.auipc ra 0x0, 4) := by decide
theorem lsm8_at_20a : fetchRel lincombShiftMod8Code 0x20A = some (.jalr ra ra 0xFFFFFCEA, 4) := by decide
theorem lsm8_at_20e : fetchRel lincombShiftMod8Code 0x20E = some (.alu .add a0 x0 sp, 2) := by decide
theorem lsm8_at_210 : fetchRel lincombShiftMod8Code 0x210 = some (.aluImm .add a1 sp 0x20, 2) := by decide
theorem lsm8_at_212 : fetchRel lincombShiftMod8Code 0x212 = some (.alu .add a2 x0 (19 : Fin 32), 2) := by decide
theorem lsm8_at_214 : fetchRel lincombShiftMod8Code 0x214 = some (.auipc ra 0x0, 4) := by decide
theorem lsm8_at_218 : fetchRel lincombShiftMod8Code 0x218 = some (.jalr ra ra 0xFFFFF9E0, 4) := by decide
theorem lsm8_at_21c : fetchRel lincombShiftMod8Code 0x21C = some (.load .lw (19 : Fin 32) sp 0x20, 2) := by decide
theorem lsm8_at_21e : fetchRel lincombShiftMod8Code 0x21E = some (.aluImm .add a0 sp 0xA8, 2) := by decide
theorem lsm8_at_220 : fetchRel lincombShiftMod8Code 0x220 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem lsm8_at_224 : fetchRel lincombShiftMod8Code 0x224 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem lsm8_at_226 : fetchRel lincombShiftMod8Code 0x226 = some (.aluImm .add (8 : Fin 32) sp 0xA8, 2) := by decide
theorem lsm8_at_228 : fetchRel lincombShiftMod8Code 0x228 = some (.auipc ra 0x3000, 4) := by decide
theorem lsm8_at_22c : fetchRel lincombShiftMod8Code 0x22C = some (.jalr ra ra 0x28C, 4) := by decide
theorem lsm8_at_230 : fetchRel lincombShiftMod8Code 0x230 = some (.aluImm .add a2 x0 0x0, 2) := by decide
theorem lsm8_at_232 : fetchRel lincombShiftMod8Code 0x232 = some (.aluImm .add (9 : Fin 32) x0 0x8, 2) := by decide
theorem lsm8_at_234 : fetchRel lincombShiftMod8Code 0x234 = some (.branch .beq (9 : Fin 32) x0 0x20, 2) := by decide
theorem lsm8_at_236 : fetchRel lincombShiftMod8Code 0x236 = some (.load .lw a0 (21 : Fin 32) 0x0, 4) := by decide
theorem lsm8_at_23a : fetchRel lincombShiftMod8Code 0x23A = some (.load .lw a1 (23 : Fin 32) 0x0, 4) := by decide
theorem lsm8_at_23e : fetchRel lincombShiftMod8Code 0x23E = some (.auipc ra 0xFFFF1000, 4) := by decide
theorem lsm8_at_242 : fetchRel lincombShiftMod8Code 0x242 = some (.jalr ra ra 0xFFFFFDB0, 4) := by decide
theorem lsm8_at_246 : fetchRel lincombShiftMod8Code 0x246 = some (.alu .add a2 x0 a1, 2) := by decide
theorem lsm8_at_248 : fetchRel lincombShiftMod8Code 0x248 = some (.aluImm .add (21 : Fin 32) (21 : Fin 32) 0x4, 2) := by decide
theorem lsm8_at_24a : fetchRel lincombShiftMod8Code 0x24A = some (.store .sw (8 : Fin 32) a0 0x0, 2) := by decide
theorem lsm8_at_24c : fetchRel lincombShiftMod8Code 0x24C = some (.aluImm .add (23 : Fin 32) (23 : Fin 32) 0x4, 2) := by decide
theorem lsm8_at_24e : fetchRel lincombShiftMod8Code 0x24E = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, 2) := by decide
theorem lsm8_at_250 : fetchRel lincombShiftMod8Code 0x250 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem lsm8_at_252 : fetchRel lincombShiftMod8Code 0x252 = some (.branch .bne (9 : Fin 32) x0 0xFFFFFFE4, 2) := by decide
theorem lsm8_at_254 : fetchRel lincombShiftMod8Code 0x254 = some (.store .sw sp (19 : Fin 32) 0x28, 2) := by decide
theorem lsm8_at_256 : fetchRel lincombShiftMod8Code 0x256 = some (.aluImm .add a0 sp 0x28, 2) := by decide
theorem lsm8_at_258 : fetchRel lincombShiftMod8Code 0x258 = some (.load .lw a0 sp 0x28, 2) := by decide
theorem lsm8_at_25a : fetchRel lincombShiftMod8Code 0x25A = some (.aluImm .sltu (9 : Fin 32) a0 0x1, 4) := by decide
theorem lsm8_at_25e : fetchRel lincombShiftMod8Code 0x25E = some (.alu .and (9 : Fin 32) (9 : Fin 32) a2, 2) := by decide
theorem lsm8_at_260 : fetchRel lincombShiftMod8Code 0x260 = some (.store .sb sp (9 : Fin 32) 0x28, 4) := by decide
theorem lsm8_at_264 : fetchRel lincombShiftMod8Code 0x264 = some (.aluImm .add a0 sp 0x28, 2) := by decide
theorem lsm8_at_266 : fetchRel lincombShiftMod8Code 0x266 = some (.load .lbu a0 sp 0x28, 4) := by decide
theorem lsm8_at_26a : fetchRel lincombShiftMod8Code 0x26A = some (.aluImm .add a0 a0 0xFFFFFFFF, 2) := by decide
theorem lsm8_at_26c : fetchRel lincombShiftMod8Code 0x26C = some (.alu .xor (8 : Fin 32) (22 : Fin 32) (20 : Fin 32), 4) := by decide
theorem lsm8_at_270 : fetchRel lincombShiftMod8Code 0x270 = some (.alu .and a2 a2 a0, 2) := by decide
theorem lsm8_at_272 : fetchRel lincombShiftMod8Code 0x272 = some (.alu .add a0 x0 (19 : Fin 32), 2) := by decide
theorem lsm8_at_274 : fetchRel lincombShiftMod8Code 0x274 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem lsm8_at_276 : fetchRel lincombShiftMod8Code 0x276 = some (.auipc ra 0xFFFF1000, 4) := by decide
theorem lsm8_at_27a : fetchRel lincombShiftMod8Code 0x27A = some (.jalr ra ra 0xFFFFFD78, 4) := by decide
theorem lsm8_at_27e : fetchRel lincombShiftMod8Code 0x27E = some (.aluImm .add a0 sp 0x28, 2) := by decide
theorem lsm8_at_280 : fetchRel lincombShiftMod8Code 0x280 = some (.aluImm .add a1 sp 0xA8, 2) := by decide
theorem lsm8_at_282 : fetchRel lincombShiftMod8Code 0x282 = some (.alu .add a2 x0 sp, 2) := by decide
theorem lsm8_at_284 : fetchRel lincombShiftMod8Code 0x284 = some (.alu .add a3 x0 (9 : Fin 32), 2) := by decide
theorem lsm8_at_286 : fetchRel lincombShiftMod8Code 0x286 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem lsm8_at_28a : fetchRel lincombShiftMod8Code 0x28A = some (.jalr ra ra 0x714, 4) := by decide
theorem lsm8_at_28e : fetchRel lincombShiftMod8Code 0x28E = some (.alu .add a0 x0 sp, 2) := by decide
theorem lsm8_at_290 : fetchRel lincombShiftMod8Code 0x290 = some (.aluImm .add a1 sp 0x28, 2) := by decide
theorem lsm8_at_292 : fetchRel lincombShiftMod8Code 0x292 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem lsm8_at_296 : fetchRel lincombShiftMod8Code 0x296 = some (.auipc ra 0x3000, 4) := by decide
theorem lsm8_at_29a : fetchRel lincombShiftMod8Code 0x29A = some (.jalr ra ra 0x286, 4) := by decide
theorem lsm8_at_29e : fetchRel lincombShiftMod8Code 0x29E = some (.alu .add a1 x0 sp, 2) := by decide
theorem lsm8_at_2a0 : fetchRel lincombShiftMod8Code 0x2A0 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem lsm8_at_2a4 : fetchRel lincombShiftMod8Code 0x2A4 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem lsm8_at_2a6 : fetchRel lincombShiftMod8Code 0x2A6 = some (.auipc ra 0x3000, 4) := by decide
theorem lsm8_at_2aa : fetchRel lincombShiftMod8Code 0x2AA = some (.jalr ra ra 0x276, 4) := by decide
theorem lsm8_at_2ae : fetchRel lincombShiftMod8Code 0x2AE = some (.store .sb (18 : Fin 32) (8 : Fin 32) 0x20, 4) := by decide
theorem lsm8_at_2b2 : fetchRel lincombShiftMod8Code 0x2B2 = some (.load .lw ra sp 0xFC, 2) := by decide
theorem lsm8_at_2b4 : fetchRel lincombShiftMod8Code 0x2B4 = some (.load .lw (8 : Fin 32) sp 0xF8, 2) := by decide
theorem lsm8_at_2b6 : fetchRel lincombShiftMod8Code 0x2B6 = some (.load .lw (9 : Fin 32) sp 0xF4, 2) := by decide
theorem lsm8_at_2b8 : fetchRel lincombShiftMod8Code 0x2B8 = some (.load .lw (18 : Fin 32) sp 0xF0, 2) := by decide
theorem lsm8_at_2ba : fetchRel lincombShiftMod8Code 0x2BA = some (.load .lw (19 : Fin 32) sp 0xEC, 2) := by decide
theorem lsm8_at_2bc : fetchRel lincombShiftMod8Code 0x2BC = some (.load .lw (20 : Fin 32) sp 0xE8, 2) := by decide
theorem lsm8_at_2be : fetchRel lincombShiftMod8Code 0x2BE = some (.load .lw (21 : Fin 32) sp 0xE4, 2) := by decide
theorem lsm8_at_2c0 : fetchRel lincombShiftMod8Code 0x2C0 = some (.load .lw (22 : Fin 32) sp 0xE0, 2) := by decide
theorem lsm8_at_2c2 : fetchRel lincombShiftMod8Code 0x2C2 = some (.load .lw (23 : Fin 32) sp 0xDC, 2) := by decide
theorem lsm8_at_2c4 : fetchRel lincombShiftMod8Code 0x2C4 = some (.load .lw (24 : Fin 32) sp 0xD8, 2) := by decide
theorem lsm8_at_2c6 : fetchRel lincombShiftMod8Code 0x2C6 = some (.load .lw (25 : Fin 32) sp 0xD4, 2) := by decide
theorem lsm8_at_2c8 : fetchRel lincombShiftMod8Code 0x2C8 = some (.aluImm .add sp sp 0x100, 2) := by decide
theorem lsm8_at_2ca : fetchRel lincombShiftMod8Code 0x2CA = some (.jalr x0 ra 0x0, 2) := by decide
theorem lsm8_at_2cc : fetchRel lincombShiftMod8Code 0x2CC = some (.auipc ra 0xFFFFC000, 4) := by decide
theorem lsm8_at_2d0 : fetchRel lincombShiftMod8Code 0x2D0 = some (.jalr ra ra 0xFFFFFC60, 4) := by decide
theorem lsm8_at_2d4 : fetchRel lincombShiftMod8Code 0x2D4 = some (.aluImm .add a0 x0 0x1B, 2) := by decide
theorem lsm8_at_2d6 : fetchRel lincombShiftMod8Code 0x2D6 = some (.auipc ra 0xFFFFC000, 4) := by decide
theorem lsm8_at_2da : fetchRel lincombShiftMod8Code 0x2DA = some (.jalr ra ra 0xFFFFFCB0, 4) := by decide
end

/-- What `lincomb_int_reduce_shift_mod` stores, from the linear combination's
sign `σ` and 320-bit magnitude `A`, `mi`'s value `MI`, the shift `s`, and the
modulus `M`: the sign byte, and the 8-limb magnitude. -/
def lrsm8 (σ A MI s M : Nat) : Nat × Nat :=
  let XA := M * lrsmMf A MI s
  let Y := if A < XA then XA - A else A - XA
  let Z := Y / 2 ^ s
  let lo := Z % 2 ^ 256
  (if A < XA then 1 - σ else σ,
    if Z / 2 ^ 256 % 2 ^ 32 = 0 ∧ lo < M then lo else (lo + 2 ^ 256 - M) % 2 ^ 256)

/-- `lincomb_int`'s address, from the function's. -/
abbrev lm8Lc (P : Word) : Word := P + 0xFFFFFA70

/-- `shr_in_place_wide`'s address, from the function's. -/
abbrev lm8Shr (P : Word) : Word := P + 0xFFFFFBF4

/-- Where the function runs: its code, its callees' code at their offsets,
the 0x280 bytes of stack at `G` that it and its callees use (its frame is
the top 0x100), the result `res`, the operands, the modulus at `mp`, and
`mi` at `mip`, each apart from what it must not touch. -/
structure LMEnv8 (M : Word → BitVec 8) (P G res ap bp cp dp mp mip : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P lincombShiftMod8Code
  lc : CodeIn M (lm8Lc P) lincomb8Code
  abs : CodeIn M (lm8Lc P + 0xFFFFC6EA) absSign2Code
  wide : CodeIn M (lm8Lc P + 0x398) wideMul8x2Code
  neg : CodeIn M (lm8Lc P + 0x480) condNeg8Code
  mset : CodeIn M (lm8Lc P + 0x3A44) memsetCode
  stub : CodeIn M (lm8Lc P + 0x3AAC) memcpyStubCode
  body : CodeIn M (lm8Lc P + 0x3AB4) memcpyBodyCode
  bsub : CodeIn M (lcBsub8 (lm8Lc P)) borrowingSubCode
  sel2 : CodeIn M (lm8Lc P + 0x272E) uintSelect2Code
  sel12 : CodeIn M (lm8Lc P + 0xFFFFFF2A) uintSelect8Code
  zero : CodeIn M (BitVec.ofNat 32 u2ZeroAddress) u2ZeroData
  one : CodeIn M (BitVec.ofNat 32 u2OneAddress) u2OneData
  shr : CodeIn M (lm8Shr P) shr8Code
  lm : CodeIn M (lm8Shr P + 0x1EE) leadMut8Code
  tr : CodeIn M (lm8Shr P + 0x1FE) trailing8Code
  tur : CodeIn M (P + 0xFFFFBFB6) toUintResize2Code
  max : CodeIn M (BitVec.ofNat 32 u2MaxAddress) u2MaxData
  hG : G.toNat % 4 = 0
  hGt : G.toNat + 0x280 ≤ 2 ^ 32
  hres : res.toNat % 4 = 0
  hap : ap.toNat % 4 = 0
  hbp : bp.toNat % 4 = 0
  hcp : cp.toNat % 4 = 0
  hdp : dp.toNat % 4 = 0
  hmp : mp.toNat % 4 = 0
  hmip : mip.toNat % 4 = 0
  hwr : res.toNat + 33 < 2 ^ 32
  hwa : ap.toNat + 33 < 2 ^ 32
  hwb : bp.toNat + 33 < 2 ^ 32
  sC : Sep G 0x280 P lincombShiftMod8Code.length
  sL : Sep G 0x280 (lm8Lc P) lincomb8Code.length
  sA : Sep G 0x280 (lm8Lc P + 0xFFFFC6EA) absSign2Code.length
  sW : Sep G 0x280 (lm8Lc P + 0x398) wideMul8x2Code.length
  sN : Sep G 0x280 (lm8Lc P + 0x480) condNeg8Code.length
  sM : Sep G 0x280 (lm8Lc P + 0x3A44) memsetCode.length
  sU : Sep G 0x280 (lm8Lc P + 0x3AAC) memcpyStubCode.length
  sB : Sep G 0x280 (lm8Lc P + 0x3AB4) memcpyBodyCode.length
  sBs : Sep G 0x280 (lcBsub8 (lm8Lc P)) borrowingSubCode.length
  s2 : Sep G 0x280 (lm8Lc P + 0x272E) uintSelect2Code.length
  s12 : Sep G 0x280 (lm8Lc P + 0xFFFFFF2A) uintSelect8Code.length
  sZ : Sep G 0x280 (BitVec.ofNat 32 u2ZeroAddress) 8
  sO : Sep G 0x280 (BitVec.ofNat 32 u2OneAddress) 8
  sS : Sep G 0x280 (lm8Shr P) shr8Code.length
  sLm : Sep G 0x280 (lm8Shr P + 0x1EE) leadMut8Code.length
  sTr : Sep G 0x280 (lm8Shr P + 0x1FE) trailing8Code.length
  sT : Sep G 0x280 (P + 0xFFFFBFB6) toUintResize2Code.length
  sX : Sep G 0x280 (BitVec.ofNat 32 u2MaxAddress) 8
  rG : Sep res 33 G 0x280
  aG : Sep ap 33 G 0x280
  bG : Sep bp 33 G 0x280
  cG : Sep cp 8 G 0x280
  dG : Sep dp 8 G 0x280
  mG : Sep mp 32 G 0x280
  iG : Sep mip 8 G 0x280
  rC : Sep res 33 P lincombShiftMod8Code.length
  rB : Sep res 33 (lm8Lc P + 0x3AB4) memcpyBodyCode.length

/-- The prologue, from 0 to the call at 0x26: the frame, the saved
registers, and the arguments kept in saved registers. -/
def lm8Pro : List BInstr :=
  [.aluImm .add sp sp 0xFFFFFF00, .sw sp ra 0xFC, .sw sp (8 : Fin 32) 0xF8, .sw sp (9 : Fin 32) 0xF4,
   .sw sp (18 : Fin 32) 0xF0, .sw sp (19 : Fin 32) 0xEC, .sw sp (20 : Fin 32) 0xE8, .sw sp (21 : Fin 32) 0xE4,
   .sw sp (22 : Fin 32) 0xE0, .sw sp (23 : Fin 32) 0xDC, .sw sp (24 : Fin 32) 0xD8, .sw sp (25 : Fin 32) 0xD4,
   .alu .add (21 : Fin 32) x0 (17 : Fin 32), .alu .add (23 : Fin 32) x0 a6, .alu .add (19 : Fin 32) x0 a5,
   .alu .add (18 : Fin 32) x0 a0, .aluImm .add a0 sp 0x28, .aluImm .add (20 : Fin 32) sp 0x28]

/-- The registers the function saves, at offsets from its `sp`. -/
abbrev lm8Ps : List (Fin 32 × Word) :=
  [(ra, 0xFC), ((8 : Fin 32), 0xF8), ((9 : Fin 32), 0xF4), ((18 : Fin 32), 0xF0), ((19 : Fin 32), 0xEC),
   ((20 : Fin 32), 0xE8), ((21 : Fin 32), 0xE4), ((22 : Fin 32), 0xE0), ((23 : Fin 32), 0xDC),
   ((24 : Fin 32), 0xD8), ((25 : Fin 32), 0xD4)]

/-- The epilogue, from 0x2B2 to the frame's release at 0x2AA. -/
abbrev lm8Epi : List BInstr := restoreBlock lm8Ps

section
set_option maxRecDepth 20000
theorem lm8Pro_end : blockEnd lincombShiftMod8Code 0 lm8Pro = some 0x26 := by decide
theorem lm8Epi_end : blockEnd lincombShiftMod8Code 0x2B2 lm8Epi = some 0x2C8 := by decide
end

theorem lm8Ps_range : ∀ p ∈ lm8Ps, p.2.toNat % 4 = 0 ∧ 0xD4 ≤ p.2.toNat ∧ p.2.toNat + 4 ≤ 0x100 := by decide

theorem lm8_zadd (x : Word) : (0 : Word) + x = x := BitVec.zero_add x

set_option maxRecDepth 200000 in
theorem lm8Pro_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lm8Pro (M, f)).1 = saveMem M (f sp + 0xFFFFFF00) f lm8Ps ∧
    (runBlock lm8Pro (M, f)).2 sp = f sp + 0xFFFFFF00 ∧
    (runBlock lm8Pro (M, f)).2 (21 : Fin 32) = f (17 : Fin 32) ∧
    (runBlock lm8Pro (M, f)).2 (23 : Fin 32) = f a6 ∧
    (runBlock lm8Pro (M, f)).2 (19 : Fin 32) = f a5 ∧
    (runBlock lm8Pro (M, f)).2 (18 : Fin 32) = f a0 ∧
    (runBlock lm8Pro (M, f)).2 a0 = f sp + 0xFFFFFF00 + 0x28 ∧
    (runBlock lm8Pro (M, f)).2 (20 : Fin 32) = f sp + 0xFFFFFF00 + 0x28 ∧
    ∀ q : Fin 32, q.val ∉ [2, 10, 18, 19, 20, 21, 23] → (runBlock lm8Pro (M, f)).2 q = f q := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => runBlock_keepL (by decide) hz hq⟩ <;>
    simp only [runBlock, BInstr.run, lm8Pro] <;>
    simp +decide only [upd, ↓reduceIte, saveMem, lm8Ps, ev_add, BitVec.add_assoc, hz, add_lit_zero, lm8_zadd] <;>
    first | rfl | exact BitVec.zero_add _ | skip

set_option maxRecDepth 20000 in
theorem lm8Epi_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (∀ r o, (r, o) ∈ lm8Ps → (runBlock lm8Epi (M, f)).2 r = memLoad32 M (f sp + o)) ∧
    (runBlock lm8Epi (M, f)).1 = M ∧
    ∀ q : Fin 32, q.val ∉ [1, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25] → (runBlock lm8Epi (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, lm8Epi, restoreBlock, lm8Ps, List.map]
  refine ⟨fun r o h => ?_, trivial, fun q hq => ?_⟩
  · simp only [lm8Ps, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp +decide only [upd, ↓reduceIte, ev_add]
  · have nq : ∀ w : Fin 32, w.val ∈ [1, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25] → q ≠ w := fun w hw e => hq (e ▸ hw)
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [hz]
    · simp only [upd, h0, nq ra (by decide), nq 8 (by decide), nq 9 (by decide), nq 18 (by decide),
        nq 19 (by decide), nq 20 (by decide), nq 21 (by decide), nq 22 (by decide), nq 23 (by decide),
        nq 24 (by decide), nq 25 (by decide), ite_false]

/-! ## The 64-bit product `x · mi`, from 0x56 to 0xAC -/

/-- From 0x6C to the branch at 0x64: zero the product, and the loop
counters. -/
def lm8M0 : List BInstr :=
  [.aluImm .add (6 : Fin 32) x0 0, .sw sp x0 0xC8, .sw sp x0 0xCC, .aluImm .add (17 : Fin 32) sp 0xC8,
   .aluImm .add a6 x0 2, .aluImm .add (5 : Fin 32) x0 2]

/-- From 0x82 to the branch at 0x78: start row `t1`. -/
def lm8M1 : List BInstr :=
  [.aluImm .add (9 : Fin 32) x0 0, .aluImm .sll a1 (6 : Fin 32) 2, .alu .add a1 a1 (20 : Fin 32), .lw a4 a1 0,
   .alu .add a5 x0 (5 : Fin 32), .alu .add a1 x0 (17 : Fin 32), .alu .add (8 : Fin 32) x0 (21 : Fin 32)]

/-- From 0x96 to the branch at 0xA0: one multiply-accumulate step. -/
def lm8M2 : List BInstr :=
  [.lw a2 (8 : Fin 32) 0, .alu .mul a3 a2 a4, .lw a0 a1 0, .alu .mulhu a2 a2 a4, .aluImm .add (8 : Fin 32) (8 : Fin 32) 4,
   .alu .add (9 : Fin 32) (9 : Fin 32) a0, .alu .sltu a0 (9 : Fin 32) a0, .alu .add a3 a3 (9 : Fin 32),
   .alu .add a0 a0 a2, .alu .sltu (9 : Fin 32) a3 (9 : Fin 32), .sw a1 a3 0, .alu .add (9 : Fin 32) (9 : Fin 32) a0,
   .aluImm .add a1 a1 4, .aluImm .add a5 a5 0xFFFFFFFF]

/-- From 0xBC to the branch at 0xA8: the next row. -/
def lm8M3 : List BInstr :=
  [.aluImm .add (6 : Fin 32) (6 : Fin 32) 1, .aluImm .add (17 : Fin 32) (17 : Fin 32) 4,
   .aluImm .add (5 : Fin 32) (5 : Fin 32) 0xFFFFFFFF]

section
set_option maxRecDepth 20000
theorem lm8M0_end : blockEnd lincombShiftMod8Code 0x56 lm8M0 = some 0x64 := by decide
theorem lm8M1_end : blockEnd lincombShiftMod8Code 0x68 lm8M1 = some 0x78 := by decide
theorem lm8M2_end : blockEnd lincombShiftMod8Code 0x7C lm8M2 = some 0xA0 := by decide
theorem lm8M3_end : blockEnd lincombShiftMod8Code 0xA2 lm8M3 = some 0xA8 := by decide
end

set_option maxRecDepth 20000 in
theorem lm8M2_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lm8M2 (M, f)).1 = memStore32 M (f a1 + 0)
      (macLo (memLoad32 M (f 8 + 0)) (f a4) (memLoad32 M (f a1 + 0)) (f 9)) ∧
    (runBlock lm8M2 (M, f)).2 (9 : Fin 32) =
      macHi (memLoad32 M (f 8 + 0)) (f a4) (memLoad32 M (f a1 + 0)) (f 9) ∧
    (runBlock lm8M2 (M, f)).2 (8 : Fin 32) = f 8 + 4 ∧ (runBlock lm8M2 (M, f)).2 a1 = f a1 + 4 ∧
    (runBlock lm8M2 (M, f)).2 a5 = f a5 + 0xFFFFFFFF ∧
    ∀ q : Fin 32, q.val ∉ [8, 9, 10, 11, 12, 13, 15] → (runBlock lm8M2 (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, lm8M2]
  refine ⟨?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · simp +decide only [upd, ↓reduceIte, macLo]; rfl
  · simp +decide only [upd, ↓reduceIte, macHi]; rfl
  any_goals (simp +decide only [upd, ↓reduceIte]; first | rfl | skip)
  have nq : ∀ w : Fin 32, w.val ∈ [8, 9, 10, 11, 12, 13, 15] → q ≠ w := fun w hw e => hq (e ▸ hw)
  by_cases h0 : q.val = 0
  · have : q = 0 := Fin.ext h0
    subst this; simp [hz]
  · simp only [h0, nq 8 (by decide), nq 9 (by decide), nq a0 (by decide), nq a1 (by decide),
      nq a2 (by decide), nq a3 (by decide), nq a5 (by decide), ite_false]

set_option maxRecDepth 20000 in
theorem lm8M0_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lm8M0 (M, f)).1 = memStore32 (memStore32 M (f sp + 0xC8) 0) (f sp + 0xCC) 0 ∧
    (runBlock lm8M0 (M, f)).2 (6 : Fin 32) = 0 ∧ (runBlock lm8M0 (M, f)).2 (17 : Fin 32) = f sp + 0xC8 ∧
    (runBlock lm8M0 (M, f)).2 a6 = 2 ∧ (runBlock lm8M0 (M, f)).2 (5 : Fin 32) = 2 ∧
    ∀ q : Fin 32, q.val ∉ [5, 6, 16, 17] → (runBlock lm8M0 (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, lm8M0]
  refine ⟨?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · simp +decide only [upd, ↓reduceIte, hz]
  any_goals (simp +decide only [upd, ↓reduceIte, hz, ev_add]; first | rfl | skip)
  have nq : ∀ w : Fin 32, w.val ∈ [5, 6, 16, 17] → q ≠ w := fun w hw e => hq (e ▸ hw)
  by_cases h0 : q.val = 0
  · have : q = 0 := Fin.ext h0
    subst this; simp [hz]
  · simp only [upd, h0, nq 5 (by decide), nq 6 (by decide), nq a6 (by decide), nq 17 (by decide), ite_false]

theorem lm8M0_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h0 : (f sp + 0xC8).toNat % 4 = 0) (h4 : (f sp + 0xCC).toNat % 4 = 0)
    (s0 : Sep (f sp + 0xC8) 4 base len) (s4 : Sep (f sp + 0xCC) 4 base len) :
    BlockOk base len lm8M0 (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, lm8M0, upd, ↓reduceIte, and_true, true_and]
  exact ⟨⟨h0, s0⟩, h4, s4⟩

set_option maxRecDepth 20000 in
theorem lm8M1_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lm8M1 (M, f)).1 = M ∧
    (runBlock lm8M1 (M, f)).2 (9 : Fin 32) = 0 ∧
    (runBlock lm8M1 (M, f)).2 a4 = memLoad32 M (aluEval .sll (f 6) 2 + f 20 + 0) ∧
    (runBlock lm8M1 (M, f)).2 a5 = f 5 ∧ (runBlock lm8M1 (M, f)).2 a1 = f 17 ∧
    (runBlock lm8M1 (M, f)).2 (8 : Fin 32) = f 21 ∧
    ∀ q : Fin 32, q.val ∉ [8, 9, 11, 14, 15] → (runBlock lm8M1 (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, lm8M1]
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  any_goals (simp +decide only [upd, ↓reduceIte, hz, ev_add]; first | rfl | exact BitVec.zero_add _ | skip)
  have nq : ∀ w : Fin 32, w.val ∈ [8, 9, 11, 14, 15] → q ≠ w := fun w hw e => hq (e ▸ hw)
  by_cases h0 : q.val = 0
  · have : q = 0 := Fin.ext h0
    subst this; simp [hz]
  · simp only [upd, h0, nq 8 (by decide), nq 9 (by decide), nq a1 (by decide), nq a4 (by decide),
      nq a5 (by decide), ite_false]

theorem lm8M1_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h : (aluEval .sll (f 6) 2 + f 20 + 0).toNat % 4 = 0) : BlockOk base len lm8M1 (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, lm8M1, upd, ↓reduceIte, and_true, true_and]
  exact h

theorem lm8M2_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h8 : (f 8 + 0).toNat % 4 = 0) (h1 : (f a1 + 0).toNat % 4 = 0) (s1 : Sep (f a1 + 0) 4 base len) :
    BlockOk base len lm8M2 (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, lm8M2, upd, ↓reduceIte, and_true, true_and]
  exact ⟨h8, h1, h1, s1⟩

set_option maxRecDepth 20000 in
theorem lm8M3_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lm8M3 (M, f)).1 = M ∧
    (runBlock lm8M3 (M, f)).2 (6 : Fin 32) = f 6 + 1 ∧ (runBlock lm8M3 (M, f)).2 (17 : Fin 32) = f 17 + 4 ∧
    (runBlock lm8M3 (M, f)).2 (5 : Fin 32) = f 5 + 0xFFFFFFFF ∧
    ∀ q : Fin 32, q.val ∉ [5, 6, 17] → (runBlock lm8M3 (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, lm8M3]
  refine ⟨trivial, ?_, ?_, ?_, fun q hq => ?_⟩
  any_goals (simp +decide only [upd, ↓reduceIte, ev_add]; first | rfl | skip)
  have nq : ∀ w : Fin 32, w.val ∈ [5, 6, 17] → q ≠ w := fun w hw e => hq (e ▸ hw)
  by_cases h0 : q.val = 0
  · have : q = 0 := Fin.ext h0
    subst this; simp [hz]
  · simp only [upd, h0, nq 5 (by decide), nq 6 (by decide), nq 17 (by decide), ite_false]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **The 64-bit product**, from 0x56 to 0xAC: the two words at `F + 0xC8`
get `x · mi` modulo 2^64, for `x` the two words at `F + 0x28` and `mi` the
two at `mip`. -/
theorem lm8_mul {M : Word → BitVec 8} {P F mip : Word} {n : Machine} (s : St M P n 0x56 (reg n))
    (hc : CodeIn M P lincombShiftMod8Code) (rsp : reg n sp = F) (r20 : reg n 20 = F + 0x28)
    (r21 : reg n 21 = mip) (hF : F.toNat % 4 = 0) (hmip : mip.toNat % 4 = 0)
    (sC : Sep (F + 0xC8) 8 P lincombShiftMod8Code.length) (sX : Sep (F + 0xC8) 8 (F + 0x28) 8)
    (sI : Sep (F + 0xC8) 8 mip 8) :
    ∃ n' M', Steps n n' ∧ St M' P n' 0xAC (reg n') ∧ CodeIn M' P lincombShiftMod8Code ∧
      (∀ x, Sep (F + 0xC8) 8 x 1 → M' x = M x) ∧
      (memLoad32 M' (F + 0xC8)).toNat + 2 ^ 32 * (memLoad32 M' (F + 0xCC)).toNat =
        ((memLoad32 M (F + 0x28)).toNat + 2 ^ 32 * (memLoad32 M (F + 0x2C)).toNat) *
          ((memLoad32 M mip).toNat + 2 ^ 32 * (memLoad32 M (mip + 4)).toNat) % 2 ^ 64 ∧
      ∀ q : Fin 32, q.val ∉ [5, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17] → reg n' q = reg n q := by
  have hz := s.zero
  have s0 : Sep (F + 0xC8) 4 P lincombShiftMod8Code.length := by
    have := sC.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
  have s4 : Sep (F + 0xCC) 4 P lincombShiftMod8Code.length := by
    have := sC.sub (c := 4) (l := 4) (by decide); rw [BitVec.add_assoc] at this; exact this
  have a0' : (F + 0xC8).toNat % 4 = 0 := aligned_add hF (by decide)
  have a4' : (F + 0xCC).toNat % 4 = 0 := aligned_add hF (by decide)
  -- zero the product
  obtain ⟨n1, c1, u1⟩ := St.block lm8M0 s hc lm8M0_end
    (lm8M0_ok (by rw [rsp]; exact a0') (by rw [rsp]; exact a4') (by rw [rsp]; exact s0) (by rw [rsp]; exact s4))
  obtain ⟨m0e, m0t1, m0a7, m0a6, m0t0, m0k⟩ := lm8M0_run (M := M) (f := reg n) hz
  rw [m0e, rsp] at u1
  obtain ⟨Mz, hMz⟩ : ∃ Mz, memStore32 (memStore32 M (F + 0xC8) 0) (F + 0xCC) 0 = Mz := ⟨_, rfl⟩
  rw [hMz] at u1
  have hcz : CodeIn Mz P lincombShiftMod8Code := by rw [← hMz]; exact (hc.store32 s0).store32 s4
  have frz : ∀ x, Sep (F + 0xC8) 8 x 1 → Mz x = M x := fun x hx => by
    have h4 : Sep (F + 0xCC) 4 x 1 := by
      have := hx.sub (c := 4) (l := 4) (by decide); rw [BitVec.add_assoc] at this; exact this
    have h0 : Sep (F + 0xC8) 4 x 1 := by
      have := hx.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    rw [← hMz, memStore32_get_sep h4, memStore32_get_sep h0]
  have ldz : ∀ {a : Word}, Sep (F + 0xC8) 8 a 4 → memLoad32 Mz a = memLoad32 M a := fun h =>
    memLoad32_congr fun j hj => frz _ (h.subR (c := j) (l := 1) (by omega))
  have g1 : ∀ q, reg n1 q = (runBlock lm8M0 (M, reg n)).2 q := u1.regs
  have k1 : ∀ q : Fin 32, q.val ∉ [5, 6, 16, 17] → reg n1 q = reg n q := fun q hq => by rw [g1, m0k q hq]
  obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hcz 0x68 lsm8_at_64 (by decide) (by rw [g1, m0a6, u1.self.zero]; decide)
  have k2 : ∀ q, reg n2 q = reg n1 q := u2.regs
  -- row 0
  have sll0 : aluEval .sll (0 : Word) 2 = 0 := by decide
  have sll1 : aluEval .sll (1 : Word) 2 = 4 := by decide
  have e38 : (0 : Word) + (F + 0x28) + 0 = F + 0x28 := by rw [add_lit_zero]; exact BitVec.zero_add _
  have e3c : (4 : Word) + (F + 0x28) + 0 = F + 0x2C := by
    rw [add_lit_zero, BitVec.add_comm, BitVec.add_assoc]; rfl
  have r2t1 : reg n2 6 = 0 := by rw [k2, g1, m0t1]
  have r2s4 : reg n2 20 = F + 0x28 := by rw [k2, k1 20 (by decide), r20]
  have r2s5 : reg n2 21 = mip := by rw [k2, k1 21 (by decide), r21]
  have r2a7 : reg n2 17 = F + 0xC8 := by rw [k2, g1, m0a7, rsp]
  have r2t0 : reg n2 5 = 2 := by rw [k2, g1, m0t0]
  have r2a6 : reg n2 16 = 2 := by rw [k2, g1, m0a6]
  obtain ⟨n3, c3, u3⟩ := St.block lm8M1 u2.self hcz lm8M1_end
    (lm8M1_ok (by rw [r2t1, r2s4, sll0, e38]; exact aligned_add hF (by decide)))
  obtain ⟨m1e, m1s1, m1a4, m1a5, m1a1, m1s0, m1k⟩ := lm8M1_run (M := Mz) (f := reg n2) u2.self.zero
  rw [m1e] at u3
  have g3 : ∀ q, reg n3 q = (runBlock lm8M1 (Mz, reg n2)).2 q := u3.regs
  have x0e : reg n3 a4 = memLoad32 M (F + 0x28) := by
    rw [g3, m1a4, r2t1, r2s4, sll0, e38]
    exact ldz (by have := sX.subR (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this)
  obtain ⟨n4, d4, u4⟩ := u3.self.notTaken hcz 0x7C lsm8_at_78 (by decide)
    (by rw [g3, m1k 5 (by decide), r2t0, u3.self.zero]; decide)
  have k4 : ∀ q, reg n4 q = reg n3 q := u4.regs
  have r4s0 : reg n4 8 = mip := by rw [k4, g3, m1s0, r2s5]
  have r4a1 : reg n4 a1 = F + 0xC8 := by rw [k4, g3, m1a1, r2a7]
  have r4s1 : reg n4 9 = 0 := by rw [k4, g3, m1s1]
  have hm0 : memLoad32 Mz mip = memLoad32 M mip :=
    ldz (by have := sI.subR (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this)
  have hm1 : memLoad32 Mz (mip + 4) = memLoad32 M (mip + 4) := ldz (sI.subR (c := 4) (l := 4) (by decide))
  have z0 : memLoad32 Mz (F + 0xC8) = 0 := by
    rw [← hMz, memLoad32_store32_sep (by
      have := sep_offsets F (c := 0xCC) (n := 4) (d := 0xC8) (k := 4) (.inr (by decide)) (by decide) (by decide)
      exact this), memLoad32_store32_same]
  have z4 : memLoad32 Mz (F + 0xCC) = 0 := by rw [← hMz, memLoad32_store32_same]
  -- the first multiply-accumulate step
  obtain ⟨n5, c5, u5⟩ := St.block lm8M2 u4.self hcz lm8M2_end
    (lm8M2_ok (by rw [r4s0, add_lit_zero]; exact hmip) (by rw [r4a1, add_lit_zero]; exact a0')
      (by rw [r4a1, add_lit_zero]; exact s0))
  obtain ⟨m2e, m2s1, m2s0, m2a1, m2a5, m2k⟩ := lm8M2_run (M := Mz) (f := reg n4) u4.self.zero
  have r4a4 : reg n4 a4 = memLoad32 M (F + 0x28) := by rw [k4, x0e]
  rw [m2e, r4s0, r4a1, add_lit_zero, add_lit_zero, hm0, z0, r4a4, r4s1] at u5
  obtain ⟨x0, hx0⟩ : ∃ x0, memLoad32 M (F + 0x28) = x0 := ⟨_, rfl⟩
  obtain ⟨m0, hm0'⟩ : ∃ m0, memLoad32 M mip = m0 := ⟨_, rfl⟩
  obtain ⟨m1, hm1'⟩ : ∃ m1, memLoad32 M (mip + 4) = m1 := ⟨_, rfl⟩
  rw [hx0, hm0'] at u5
  have g5 : ∀ q, reg n5 q = (runBlock lm8M2 (Mz, reg n4)).2 q := u5.regs
  have e11c : F + 0xC8 + 4 = F + 0xCC := by rw [BitVec.add_assoc]; rfl
  have hcA : CodeIn (memStore32 Mz (F + 0xC8) (macLo m0 x0 0 0)) P lincombShiftMod8Code := hcz.store32 s0
  obtain ⟨n6, d6, u6⟩ := u5.self.taken hcA 0x7C lsm8_at_a0 (by decide)
    (by rw [g5, m2a5, k4, g3, m1a5, r2t0, u5.self.zero]; decide)
  have k6 : ∀ q, reg n6 q = reg n5 q := u6.regs
  have r6s0 : reg n6 8 = mip + 4 := by rw [k6, g5, m2s0, r4s0]
  have r6a1 : reg n6 a1 = F + 0xCC := by rw [k6, g5, m2a1, r4a1, e11c]
  have r6s1 : reg n6 9 = macHi m0 x0 0 0 := by
    rw [k6, g5, m2s1, r4s0, r4a1, add_lit_zero, add_lit_zero, hm0, z0, r4a4, r4s1, hx0, hm0']
  have r6a4 : reg n6 a4 = x0 := by rw [k6, g5, m2k a4 (by decide), r4a4, hx0]
  have r6a5 : reg n6 a5 = 1 := by rw [k6, g5, m2a5, k4, g3, m1a5, r2t0]; rfl
  -- the second step of row 0
  obtain ⟨n7, c7, u7⟩ := St.block lm8M2 u6.self hcA lm8M2_end
    (lm8M2_ok (by rw [r6s0, add_lit_zero]; exact aligned_add hmip (by decide)) (by rw [r6a1, add_lit_zero]; exact a4')
      (by rw [r6a1, add_lit_zero]; exact s4))
  obtain ⟨m2e', m2s1', m2s0', m2a1', m2a5', m2k'⟩ := lm8M2_run (M := memStore32 Mz (F + 0xC8) (macLo m0 x0 0 0))
    (f := reg n6) u6.self.zero
  have sIm : Sep (F + 0xC8) 4 (mip + 4) 4 := by
    have := (sI.sub (c := 0) (l := 4) (by decide)).subR (c := 4) (l := 4) (by decide)
    rwa [add_ofNat_zero] at this
  have s11c : Sep (F + 0xC8) 4 (F + 0xCC) 4 := by
    have := sep_offsets F (c := 0xC8) (n := 4) (d := 0xCC) (k := 4) (.inl (by decide)) (by decide) (by decide)
    exact this
  have l1 : memLoad32 (memStore32 Mz (F + 0xC8) (macLo m0 x0 0 0)) (mip + 4) = m1 := by
    rw [memLoad32_store32_sep sIm, hm1, hm1']
  have l2 : memLoad32 (memStore32 Mz (F + 0xC8) (macLo m0 x0 0 0)) (F + 0xCC) = 0 := by
    rw [memLoad32_store32_sep s11c, z4]
  rw [m2e', r6s0, r6a1, add_lit_zero, add_lit_zero, l1, l2, r6a4, r6s1] at u7
  obtain ⟨MB, hMB⟩ : ∃ MB, memStore32 (memStore32 Mz (F + 0xC8) (macLo m0 x0 0 0)) (F + 0xCC)
      (macLo m1 x0 0 (macHi m0 x0 0 0)) = MB := ⟨_, rfl⟩
  rw [hMB] at u7
  have hcB : CodeIn MB P lincombShiftMod8Code := by rw [← hMB]; exact hcA.store32 s4
  have g7 : ∀ q, reg n7 q = (runBlock lm8M2 (memStore32 Mz (F + 0xC8) (macLo m0 x0 0 0), reg n6)).2 q := u7.regs
  obtain ⟨n8, d8, u8⟩ := u7.self.notTaken hcB 0xA2 lsm8_at_a0 (by decide)
    (by rw [g7, m2a5', r6a5, u7.self.zero]; decide)
  -- the next row
  obtain ⟨n9, c9, u9⟩ := St.block lm8M3 u8.self hcB lm8M3_end (by simp [BlockOk, BInstr.ok, lm8M3])
  obtain ⟨m3e, m3t1, m3a7, m3t0, m3k⟩ := lm8M3_run (M := MB) (f := reg n8) u8.self.zero
  rw [m3e] at u9
  have g9 : ∀ q, reg n9 q = (runBlock lm8M3 (MB, reg n8)).2 q := u9.regs
  have k8 : ∀ q, reg n8 q = reg n7 q := u8.regs
  -- registers the inner loop leaves alone
  have kin : ∀ q : Fin 32, q.val ∉ [8, 9, 10, 11, 12, 13, 15] → reg n8 q = reg n4 q := fun q hq => by
    rw [k8, g7, m2k' q hq, k6, g5, m2k q hq]
  have r9t1 : reg n9 6 = 1 := by
    rw [g9, m3t1, kin 6 (by decide), k4, g3, m1k 6 (by decide), r2t1]; rfl
  have r9a6 : reg n9 16 = 2 := by
    rw [g9, m3k 16 (by decide), kin 16 (by decide), k4, g3, m1k 16 (by decide), r2a6]
  obtain ⟨n10, d10, u10⟩ := u9.self.taken hcB 0x68 lsm8_at_a8 (by decide)
    (by rw [r9t1, r9a6]; decide)
  have k10 : ∀ q, reg n10 q = reg n9 q := u10.regs
  have r10t1 : reg n10 6 = 1 := by rw [k10, r9t1]
  have r10s4 : reg n10 20 = F + 0x28 := by
    rw [k10, g9, m3k 20 (by decide), kin 20 (by decide), k4, g3, m1k 20 (by decide), r2s4]
  have r10s5 : reg n10 21 = mip := by
    rw [k10, g9, m3k 21 (by decide), kin 21 (by decide), k4, g3, m1k 21 (by decide), r2s5]
  have r10a7 : reg n10 17 = F + 0xCC := by
    rw [k10, g9, m3a7, kin 17 (by decide), k4, g3, m1k 17 (by decide), r2a7, e11c]
  have r10t0 : reg n10 5 = 1 := by
    rw [k10, g9, m3t0, kin 5 (by decide), k4, g3, m1k 5 (by decide), r2t0]; rfl
  -- row 1
  obtain ⟨n11, c11, u11⟩ := St.block lm8M1 u10.self hcB lm8M1_end
    (lm8M1_ok (by rw [r10t1, r10s4, sll1, e3c]; exact aligned_add hF (by decide)))
  obtain ⟨m1e', m1s1', m1a4', m1a5', m1a1', m1s0', m1k'⟩ := lm8M1_run (M := MB) (f := reg n10) u10.self.zero
  rw [m1e'] at u11
  have g11 : ∀ q, reg n11 q = (runBlock lm8M1 (MB, reg n10)).2 q := u11.regs
  obtain ⟨x1, hx1⟩ : ∃ x1, memLoad32 M (F + 0x2C) = x1 := ⟨_, rfl⟩
  have sX4 : Sep (F + 0xC8) 8 (F + 0x2C) 4 := by
    have := sX.subR (c := 4) (l := 4) (by decide); rw [BitVec.add_assoc] at this; exact this
  have mbX : ∀ {a : Word}, Sep (F + 0xC8) 8 a 4 → memLoad32 MB a = memLoad32 M a := fun {a} h => by
    have h4 : Sep (F + 0xCC) 4 a 4 := by
      have := h.sub (c := 4) (l := 4) (by decide); rw [BitVec.add_assoc] at this; exact this
    have h0 : Sep (F + 0xC8) 4 a 4 := by
      have := h.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    rw [← hMB, memLoad32_store32_sep h4, memLoad32_store32_sep h0]
    exact ldz h
  have r11a4 : reg n11 a4 = x1 := by rw [g11, m1a4', r10t1, r10s4, sll1, e3c, mbX sX4, hx1]
  obtain ⟨n12, d12, u12⟩ := u11.self.notTaken hcB 0x7C lsm8_at_78 (by decide)
    (by rw [g11, m1k' 5 (by decide), r10t0, u11.self.zero]; decide)
  have k12 : ∀ q, reg n12 q = reg n11 q := u12.regs
  have r12s0 : reg n12 8 = mip := by rw [k12, g11, m1s0', r10s5]
  have r12a1 : reg n12 a1 = F + 0xCC := by rw [k12, g11, m1a1', r10a7]
  have r12s1 : reg n12 9 = 0 := by rw [k12, g11, m1s1']
  have r12a4 : reg n12 a4 = x1 := by rw [k12, r11a4]
  have r12a5 : reg n12 a5 = 1 := by rw [k12, g11, m1a5', r10t0]
  obtain ⟨n13, c13, u13⟩ := St.block lm8M2 u12.self hcB lm8M2_end
    (lm8M2_ok (by rw [r12s0, add_lit_zero]; exact hmip) (by rw [r12a1, add_lit_zero]; exact a4')
      (by rw [r12a1, add_lit_zero]; exact s4))
  obtain ⟨m2e'', m2s1'', m2s0'', m2a1'', m2a5'', m2k''⟩ := lm8M2_run (M := MB) (f := reg n12) u12.self.zero
  have l3 : memLoad32 MB mip = m0 := by
    rw [mbX (by have := sI.subR (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this), hm0']
  have l4 : memLoad32 MB (F + 0xCC) = macLo m1 x0 0 (macHi m0 x0 0 0) := by
    rw [← hMB, memLoad32_store32_same]
  rw [m2e'', r12s0, r12a1, add_lit_zero, add_lit_zero, l3, l4, r12a4, r12s1] at u13
  have hcC := hcB.store32 (v := macLo m0 x1 (macLo m1 x0 0 (macHi m0 x0 0 0)) 0) s4
  have g13 : ∀ q, reg n13 q = (runBlock lm8M2 (MB, reg n12)).2 q := u13.regs
  obtain ⟨n14, d14, u14⟩ := u13.self.notTaken hcC 0xA2 lsm8_at_a0 (by decide)
    (by rw [g13, m2a5'', r12a5, u13.self.zero]; decide)
  obtain ⟨n15, c15, u15⟩ := St.block lm8M3 u14.self hcC lm8M3_end (by simp [BlockOk, BInstr.ok, lm8M3])
  obtain ⟨m3e', m3t1', m3a7', m3t0', m3k'⟩ := lm8M3_run (M := memStore32 MB (F + 0xCC)
    (macLo m0 x1 (macLo m1 x0 0 (macHi m0 x0 0 0)) 0)) (f := reg n14) u14.self.zero
  rw [m3e'] at u15
  have g15 : ∀ q, reg n15 q = _ := u15.regs
  have k14 : ∀ q, reg n14 q = reg n13 q := u14.regs
  have kin2 : ∀ q : Fin 32, q.val ∉ [8, 9, 10, 11, 12, 13, 14, 15] → reg n14 q = reg n10 q := fun q hq => by
    rw [k14, g13, m2k'' q (nmem_of (by decide) hq), k12, g11, m1k' q (nmem_of (by decide) hq)]
  have r15t1 : reg n15 6 = 2 := by rw [g15, m3t1', kin2 6 (by decide), r10t1]; rfl
  have r15a6 : reg n15 16 = 2 := by rw [g15, m3k' 16 (by decide), kin2 16 (by decide), k10, r9a6]
  obtain ⟨n16, d16, u16⟩ := u15.self.notTaken hcC 0xAC lsm8_at_a8 (by decide)
    (by rw [r15t1, r15a6]; decide)
  have m1x : memLoad32 M (mip + 4) = m1 := hm1'
  refine ⟨n16, memStore32 MB (F + 0xCC) (macLo m0 x1 (macLo m1 x0 0 (macHi m0 x0 0 0)) 0),
    c1.trans (.cons d2 (c3.trans (.cons d4 (c5.trans (.cons d6 (c7.trans (.cons d8 (c9.trans (.cons d10
      (c11.trans (.cons d12 (c13.trans (.cons d14 (c15.trans (.single d16))))))))))))))),
    u16.self, hcC, fun x hx => ?_, ?_, fun q hq => ?_⟩
  · have h4 : Sep (F + 0xCC) 4 x 1 := by
      have := hx.sub (c := 4) (l := 4) (by decide); rw [BitVec.add_assoc] at this; exact this
    have h0 : Sep (F + 0xC8) 4 x 1 := by
      have := hx.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    rw [memStore32_get_sep h4, ← hMB, memStore32_get_sep h4, memStore32_get_sep h0, frz x hx]
  · rw [memLoad32_store32_same, memLoad32_store32_sep s11c.symm, ← hMB, memLoad32_store32_sep s11c.symm,
      memLoad32_store32_same, hx0, hx1, hm0', m1x]
    exact mul64_val x0 x1 m0 m1
  · rw [u16.regs, g15, m3k' q (nmem_of (by decide) hq), kin2 q (nmem_of (by decide) hq), k10, g9,
      m3k q (nmem_of (by decide) hq), kin q (nmem_of (by decide) hq), k4, g3, m1k q (nmem_of (by decide) hq),
      k2, k1 q (nmem_of (by decide) hq)]


/-! ## The mask `2^s - 1` and `mf`, from 0xAC to 0x160 -/

/-- From 0xC6 to the panic check at 0xB4: `s8 = 64 - shift`. -/
def lm8K0 : List BInstr := [.aluImm .add a0 x0 0x40, .alu .sub (24 : Fin 32) a0 (19 : Fin 32)]

/-- From 0xD2 to `leading_mut`'s call at 0xCA: the word shift, and a zeroed
mask buffer. -/
def lm8K1 : List BInstr :=
  [.aluImm .srl (21 : Fin 32) (24 : Fin 32) 5, .aluImm .add a0 x0 2, .sw sp x0 0x28, .sw sp x0 0x2C,
   .alu .sub a2 a0 (21 : Fin 32), .aluImm .add a0 sp 0x28, .aluImm .add a1 x0 2]

/-- From 0xEC to `trailing`'s call at 0xE2: keep the buffer, and pass
`Uint<2>::MAX`. -/
def lm8K2 : List BInstr :=
  [.alu .add (20 : Fin 32) x0 a0, .alu .add (8 : Fin 32) x0 a1, .lui a0 0x3FCC5000, .aluImm .add a0 a0 0xFFFFF838,
   .aluImm .add a1 x0 2, .alu .add a2 x0 (21 : Fin 32)]

/-- From 0x108 to the branch at 0xF6: `xa`'s high limbs, and the copy's
count and destination. -/
def lm8K3 : List BInstr :=
  [.aluImm .add (21 : Fin 32) sp 0x80, .alu .add a1 x0 (8 : Fin 32), .alu .add a2 x0 (20 : Fin 32)]

/-- From 0x112 to the branch at 0x102: copy one word. -/
def lm8K4 : List BInstr :=
  [.lw a3 a0 0, .aluImm .add a0 a0 4, .sw a2 a3 0, .aluImm .add a2 a2 4, .aluImm .add a1 a1 0xFFFFFFFF]

/-- From 0xD4 to the branch at 0x11C: the bit shift's setup. -/
def lm8K6 : List BInstr :=
  [.aluImm .add a1 x0 0, .aluImm .sll a2 (8 : Fin 32) 2, .alu .add a3 a2 (20 : Fin 32), .aluImm .add a2 x0 0x20,
   .alu .sub a2 a2 a0, .aluImm .add a3 a3 0xFFFFFFFC]

/-- From 0x138 to the jump at 0x12E: shift one word right, bringing in the
bits from the word above. -/
def lm8K7 : List BInstr :=
  [.lw a4 a3 0, .aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF, .alu .srl a5 a4 a0, .alu .or a5 a5 a1,
   .alu .sll a1 a4 a2, .sw a3 a5 0]

/-- From 0x14A to the branch at 0x144: take the mask, store it at
`sp + 0x58`, and set up the AND. -/
def lm8K8 : List BInstr :=
  [.lw a2 sp 0x28, .lw a3 sp 0x2C, .sw sp x0 0x28, .sw sp x0 0x2C, .aluImm .add a0 sp 0xC8,
   .aluImm .add a1 sp 0x58, .sw sp a2 0x58, .sw sp a3 0x5C, .aluImm .add a2 sp 0x28, .aluImm .add a3 x0 2]

/-- From 0x160 to the branch at 0x156: AND one word. -/
def lm8K9 : List BInstr :=
  [.lw a4 a0 0, .lw a5 a1 0, .aluImm .add a0 a0 4, .alu .and a4 a4 a5, .aluImm .add a1 a1 4, .sw a2 a4 0,
   .aluImm .add a2 a2 4, .aluImm .add a3 a3 0xFFFFFFFF]

/-- From 0x172 to 0x160: copy the masked `mf` back to `sp + 0xC8`. -/
def lm8K10 : List BInstr := [.lw a0 sp 0x28, .lw a1 sp 0x2C, .sw sp a0 0xC8, .sw sp a1 0xCC]

section
set_option maxRecDepth 20000
theorem lm8K0_end : blockEnd lincombShiftMod8Code 0xAC lm8K0 = some 0xB4 := by decide
theorem lm8K1_end : blockEnd lincombShiftMod8Code 0xB8 lm8K1 = some 0xCA := by decide
theorem lm8K2_end : blockEnd lincombShiftMod8Code 0xD2 lm8K2 = some 0xE2 := by decide
theorem lm8K3_end : blockEnd lincombShiftMod8Code 0xEE lm8K3 = some 0xF6 := by decide
theorem lm8K4_end : blockEnd lincombShiftMod8Code 0xF8 lm8K4 = some 0x102 := by decide
theorem lm8K6_end : blockEnd lincombShiftMod8Code 0x10A lm8K6 = some 0x11C := by decide
theorem lm8K7_end : blockEnd lincombShiftMod8Code 0x11E lm8K7 = some 0x12E := by decide
theorem lm8K8_end : blockEnd lincombShiftMod8Code 0x130 lm8K8 = some 0x144 := by decide
theorem lm8K9_end : blockEnd lincombShiftMod8Code 0x146 lm8K9 = some 0x156 := by decide
theorem lm8K10_end : blockEnd lincombShiftMod8Code 0x158 lm8K10 = some 0x160 := by decide
theorem lm8K6b_end : blockEnd lincombShiftMod8Code 0x11A [.aluImm .add a3 a3 0xFFFFFFFC] = some 0x11C := by decide
end


set_option maxRecDepth 20000 in
theorem lm8K0_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lm8K0 (M, f)).1 = M ∧ (runBlock lm8K0 (M, f)).2 a0 = 0x40 ∧
    (runBlock lm8K0 (M, f)).2 (24 : Fin 32) = 0x40 - f 19 ∧
    ∀ q : Fin 32, q.val ∉ [10, 24] → (runBlock lm8K0 (M, f)).2 q = f q := by
  refine ⟨?_, ?_, ?_, fun q hq => ?_⟩
  · simp only [runBlock, BInstr.run, lm8K0]
  · simp only [runBlock, BInstr.run, lm8K0]; simp +decide only [upd, ↓reduceIte, ev_add, hz]; try rfl
  · simp only [runBlock, BInstr.run, lm8K0]; simp +decide only [upd, ↓reduceIte, ev_add, hz]; try rfl
  · exact runBlock_keepL (by decide) hz hq


set_option maxRecDepth 20000 in
theorem lm8K1_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lm8K1 (M, f)).1 = memStore32 (memStore32 M (f sp + 0x28) 0) (f sp + 0x2C) 0 ∧
    (runBlock lm8K1 (M, f)).2 (21 : Fin 32) = aluEval .srl (f 24) 5 ∧
    (runBlock lm8K1 (M, f)).2 a2 = 2 - aluEval .srl (f 24) 5 ∧
    (runBlock lm8K1 (M, f)).2 a0 = f sp + 0x28 ∧ (runBlock lm8K1 (M, f)).2 a1 = 2 ∧
    ∀ q : Fin 32, q.val ∉ [10, 11, 12, 21] → (runBlock lm8K1 (M, f)).2 q = f q := by
  refine ⟨?_, ?_, ?_, ?_, ?_, fun q hq => runBlock_keepL (by decide) hz hq⟩ <;>
    simp only [runBlock, BInstr.run, lm8K1] <;> simp +decide only [upd, ↓reduceIte, ev_add, hz] <;> first | rfl | exact BitVec.zero_add _ | skip

set_option maxRecDepth 20000 in
theorem lm8K2_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lm8K2 (M, f)).1 = M ∧
    (runBlock lm8K2 (M, f)).2 (20 : Fin 32) = f a0 ∧ (runBlock lm8K2 (M, f)).2 (8 : Fin 32) = f a1 ∧
    (runBlock lm8K2 (M, f)).2 a0 = BitVec.ofNat 32 u2MaxAddress ∧ (runBlock lm8K2 (M, f)).2 a1 = 2 ∧
    (runBlock lm8K2 (M, f)).2 a2 = f 21 ∧
    ∀ q : Fin 32, q.val ∉ [8, 10, 11, 12, 20] → (runBlock lm8K2 (M, f)).2 q = f q := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun q hq => runBlock_keepL (by decide) hz hq⟩ <;>
    simp only [runBlock, BInstr.run, lm8K2] <;> simp +decide only [upd, ↓reduceIte, ev_add, hz] <;> first | rfl | exact BitVec.zero_add _ | skip

set_option maxRecDepth 20000 in
theorem lm8K3_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lm8K3 (M, f)).1 = M ∧
    (runBlock lm8K3 (M, f)).2 (21 : Fin 32) = f sp + 0x80 ∧ (runBlock lm8K3 (M, f)).2 a1 = f 8 ∧
    (runBlock lm8K3 (M, f)).2 a2 = f 20 ∧
    ∀ q : Fin 32, q.val ∉ [11, 12, 21] → (runBlock lm8K3 (M, f)).2 q = f q := by
  refine ⟨?_, ?_, ?_, ?_, fun q hq => runBlock_keepL (by decide) hz hq⟩ <;>
    simp only [runBlock, BInstr.run, lm8K3] <;> simp +decide only [upd, ↓reduceIte, ev_add, hz] <;> first | rfl | exact BitVec.zero_add _ | skip

set_option maxRecDepth 20000 in
theorem lm8K4_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lm8K4 (M, f)).1 = memStore32 M (f a2 + 0) (memLoad32 M (f a0 + 0)) ∧
    (runBlock lm8K4 (M, f)).2 a0 = f a0 + 4 ∧ (runBlock lm8K4 (M, f)).2 a2 = f a2 + 4 ∧
    (runBlock lm8K4 (M, f)).2 a1 = f a1 + 0xFFFFFFFF ∧
    ∀ q : Fin 32, q.val ∉ [10, 11, 12, 13] → (runBlock lm8K4 (M, f)).2 q = f q := by
  refine ⟨?_, ?_, ?_, ?_, fun q hq => runBlock_keepL (by decide) hz hq⟩ <;>
    simp only [runBlock, BInstr.run, lm8K4] <;> simp +decide only [upd, ↓reduceIte, ev_add, hz] <;> first | rfl | exact BitVec.zero_add _ | skip

theorem lm8K4_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h0 : (f a0 + 0).toNat % 4 = 0) (h2 : (f a2 + 0).toNat % 4 = 0) (s2 : Sep (f a2 + 0) 4 base len) :
    BlockOk base len lm8K4 (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, lm8K4, upd, ↓reduceIte, and_true, true_and]
  exact ⟨h0, h2, s2⟩

set_option maxRecDepth 20000 in
theorem lm8K6_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lm8K6 (M, f)).1 = M ∧ (runBlock lm8K6 (M, f)).2 a1 = 0 ∧
    (runBlock lm8K6 (M, f)).2 a2 = 0x20 - f a0 ∧
    (runBlock lm8K6 (M, f)).2 a3 = aluEval .sll (f 8) 2 + f 20 + 0xFFFFFFFC ∧
    ∀ q : Fin 32, q.val ∉ [11, 12, 13] → (runBlock lm8K6 (M, f)).2 q = f q := by
  refine ⟨?_, ?_, ?_, ?_, fun q hq => runBlock_keepL (by decide) hz hq⟩ <;>
    simp only [runBlock, BInstr.run, lm8K6] <;> simp +decide only [upd, ↓reduceIte, ev_add, hz] <;> first | rfl | exact BitVec.zero_add _ | skip

set_option maxRecDepth 20000 in
theorem lm8K7_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lm8K7 (M, f)).1 = memStore32 M (f a3 + 0)
      (aluEval .or (aluEval .srl (memLoad32 M (f a3 + 0)) (f a0)) (f a1)) ∧
    (runBlock lm8K7 (M, f)).2 a1 = aluEval .sll (memLoad32 M (f a3 + 0)) (f a2) ∧
    (runBlock lm8K7 (M, f)).2 (8 : Fin 32) = f 8 + 0xFFFFFFFF ∧
    ∀ q : Fin 32, q.val ∉ [8, 11, 14, 15] → (runBlock lm8K7 (M, f)).2 q = f q := by
  refine ⟨?_, ?_, ?_, fun q hq => runBlock_keepL (by decide) hz hq⟩ <;>
    simp only [runBlock, BInstr.run, lm8K7] <;> simp +decide only [upd, ↓reduceIte, ev_add, hz] <;> first | rfl | exact BitVec.zero_add _ | skip

theorem lm8K7_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h3 : (f a3 + 0).toNat % 4 = 0) (s3 : Sep (f a3 + 0) 4 base len) :
    BlockOk base len lm8K7 (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, lm8K7, upd, ↓reduceIte, and_true, true_and]
  exact ⟨h3, h3, s3⟩

set_option maxRecDepth 20000 in
theorem lm8K8_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lm8K8 (M, f)).1 = memStore32 (memStore32 (memStore32 (memStore32 M (f sp + 0x28) 0) (f sp + 0x2C) 0)
      (f sp + 0x58) (memLoad32 M (f sp + 0x28))) (f sp + 0x5C) (memLoad32 M (f sp + 0x2C)) ∧
    (runBlock lm8K8 (M, f)).2 a0 = f sp + 0xC8 ∧ (runBlock lm8K8 (M, f)).2 a1 = f sp + 0x58 ∧
    (runBlock lm8K8 (M, f)).2 a2 = f sp + 0x28 ∧ (runBlock lm8K8 (M, f)).2 a3 = 2 ∧
    ∀ q : Fin 32, q.val ∉ [10, 11, 12, 13] → (runBlock lm8K8 (M, f)).2 q = f q := by
  refine ⟨?_, ?_, ?_, ?_, ?_, fun q hq => runBlock_keepL (by decide) hz hq⟩ <;>
    simp only [runBlock, BInstr.run, lm8K8] <;> simp +decide only [upd, ↓reduceIte, ev_add, hz] <;> first | rfl | exact BitVec.zero_add _ | skip

set_option maxRecDepth 20000 in
theorem lm8K9_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lm8K9 (M, f)).1 = memStore32 M (f a2 + 0) (memLoad32 M (f a0 + 0) &&& memLoad32 M (f a1 + 0)) ∧
    (runBlock lm8K9 (M, f)).2 a0 = f a0 + 4 ∧ (runBlock lm8K9 (M, f)).2 a1 = f a1 + 4 ∧
    (runBlock lm8K9 (M, f)).2 a2 = f a2 + 4 ∧ (runBlock lm8K9 (M, f)).2 a3 = f a3 + 0xFFFFFFFF ∧
    ∀ q : Fin 32, q.val ∉ [10, 11, 12, 13, 14, 15] → (runBlock lm8K9 (M, f)).2 q = f q := by
  refine ⟨?_, ?_, ?_, ?_, ?_, fun q hq => runBlock_keepL (by decide) hz hq⟩ <;>
    simp only [runBlock, BInstr.run, lm8K9] <;> simp +decide only [upd, ↓reduceIte, ev_add, ev_and, hz] <;> first | rfl | exact BitVec.zero_add _ | skip

theorem lm8K9_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h0 : (f a0 + 0).toNat % 4 = 0) (h1 : (f a1 + 0).toNat % 4 = 0) (h2 : (f a2 + 0).toNat % 4 = 0)
    (s2 : Sep (f a2 + 0) 4 base len) : BlockOk base len lm8K9 (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, lm8K9, upd, ↓reduceIte, and_true, true_and]
  exact ⟨h0, h1, h2, s2⟩

set_option maxRecDepth 20000 in
theorem lm8K10_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lm8K10 (M, f)).1 = memStore32 (memStore32 M (f sp + 0xC8) (memLoad32 M (f sp + 0x28)))
      (f sp + 0xCC) (memLoad32 M (f sp + 0x2C)) ∧
    ∀ q : Fin 32, q.val ∉ [10, 11] → (runBlock lm8K10 (M, f)).2 q = f q := by
  refine ⟨?_, fun q hq => runBlock_keepL (by decide) hz hq⟩
  simp only [runBlock, BInstr.run, lm8K10]; simp +decide only [upd, ↓reduceIte, hz]


/-- A call to `UintRef::leading_mut` at `L`, from offset `off` of `code`: it
returns the buffer `a0` with length `a2`, at most the buffer's length `a1`. -/
theorem call_lead8 {M : Word → BitVec 8} {P L : Word} {code : List Nat} {n : Machine} {off : Nat}
    {imm o len want : Word} (hP : P.toNat % 2 = 0) (s : St M P n off (reg n)) (hc : CodeIn M P code)
    (hl : CodeIn M L leadMut8Code) (hL : L.toNat % 2 = 0)
    (h1 : fetchRel code off = some (.auipc ra imm, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = L) (hoff : off % 2 = 0)
    (r11 : reg n a1 = len) (r12 : reg n a2 = want) (hw : want.toNat ≤ len.toNat) :
    ∃ n', Steps n n' ∧ St M P n' (off + 8) (reg n') ∧ reg n' a1 = want ∧
      ∀ q, q ≠ a1 → q ≠ ra → reg n' q = reg n q := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hc h1 h2 hb hL
  have r1 := PEnv.reg1 regs1 s.zero
  have t0 : St M L n1 0 (reg n1) := ⟨by rw [pc1, add_ofNat_zero], mem1, fun _ => rfl⟩
  obtain ⟨n2, d2, u2⟩ := t0.notTaken hl 4 lm_at_0 (by decide) (by
    rw [r1 a1 (by decide), r1 a2 (by decide), r11, r12]; exact bltu_false hw)
  obtain ⟨n3, d3, u3⟩ := u2.alu hl lm_at_4 (off' := 6) (by decide)
  obtain ⟨n4, d4, pc4, mem4, regs4⟩ := u3.self.jalr hl lm_at_6
  have e3 : ∀ q, reg n3 q = upd (reg n1) a1 (aluEval .add (reg n1 x0) (reg n1 a2)) q := u3.regs
  refine ⟨n4, c1.trans (.cons d2 (.cons d3 (.single d4))), ⟨?_, mem4, fun _ => rfl⟩, ?_,
    fun q h11 hra => ?_⟩
  · rw [pc4, e3, upd_ne (by decide) (by decide), regs1, upd_same (by decide), add_lit_zero]
    exact even_clear _ (even_at P hP (off + 8) (by omega))
  · rw [regs4, e3, upd_same (by decide), r1 a2 (by decide), r12, t0.zero]; exact BitVec.zero_add _
  · rw [regs4, e3]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact s.zero.symm
    · rw [upd_ne h0 h11, r1 q hra]

/-- A call to `UintRef::trailing` at `T`, from offset `off` of `code`: it
returns the words from `a2` of the buffer `a0` of length `a1`. -/
theorem call_trail8 {M : Word → BitVec 8} {P T : Word} {code : List Nat} {n : Machine} {off : Nat}
    {imm o p len k : Word} (hP : P.toNat % 2 = 0) (s : St M P n off (reg n)) (hc : CodeIn M P code)
    (ht : CodeIn M T trailing8Code) (hT : T.toNat % 2 = 0)
    (h1 : fetchRel code off = some (.auipc ra imm, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = T) (hoff : off % 2 = 0)
    (r10 : reg n a0 = p) (r11 : reg n a1 = len) (r12 : reg n a2 = k) (hw : k.toNat ≤ len.toNat) :
    ∃ n', Steps n n' ∧ St M P n' (off + 8) (reg n') ∧ reg n' a0 = p + aluEval .sll k 2 ∧
      reg n' a1 = len - k ∧ ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a3 → q ≠ ra → reg n' q = reg n q := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hc h1 h2 hb hT
  have r1 := PEnv.reg1 regs1 s.zero
  have t0 : St M T n1 0 (reg n1) := ⟨by rw [pc1, add_ofNat_zero], mem1, fun _ => rfl⟩
  obtain ⟨n2, d2, u2⟩ := t0.notTaken ht 4 tr_at_0 (by decide) (by
    rw [r1 a1 (by decide), r1 a2 (by decide), r11, r12]; exact bltu_false hw)
  obtain ⟨n3, d3, u3⟩ := u2.aluImm ht tr_at_4 (off' := 8) (by decide)
  obtain ⟨n4, d4, u4⟩ := u3.self.alu ht tr_at_8 (off' := 0xA) (by decide)
  obtain ⟨n5, d5, u5⟩ := u4.self.alu ht tr_at_a (off' := 0xC) (by decide)
  obtain ⟨n6, d6, pc6, mem6, regs6⟩ := u5.self.jalr ht tr_at_c
  refine ⟨n6, c1.trans (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.single d6))))),
    ⟨?_, mem6, fun _ => rfl⟩, ?_, ?_, fun q h10 h11 h13 hra => ?_⟩
  · rw [pc6]; simp +decide only [u5.regs, u4.regs, u3.regs, upd_app, ↓reduceIte]
    rw [regs1, upd_same (by decide), add_lit_zero]
    exact even_clear _ (even_at P hP (off + 8) (by omega))
  · rw [regs6]; simp +decide only [u5.regs, u4.regs, u3.regs, upd_app, ↓reduceIte]
    rw [r1 a0 (by decide), r1 a2 (by decide), r10, r12]; rfl
  · rw [regs6]; simp +decide only [u5.regs, u4.regs, u3.regs, upd_app, ↓reduceIte]
    rw [r1 a1 (by decide), r1 a2 (by decide), r11, r12]; rfl
  · rw [regs6]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; rw [u5.self.zero]; exact s.zero.symm
    · simp only [u5.regs, u4.regs, u3.regs, upd_app, h0, h10, h11, h13, ite_false]; exact r1 q hra


/-- **The mask's setup**, from 0xAC to the copy loop at 0xF8: `s8 = k = 64 -
shift`, the buffer at `F + 0x28` zeroed, and the copy's source (the words of
`Uint<2>::MAX` from `k / 32`), count, and destination. -/
theorem lm8_maskPre {M : Word → BitVec 8} {P F : Word} {n : Machine} {sh : Nat} (hP : P.toNat % 2 = 0)
    (s : St M P n 0xAC (reg n)) (hc : CodeIn M P lincombShiftMod8Code)
    (hl : CodeIn M (lm8Shr P + 0x1EE) leadMut8Code) (ht : CodeIn M (lm8Shr P + 0x1FE) trailing8Code)
    (rsp : reg n sp = F) (r19 : reg n 19 = BitVec.ofNat 32 sh) (hs1 : 1 ≤ sh) (hs2 : sh ≤ 63)
    (hF : F.toNat % 4 = 0) (sC : Sep (F + 0x28) 8 P lincombShiftMod8Code.length)
    (sLm : Sep (F + 0x28) 8 (lm8Shr P + 0x1EE) leadMut8Code.length)
    (sTr : Sep (F + 0x28) 8 (lm8Shr P + 0x1FE) trailing8Code.length) :
    ∃ n', Steps n n' ∧
      St (memStore32 (memStore32 M (F + 0x28) 0) (F + 0x2C) 0) P n' 0xF8 (reg n') ∧
      reg n' 24 = BitVec.ofNat 32 (64 - sh) ∧ reg n' 21 = F + 0x80 ∧ reg n' 20 = F + 0x28 ∧
      reg n' 8 = BitVec.ofNat 32 (2 - (64 - sh) / 32) ∧
      reg n' a0 = BitVec.ofNat 32 u2MaxAddress + BitVec.ofNat 32 (4 * ((64 - sh) / 32)) ∧
      reg n' a1 = BitVec.ofNat 32 (2 - (64 - sh) / 32) ∧ reg n' a2 = F + 0x28 ∧
      ∀ q : Fin 32, q.val ∉ [1, 8, 10, 11, 12, 13, 20, 21, 24] → reg n' q = reg n q := by
  have hz := s.zero
  have hk : 64 - sh < 64 := by omega
  have hk32 : (64 - sh) / 32 ≤ 1 := by omega
  -- `s8 = 64 - shift`, and the panic check
  obtain ⟨n1, c1, u1⟩ := St.block lm8K0 s hc lm8K0_end (by simp [BlockOk, BInstr.ok, lm8K0])
  obtain ⟨k0e, k0a0, k0s8, k0k⟩ := lm8K0_run (M := M) (f := reg n) hz
  rw [k0e] at u1
  have g1 : ∀ q, reg n1 q = (runBlock lm8K0 (M, reg n)).2 q := u1.regs
  have r1s8 : reg n1 24 = BitVec.ofNat 32 (64 - sh) := by rw [g1, k0s8, r19, k_word hs1 hs2]
  obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc 0xB8 lsm8_at_b4 (by decide) (by
    rw [r1s8, g1, k0a0]
    show (!(BitVec.ofNat 32 (64 - sh)).ult 0x40) = false
    have : (BitVec.ofNat 32 (64 - sh)).ult 0x40 = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat]; exact decide_eq_true (by show _ < 64; omega)
    rw [this]; rfl)
  have k2 : ∀ q, reg n2 q = reg n1 q := u2.regs
  -- zero the buffer, and `leading_mut`
  have s38 : Sep (F + 0x28) 4 P lincombShiftMod8Code.length := by
    have := sC.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
  have s3c : Sep (F + 0x2C) 4 P lincombShiftMod8Code.length := by
    have := sC.sub (c := 4) (l := 4) (by decide); rw [BitVec.add_assoc] at this; exact this
  have r2sp : reg n2 sp = F := by rw [k2, g1, k0k sp (by decide), rsp]
  obtain ⟨n3, c3, u3⟩ := St.block lm8K1 u2.self hc lm8K1_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, lm8K1, upd, ↓reduceIte, and_true, true_and]
    rw [r2sp]
    exact ⟨⟨aligned_add hF (by decide), s38⟩, aligned_add hF (by decide), s3c⟩)
  obtain ⟨k1e, k1s5, k1a2, k1a0, k1a1, k1k⟩ := lm8K1_run (M := M) (f := reg n2) u2.self.zero
  rw [k1e, r2sp] at u3
  obtain ⟨Mz, hMz⟩ : ∃ Mz, memStore32 (memStore32 M (F + 0x28) 0) (F + 0x2C) 0 = Mz := ⟨_, rfl⟩
  rw [hMz] at u3
  have hcz : CodeIn Mz P lincombShiftMod8Code := by rw [← hMz]; exact (hc.store32 s38).store32 s3c
  have g3 : ∀ q, reg n3 q = (runBlock lm8K1 (M, reg n2)).2 q := u3.regs
  have r3s5 : reg n3 21 = BitVec.ofNat 32 ((64 - sh) / 32) := by rw [g3, k1s5, k2, r1s8, srl5 hk]
  have w2 : (2 : Word) - BitVec.ofNat 32 ((64 - sh) / 32) = BitVec.ofNat 32 (2 - (64 - sh) / 32) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    show (2 ^ 32 - (64 - sh) / 32 % 2 ^ 32 + 2) % 2 ^ 32 = (2 - (64 - sh) / 32) % 2 ^ 32
    omega
  have r3a2 : reg n3 a2 = BitVec.ofNat 32 (2 - (64 - sh) / 32) := by rw [g3, k1a2, k2, r1s8, srl5 hk, w2]
  have eL : lm8Shr P + 0x1EE = P + 0xFFFFFDE2 := by rw [BitVec.add_assoc]; rfl
  have eT : lm8Shr P + 0x1FE = P + 0xFFFFFDF2 := by rw [BitVec.add_assoc]; rfl
  have hlA : (lm8Shr P + 0x1EE).toNat % 2 = 0 := by rw [eL]; exact even_at P hP 0xFFFFFDE2 (by decide)
  have htA : (lm8Shr P + 0x1FE).toNat % 2 = 0 := by rw [eT]; exact even_at P hP 0xFFFFFDF2 (by decide)
  have cz : ∀ {b : Word} {code : List Nat}, CodeIn M b code → Sep (F + 0x28) 8 b code.length → CodeIn Mz b code :=
    fun {b code} h hs => by
      rw [← hMz]
      exact (h.store32 (by have := hs.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this)).store32
        (by have := hs.sub (c := 4) (l := 4) (by decide); rw [BitVec.add_assoc] at this; exact this)
  obtain ⟨n4, c4, u4, a14, k4⟩ := call_lead8 hP u3.self hcz (cz hl sLm)
    hlA lsm8_at_ca lsm8_at_ce (by rw [eL, BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    (by rw [g3, k1a1]) r3a2 (by rw [BitVec.toNat_ofNat]; show _ ≤ 2; omega)
  have r4a0 : reg n4 a0 = F + 0x28 := by rw [k4 _ (by decide) (by decide), g3, k1a0, r2sp]
  have r4s5 : reg n4 21 = BitVec.ofNat 32 ((64 - sh) / 32) := by rw [k4 _ (by decide) (by decide), r3s5]
  obtain ⟨n5, c5, u5⟩ := St.block lm8K2 u4 hcz lm8K2_end (by simp [BlockOk, BInstr.ok, lm8K2])
  obtain ⟨k2e, k2s4, k2s0, k2a0, k2a1, k2a2, k2k⟩ := lm8K2_run (M := Mz) (f := reg n4) u4.zero
  rw [k2e] at u5
  have g5 : ∀ q, reg n5 q = (runBlock lm8K2 (Mz, reg n4)).2 q := u5.regs
  obtain ⟨n6, c6, u6, a06, a16, k6⟩ := call_trail8 hP u5.self hcz (cz ht sTr) htA lsm8_at_e2 lsm8_at_e6
    (by rw [eT, BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide) (by rw [g5, k2a0]) (by rw [g5, k2a1])
    (by rw [g5, k2a2, r4s5]) (by rw [BitVec.toNat_ofNat]; show _ ≤ 2; omega)
  have w2' : (2 : Word) - BitVec.ofNat 32 ((64 - sh) / 32) = BitVec.ofNat 32 (2 - (64 - sh) / 32) := w2
  have r6s0 : reg n6 8 = BitVec.ofNat 32 (2 - (64 - sh) / 32) := by
    rw [k6 _ (by decide) (by decide) (by decide) (by decide), g5, k2s0, a14]
  obtain ⟨n7, d7, u7⟩ := u6.notTaken hcz 0xEE lsm8_at_ea (by decide) (by
    rw [r6s0, a16, w2']; simp [branchTaken])
  have k7 : ∀ q, reg n7 q = reg n6 q := u7.regs
  have r7s4 : reg n7 20 = F + 0x28 := by
    rw [k7, k6 _ (by decide) (by decide) (by decide) (by decide), g5, k2s4, r4a0]
  obtain ⟨n8, c8, u8⟩ := St.block lm8K3 u7.self hcz lm8K3_end (by simp [BlockOk, BInstr.ok, lm8K3])
  obtain ⟨k3e, k3s5, k3a1, k3a2, k3k⟩ := lm8K3_run (M := Mz) (f := reg n7) u7.self.zero
  rw [k3e] at u8
  have g8 : ∀ q, reg n8 q = (runBlock lm8K3 (Mz, reg n7)).2 q := u8.regs
  have r8s0 : reg n8 8 = BitVec.ofNat 32 (2 - (64 - sh) / 32) := by rw [g8, k3k 8 (by decide), k7, r6s0]
  obtain ⟨n9, d9, u9⟩ := u8.self.notTaken hcz 0xF8 lsm8_at_f6 (by decide) (by
    rw [r8s0, u8.self.zero]
    have : BitVec.ofNat 32 (2 - (64 - sh) / 32) ≠ 0 := fun e => by
      have := congrArg BitVec.toNat e; rw [BitVec.toNat_ofNat] at this; simp at this; omega
    simpa [branchTaken] using this)
  have k9 : ∀ q, reg n9 q = reg n8 q := u9.regs
  have r9sp : reg n9 sp = F := by
    rw [k9, g8, k3k sp (by decide), k7, k6 _ (by decide) (by decide) (by decide) (by decide), g5,
      k2k sp (by decide), k4 _ (by decide) (by decide), g3, k1k sp (by decide), r2sp]
  have sll2 : aluEval .sll (BitVec.ofNat 32 ((64 - sh) / 32)) 2 = BitVec.ofNat 32 (4 * ((64 - sh) / 32)) := by
    rcases (by omega : (64 - sh) / 32 = 0 ∨ (64 - sh) / 32 = 1) with h | h <;> rw [h] <;> decide
  refine ⟨n9, c1.trans (.cons d2 (c3.trans (c4.trans (c5.trans (c6.trans (.cons d7 (c8.trans (.single d9)))))))),
    by rw [hMz]; exact u9.self, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · rw [k9, g8, k3k 24 (by decide), k7, k6 _ (by decide) (by decide) (by decide) (by decide), g5,
      k2k 24 (by decide), k4 _ (by decide) (by decide), g3, k1k 24 (by decide), k2, r1s8]
  · rw [k9, g8, k3s5, k7, k6 _ (by decide) (by decide) (by decide) (by decide), g5, k2k sp (by decide),
      k4 _ (by decide) (by decide), g3, k1k sp (by decide), r2sp]
  · rw [k9, g8, k3k 20 (by decide), r7s4]
  · rw [k9, r8s0]
  · rw [k9, g8, k3k a0 (by decide), k7, a06, sll2]
  · rw [k9, g8, k3a1, k7, r6s0]
  · rw [k9, g8, k3a2, r7s4]
  · have q24 : q.val ∉ [24] := nmem_of (by decide) hq
    rw [k9, g8, k3k q (nmem_of (by decide) hq), k7,
      k6 q (fun e => hq (by rw [e]; decide)) (fun e => hq (by rw [e]; decide)) (fun e => hq (by rw [e]; decide))
        (fun e => hq (by rw [e]; decide)), g5, k2k q (nmem_of (by decide) hq),
      k4 q (fun e => hq (by rw [e]; decide)) (fun e => hq (by rw [e]; decide)), g3, k1k q (nmem_of (by decide) hq),
      k2, g1, k0k q (nmem_of (by decide) hq)]


set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- The copy for `shift = 32`: one word of `Uint<2>::MAX` to the buffer, and
no bit shift. -/
theorem lm8_maskB {M : Word → BitVec 8} {P F : Word} {n : Machine} (s : St M P n 0xF8 (reg n))
    (hc : CodeIn M P lincombShiftMod8Code) (hmax : CodeIn M (BitVec.ofNat 32 u2MaxAddress) u2MaxData)
    (r24 : reg n 24 = BitVec.ofNat 32 32) (ra0 : reg n a0 = BitVec.ofNat 32 u2MaxAddress + BitVec.ofNat 32 (4 * 1))
    (ra1 : reg n a1 = BitVec.ofNat 32 1) (ra2 : reg n a2 = F + 0x28) (hF : F.toNat % 4 = 0)
    (sC : Sep (F + 0x28) 8 P lincombShiftMod8Code.length)
    (sMX : Sep (F + 0x28) 8 (BitVec.ofNat 32 u2MaxAddress) 8) (hb1 : memLoad32 M (F + 0x2C) = 0) :
    ∃ n' M', Steps n n' ∧ St M' P n' 0x130 (reg n') ∧ CodeIn M' P lincombShiftMod8Code ∧
      (∀ x, Sep (F + 0x28) 8 x 1 → M' x = M x) ∧ maskOK 32 (memLoad32 M' (F + 0x28)) (memLoad32 M' (F + 0x2C)) ∧
      ∀ q : Fin 32, q.val ∉ [8, 10, 11, 12, 13, 14, 15] → reg n' q = reg n q := by
  have hz := s.zero
  have s38 : Sep (F + 0x28) 4 P lincombShiftMod8Code.length := by
    have := sC.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
  have mx1 : memLoad32 M (BitVec.ofNat 32 u2MaxAddress + BitVec.ofNat 32 (4 * 1)) = 0xFFFFFFFF := max_word hmax 1 (by decide)
  obtain ⟨n1, c1, u1⟩ := St.block lm8K4 s hc lm8K4_end
    (lm8K4_ok (by rw [ra0, add_lit_zero]; exact aligned_add (by decide) (by decide))
      (by rw [ra2, add_lit_zero]; exact aligned_add hF (by decide)) (by rw [ra2, add_lit_zero]; exact s38))
  obtain ⟨k4e, k4a0, k4a2, k4a1, k4k⟩ := lm8K4_run (M := M) (f := reg n) hz
  rw [k4e, ra0, ra2, add_lit_zero, add_lit_zero, mx1] at u1
  have hc1 : CodeIn (memStore32 M (F + 0x28) 0xFFFFFFFF) P lincombShiftMod8Code := hc.store32 s38
  have g1 : ∀ q, reg n1 q = (runBlock lm8K4 (M, reg n)).2 q := u1.regs
  obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc1 0x104 lsm8_at_102 (by decide)
    (by rw [g1, k4a1, ra1, u1.self.zero]; decide)
  obtain ⟨n3, d3, u3⟩ := u2.self.aluImm hc1 lsm8_at_104 (off' := 0x108) (by decide)
  have r3a0 : upd (reg n2) a0 (aluEval .and (reg n2 24) 0x1F) a0 = 0 := by
    rw [upd_same (by decide), u2.regs, g1, k4k 24 (by decide), r24]; decide
  obtain ⟨n4, d4, u4⟩ := u3.taken hc1 0x130 lsm8_at_108 (by decide) (by rw [r3a0, upd_zero]; decide)
  refine ⟨n4, _, c1.trans (.cons d2 (.cons d3 (.single d4))), u4.self, hc1, fun x hx => ?_, ?_, fun q hq => ?_⟩
  · exact memStore32_get_sep (by have := hx.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this)
  · rw [memLoad32_store32_same, memLoad32_store32_sep (by
      have := sep_offsets F (c := 0x28) (n := 4) (d := 0x2C) (k := 4) (.inl (by decide)) (by decide) (by decide)
      exact this), hb1]
    exact maskOK_32
  · rw [u4.regs]
    have hq0 : q ≠ a0 := fun e => hq (by rw [e]; decide)
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; rw [upd_zero]; exact hz.symm
    · rw [upd_ne h0 hq0, u2.regs, g1, k4k q (nmem_of (by decide) hq)]


set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- The copy and shift for `shift` from 1 to 31: one word of
`Uint<2>::MAX`, shifted right by `64 - shift - 32`. -/
theorem lm8_maskC {M : Word → BitVec 8} {P F : Word} {n : Machine} {sh : Nat} (hP : P.toNat % 2 = 0)
    (s : St M P n 0xF8 (reg n)) (hc : CodeIn M P lincombShiftMod8Code)
    (hmax : CodeIn M (BitVec.ofNat 32 u2MaxAddress) u2MaxData) (hs1 : 1 ≤ sh) (hs2 : sh ≤ 31)
    (r24 : reg n 24 = BitVec.ofNat 32 (64 - sh)) (ra0 : reg n a0 = BitVec.ofNat 32 u2MaxAddress + BitVec.ofNat 32 (4 * 1))
    (ra1 : reg n a1 = BitVec.ofNat 32 1) (ra2 : reg n a2 = F + 0x28) (r8 : reg n 8 = BitVec.ofNat 32 1)
    (r20 : reg n 20 = F + 0x28) (hF : F.toNat % 4 = 0)
    (sC : Sep (F + 0x28) 8 P lincombShiftMod8Code.length)
    (sMX : Sep (F + 0x28) 8 (BitVec.ofNat 32 u2MaxAddress) 8) (hb1 : memLoad32 M (F + 0x2C) = 0) :
    ∃ n' M', Steps n n' ∧ St M' P n' 0x130 (reg n') ∧ CodeIn M' P lincombShiftMod8Code ∧
      (∀ x, Sep (F + 0x28) 8 x 1 → M' x = M x) ∧ maskOK sh (memLoad32 M' (F + 0x28)) (memLoad32 M' (F + 0x2C)) ∧
      ∀ q : Fin 32, q.val ∉ [8, 10, 11, 12, 13, 14, 15] → reg n' q = reg n q := by
  have hz := s.zero
  obtain ⟨wnz, wval⟩ := maskC_words ⟨64 - sh, by omega⟩ (by show 33 ≤ 64 - sh; omega)
  simp only at wnz wval
  have s38 : Sep (F + 0x28) 4 P lincombShiftMod8Code.length := by
    have := sC.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
  have a38 : (F + 0x28).toNat % 4 = 0 := aligned_add hF (by decide)
  have mx1 : memLoad32 M (BitVec.ofNat 32 u2MaxAddress + BitVec.ofNat 32 (4 * 1)) = 0xFFFFFFFF := max_word hmax 1 (by decide)
  -- the copy
  obtain ⟨n1, c1, u1⟩ := St.block lm8K4 s hc lm8K4_end
    (lm8K4_ok (by rw [ra0, add_lit_zero]; exact aligned_add (by decide) (by decide))
      (by rw [ra2, add_lit_zero]; exact a38) (by rw [ra2, add_lit_zero]; exact s38))
  obtain ⟨k4e, k4a0, k4a2, k4a1, k4k⟩ := lm8K4_run (M := M) (f := reg n) hz
  rw [k4e, ra0, ra2, add_lit_zero, add_lit_zero, mx1] at u1
  have hc1 : CodeIn (memStore32 M (F + 0x28) 0xFFFFFFFF) P lincombShiftMod8Code := hc.store32 s38
  have g1 : ∀ q, reg n1 q = (runBlock lm8K4 (M, reg n)).2 q := u1.regs
  obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc1 0x104 lsm8_at_102 (by decide)
    (by rw [g1, k4a1, ra1, u1.self.zero]; decide)
  obtain ⟨n3, d3, u3⟩ := u2.self.aluImm hc1 lsm8_at_104 (off' := 0x108) (by decide)
  have e24 : reg n2 24 = BitVec.ofNat 32 (64 - sh) := by rw [u2.regs, g1, k4k 24 (by decide), r24]
  obtain ⟨n4, d4, u4⟩ := u3.notTaken hc1 0x10A lsm8_at_108 (by decide) (by
    rw [upd_same (by decide), upd_zero, e24]; simpa [branchTaken] using wnz)
  -- the shift's setup
  have k4r : ∀ q : Fin 32, q.val ∉ [10, 11, 12, 13] → reg n4 q = reg n q := fun q hq => by
    have hq0 : q ≠ a0 := fun e => hq (by rw [e]; decide)
    rw [u4.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; rw [upd_zero]; exact hz.symm
    · rw [upd_ne h0 hq0, u2.regs, g1, k4k q hq]
  have r4a0 : reg n4 a0 = aluEval .and (BitVec.ofNat 32 (64 - sh)) 0x1F := by
    rw [u4.regs, upd_same (by decide), e24]
  obtain ⟨n5, c5, u5⟩ := St.block lm8K6 u4.self hc1 lm8K6_end (by simp [BlockOk, BInstr.ok, lm8K6])
  obtain ⟨k6e, k6a1, k6a2, k6a3, k6k⟩ := lm8K6_run (M := memStore32 M (F + 0x28) 0xFFFFFFFF) (f := reg n4) u4.self.zero
  rw [k6e] at u5
  have g5 : ∀ q, reg n5 q = (runBlock lm8K6 (memStore32 M (F + 0x28) 0xFFFFFFFF, reg n4)).2 q := u5.regs
  have r5a3 : reg n5 a3 = F + 0x28 := by
    rw [g5, k6a3, k4r 8 (by decide), k4r 20 (by decide), r8, r20]
    show aluEval .sll (BitVec.ofNat 32 1) 2 + (F + 0x28) + 0xFFFFFFFC = F + 0x28
    rw [show aluEval .sll (BitVec.ofNat 32 1) 2 = 4 by decide, BitVec.add_comm (4 : Word), BitVec.add_assoc,
      BitVec.add_assoc]
    rfl
  have r5s0 : reg n5 8 = BitVec.ofNat 32 1 := by rw [g5, k6k 8 (by decide), k4r 8 (by decide), r8]
  obtain ⟨n6, d6, u6⟩ := u5.self.notTaken hc1 0x11E lsm8_at_11c (by decide)
    (by rw [r5s0, u5.self.zero]; decide)
  -- one pass of the shift
  obtain ⟨n7, c7, u7⟩ := St.block lm8K7 u6.self hc1 lm8K7_end
    (lm8K7_ok (by rw [u6.regs, r5a3, add_lit_zero]; exact a38) (by rw [u6.regs, r5a3, add_lit_zero]; exact s38))
  obtain ⟨k7e, k7a1, k7s0, k7k⟩ := lm8K7_run (M := memStore32 M (F + 0x28) 0xFFFFFFFF) (f := reg n6) u6.self.zero
  have e6a3 : reg n6 a3 = F + 0x28 := by rw [u6.regs, r5a3]
  have e6a0 : reg n6 a0 = aluEval .and (BitVec.ofNat 32 (64 - sh)) 0x1F := by
    rw [u6.regs, g5, k6k a0 (by decide), r4a0]
  have e6a1 : reg n6 a1 = 0 := by rw [u6.regs, g5, k6a1]
  rw [k7e, e6a3, add_lit_zero, memLoad32_store32_same, e6a0, e6a1] at u7
  obtain ⟨Mw, hMw⟩ : ∃ Mw, memStore32 (memStore32 M (F + 0x28) 0xFFFFFFFF) (F + 0x28)
      (aluEval .or (aluEval .srl 0xFFFFFFFF (aluEval .and (BitVec.ofNat 32 (64 - sh)) 0x1F)) 0) = Mw := ⟨_, rfl⟩
  rw [hMw] at u7
  have hc7 : CodeIn Mw P lincombShiftMod8Code := by rw [← hMw]; exact hc1.store32 s38
  have g7 : ∀ q, reg n7 q = (runBlock lm8K7 (memStore32 M (F + 0x28) 0xFFFFFFFF, reg n6)).2 q := u7.regs
  obtain ⟨n8, d8, u8⟩ := u7.self.jump hc7 lsm8_at_12e (off' := 0x11A) (by decide) (by
    rw [u7.pc, show P + BitVec.ofNat 32 0x12E + 0xFFFFFFEC = P + BitVec.ofNat 32 0x11A by rw [BitVec.add_assoc]; rfl]
    exact even_bit0 (even_at P hP 0x11A (by decide)))
  obtain ⟨n9, d9, u9⟩ := u8.self.aluImm hc7 lsm8_at_11a (off' := 0x11C) (by decide)
  have r9s0 : upd (reg n8) a3 (aluEval .add (reg n8 a3) 0xFFFFFFFC) 8 = 0 := by
    rw [upd_ne (by decide) (by decide), u8.regs, g7, k7s0, u6.regs, r5s0]; rfl
  obtain ⟨n10, d10, u10⟩ := u9.taken hc7 0x130 lsm8_at_11c (by decide) (by rw [r9s0, upd_zero]; decide)
  refine ⟨n10, Mw, c1.trans (.cons d2 (.cons d3 (.cons d4 (c5.trans (.cons d6 (c7.trans (.cons d8 (.cons d9
    (.single d10))))))))), u10.self, hc7, fun x hx => ?_, ?_, fun q hq => ?_⟩
  · have h0 : Sep (F + 0x28) 4 x 1 := by
      have := hx.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    rw [← hMw, memStore32_get_sep h0, memStore32_get_sep h0]
  · have s3c : Sep (F + 0x28) 4 (F + 0x2C) 4 := by
      have := sep_offsets F (c := 0x28) (n := 4) (d := 0x2C) (k := 4) (.inl (by decide)) (by decide) (by decide)
      exact this
    rw [← hMw, memLoad32_store32_same, memLoad32_store32_sep s3c, memLoad32_store32_sep s3c, hb1]
    exact maskOK_lo (by omega) (by rw [wval]; congr 1; congr 1; omega)
  · rw [u10.regs]
    have hq3 : q ≠ a3 := fun e => hq (by rw [e]; decide)
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; rw [upd_zero]; exact hz.symm
    · rw [upd_ne h0 hq3, u8.regs, g7, k7k q (nmem_of (by decide) hq), u6.regs, g5, k6k q (nmem_of (by decide) hq),
        k4r q (nmem_of (by decide) hq)]


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- The copy and shift for `shift` from 33 to 63: both words of
`Uint<2>::MAX`, shifted right by `64 - shift`. -/
theorem lm8_maskA {M : Word → BitVec 8} {P F : Word} {n : Machine} {sh : Nat} (hP : P.toNat % 2 = 0)
    (s : St M P n 0xF8 (reg n)) (hc : CodeIn M P lincombShiftMod8Code)
    (hmax : CodeIn M (BitVec.ofNat 32 u2MaxAddress) u2MaxData) (hs1 : 33 ≤ sh) (hs2 : sh ≤ 63)
    (r24 : reg n 24 = BitVec.ofNat 32 (64 - sh)) (ra0 : reg n a0 = BitVec.ofNat 32 u2MaxAddress + BitVec.ofNat 32 (4 * 0))
    (ra1 : reg n a1 = BitVec.ofNat 32 2) (ra2 : reg n a2 = F + 0x28) (r8 : reg n 8 = BitVec.ofNat 32 2)
    (r20 : reg n 20 = F + 0x28) (hF : F.toNat % 4 = 0)
    (sC : Sep (F + 0x28) 8 P lincombShiftMod8Code.length)
    (sMX : Sep (F + 0x28) 8 (BitVec.ofNat 32 u2MaxAddress) 8) :
    ∃ n' M', Steps n n' ∧ St M' P n' 0x130 (reg n') ∧ CodeIn M' P lincombShiftMod8Code ∧
      (∀ x, Sep (F + 0x28) 8 x 1 → M' x = M x) ∧ maskOK sh (memLoad32 M' (F + 0x28)) (memLoad32 M' (F + 0x2C)) ∧
      ∀ q : Fin 32, q.val ∉ [8, 10, 11, 12, 13, 14, 15] → reg n' q = reg n q := by
  have hz := s.zero
  obtain ⟨wnz, wtop, wlow⟩ := maskA_words ⟨64 - sh, by omega⟩ (by show 1 ≤ 64 - sh; omega)
  simp only at wnz wtop wlow
  have s38 : Sep (F + 0x28) 4 P lincombShiftMod8Code.length := by
    have := sC.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
  have s3c : Sep (F + 0x2C) 4 P lincombShiftMod8Code.length := by
    have := sC.sub (c := 4) (l := 4) (by decide); rw [BitVec.add_assoc] at this; exact this
  have a38 : (F + 0x28).toNat % 4 = 0 := aligned_add hF (by decide)
  have a3c : (F + 0x2C).toNat % 4 = 0 := aligned_add hF (by decide)
  have e3c : F + 0x28 + 4 = F + 0x2C := by rw [BitVec.add_assoc]; rfl
  have s83 : Sep (F + 0x28) 4 (F + 0x2C) 4 := by
    have := sep_offsets F (c := 0x28) (n := 4) (d := 0x2C) (k := 4) (.inl (by decide)) (by decide) (by decide)
    exact this
  have mx0 : memLoad32 M (BitVec.ofNat 32 u2MaxAddress + BitVec.ofNat 32 (4 * 0)) = 0xFFFFFFFF :=
    max_word hmax 0 (by decide)
  have mx1 : memLoad32 M (BitVec.ofNat 32 u2MaxAddress + BitVec.ofNat 32 (4 * 1)) = 0xFFFFFFFF :=
    max_word hmax 1 (by decide)
  have eMX : BitVec.ofNat 32 u2MaxAddress + BitVec.ofNat 32 (4 * 0) + 4 = BitVec.ofNat 32 u2MaxAddress + BitVec.ofNat 32 (4 * 1) := by
    rw [BitVec.add_assoc]; rfl
  -- the first copy
  obtain ⟨n1, c1, u1⟩ := St.block lm8K4 s hc lm8K4_end
    (lm8K4_ok (by rw [ra0, add_lit_zero]; exact aligned_add (by decide) (by decide))
      (by rw [ra2, add_lit_zero]; exact a38) (by rw [ra2, add_lit_zero]; exact s38))
  obtain ⟨k4e, k4a0, k4a2, k4a1, k4k⟩ := lm8K4_run (M := M) (f := reg n) hz
  rw [k4e, ra0, ra2, add_lit_zero, add_lit_zero, mx0] at u1
  have hc1 : CodeIn (memStore32 M (F + 0x28) 0xFFFFFFFF) P lincombShiftMod8Code := hc.store32 s38
  have g1 : ∀ q, reg n1 q = (runBlock lm8K4 (M, reg n)).2 q := u1.regs
  obtain ⟨n2, d2, u2⟩ := u1.self.taken hc1 0xF8 lsm8_at_102 (by decide)
    (by rw [g1, k4a1, ra1, u1.self.zero]; decide)
  -- the second copy
  have r2a0 : reg n2 a0 = BitVec.ofNat 32 u2MaxAddress + BitVec.ofNat 32 (4 * 1) := by rw [u2.regs, g1, k4a0, ra0, eMX]
  have r2a2 : reg n2 a2 = F + 0x2C := by rw [u2.regs, g1, k4a2, ra2, e3c]
  have r2a1 : reg n2 a1 = BitVec.ofNat 32 1 := by rw [u2.regs, g1, k4a1, ra1]; rfl
  have mx1' : memLoad32 (memStore32 M (F + 0x28) 0xFFFFFFFF) (BitVec.ofNat 32 u2MaxAddress + BitVec.ofNat 32 (4 * 1)) =
      0xFFFFFFFF := by
    rw [memLoad32_store32_sep (by
      have := (sMX.sub (c := 0) (l := 4) (by decide)).subR (c := 4) (l := 4) (by decide)
      rwa [add_ofNat_zero] at this), mx1]
  obtain ⟨n3, c3, u3⟩ := St.block lm8K4 u2.self hc1 lm8K4_end
    (lm8K4_ok (by rw [r2a0, add_lit_zero]; exact aligned_add (by decide) (by decide))
      (by rw [r2a2, add_lit_zero]; exact a3c) (by rw [r2a2, add_lit_zero]; exact s3c))
  obtain ⟨k4e', k4a0', k4a2', k4a1', k4k'⟩ := lm8K4_run (M := memStore32 M (F + 0x28) 0xFFFFFFFF) (f := reg n2)
    u2.self.zero
  rw [k4e', r2a0, r2a2, add_lit_zero, add_lit_zero, mx1'] at u3
  obtain ⟨Mc, hMc⟩ : ∃ Mc, memStore32 (memStore32 M (F + 0x28) 0xFFFFFFFF) (F + 0x2C) 0xFFFFFFFF = Mc := ⟨_, rfl⟩
  rw [hMc] at u3
  have hc3 : CodeIn Mc P lincombShiftMod8Code := by rw [← hMc]; exact hc1.store32 s3c
  have g3 : ∀ q, reg n3 q = (runBlock lm8K4 (memStore32 M (F + 0x28) 0xFFFFFFFF, reg n2)).2 q := u3.regs
  obtain ⟨n4, d4, u4⟩ := u3.self.notTaken hc3 0x104 lsm8_at_102 (by decide)
    (by rw [g3, k4a1', r2a1, u3.self.zero]; decide)
  have k4r : ∀ q : Fin 32, q.val ∉ [10, 11, 12, 13] → reg n4 q = reg n q := fun q hq => by
    rw [u4.regs, g3, k4k' q hq, u2.regs, g1, k4k q hq]
  obtain ⟨n5, d5, u5⟩ := u4.self.aluImm hc3 lsm8_at_104 (off' := 0x108) (by decide)
  have e24 : reg n4 24 = BitVec.ofNat 32 (64 - sh) := by rw [k4r 24 (by decide), r24]
  obtain ⟨n6, d6, u6⟩ := u5.notTaken hc3 0x10A lsm8_at_108 (by decide) (by
    rw [upd_same (by decide), upd_zero, e24]; simpa [branchTaken] using wnz)
  have k6r : ∀ q : Fin 32, q.val ∉ [10, 11, 12, 13] → reg n6 q = reg n q := fun q hq => by
    have hq0 : q ≠ a0 := fun e => hq (by rw [e]; decide)
    rw [u6.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; rw [upd_zero]; exact hz.symm
    · rw [upd_ne h0 hq0, k4r q hq]
  have r6a0 : reg n6 a0 = aluEval .and (BitVec.ofNat 32 (64 - sh)) 0x1F := by
    rw [u6.regs, upd_same (by decide), e24]
  -- the shift's setup
  obtain ⟨n7, c7, u7⟩ := St.block lm8K6 u6.self hc3 lm8K6_end (by simp [BlockOk, BInstr.ok, lm8K6])
  obtain ⟨k6e, k6a1, k6a2, k6a3, k6k⟩ := lm8K6_run (M := Mc) (f := reg n6) u6.self.zero
  rw [k6e] at u7
  have g7 : ∀ q, reg n7 q = (runBlock lm8K6 (Mc, reg n6)).2 q := u7.regs
  have r7a3 : reg n7 a3 = F + 0x2C := by
    rw [g7, k6a3, k6r 8 (by decide), k6r 20 (by decide), r8, r20]
    show aluEval .sll (BitVec.ofNat 32 2) 2 + (F + 0x28) + 0xFFFFFFFC = F + 0x2C
    rw [show aluEval .sll (BitVec.ofNat 32 2) 2 = 8 by decide, BitVec.add_comm (8 : Word), BitVec.add_assoc,
      BitVec.add_assoc]
    rfl
  have r7s0 : reg n7 8 = BitVec.ofNat 32 2 := by rw [g7, k6k 8 (by decide), k6r 8 (by decide), r8]
  have r7a0 : reg n7 a0 = aluEval .and (BitVec.ofNat 32 (64 - sh)) 0x1F := by rw [g7, k6k a0 (by decide), r6a0]
  have r7a2 : reg n7 a2 = 0x20 - aluEval .and (BitVec.ofNat 32 (64 - sh)) 0x1F := by rw [g7, k6a2, r6a0]
  have r7a1 : reg n7 a1 = 0 := by rw [g7, k6a1]
  obtain ⟨n8, d8, u8⟩ := u7.self.notTaken hc3 0x11E lsm8_at_11c (by decide)
    (by rw [r7s0, u7.self.zero]; decide)
  -- the top word
  have e8 : ∀ q, reg n8 q = reg n7 q := u8.regs
  obtain ⟨n9, c9, u9⟩ := St.block lm8K7 u8.self hc3 lm8K7_end
    (lm8K7_ok (by rw [e8, r7a3, add_lit_zero]; exact a3c) (by rw [e8, r7a3, add_lit_zero]; exact s3c))
  obtain ⟨k7e, k7a1, k7s0, k7k⟩ := lm8K7_run (M := Mc) (f := reg n8) u8.self.zero
  have ldc : memLoad32 Mc (F + 0x2C) = 0xFFFFFFFF := by rw [← hMc, memLoad32_store32_same]
  rw [k7e, e8, r7a3, add_lit_zero, ldc, e8, r7a0, e8, r7a1] at u9
  obtain ⟨top, htop⟩ : ∃ top, aluEval .or (aluEval .srl 0xFFFFFFFF (aluEval .and (BitVec.ofNat 32 (64 - sh)) 0x1F)) 0 = top :=
    ⟨_, rfl⟩
  rw [htop] at u9 wtop
  have hc9 : CodeIn (memStore32 Mc (F + 0x2C) top) P lincombShiftMod8Code := hc3.store32 s3c
  have g9 : ∀ q, reg n9 q = (runBlock lm8K7 (Mc, reg n8)).2 q := u9.regs
  obtain ⟨n10, d10, u10⟩ := u9.self.jump hc9 lsm8_at_12e (off' := 0x11A) (by decide) (by
    rw [u9.pc, show P + BitVec.ofNat 32 0x12E + 0xFFFFFFEC = P + BitVec.ofNat 32 0x11A by rw [BitVec.add_assoc]; rfl]
    exact even_bit0 (even_at P hP 0x11A (by decide)))
  obtain ⟨n11, d11, u11⟩ := u10.self.aluImm hc9 lsm8_at_11a (off' := 0x11C) (by decide)
  have r11s0 : upd (reg n10) a3 (aluEval .add (reg n10 a3) 0xFFFFFFFC) 8 = BitVec.ofNat 32 1 := by
    rw [upd_ne (by decide) (by decide), u10.regs, g9, k7s0, e8, r7s0]; rfl
  obtain ⟨n12, d12, u12⟩ := u11.notTaken hc9 0x11E lsm8_at_11c (by decide) (by rw [r11s0, upd_zero]; decide)
  -- the low word
  have r12 : ∀ q, reg n12 q = upd (reg n10) a3 (aluEval .add (reg n10 a3) 0xFFFFFFFC) q := u12.regs
  have r12a3 : reg n12 a3 = F + 0x28 := by
    rw [r12, upd_same (by decide), u10.regs, g9, k7k a3 (by decide), e8, r7a3]
    show F + 0x2C + 0xFFFFFFFC = F + 0x28
    rw [BitVec.add_assoc]; rfl
  have r12a0 : reg n12 a0 = aluEval .and (BitVec.ofNat 32 (64 - sh)) 0x1F := by
    rw [r12, upd_ne (by decide) (by decide), u10.regs, g9, k7k a0 (by decide), e8, r7a0]
  have r12a1 : reg n12 a1 = aluEval .sll 0xFFFFFFFF (0x20 - aluEval .and (BitVec.ofNat 32 (64 - sh)) 0x1F) := by
    rw [r12, upd_ne (by decide) (by decide), u10.regs, g9, k7a1, e8, r7a3, add_lit_zero, ldc, e8, r7a2]
  have r12s0 : reg n12 8 = BitVec.ofNat 32 1 := by rw [r12, r11s0]
  obtain ⟨n13, c13, u13⟩ := St.block lm8K7 u12.self hc9 lm8K7_end
    (lm8K7_ok (by rw [r12a3, add_lit_zero]; exact a38) (by rw [r12a3, add_lit_zero]; exact s38))
  obtain ⟨k7e', k7a1', k7s0', k7k'⟩ := lm8K7_run (M := memStore32 Mc (F + 0x2C) top) (f := reg n12) u12.self.zero
  have ldl : memLoad32 (memStore32 Mc (F + 0x2C) top) (F + 0x28) = 0xFFFFFFFF := by
    rw [memLoad32_store32_sep s83.symm, ← hMc, memLoad32_store32_sep s83.symm, memLoad32_store32_same]
  rw [k7e', r12a3, add_lit_zero, ldl, r12a0, r12a1, wlow] at u13
  have hc13 : CodeIn (memStore32 (memStore32 Mc (F + 0x2C) top) (F + 0x28) 0xFFFFFFFF) P lincombShiftMod8Code :=
    hc9.store32 s38
  have g13 : ∀ q, reg n13 q = (runBlock lm8K7 (memStore32 Mc (F + 0x2C) top, reg n12)).2 q := u13.regs
  obtain ⟨n14, d14, u14⟩ := u13.self.jump hc13 lsm8_at_12e (off' := 0x11A) (by decide) (by
    rw [u13.pc, show P + BitVec.ofNat 32 0x12E + 0xFFFFFFEC = P + BitVec.ofNat 32 0x11A by rw [BitVec.add_assoc]; rfl]
    exact even_bit0 (even_at P hP 0x11A (by decide)))
  obtain ⟨n15, d15, u15⟩ := u14.self.aluImm hc13 lsm8_at_11a (off' := 0x11C) (by decide)
  have r15s0 : upd (reg n14) a3 (aluEval .add (reg n14 a3) 0xFFFFFFFC) 8 = 0 := by
    rw [upd_ne (by decide) (by decide), u14.regs, g13, k7s0', r12s0]; rfl
  obtain ⟨n16, d16, u16⟩ := u15.taken hc13 0x130 lsm8_at_11c (by decide) (by rw [r15s0, upd_zero]; decide)
  refine ⟨n16, _, c1.trans (.cons d2 (c3.trans (.cons d4 (.cons d5 (.cons d6 (c7.trans (.cons d8 (c9.trans
    (.cons d10 (.cons d11 (.cons d12 (c13.trans (.cons d14 (.cons d15 (.single d16))))))))))))))),
    u16.self, hc13, fun x hx => ?_, ?_, fun q hq => ?_⟩
  · have h0 : Sep (F + 0x28) 4 x 1 := by
      have := hx.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    have h4 : Sep (F + 0x2C) 4 x 1 := by
      have := hx.sub (c := 4) (l := 4) (by decide); rw [BitVec.add_assoc] at this; exact this
    rw [memStore32_get_sep h0, memStore32_get_sep h4, ← hMc, memStore32_get_sep h4, memStore32_get_sep h0]
  · rw [memLoad32_store32_same, memLoad32_store32_sep s83, memLoad32_store32_same]
    exact maskOK_hi (by omega) (by rw [wtop]; congr 1; congr 1; omega)
  · have hq3 : q ≠ a3 := fun e => hq (by rw [e]; decide)
    rw [u16.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; rw [upd_zero]; exact hz.symm
    · rw [upd_ne h0 hq3, u14.regs, g13, k7k' q (nmem_of (by decide) hq), r12, upd_ne h0 hq3, u10.regs, g9,
        k7k q (nmem_of (by decide) hq), e8, g7, k6k q (nmem_of (by decide) hq), k6r q (nmem_of (by decide) hq)]


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **Masking `mf`**, from 0x130 to 0x160: with the mask words in the buffer
at `F + 0x28`, AND them into the two words of `mf` at `F + 0xC8`. -/
theorem lm8_maskEnd {M : Word → BitVec 8} {P F : Word} {n : Machine} {sh : Nat} (s : St M P n 0x130 (reg n))
    (hc : CodeIn M P lincombShiftMod8Code) (rsp : reg n sp = F) (hF : F.toNat % 4 = 0)
    (hm : maskOK sh (memLoad32 M (F + 0x28)) (memLoad32 M (F + 0x2C)))
    (sC1 : Sep (F + 0x28) 8 P lincombShiftMod8Code.length) (sC2 : Sep (F + 0x58) 8 P lincombShiftMod8Code.length)
    (sC3 : Sep (F + 0xC8) 8 P lincombShiftMod8Code.length) :
    ∃ n' M', Steps n n' ∧ St M' P n' 0x160 (reg n') ∧ CodeIn M' P lincombShiftMod8Code ∧
      (∀ x, Sep (F + 0x28) 8 x 1 → Sep (F + 0x58) 8 x 1 → Sep (F + 0xC8) 8 x 1 → M' x = M x) ∧
      (memLoad32 M' (F + 0xC8)).toNat + 2 ^ 32 * (memLoad32 M' (F + 0xCC)).toNat =
        ((memLoad32 M (F + 0xC8)).toNat + 2 ^ 32 * (memLoad32 M (F + 0xCC)).toNat) % 2 ^ sh ∧
      ∀ q : Fin 32, q.val ∉ [10, 11, 12, 13, 14, 15] → reg n' q = reg n q := by
  have hz := s.zero
  have sw : ∀ c d : Nat, c + 4 ≤ d ∨ d + 4 ≤ c → c + 4 ≤ 0x120 → d + 4 ≤ 0x120 →
      Sep (F + BitVec.ofNat 32 c) 4 (F + BitVec.ofNat 32 d) 4 := fun c d h h1 h2 =>
    sep_offsets F h (by omega) (by omega)
  have al : ∀ c : Nat, c % 4 = 0 → (F + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h => aligned_add hF h
  have sc : ∀ {c : Nat} {b : Word} {k : Nat}, Sep (F + BitVec.ofNat 32 c) 8 b k → Sep (F + BitVec.ofNat 32 c) 4 b k ∧
      Sep (F + BitVec.ofNat 32 (c + 4)) 4 b k := fun {c b k} h => by
    refine ⟨?_, ?_⟩
    · have := h.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    · have := h.sub (c := 4) (l := 4) (by decide); rwa [add_ofNat_assoc] at this
  obtain ⟨c38, c3c⟩ := sc (c := 0x28) sC1
  obtain ⟨c78, c7c⟩ := sc (c := 0x58) sC2
  obtain ⟨c118, c11c⟩ := sc (c := 0xC8) sC3
  obtain ⟨m0, hm0⟩ : ∃ m0, memLoad32 M (F + 0x28) = m0 := ⟨_, rfl⟩
  obtain ⟨m1, hm1⟩ : ∃ m1, memLoad32 M (F + 0x2C) = m1 := ⟨_, rfl⟩
  obtain ⟨w0, hw0⟩ : ∃ w0, memLoad32 M (F + 0xC8) = w0 := ⟨_, rfl⟩
  obtain ⟨w1, hw1⟩ : ∃ w1, memLoad32 M (F + 0xCC) = w1 := ⟨_, rfl⟩
  rw [hm0, hm1] at hm
  -- save the mask
  obtain ⟨n1, c1, u1⟩ := St.block lm8K8 s hc lm8K8_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, lm8K8, upd, ↓reduceIte, and_true, true_and]
    rw [rsp]
    exact ⟨al 0x28 rfl, al 0x2C rfl, ⟨al 0x28 rfl, c38⟩, ⟨al 0x2C rfl, c3c⟩, ⟨al 0x58 rfl, c78⟩, al 0x5C rfl, c7c⟩)
  obtain ⟨k8e, k8a0, k8a1, k8a2, k8a3, k8k⟩ := lm8K8_run (M := M) (f := reg n) hz
  rw [k8e, rsp, hm0, hm1] at u1
  obtain ⟨M8, hM8⟩ : ∃ M8, memStore32 (memStore32 (memStore32 (memStore32 M (F + 0x28) 0) (F + 0x2C) 0)
      (F + 0x58) m0) (F + 0x5C) m1 = M8 := ⟨_, rfl⟩
  rw [hM8] at u1
  have hc8 : CodeIn M8 P lincombShiftMod8Code := by
    rw [← hM8]; exact (((hc.store32 c38).store32 c3c).store32 c78).store32 c7c
  have g1 : ∀ q, reg n1 q = (runBlock lm8K8 (M, reg n)).2 q := u1.regs
  obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc8 0x146 lsm8_at_144 (by decide)
    (by rw [g1, k8a3, u1.self.zero]; decide)
  have r2a0 : reg n2 a0 = F + 0xC8 := by rw [u2.regs, g1, k8a0, rsp]
  have r2a1 : reg n2 a1 = F + 0x58 := by rw [u2.regs, g1, k8a1, rsp]
  have r2a2 : reg n2 a2 = F + 0x28 := by rw [u2.regs, g1, k8a2, rsp]
  have r2a3 : reg n2 a3 = 2 := by rw [u2.regs, g1, k8a3]
  have l8 : memLoad32 M8 (F + 0xC8) = w0 ∧ memLoad32 M8 (F + 0xCC) = w1 ∧ memLoad32 M8 (F + 0x58) = m0 ∧
      memLoad32 M8 (F + 0x5C) = m1 := by
    rw [← hM8, ← hw0, ← hw1]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp (disch := decide) only [ls_lit, ls_same]
  -- AND the low words
  obtain ⟨n3, c3, u3⟩ := St.block lm8K9 u2.self hc8 lm8K9_end
    (lm8K9_ok (by rw [r2a0, add_lit_zero]; exact al 0xC8 rfl) (by rw [r2a1, add_lit_zero]; exact al 0x58 rfl)
      (by rw [r2a2, add_lit_zero]; exact al 0x28 rfl) (by rw [r2a2, add_lit_zero]; exact c38))
  obtain ⟨k9e, k9a0, k9a1, k9a2, k9a3, k9k⟩ := lm8K9_run (M := M8) (f := reg n2) u2.self.zero
  rw [k9e, r2a0, r2a1, r2a2, add_lit_zero, add_lit_zero, add_lit_zero, l8.1, l8.2.2.1] at u3
  have hc3 := hc8.store32 (v := w0 &&& m0) c38
  have g3 : ∀ q, reg n3 q = (runBlock lm8K9 (M8, reg n2)).2 q := u3.regs
  obtain ⟨n4, d4, u4⟩ := u3.self.taken hc3 0x146 lsm8_at_156 (by decide)
    (by rw [g3, k9a3, r2a3, u3.self.zero]; decide)
  have e4 : ∀ c : Nat, F + BitVec.ofNat 32 c + 4 = F + BitVec.ofNat 32 (c + 4) := fun c => by
    rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]
  have r4a0 : reg n4 a0 = F + 0xCC := by rw [u4.regs, g3, k9a0, r2a0]; exact e4 0xC8
  have r4a1 : reg n4 a1 = F + 0x5C := by rw [u4.regs, g3, k9a1, r2a1]; exact e4 0x58
  have r4a2 : reg n4 a2 = F + 0x2C := by rw [u4.regs, g3, k9a2, r2a2]; exact e4 0x28
  have r4a3 : reg n4 a3 = 1 := by rw [u4.regs, g3, k9a3, r2a3]; rfl
  -- AND the high words
  obtain ⟨n5, c5, u5⟩ := St.block lm8K9 u4.self hc3 lm8K9_end
    (lm8K9_ok (by rw [r4a0, add_lit_zero]; exact al 0xCC rfl) (by rw [r4a1, add_lit_zero]; exact al 0x5C rfl)
      (by rw [r4a2, add_lit_zero]; exact al 0x2C rfl) (by rw [r4a2, add_lit_zero]; exact c3c))
  obtain ⟨k9e', k9a0', k9a1', k9a2', k9a3', k9k'⟩ := lm8K9_run (M := memStore32 M8 (F + 0x28) (w0 &&& m0)) (f := reg n4)
    u4.self.zero
  have l9 : memLoad32 (memStore32 M8 (F + 0x28) (w0 &&& m0)) (F + 0xCC) = w1 ∧
      memLoad32 (memStore32 M8 (F + 0x28) (w0 &&& m0)) (F + 0x5C) = m1 := by
    refine ⟨?_, ?_⟩
    · simp (disch := decide) only [ls_lit]; exact l8.2.1
    · simp (disch := decide) only [ls_lit]; exact l8.2.2.2
  rw [k9e', r4a0, r4a1, r4a2, add_lit_zero, add_lit_zero, add_lit_zero, l9.1, l9.2] at u5
  have hc5 := hc3.store32 (v := w1 &&& m1) c3c
  have g5 : ∀ q, reg n5 q = (runBlock lm8K9 (memStore32 M8 (F + 0x28) (w0 &&& m0), reg n4)).2 q := u5.regs
  obtain ⟨n6, d6, u6⟩ := u5.self.notTaken hc5 0x158 lsm8_at_156 (by decide)
    (by rw [g5, k9a3', r4a3, u5.self.zero]; decide)
  -- copy back
  have r6sp : reg n6 sp = F := by
    rw [u6.regs, g5, k9k' sp (by decide), u4.regs, g3, k9k sp (by decide), u2.regs, g1, k8k sp (by decide), rsp]
  obtain ⟨n7, c7, u7⟩ := St.block lm8K10 u6.self hc5 lm8K10_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, lm8K10, upd, ↓reduceIte, and_true, true_and]
    rw [r6sp]
    exact ⟨al 0x28 rfl, al 0x2C rfl, ⟨al 0xC8 rfl, c118⟩, al 0xCC rfl, c11c⟩)
  obtain ⟨k10e, k10k⟩ := lm8K10_run (M := memStore32 (memStore32 M8 (F + 0x28) (w0 &&& m0)) (F + 0x2C) (w1 &&& m1))
    (f := reg n6) u6.self.zero
  rw [k10e, r6sp] at u7
  have lA : memLoad32 (memStore32 (memStore32 M8 (F + 0x28) (w0 &&& m0)) (F + 0x2C) (w1 &&& m1)) (F + 0x28) = w0 &&& m0 ∧
      memLoad32 (memStore32 (memStore32 M8 (F + 0x28) (w0 &&& m0)) (F + 0x2C) (w1 &&& m1)) (F + 0x2C) = w1 &&& m1 := by
    refine ⟨?_, ?_⟩ <;> simp (disch := decide) only [ls_lit, ls_same]
  rw [lA.1, lA.2] at u7
  obtain ⟨MF, hMF⟩ : ∃ MF, memStore32 (memStore32 (memStore32 (memStore32 M8 (F + 0x28) (w0 &&& m0)) (F + 0x2C)
      (w1 &&& m1)) (F + 0xC8) (w0 &&& m0)) (F + 0xCC) (w1 &&& m1) = MF := ⟨_, rfl⟩
  rw [hMF] at u7
  have hc7 : CodeIn MF P lincombShiftMod8Code := by
    rw [← hMF]; exact (hc5.store32 (v := w0 &&& m0) c118).store32 (v := w1 &&& m1) c11c
  have lF : memLoad32 MF (F + 0xC8) = w0 &&& m0 ∧ memLoad32 MF (F + 0xCC) = w1 &&& m1 := by
    rw [← hMF]; refine ⟨?_, ?_⟩ <;> simp (disch := decide) only [ls_lit, ls_same]
  refine ⟨n7, MF, c1.trans (.cons d2 (c3.trans (.cons d4 (c5.trans (.cons d6 c7))))), u7.self, hc7,
    fun x h1 h2 h3 => ?_, ?_, fun q hq => ?_⟩
  · obtain ⟨x38, x3c⟩ := sc (c := 0x28) h1
    obtain ⟨x78, x7c⟩ := sc (c := 0x58) h2
    obtain ⟨x118, x11c⟩ := sc (c := 0xC8) h3
    rw [← hMF, memStore32_get_sep (a := F + 0xCC) x11c, memStore32_get_sep (a := F + 0xC8) x118,
      memStore32_get_sep (a := F + 0x2C) x3c, memStore32_get_sep (a := F + 0x28) x38, ← hM8,
      memStore32_get_sep (a := F + 0x5C) x7c, memStore32_get_sep (a := F + 0x58) x78,
      memStore32_get_sep (a := F + 0x2C) x3c, memStore32_get_sep (a := F + 0x28) x38]
  · rw [lF.1, lF.2, hw0, hw1]; exact hm w0 w1
  · rw [u7.regs, k10k q (nmem_of (by decide) hq), u6.regs, g5, k9k' q hq, u4.regs, g3, k9k q hq, u2.regs, g1,
      k8k q (nmem_of (by decide) hq)]


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **The mask**, from 0xAC to 0x160: the two words of `mf` at `F + 0xC8`
get their value modulo `2^shift`, and `s5` points at `F + 0x80`. -/
theorem lm8_mask {M : Word → BitVec 8} {P F : Word} {n : Machine} {sh : Nat} (hP : P.toNat % 2 = 0)
    (s : St M P n 0xAC (reg n)) (hc : CodeIn M P lincombShiftMod8Code)
    (hl : CodeIn M (lm8Shr P + 0x1EE) leadMut8Code) (ht : CodeIn M (lm8Shr P + 0x1FE) trailing8Code)
    (hmax : CodeIn M (BitVec.ofNat 32 u2MaxAddress) u2MaxData)
    (rsp : reg n sp = F) (r19 : reg n 19 = BitVec.ofNat 32 sh) (hs1 : 1 ≤ sh) (hs2 : sh ≤ 63)
    (hF : F.toNat % 4 = 0) (sC1 : Sep (F + 0x28) 8 P lincombShiftMod8Code.length)
    (sC2 : Sep (F + 0x58) 8 P lincombShiftMod8Code.length) (sC3 : Sep (F + 0xC8) 8 P lincombShiftMod8Code.length)
    (sLm : Sep (F + 0x28) 8 (lm8Shr P + 0x1EE) leadMut8Code.length)
    (sTr : Sep (F + 0x28) 8 (lm8Shr P + 0x1FE) trailing8Code.length)
    (sMX : Sep (F + 0x28) 8 (BitVec.ofNat 32 u2MaxAddress) 8) :
    ∃ n' M', Steps n n' ∧ St M' P n' 0x160 (reg n') ∧ CodeIn M' P lincombShiftMod8Code ∧
      (∀ x, Sep (F + 0x28) 8 x 1 → Sep (F + 0x58) 8 x 1 → Sep (F + 0xC8) 8 x 1 → M' x = M x) ∧
      (memLoad32 M' (F + 0xC8)).toNat + 2 ^ 32 * (memLoad32 M' (F + 0xCC)).toNat =
        ((memLoad32 M (F + 0xC8)).toNat + 2 ^ 32 * (memLoad32 M (F + 0xCC)).toNat) % 2 ^ sh ∧
      reg n' 21 = F + 0x80 ∧ reg n' sp = F ∧
      ∀ q : Fin 32, q.val ∉ [1, 8, 10, 11, 12, 13, 14, 15, 20, 21, 24] → reg n' q = reg n q := by
  obtain ⟨n1, c1, u1, r24, r21, r20, r8, ra0, ra1, ra2, k1⟩ :=
    lm8_maskPre hP s hc hl ht rsp r19 hs1 hs2 hF sC1 sLm sTr
  obtain ⟨Mz, hMz⟩ : ∃ Mz, memStore32 (memStore32 M (F + 0x28) 0) (F + 0x2C) 0 = Mz := ⟨_, rfl⟩
  rw [hMz] at u1
  have sc : ∀ {c : Nat} {b : Word} {k : Nat}, Sep (F + BitVec.ofNat 32 c) 8 b k → Sep (F + BitVec.ofNat 32 c) 4 b k ∧
      Sep (F + BitVec.ofNat 32 (c + 4)) 4 b k := fun {c b k} h => by
    refine ⟨?_, ?_⟩
    · have := h.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    · have := h.sub (c := 4) (l := 4) (by decide); rwa [add_ofNat_assoc] at this
  have frz : ∀ x, Sep (F + 0x28) 8 x 1 → Mz x = M x := fun x hx => by
    obtain ⟨h0, h4⟩ := sc (c := 0x28) hx
    rw [← hMz, memStore32_get_sep (a := F + 0x2C) h4, memStore32_get_sep (a := F + 0x28) h0]
  have cz : ∀ {b : Word} {code : List Nat}, CodeIn M b code → Sep (F + 0x28) 8 b code.length → CodeIn Mz b code :=
    fun h hs i hi => by rw [frz _ (hs.subR (c := i) (l := 1) (by omega))]; exact h i hi
  have hcz := cz hc sC1
  have hmz : CodeIn Mz (BitVec.ofNat 32 u2MaxAddress) u2MaxData := cz hmax sMX
  have z3c : memLoad32 Mz (F + 0x2C) = 0 := by rw [← hMz, memLoad32_store32_same]
  have hF8 : (F + 0x28).toNat % 4 = 0 := aligned_add hF (by decide)
  -- the copy and the shift, by the shape of the mask
  obtain ⟨n2, M2, c2, u2, hc2, fr2, ok2, k2⟩ : ∃ n2 M2, Steps n1 n2 ∧ St M2 P n2 0x130 (reg n2) ∧
      CodeIn M2 P lincombShiftMod8Code ∧ (∀ x, Sep (F + 0x28) 8 x 1 → M2 x = Mz x) ∧
      maskOK sh (memLoad32 M2 (F + 0x28)) (memLoad32 M2 (F + 0x2C)) ∧
      ∀ q : Fin 32, q.val ∉ [8, 10, 11, 12, 13, 14, 15] → reg n2 q = reg n1 q := by
    rcases (by omega : 33 ≤ sh ∨ sh = 32 ∨ sh ≤ 31) with h | h | h
    · have hq : (64 - sh) / 32 = 0 := by omega
      rw [hq] at r8 ra0 ra1
      exact lm8_maskA hP u1 hcz hmz h hs2 r24 ra0 ra1 ra2 r8 r20 hF sC1 sMX
    · subst h
      exact lm8_maskB u1 hcz hmz r24 ra0 ra1 ra2 hF sC1 sMX z3c
    · have hq : (64 - sh) / 32 = 1 := by omega
      rw [hq] at r8 ra0 ra1
      exact lm8_maskC hP u1 hcz hmz hs1 h r24 ra0 ra1 ra2 r8 r20 hF sC1 sMX z3c
  have r2sp : reg n2 sp = F := by rw [k2 sp (by decide), k1 sp (by decide), rsp]
  obtain ⟨n3, M3, c3, u3, hc3, fr3, v3, k3⟩ := lm8_maskEnd u2 hc2 r2sp hF ok2 sC1 sC2 sC3
  have l118 : ∀ {c : Nat}, 0x48 ≤ c → c + 4 ≤ 0x120 → memLoad32 M2 (F + BitVec.ofNat 32 c) = memLoad32 M (F + BitVec.ofNat 32 c) :=
    fun {c} h1 h2 => memLoad32_congr fun j hj => by
      have hx : Sep (F + 0x28) 8 (F + BitVec.ofNat 32 c + BitVec.ofNat 32 j) 1 := by
        rw [add_ofNat_assoc]
        exact sep_offsets F (c := 0x28) (n := 8) (d := c + j) (k := 1) (.inl (by omega)) (by decide) (by omega)
      rw [fr2 _ hx, frz _ hx]
  have m118 : memLoad32 M2 (F + 0xC8) = memLoad32 M (F + 0xC8) := l118 (c := 0xC8) (by decide) (by decide)
  have m11c : memLoad32 M2 (F + 0xCC) = memLoad32 M (F + 0xCC) := l118 (c := 0xCC) (by decide) (by decide)
  refine ⟨n3, M3, c1.trans (c2.trans c3), u3, hc3, fun x h1 h2 h3 => ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · rw [fr3 x h1 h2 h3, fr2 x h1, frz x h1]
  · rw [v3, m118, m11c]
  · rw [k3 21 (by decide), k2 21 (by decide), r21]
  · rw [k3 sp (by decide), r2sp]
  · rw [k3 q (nmem_of (by decide) hq), k2 q (nmem_of (by decide) hq), k1 q (nmem_of (by decide) hq)]

/-! ## The subtraction `x - m`, from 0x236 to 0x254 -/

/-- `borrowing_sub`'s offset from `lincomb_int_reduce_shift_mod`. -/
abbrev lm8Bsub (P : Word) : Word := P + 0xFFFF0FEE

/-- The end of a subtraction round, from 0x246: keep the borrow, store the
difference, and advance the pointers and the count. -/
def lm8SubTail : List BInstr :=
  [.alu .add a2 x0 a1, .aluImm .add (21 : Fin 32) (21 : Fin 32) 4, .sw (8 : Fin 32) a0 0,
   .aluImm .add (23 : Fin 32) (23 : Fin 32) 4, .aluImm .add (8 : Fin 32) (8 : Fin 32) 4,
   .aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFF]

section
set_option maxRecDepth 20000
theorem lm8SubTail_end : blockEnd lincombShiftMod8Code 0x246 lm8SubTail = some 0x252 := by decide
end

set_option maxRecDepth 20000 in
theorem lm8SubTail_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lm8SubTail (M, f)).1 = memStore32 M (f (8 : Fin 32) + 0) (f a0) ∧
    (runBlock lm8SubTail (M, f)).2 a2 = f a1 ∧
    (runBlock lm8SubTail (M, f)).2 (21 : Fin 32) = f (21 : Fin 32) + 4 ∧
    (runBlock lm8SubTail (M, f)).2 (23 : Fin 32) = f (23 : Fin 32) + 4 ∧
    (runBlock lm8SubTail (M, f)).2 (8 : Fin 32) = f (8 : Fin 32) + 4 ∧
    (runBlock lm8SubTail (M, f)).2 (9 : Fin 32) = f (9 : Fin 32) + 0xFFFFFFFF ∧
    ∀ q, q ≠ a2 → q ≠ (21 : Fin 32) → q ≠ (23 : Fin 32) → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) →
      (runBlock lm8SubTail (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, lm8SubTail]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun q q2 qnp qxp qd qc => ?_⟩
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte, hz]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q2, qnp, qxp, qd, qc]

theorem lm8SubTail_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h : (f (8 : Fin 32) + 0).toNat % 4 = 0) (hs : Sep (f (8 : Fin 32) + 0) 4 base len) :
    BlockOk base len lm8SubTail (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, lm8SubTail, upd, ↓reduceIte, and_true, true_and]
  exact ⟨h, hs⟩

/-- **One round of the subtraction**, from 0x236: subtract limb `i` of `x`
and the borrow from limb `i` of the modulus at `np`, and store the
difference at limb `i` of the buffer at `D`. `borrowing_sub` also writes
the word below `sp`. -/
theorem lm8_sub_iter {M : Word → BitVec 8} {P F np xp D b : Word} {n : Machine} {i : Nat}
    (s : St M P n 0x236 (reg n)) (hc : CodeIn M P lincombShiftMod8Code) (hb : CodeIn M (lm8Bsub P) borrowingSubCode)
    (hP : P.toNat % 2 = 0) (hi : i < 8) (hF : F.toNat % 4 = 0) (hnp : np.toNat % 4 = 0)
    (hxp : xp.toNat % 4 = 0) (hD : D.toNat % 4 = 0)
    (sFB : Sep (F + 0xFFFFFFFC) 4 (lm8Bsub P) borrowingSubCode.length)
    (sFC : Sep (F + 0xFFFFFFFC) 4 P lincombShiftMod8Code.length)
    (sDC : Sep (D + BitVec.ofNat 32 (4 * i)) 4 P lincombShiftMod8Code.length)
    (rsp : reg n sp = F) (rnp : reg n (21 : Fin 32) = np + BitVec.ofNat 32 (4 * i))
    (rxp : reg n (23 : Fin 32) = xp + BitVec.ofNat 32 (4 * i)) (rd : reg n (8 : Fin 32) = D + BitVec.ofNat 32 (4 * i))
    (rc : reg n (9 : Fin 32) = BitVec.ofNat 32 (8 - i)) (ra2 : reg n a2 = b) :
    ∃ n' Mb, Steps n n' ∧
      St (memStore32 Mb (D + BitVec.ofNat 32 (4 * i))
          (bsubD (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) b))
        P n' (if i + 1 < 8 then 0x236 else 0x254) (reg n') ∧
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Mb x = M x) ∧
      reg n' a2 = bsubB (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i)))
        (bsubD (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) b) ∧
      reg n' sp = F ∧ reg n' (21 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (23 : Fin 32) = xp + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (8 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (9 : Fin 32) = BitVec.ofNat 32 (8 - (i + 1)) ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (21 : Fin 32) → q ≠ (23 : Fin 32) →
        q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → reg n' q = reg n q := by
  have hz := s.zero
  obtain ⟨n1, d1, u1⟩ := s.lw hc lsm8_at_236 (off' := 0x23A) (by decide)
    (by rw [rnp, add_lit_zero]; exact aligned_add hnp (by omega))
  obtain ⟨n2, d2, u2⟩ := u1.lw hc lsm8_at_23a (off' := 0x23E) (by decide)
    (by rw [upd_ne (by decide) (by decide), rxp, add_lit_zero]; exact aligned_add hxp (by omega))
  rw [rnp, add_lit_zero] at u2
  have f0 : upd (upd (reg n) a0 (memLoad32 M (np + BitVec.ofNat 32 (4 * i)))) a1
      (memLoad32 M (upd (reg n) a0 (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (23 : Fin 32) + 0)) a0 =
      memLoad32 M (np + BitVec.ofNat 32 (4 * i)) := by simp +decide [upd]
  have f1 : upd (upd (reg n) a0 (memLoad32 M (np + BitVec.ofNat 32 (4 * i)))) a1
      (memLoad32 M (upd (reg n) a0 (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (23 : Fin 32) + 0)) a1 =
      memLoad32 M (xp + BitVec.ofNat 32 (4 * i)) := by
    simp +decide only [upd, ↓reduceIte]; rw [rxp, add_lit_zero]
  have u2' := u2.self
  have g2a0 : reg n2 a0 = memLoad32 M (np + BitVec.ofNat 32 (4 * i)) := by rw [u2.regs, f0]
  have g2a1 : reg n2 a1 = memLoad32 M (xp + BitVec.ofNat 32 (4 * i)) := by rw [u2.regs, f1]
  have k2 : ∀ q, q ≠ a0 → q ≠ a1 → reg n2 q = reg n q := fun q q0 q1 => by
    rw [u2.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q0, q1]
  obtain ⟨n3, c3, u3, a03, a13, sp3, fr3, mem3⟩ := u2'.bsubCall hc hb (even_at P hP 0xFFFF0FEE (by decide))
    lsm8_at_23e lsm8_at_242 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P hP (0x23E + 8) (by decide))
    (by rw [k2 sp (by decide) (by decide), rsp]) hF sFB
  rw [g2a0, g2a1, k2 a2 (by decide) (by decide), ra2] at a03 a13
  have hc3 : CodeIn n3.mem P lincombShiftMod8Code := fun j hj => by
    rw [mem3 _ (sFC.subR (c := j) (l := 1) (by omega))]; exact hc j hj
  have k3 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → reg n3 q = reg n q := fun q q0 q1 q2 q3 q4 qr =>
    by rw [fr3 q q0 q1 q2 q3 q4 qr, k2 q q0 q1]
  have ed : reg n3 (8 : Fin 32) + 0 = D + BitVec.ofNat 32 (4 * i) := by
    rw [k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rd, add_lit_zero]
  obtain ⟨n4, c4, u4⟩ := St.block lm8SubTail u3 hc3 lm8SubTail_end
    (lm8SubTail_ok (by rw [ed]; exact aligned_add hD (by omega)) (by rw [ed]; exact sDC))
  obtain ⟨em4, t2, tnp, txp, td, tc, tk⟩ := lm8SubTail_run (M := n3.mem) (f := reg n3) u3.zero
  have u4' := u4.self
  rw [em4, ed, a03] at u4'
  have g4 : ∀ q, reg n4 q = (runBlock lm8SubTail (n3.mem, reg n3)).2 q := u4.regs
  have hc4 := CodeIn.store32 (v := bsubD (memLoad32 M (np + BitVec.ofNat 32 (4 * i)))
    (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) b) hc3 sDC
  have ec : reg n4 (9 : Fin 32) = BitVec.ofNat 32 (8 - (i + 1)) := by
    rw [g4, tc, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rc, cnt8_dec i hi]
  have hb4 : branchTaken .bne (reg n4 (9 : Fin 32)) (reg n4 x0) = decide (i + 1 < 8) := by
    rw [ec, u4'.zero]; exact cnt8_ne i hi
  have post : ∀ n5 : Machine, (∀ q, reg n5 q = reg n4 q) →
      reg n5 a2 = bsubB (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i)))
        (bsubD (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) b) ∧
      reg n5 sp = F ∧ reg n5 (21 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n5 (23 : Fin 32) = xp + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n5 (8 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n5 (9 : Fin 32) = BitVec.ofNat 32 (8 - (i + 1)) ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (21 : Fin 32) → q ≠ (23 : Fin 32) →
        q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → reg n5 q = reg n q := fun n5 h5 => by
    refine ⟨by rw [h5, g4, t2, a13], by rw [h5, g4, tk _ (by decide) (by decide) (by decide) (by decide) (by decide), sp3],
      ?_, ?_, ?_, by rw [h5, ec], fun q q0 q1 q2 q3 q4 qr qnp qxp qd qc => ?_⟩
    · rw [h5, g4, tnp, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rnp, ptr4]
    · rw [h5, g4, txp, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rxp, ptr4]
    · rw [h5, g4, td, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rd, ptr4]
    · rw [h5, g4, tk q q2 qnp qxp qd qc, k3 q q0 q1 q2 q3 q4 qr]
  by_cases hl : i + 1 < 8
  · obtain ⟨n5, d5, u5⟩ := u4'.taken hc4 0x236 lsm8_at_252 (by decide) (by rw [hb4]; exact decide_eq_true hl)
    exact ⟨n5, n3.mem, .cons d1 (.cons d2 (c3.trans (c4.trans (.single d5)))), by rw [ite_eq_left hl]; exact u5.self,
      mem3, post n5 u5.regs⟩
  · obtain ⟨n5, d5, u5⟩ := u4'.notTaken hc4 0x254 lsm8_at_252 (by decide) (by rw [hb4]; exact decide_eq_false hl)
    exact ⟨n5, n3.mem, .cons d1 (.cons d2 (c3.trans (c4.trans (.single d5)))), by rw [ite_eq_right hl]; exact u5.self,
      mem3, post n5 u5.regs⟩

set_option exponentiation.threshold 400 in
/-- **The subtraction**, from round `i` to its end at 0x254: the buffer at
`D` gets the modulus minus `x`, and `a2` the borrow out as a mask. -/
theorem lm8_sub_loop {P F np xp D : Word} {M0 : Word → BitVec 8} (hP : P.toNat % 2 = 0) (hF : F.toNat % 4 = 0)
    (hnp : np.toNat % 4 = 0) (hxp : xp.toNat % 4 = 0) (hD : D.toNat % 4 = 0) (hDw : D.toNat + 32 ≤ 2 ^ 32)
    (sFN : Sep (F + 0xFFFFFFFC) 4 np 32) (sFX : Sep (F + 0xFFFFFFFC) 4 xp 32) (sFD : Sep (F + 0xFFFFFFFC) 4 D 32)
    (sDN : Sep D 32 np 32) (sDX : Sep D 32 xp 32)
    (sFB : Sep (F + 0xFFFFFFFC) 4 (lm8Bsub P) borrowingSubCode.length)
    (sFC : Sep (F + 0xFFFFFFFC) 4 P lincombShiftMod8Code.length)
    (sDB : Sep D 32 (lm8Bsub P) borrowingSubCode.length) (sDC : Sep D 32 P lincombShiftMod8Code.length) :
    ∀ m i, i + m + 1 = 8 → ∀ {M : Word → BitVec 8} {n : Machine} {b : Word},
      St M P n 0x236 (reg n) → CodeIn M P lincombShiftMod8Code → CodeIn M (lm8Bsub P) borrowingSubCode →
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 32 x 1 → M x = M0 x) → (b = 0 ∨ b = 0xFFFFFFFF) →
      accV M0 np i + 2 ^ (32 * i) * maskBit b = accV M0 xp i + accV M D i →
      reg n sp = F → reg n (21 : Fin 32) = np + BitVec.ofNat 32 (4 * i) →
      reg n (23 : Fin 32) = xp + BitVec.ofNat 32 (4 * i) → reg n (8 : Fin 32) = D + BitVec.ofNat 32 (4 * i) →
      reg n (9 : Fin 32) = BitVec.ofNat 32 (8 - i) → reg n a2 = b →
      ∃ n' M', Steps n n' ∧ St M' P n' 0x254 (reg n') ∧ CodeIn M' P lincombShiftMod8Code ∧
        (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 32 x 1 → M' x = M0 x) ∧
        (reg n' a2 = 0 ∨ reg n' a2 = 0xFFFFFFFF) ∧
        accV M0 np 8 + 2 ^ (32 * 8) * maskBit (reg n' a2) = accV M0 xp 8 + accV M' D 8 ∧
        reg n' sp = F ∧
        ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (21 : Fin 32) → q ≠ (23 : Fin 32) →
          q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → reg n' q = reg n q := by
  have step : ∀ i, i < 8 → ∀ {M : Word → BitVec 8} {n : Machine} {b : Word},
      St M P n 0x236 (reg n) → CodeIn M P lincombShiftMod8Code → CodeIn M (lm8Bsub P) borrowingSubCode →
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 32 x 1 → M x = M0 x) → (b = 0 ∨ b = 0xFFFFFFFF) →
      accV M0 np i + 2 ^ (32 * i) * maskBit b = accV M0 xp i + accV M D i →
      reg n sp = F → reg n (21 : Fin 32) = np + BitVec.ofNat 32 (4 * i) →
      reg n (23 : Fin 32) = xp + BitVec.ofNat 32 (4 * i) → reg n (8 : Fin 32) = D + BitVec.ofNat 32 (4 * i) →
      reg n (9 : Fin 32) = BitVec.ofNat 32 (8 - i) → reg n a2 = b →
      ∃ n' M', Steps n n' ∧ St M' P n' (if i + 1 < 8 then 0x236 else 0x254) (reg n') ∧
        CodeIn M' P lincombShiftMod8Code ∧ CodeIn M' (lm8Bsub P) borrowingSubCode ∧
        (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 32 x 1 → M' x = M0 x) ∧
        (reg n' a2 = 0 ∨ reg n' a2 = 0xFFFFFFFF) ∧
        accV M0 np (i + 1) + 2 ^ (32 * (i + 1)) * maskBit (reg n' a2) = accV M0 xp (i + 1) + accV M' D (i + 1) ∧
        reg n' sp = F ∧ reg n' (21 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (23 : Fin 32) = xp + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (8 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (9 : Fin 32) = BitVec.ofNat 32 (8 - (i + 1)) ∧
        ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (21 : Fin 32) → q ≠ (23 : Fin 32) →
          q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → reg n' q = reg n q := by
    intro i hi M n b s hc hb hfr hbm hv rsp rnp rxp rd rc ra2
    obtain ⟨n1, Mb, c1, u1, hMb, e2, esp, enp, exp, ed, ec, fr⟩ := lm8_sub_iter (i := i) s hc hb hP hi hF hnp hxp hD
      sFB sFC (sDC.sub (by omega)) rsp rnp rxp rd rc ra2
    have eA : memLoad32 M (np + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (np + BitVec.ofNat 32 (4 * i)) :=
      load_frame2 hfr (sFN.subR (by omega)) (sDN.subR (by omega))
    have eN : memLoad32 M (xp + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i)) :=
      load_frame2 hfr (sFX.subR (by omega)) (sDX.subR (by omega))
    rw [eA, eN] at u1 e2
    obtain ⟨bv, bm⟩ := bsub_val (memLoad32 M0 (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i)))
      b hbm
    have hDb : CodeIn Mb (lm8Bsub P) borrowingSubCode := fun j hj => by
      rw [hMb _ (sFB.subR (c := j) (l := 1) (by omega))]; exact hb j hj
    have hCb : CodeIn Mb P lincombShiftMod8Code := fun j hj => by
      rw [hMb _ (sFC.subR (c := j) (l := 1) (by omega))]; exact hc j hj
    refine ⟨n1, _, c1, u1, CodeIn.store32 hCb (sDC.sub (by omega)), CodeIn.store32 hDb (sDB.sub (by omega)),
      fun x hx hd => ?_, by rw [e2]; exact bm, ?_, esp, enp, exp, ed, ec, fr⟩
    · rw [memStore32_get_sep (hd.sub (c := 4 * i) (l := 4) (by omega)), hMb x hx, hfr x hx hd]
    · have hA : accV (memStore32 Mb (D + BitVec.ofNat 32 (4 * i)) (bsubD (memLoad32 M0 (np + BitVec.ofNat 32 (4 * i)))
          (memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i))) b)) D (i + 1) = accV M D i +
          (bsubD (memLoad32 M0 (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i))) b).toNat *
            2 ^ (32 * i) := by
        rw [accV_succ1, accV_store_above (by omega) i (Nat.le_refl i), memLoad32_store32_same]
        congr 1
        exact accV_congr i fun j hj => memLoad32_congr fun q hq =>
          hMb _ ((sFD.subR (c := 4 * j) (l := 4) (by omega)).subR (c := q) (l := 1) (by omega))
      rw [hA, accV_succ1, accV_succ1, pow32_succ, e2]
      exact sub_arith hv bv
  intro m
  induction m with
  | zero =>
    intro i hi M n b s hc hb hfr hbm hv rsp rnp rxp rd rc ra2
    have i11 : i = 7 := Nat.succ.inj hi
    subst i11
    obtain ⟨n1, M1, c1, u1, hc1, _, hf1, hm1, hv1, sp1, _, _, _, _, fr⟩ :=
      step 7 (by decide) s hc hb hfr hbm hv rsp rnp rxp rd rc ra2
    exact ⟨n1, M1, c1, u1, hc1, hf1, hm1, hv1, sp1, fr⟩
  | succ m ih =>
    intro i hi M n b s hc hb hfr hbm hv rsp rnp rxp rd rc ra2
    have hl : i + 1 < 8 := sel_lt1 hi
    obtain ⟨n1, M1, c1, u1, hc1, hb1, hf1, hm1, hv1, sp1, enp, exp, ed, ec, fr⟩ :=
      step i (Nat.lt_trans (Nat.lt_succ_self i) hl) s hc hb hfr hbm hv rsp rnp rxp rd rc ra2
    rw [ite_eq_left hl] at u1
    obtain ⟨n', M', c', u', hc', hf', hm', hv', sp', fr'⟩ :=
      ih (i + 1) (sel_succ hi) u1 hc1 hb1 hf1 hm1 hv1 sp1 enp exp ed ec rfl
    exact ⟨n', M', c1.trans c', u', hc', hf', hm', hv', sp', fun q q0 q1 q2 q3 q4 qr qnp qxp qd qc => by
      rw [fr' q q0 q1 q2 q3 q4 qr qnp qxp qd qc, fr q q0 q1 q2 q3 q4 qr qnp qxp qd qc]⟩




/-! ## The subtraction `x - m·mf`, from 0x18E to 0x1EC -/
/-- The end of a subtraction round, from 0x19E: keep the borrow, store the
difference, and advance the pointers and the count. -/
def lm8S1Tail : List BInstr :=
  [.alu .add (20 : Fin 32) x0 a1, .aluImm .add (9 : Fin 32) (9 : Fin 32) 4, .sw (25 : Fin 32) a0 0,
   .aluImm .add (24 : Fin 32) (24 : Fin 32) 4, .aluImm .add (25 : Fin 32) (25 : Fin 32) 4,
   .aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF]

section
set_option maxRecDepth 20000
theorem lm8S1Tail_end : blockEnd lincombShiftMod8Code 0x19E lm8S1Tail = some 0x1AC := by decide
end

set_option maxRecDepth 20000 in
theorem lm8S1Tail_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lm8S1Tail (M, f)).1 = memStore32 M (f (25 : Fin 32) + 0) (f a0) ∧
    (runBlock lm8S1Tail (M, f)).2 (20 : Fin 32) = f a1 ∧
    (runBlock lm8S1Tail (M, f)).2 (9 : Fin 32) = f (9 : Fin 32) + 4 ∧
    (runBlock lm8S1Tail (M, f)).2 (24 : Fin 32) = f (24 : Fin 32) + 4 ∧
    (runBlock lm8S1Tail (M, f)).2 (25 : Fin 32) = f (25 : Fin 32) + 4 ∧
    (runBlock lm8S1Tail (M, f)).2 (8 : Fin 32) = f (8 : Fin 32) + 0xFFFFFFFF ∧
    ∀ q, q ≠ (20 : Fin 32) → q ≠ (9 : Fin 32) → q ≠ (24 : Fin 32) → q ≠ (25 : Fin 32) → q ≠ (8 : Fin 32) →
      (runBlock lm8S1Tail (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, lm8S1Tail]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun q q2 qnp qxp qd qc => ?_⟩
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte, hz]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q2, qnp, qxp, qd, qc]

theorem lm8S1Tail_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h : (f (25 : Fin 32) + 0).toNat % 4 = 0) (hs : Sep (f (25 : Fin 32) + 0) 4 base len) :
    BlockOk base len lm8S1Tail (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, lm8S1Tail, upd, ↓reduceIte, and_true, true_and]
  exact ⟨h, hs⟩

/-- **One round of the subtraction**, from 0x18E: subtract limb `i` of `x`
and the borrow from limb `i` of the modulus at `np`, and store the
difference at limb `i` of the buffer at `D`. `borrowing_sub` also writes
the word below `sp`. -/
theorem lm8_s1_iter {M : Word → BitVec 8} {P F np xp D b : Word} {n : Machine} {i : Nat}
    (s : St M P n 0x18E (reg n)) (hc : CodeIn M P lincombShiftMod8Code) (hb : CodeIn M (lm8Bsub P) borrowingSubCode)
    (hP : P.toNat % 2 = 0) (hi : i < 8) (hF : F.toNat % 4 = 0) (hnp : np.toNat % 4 = 0)
    (hxp : xp.toNat % 4 = 0) (hD : D.toNat % 4 = 0)
    (sFB : Sep (F + 0xFFFFFFFC) 4 (lm8Bsub P) borrowingSubCode.length)
    (sFC : Sep (F + 0xFFFFFFFC) 4 P lincombShiftMod8Code.length)
    (sDC : Sep (D + BitVec.ofNat 32 (4 * i)) 4 P lincombShiftMod8Code.length)
    (rsp : reg n sp = F) (rnp : reg n (9 : Fin 32) = np + BitVec.ofNat 32 (4 * i))
    (rxp : reg n (24 : Fin 32) = xp + BitVec.ofNat 32 (4 * i)) (rd : reg n (25 : Fin 32) = D + BitVec.ofNat 32 (4 * i))
    (rc : reg n (8 : Fin 32) = BitVec.ofNat 32 (8 - i)) (rb : reg n (20 : Fin 32) = b) :
    ∃ n' Mb, Steps n n' ∧
      St (memStore32 Mb (D + BitVec.ofNat 32 (4 * i))
          (bsubD (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) b))
        P n' (if i + 1 < 8 then 0x18E else 0x1AE) (reg n') ∧
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Mb x = M x) ∧
      reg n' (20 : Fin 32) = bsubB (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i)))
        (bsubD (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) b) ∧
      reg n' sp = F ∧ reg n' (9 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (24 : Fin 32) = xp + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (25 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (8 : Fin 32) = BitVec.ofNat 32 (8 - (i + 1)) ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ (20 : Fin 32) → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (9 : Fin 32) → q ≠ (24 : Fin 32) →
        q ≠ (25 : Fin 32) → q ≠ (8 : Fin 32) → reg n' q = reg n q := by
  have hz := s.zero
  obtain ⟨n1, d1, u1⟩ := s.lw hc lsm8_at_18e (off' := 0x190) (by decide)
    (by rw [rnp, add_lit_zero]; exact aligned_add hnp (by omega))
  obtain ⟨n2, d2, u2⟩ := u1.lw hc lsm8_at_190 (off' := 0x194) (by decide)
    (by rw [upd_ne (by decide) (by decide), rxp, add_lit_zero]; exact aligned_add hxp (by omega))
  rw [rnp, add_lit_zero] at u2
  have f0 : upd (upd (reg n) a0 (memLoad32 M (np + BitVec.ofNat 32 (4 * i)))) a1
      (memLoad32 M (upd (reg n) a0 (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (24 : Fin 32) + 0)) a0 =
      memLoad32 M (np + BitVec.ofNat 32 (4 * i)) := by simp +decide [upd]
  have f1 : upd (upd (reg n) a0 (memLoad32 M (np + BitVec.ofNat 32 (4 * i)))) a1
      (memLoad32 M (upd (reg n) a0 (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (24 : Fin 32) + 0)) a1 =
      memLoad32 M (xp + BitVec.ofNat 32 (4 * i)) := by
    simp +decide only [upd, ↓reduceIte]; rw [rxp, add_lit_zero]
  have u2' := u2.self
  have g2a0 : reg n2 a0 = memLoad32 M (np + BitVec.ofNat 32 (4 * i)) := by rw [u2.regs, f0]
  have g2a1 : reg n2 a1 = memLoad32 M (xp + BitVec.ofNat 32 (4 * i)) := by rw [u2.regs, f1]
  have k2 : ∀ q, q ≠ a0 → q ≠ a1 → reg n2 q = reg n q := fun q q0 q1 => by
    rw [u2.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q0, q1]
  obtain ⟨n2m, d2m, u2m⟩ := u2'.alu hc lsm8_at_194 (off' := 0x196) (by decide)
  have k2m : ∀ q, q ≠ a2 → reg n2m q = reg n2 q := fun q q2 => by
    rw [u2m.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, u2'.zero]
    · simp [upd, h0, q2]
  have r2a2 : reg n2m a2 = b := by
    rw [u2m.regs, upd_same (by decide), u2'.zero, k2 20 (by decide) (by decide), rb]; exact BitVec.zero_add _
  obtain ⟨n3, c3, u3, a03, a13, sp3, fr3, mem3⟩ := u2m.self.bsubCall hc hb (even_at P hP 0xFFFF0FEE (by decide))
    lsm8_at_196 lsm8_at_19a (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P hP (0x196 + 8) (by decide))
    (by rw [k2m sp (by decide), k2 sp (by decide) (by decide), rsp]) hF sFB
  rw [k2m a0 (by decide), k2m a1 (by decide), r2a2, g2a0, g2a1] at a03 a13
  have hc3 : CodeIn n3.mem P lincombShiftMod8Code := fun j hj => by
    rw [mem3 _ (sFC.subR (c := j) (l := 1) (by omega))]; exact hc j hj
  have k3 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → reg n3 q = reg n q := fun q q0 q1 q2 q3 q4 qr =>
    by rw [fr3 q q0 q1 q2 q3 q4 qr, k2m q q2, k2 q q0 q1]
  have ed : reg n3 (25 : Fin 32) + 0 = D + BitVec.ofNat 32 (4 * i) := by
    rw [k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rd, add_lit_zero]
  obtain ⟨n4, c4, u4⟩ := St.block lm8S1Tail u3 hc3 lm8S1Tail_end
    (lm8S1Tail_ok (by rw [ed]; exact aligned_add hD (by omega)) (by rw [ed]; exact sDC))
  obtain ⟨em4, t2, tnp, txp, td, tc, tk⟩ := lm8S1Tail_run (M := n3.mem) (f := reg n3) u3.zero
  have u4' := u4.self
  rw [em4, ed, a03] at u4'
  have g4 : ∀ q, reg n4 q = (runBlock lm8S1Tail (n3.mem, reg n3)).2 q := u4.regs
  have hc4 := CodeIn.store32 (v := bsubD (memLoad32 M (np + BitVec.ofNat 32 (4 * i)))
    (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) b) hc3 sDC
  have ec : reg n4 (8 : Fin 32) = BitVec.ofNat 32 (8 - (i + 1)) := by
    rw [g4, tc, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rc, cnt8_dec i hi]
  have hb4 : branchTaken .bne (reg n4 (8 : Fin 32)) (reg n4 x0) = decide (i + 1 < 8) := by
    rw [ec, u4'.zero]; exact cnt8_ne i hi
  have post : ∀ n5 : Machine, (∀ q, reg n5 q = reg n4 q) →
      reg n5 (20 : Fin 32) = bsubB (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i)))
        (bsubD (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) b) ∧
      reg n5 sp = F ∧ reg n5 (9 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n5 (24 : Fin 32) = xp + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n5 (25 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n5 (8 : Fin 32) = BitVec.ofNat 32 (8 - (i + 1)) ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ (20 : Fin 32) → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (9 : Fin 32) → q ≠ (24 : Fin 32) →
        q ≠ (25 : Fin 32) → q ≠ (8 : Fin 32) → reg n5 q = reg n q := fun n5 h5 => by
    refine ⟨by rw [h5, g4, t2, a13], by rw [h5, g4, tk _ (by decide) (by decide) (by decide) (by decide) (by decide), sp3],
      ?_, ?_, ?_, by rw [h5, ec], fun q q0 q1 q2 q20 q3 q4 qr qnp qxp qd qc => ?_⟩
    · rw [h5, g4, tnp, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rnp, ptr4]
    · rw [h5, g4, txp, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rxp, ptr4]
    · rw [h5, g4, td, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rd, ptr4]
    · rw [h5, g4, tk q q20 qnp qxp qd qc, k3 q q0 q1 q2 q3 q4 qr]
  by_cases hl : i + 1 < 8
  · obtain ⟨n5, d5, u5⟩ := u4'.taken hc4 0x18E lsm8_at_1ac (by decide) (by rw [hb4]; exact decide_eq_true hl)
    exact ⟨n5, n3.mem, .cons d1 (.cons d2 (.cons d2m (c3.trans (c4.trans (.single d5))))), by rw [ite_eq_left hl]; exact u5.self,
      mem3, post n5 u5.regs⟩
  · obtain ⟨n5, d5, u5⟩ := u4'.notTaken hc4 0x1AE lsm8_at_1ac (by decide) (by rw [hb4]; exact decide_eq_false hl)
    exact ⟨n5, n3.mem, .cons d1 (.cons d2 (.cons d2m (c3.trans (c4.trans (.single d5))))), by rw [ite_eq_right hl]; exact u5.self,
      mem3, post n5 u5.regs⟩

set_option exponentiation.threshold 400 in
/-- **The subtraction**, from round `i` to its end at 0x1AE: the buffer at
`D` gets the modulus minus `x`, and `a2` the borrow out as a mask. -/
theorem lm8_s1_loop {P F np xp D : Word} {M0 : Word → BitVec 8} {z : Nat} (hP : P.toNat % 2 = 0) (hF : F.toNat % 4 = 0)
    (hnp : np.toNat % 4 = 0) (hxp : xp.toNat % 4 = 0) (hD : D.toNat % 4 = 0) (hDw : D.toNat + 32 ≤ 2 ^ 32)
    (sFN : Sep (F + 0xFFFFFFFC) 4 np 32) (sFX : Sep (F + 0xFFFFFFFC) 4 xp 32) (sFD : Sep (F + 0xFFFFFFFC) 4 D 32)
    (sDN : Sep D 32 np 32) (sDX : Sep D 32 xp 32)
    (sFB : Sep (F + 0xFFFFFFFC) 4 (lm8Bsub P) borrowingSubCode.length)
    (sFC : Sep (F + 0xFFFFFFFC) 4 P lincombShiftMod8Code.length)
    (sDB : Sep D 32 (lm8Bsub P) borrowingSubCode.length) (sDC : Sep D 32 P lincombShiftMod8Code.length) :
    ∀ m i, i + m + 1 = 8 → ∀ {M : Word → BitVec 8} {n : Machine} {b : Word},
      St M P n 0x18E (reg n) → CodeIn M P lincombShiftMod8Code → CodeIn M (lm8Bsub P) borrowingSubCode →
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 32 x 1 → M x = M0 x) → (b = 0 ∨ b = 0xFFFFFFFF) →
      accV M0 np i + 2 ^ (32 * i) * maskBit b = accV M0 xp i + accV M D i + z →
      reg n sp = F → reg n (9 : Fin 32) = np + BitVec.ofNat 32 (4 * i) →
      reg n (24 : Fin 32) = xp + BitVec.ofNat 32 (4 * i) → reg n (25 : Fin 32) = D + BitVec.ofNat 32 (4 * i) →
      reg n (8 : Fin 32) = BitVec.ofNat 32 (8 - i) → reg n (20 : Fin 32) = b →
      ∃ n' M', Steps n n' ∧ St M' P n' 0x1AE (reg n') ∧ CodeIn M' P lincombShiftMod8Code ∧
        (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 32 x 1 → M' x = M0 x) ∧
        (reg n' (20 : Fin 32) = 0 ∨ reg n' (20 : Fin 32) = 0xFFFFFFFF) ∧
        accV M0 np 8 + 2 ^ (32 * 8) * maskBit (reg n' (20 : Fin 32)) = accV M0 xp 8 + accV M' D 8 + z ∧
        reg n' sp = F ∧
        ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ (20 : Fin 32) → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (9 : Fin 32) → q ≠ (24 : Fin 32) →
          q ≠ (25 : Fin 32) → q ≠ (8 : Fin 32) → reg n' q = reg n q := by
  have step : ∀ i, i < 8 → ∀ {M : Word → BitVec 8} {n : Machine} {b : Word},
      St M P n 0x18E (reg n) → CodeIn M P lincombShiftMod8Code → CodeIn M (lm8Bsub P) borrowingSubCode →
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 32 x 1 → M x = M0 x) → (b = 0 ∨ b = 0xFFFFFFFF) →
      accV M0 np i + 2 ^ (32 * i) * maskBit b = accV M0 xp i + accV M D i + z →
      reg n sp = F → reg n (9 : Fin 32) = np + BitVec.ofNat 32 (4 * i) →
      reg n (24 : Fin 32) = xp + BitVec.ofNat 32 (4 * i) → reg n (25 : Fin 32) = D + BitVec.ofNat 32 (4 * i) →
      reg n (8 : Fin 32) = BitVec.ofNat 32 (8 - i) → reg n (20 : Fin 32) = b →
      ∃ n' M', Steps n n' ∧ St M' P n' (if i + 1 < 8 then 0x18E else 0x1AE) (reg n') ∧
        CodeIn M' P lincombShiftMod8Code ∧ CodeIn M' (lm8Bsub P) borrowingSubCode ∧
        (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 32 x 1 → M' x = M0 x) ∧
        (reg n' (20 : Fin 32) = 0 ∨ reg n' (20 : Fin 32) = 0xFFFFFFFF) ∧
        accV M0 np (i + 1) + 2 ^ (32 * (i + 1)) * maskBit (reg n' (20 : Fin 32)) = accV M0 xp (i + 1) + accV M' D (i + 1) + z ∧
        reg n' sp = F ∧ reg n' (9 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (24 : Fin 32) = xp + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (25 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (8 : Fin 32) = BitVec.ofNat 32 (8 - (i + 1)) ∧
        ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ (20 : Fin 32) → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (9 : Fin 32) → q ≠ (24 : Fin 32) →
          q ≠ (25 : Fin 32) → q ≠ (8 : Fin 32) → reg n' q = reg n q := by
    intro i hi M n b s hc hb hfr hbm hv rsp rnp rxp rd rc rb
    obtain ⟨n1, Mb, c1, u1, hMb, e2, esp, enp, exp, ed, ec, fr⟩ := lm8_s1_iter (i := i) s hc hb hP hi hF hnp hxp hD
      sFB sFC (sDC.sub (by omega)) rsp rnp rxp rd rc rb
    have eA : memLoad32 M (np + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (np + BitVec.ofNat 32 (4 * i)) :=
      load_frame2 hfr (sFN.subR (by omega)) (sDN.subR (by omega))
    have eN : memLoad32 M (xp + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i)) :=
      load_frame2 hfr (sFX.subR (by omega)) (sDX.subR (by omega))
    rw [eA, eN] at u1 e2
    obtain ⟨bv, bm⟩ := bsub_val (memLoad32 M0 (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i)))
      b hbm
    have hDb : CodeIn Mb (lm8Bsub P) borrowingSubCode := fun j hj => by
      rw [hMb _ (sFB.subR (c := j) (l := 1) (by omega))]; exact hb j hj
    have hCb : CodeIn Mb P lincombShiftMod8Code := fun j hj => by
      rw [hMb _ (sFC.subR (c := j) (l := 1) (by omega))]; exact hc j hj
    refine ⟨n1, _, c1, u1, CodeIn.store32 hCb (sDC.sub (by omega)), CodeIn.store32 hDb (sDB.sub (by omega)),
      fun x hx hd => ?_, by rw [e2]; exact bm, ?_, esp, enp, exp, ed, ec, fr⟩
    · rw [memStore32_get_sep (hd.sub (c := 4 * i) (l := 4) (by omega)), hMb x hx, hfr x hx hd]
    · have hA : accV (memStore32 Mb (D + BitVec.ofNat 32 (4 * i)) (bsubD (memLoad32 M0 (np + BitVec.ofNat 32 (4 * i)))
          (memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i))) b)) D (i + 1) = accV M D i +
          (bsubD (memLoad32 M0 (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i))) b).toNat *
            2 ^ (32 * i) := by
        rw [accV_succ1, accV_store_above (by omega) i (Nat.le_refl i), memLoad32_store32_same]
        congr 1
        exact accV_congr i fun j hj => memLoad32_congr fun q hq =>
          hMb _ ((sFD.subR (c := 4 * j) (l := 4) (by omega)).subR (c := q) (l := 1) (by omega))
      rw [hA, accV_succ1, accV_succ1, pow32_succ, e2]
      exact sub_arith_z hv bv
  intro m
  induction m with
  | zero =>
    intro i hi M n b s hc hb hfr hbm hv rsp rnp rxp rd rc rb
    have i11 : i = 7 := Nat.succ.inj hi
    subst i11
    obtain ⟨n1, M1, c1, u1, hc1, _, hf1, hm1, hv1, sp1, _, _, _, _, fr⟩ :=
      step 7 (by decide) s hc hb hfr hbm hv rsp rnp rxp rd rc rb
    exact ⟨n1, M1, c1, u1, hc1, hf1, hm1, hv1, sp1, fr⟩
  | succ m ih =>
    intro i hi M n b s hc hb hfr hbm hv rsp rnp rxp rd rc rb
    have hl : i + 1 < 8 := sel_lt1 hi
    obtain ⟨n1, M1, c1, u1, hc1, hb1, hf1, hm1, hv1, sp1, enp, exp, ed, ec, fr⟩ :=
      step i (Nat.lt_trans (Nat.lt_succ_self i) hl) s hc hb hfr hbm hv rsp rnp rxp rd rc rb
    rw [ite_eq_left hl] at u1
    obtain ⟨n', M', c', u', hc', hf', hm', hv', sp', fr'⟩ :=
      ih (i + 1) (sel_succ hi) u1 hc1 hb1 hf1 hm1 hv1 sp1 enp exp ed ec rfl
    exact ⟨n', M', c1.trans c', u', hc', hf', hm', hv', sp', fun q q0 q1 q2 q20 q3 q4 qr qnp qxp qd qc => by
      rw [fr' q q0 q1 q2 q20 q3 q4 qr qnp qxp qd qc, fr q q0 q1 q2 q20 q3 q4 qr qnp qxp qd qc]⟩

/-- The end of a subtraction round, from 0x1DE: keep the borrow, store the
difference, and advance the pointers and the count. -/
def lm8S2Tail : List BInstr :=
  [.alu .add (20 : Fin 32) x0 a1, .aluImm .add (24 : Fin 32) (24 : Fin 32) 4, .sw (9 : Fin 32) a0 0,
   .aluImm .add (21 : Fin 32) (21 : Fin 32) 4, .aluImm .add (9 : Fin 32) (9 : Fin 32) 4,
   .aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF]

section
set_option maxRecDepth 20000
theorem lm8S2Tail_end : blockEnd lincombShiftMod8Code 0x1DE lm8S2Tail = some 0x1EA := by decide
end

set_option maxRecDepth 20000 in
theorem lm8S2Tail_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lm8S2Tail (M, f)).1 = memStore32 M (f (9 : Fin 32) + 0) (f a0) ∧
    (runBlock lm8S2Tail (M, f)).2 (20 : Fin 32) = f a1 ∧
    (runBlock lm8S2Tail (M, f)).2 (24 : Fin 32) = f (24 : Fin 32) + 4 ∧
    (runBlock lm8S2Tail (M, f)).2 (21 : Fin 32) = f (21 : Fin 32) + 4 ∧
    (runBlock lm8S2Tail (M, f)).2 (9 : Fin 32) = f (9 : Fin 32) + 4 ∧
    (runBlock lm8S2Tail (M, f)).2 (8 : Fin 32) = f (8 : Fin 32) + 0xFFFFFFFF ∧
    ∀ q, q ≠ (20 : Fin 32) → q ≠ (24 : Fin 32) → q ≠ (21 : Fin 32) → q ≠ (9 : Fin 32) → q ≠ (8 : Fin 32) →
      (runBlock lm8S2Tail (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, lm8S2Tail]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun q q2 qnp qxp qd qc => ?_⟩
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte, hz]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q2, qnp, qxp, qd, qc]

theorem lm8S2Tail_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h : (f (9 : Fin 32) + 0).toNat % 4 = 0) (hs : Sep (f (9 : Fin 32) + 0) 4 base len) :
    BlockOk base len lm8S2Tail (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, lm8S2Tail, upd, ↓reduceIte, and_true, true_and]
  exact ⟨h, hs⟩

/-- **One round of the subtraction**, from 0x1CC: subtract limb `i` of `x`
and the borrow from limb `i` of the modulus at `np`, and store the
difference at limb `i` of the buffer at `D`. `borrowing_sub` also writes
the word below `sp`. -/
theorem lm8_s2_iter {M : Word → BitVec 8} {P F np xp D b : Word} {n : Machine} {i : Nat}
    (s : St M P n 0x1CC (reg n)) (hc : CodeIn M P lincombShiftMod8Code) (hb : CodeIn M (lm8Bsub P) borrowingSubCode)
    (hP : P.toNat % 2 = 0) (hi : i < 2) (hF : F.toNat % 4 = 0) (hnp : np.toNat % 4 = 0)
    (hxp : xp.toNat % 4 = 0) (hD : D.toNat % 4 = 0)
    (sFB : Sep (F + 0xFFFFFFFC) 4 (lm8Bsub P) borrowingSubCode.length)
    (sFC : Sep (F + 0xFFFFFFFC) 4 P lincombShiftMod8Code.length)
    (sDC : Sep (D + BitVec.ofNat 32 (4 * i)) 4 P lincombShiftMod8Code.length)
    (rsp : reg n sp = F) (rnp : reg n (24 : Fin 32) = np + BitVec.ofNat 32 (4 * i))
    (rxp : reg n (21 : Fin 32) = xp + BitVec.ofNat 32 (4 * i)) (rd : reg n (9 : Fin 32) = D + BitVec.ofNat 32 (4 * i))
    (rc : reg n (8 : Fin 32) = BitVec.ofNat 32 (2 - i)) (rb : reg n (20 : Fin 32) = b) :
    ∃ n' Mb, Steps n n' ∧
      St (memStore32 Mb (D + BitVec.ofNat 32 (4 * i))
          (bsubD (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) b))
        P n' (if i + 1 < 2 then 0x1CC else 0x1EC) (reg n') ∧
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Mb x = M x) ∧
      reg n' (20 : Fin 32) = bsubB (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i)))
        (bsubD (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) b) ∧
      reg n' sp = F ∧ reg n' (24 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (21 : Fin 32) = xp + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (9 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (8 : Fin 32) = BitVec.ofNat 32 (2 - (i + 1)) ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ (20 : Fin 32) → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (24 : Fin 32) → q ≠ (21 : Fin 32) →
        q ≠ (9 : Fin 32) → q ≠ (8 : Fin 32) → reg n' q = reg n q := by
  have hz := s.zero
  obtain ⟨n1, d1, u1⟩ := s.lw hc lsm8_at_1cc (off' := 0x1D0) (by decide)
    (by rw [rnp, add_lit_zero]; exact aligned_add hnp (by omega))
  obtain ⟨n2, d2, u2⟩ := u1.lw hc lsm8_at_1d0 (off' := 0x1D4) (by decide)
    (by rw [upd_ne (by decide) (by decide), rxp, add_lit_zero]; exact aligned_add hxp (by omega))
  rw [rnp, add_lit_zero] at u2
  have f0 : upd (upd (reg n) a0 (memLoad32 M (np + BitVec.ofNat 32 (4 * i)))) a1
      (memLoad32 M (upd (reg n) a0 (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (21 : Fin 32) + 0)) a0 =
      memLoad32 M (np + BitVec.ofNat 32 (4 * i)) := by simp +decide [upd]
  have f1 : upd (upd (reg n) a0 (memLoad32 M (np + BitVec.ofNat 32 (4 * i)))) a1
      (memLoad32 M (upd (reg n) a0 (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (21 : Fin 32) + 0)) a1 =
      memLoad32 M (xp + BitVec.ofNat 32 (4 * i)) := by
    simp +decide only [upd, ↓reduceIte]; rw [rxp, add_lit_zero]
  have u2' := u2.self
  have g2a0 : reg n2 a0 = memLoad32 M (np + BitVec.ofNat 32 (4 * i)) := by rw [u2.regs, f0]
  have g2a1 : reg n2 a1 = memLoad32 M (xp + BitVec.ofNat 32 (4 * i)) := by rw [u2.regs, f1]
  have k2 : ∀ q, q ≠ a0 → q ≠ a1 → reg n2 q = reg n q := fun q q0 q1 => by
    rw [u2.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q0, q1]
  obtain ⟨n2m, d2m, u2m⟩ := u2'.alu hc lsm8_at_1d4 (off' := 0x1D6) (by decide)
  have k2m : ∀ q, q ≠ a2 → reg n2m q = reg n2 q := fun q q2 => by
    rw [u2m.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, u2'.zero]
    · simp [upd, h0, q2]
  have r2a2 : reg n2m a2 = b := by
    rw [u2m.regs, upd_same (by decide), u2'.zero, k2 20 (by decide) (by decide), rb]; exact BitVec.zero_add _
  obtain ⟨n3, c3, u3, a03, a13, sp3, fr3, mem3⟩ := u2m.self.bsubCall hc hb (even_at P hP 0xFFFF0FEE (by decide))
    lsm8_at_1d6 lsm8_at_1da (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P hP (0x1D6 + 8) (by decide))
    (by rw [k2m sp (by decide), k2 sp (by decide) (by decide), rsp]) hF sFB
  rw [k2m a0 (by decide), k2m a1 (by decide), r2a2, g2a0, g2a1] at a03 a13
  have hc3 : CodeIn n3.mem P lincombShiftMod8Code := fun j hj => by
    rw [mem3 _ (sFC.subR (c := j) (l := 1) (by omega))]; exact hc j hj
  have k3 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → reg n3 q = reg n q := fun q q0 q1 q2 q3 q4 qr =>
    by rw [fr3 q q0 q1 q2 q3 q4 qr, k2m q q2, k2 q q0 q1]
  have ed : reg n3 (9 : Fin 32) + 0 = D + BitVec.ofNat 32 (4 * i) := by
    rw [k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rd, add_lit_zero]
  obtain ⟨n4, c4, u4⟩ := St.block lm8S2Tail u3 hc3 lm8S2Tail_end
    (lm8S2Tail_ok (by rw [ed]; exact aligned_add hD (by omega)) (by rw [ed]; exact sDC))
  obtain ⟨em4, t2, tnp, txp, td, tc, tk⟩ := lm8S2Tail_run (M := n3.mem) (f := reg n3) u3.zero
  have u4' := u4.self
  rw [em4, ed, a03] at u4'
  have g4 : ∀ q, reg n4 q = (runBlock lm8S2Tail (n3.mem, reg n3)).2 q := u4.regs
  have hc4 := CodeIn.store32 (v := bsubD (memLoad32 M (np + BitVec.ofNat 32 (4 * i)))
    (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) b) hc3 sDC
  have ec : reg n4 (8 : Fin 32) = BitVec.ofNat 32 (2 - (i + 1)) := by
    rw [g4, tc, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rc, cnt2_dec i hi]
  have hb4 : branchTaken .bne (reg n4 (8 : Fin 32)) (reg n4 x0) = decide (i + 1 < 2) := by
    rw [ec, u4'.zero]; exact cnt2_ne i hi
  have post : ∀ n5 : Machine, (∀ q, reg n5 q = reg n4 q) →
      reg n5 (20 : Fin 32) = bsubB (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i)))
        (bsubD (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) b) ∧
      reg n5 sp = F ∧ reg n5 (24 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n5 (21 : Fin 32) = xp + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n5 (9 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n5 (8 : Fin 32) = BitVec.ofNat 32 (2 - (i + 1)) ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ (20 : Fin 32) → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (24 : Fin 32) → q ≠ (21 : Fin 32) →
        q ≠ (9 : Fin 32) → q ≠ (8 : Fin 32) → reg n5 q = reg n q := fun n5 h5 => by
    refine ⟨by rw [h5, g4, t2, a13], by rw [h5, g4, tk _ (by decide) (by decide) (by decide) (by decide) (by decide), sp3],
      ?_, ?_, ?_, by rw [h5, ec], fun q q0 q1 q2 q20 q3 q4 qr qnp qxp qd qc => ?_⟩
    · rw [h5, g4, tnp, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rnp, ptr4]
    · rw [h5, g4, txp, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rxp, ptr4]
    · rw [h5, g4, td, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rd, ptr4]
    · rw [h5, g4, tk q q20 qnp qxp qd qc, k3 q q0 q1 q2 q3 q4 qr]
  by_cases hl : i + 1 < 2
  · obtain ⟨n5, d5, u5⟩ := u4'.taken hc4 0x1CC lsm8_at_1ea (by decide) (by rw [hb4]; exact decide_eq_true hl)
    exact ⟨n5, n3.mem, .cons d1 (.cons d2 (.cons d2m (c3.trans (c4.trans (.single d5))))), by rw [ite_eq_left hl]; exact u5.self,
      mem3, post n5 u5.regs⟩
  · obtain ⟨n5, d5, u5⟩ := u4'.notTaken hc4 0x1EC lsm8_at_1ea (by decide) (by rw [hb4]; exact decide_eq_false hl)
    exact ⟨n5, n3.mem, .cons d1 (.cons d2 (.cons d2m (c3.trans (c4.trans (.single d5))))), by rw [ite_eq_right hl]; exact u5.self,
      mem3, post n5 u5.regs⟩

set_option exponentiation.threshold 400 in
/-- **The subtraction**, from round `i` to its end at 0x1EC: the buffer at
`D` gets the modulus minus `x`, and `a2` the borrow out as a mask. -/
theorem lm8_s2_loop {P F np xp D : Word} {M0 : Word → BitVec 8} {z : Nat} (hP : P.toNat % 2 = 0) (hF : F.toNat % 4 = 0)
    (hnp : np.toNat % 4 = 0) (hxp : xp.toNat % 4 = 0) (hD : D.toNat % 4 = 0) (hDw : D.toNat + 8 ≤ 2 ^ 32)
    (sFN : Sep (F + 0xFFFFFFFC) 4 np 8) (sFX : Sep (F + 0xFFFFFFFC) 4 xp 8) (sFD : Sep (F + 0xFFFFFFFC) 4 D 8)
    (sDN : Sep D 8 np 8) (sDX : Sep D 8 xp 8)
    (sFB : Sep (F + 0xFFFFFFFC) 4 (lm8Bsub P) borrowingSubCode.length)
    (sFC : Sep (F + 0xFFFFFFFC) 4 P lincombShiftMod8Code.length)
    (sDB : Sep D 8 (lm8Bsub P) borrowingSubCode.length) (sDC : Sep D 8 P lincombShiftMod8Code.length) :
    ∀ m i, i + m + 1 = 2 → ∀ {M : Word → BitVec 8} {n : Machine} {b : Word},
      St M P n 0x1CC (reg n) → CodeIn M P lincombShiftMod8Code → CodeIn M (lm8Bsub P) borrowingSubCode →
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 8 x 1 → M x = M0 x) → (b = 0 ∨ b = 0xFFFFFFFF) →
      accV M0 np i + 2 ^ (32 * i) * maskBit b = accV M0 xp i + accV M D i + z →
      reg n sp = F → reg n (24 : Fin 32) = np + BitVec.ofNat 32 (4 * i) →
      reg n (21 : Fin 32) = xp + BitVec.ofNat 32 (4 * i) → reg n (9 : Fin 32) = D + BitVec.ofNat 32 (4 * i) →
      reg n (8 : Fin 32) = BitVec.ofNat 32 (2 - i) → reg n (20 : Fin 32) = b →
      ∃ n' M', Steps n n' ∧ St M' P n' 0x1EC (reg n') ∧ CodeIn M' P lincombShiftMod8Code ∧
        (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 8 x 1 → M' x = M0 x) ∧
        (reg n' (20 : Fin 32) = 0 ∨ reg n' (20 : Fin 32) = 0xFFFFFFFF) ∧
        accV M0 np 2 + 2 ^ (32 * 2) * maskBit (reg n' (20 : Fin 32)) = accV M0 xp 2 + accV M' D 2 + z ∧
        reg n' sp = F ∧
        ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ (20 : Fin 32) → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (24 : Fin 32) → q ≠ (21 : Fin 32) →
          q ≠ (9 : Fin 32) → q ≠ (8 : Fin 32) → reg n' q = reg n q := by
  have step : ∀ i, i < 2 → ∀ {M : Word → BitVec 8} {n : Machine} {b : Word},
      St M P n 0x1CC (reg n) → CodeIn M P lincombShiftMod8Code → CodeIn M (lm8Bsub P) borrowingSubCode →
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 8 x 1 → M x = M0 x) → (b = 0 ∨ b = 0xFFFFFFFF) →
      accV M0 np i + 2 ^ (32 * i) * maskBit b = accV M0 xp i + accV M D i + z →
      reg n sp = F → reg n (24 : Fin 32) = np + BitVec.ofNat 32 (4 * i) →
      reg n (21 : Fin 32) = xp + BitVec.ofNat 32 (4 * i) → reg n (9 : Fin 32) = D + BitVec.ofNat 32 (4 * i) →
      reg n (8 : Fin 32) = BitVec.ofNat 32 (2 - i) → reg n (20 : Fin 32) = b →
      ∃ n' M', Steps n n' ∧ St M' P n' (if i + 1 < 2 then 0x1CC else 0x1EC) (reg n') ∧
        CodeIn M' P lincombShiftMod8Code ∧ CodeIn M' (lm8Bsub P) borrowingSubCode ∧
        (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 8 x 1 → M' x = M0 x) ∧
        (reg n' (20 : Fin 32) = 0 ∨ reg n' (20 : Fin 32) = 0xFFFFFFFF) ∧
        accV M0 np (i + 1) + 2 ^ (32 * (i + 1)) * maskBit (reg n' (20 : Fin 32)) = accV M0 xp (i + 1) + accV M' D (i + 1) + z ∧
        reg n' sp = F ∧ reg n' (24 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (21 : Fin 32) = xp + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (9 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (8 : Fin 32) = BitVec.ofNat 32 (2 - (i + 1)) ∧
        ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ (20 : Fin 32) → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (24 : Fin 32) → q ≠ (21 : Fin 32) →
          q ≠ (9 : Fin 32) → q ≠ (8 : Fin 32) → reg n' q = reg n q := by
    intro i hi M n b s hc hb hfr hbm hv rsp rnp rxp rd rc rb
    obtain ⟨n1, Mb, c1, u1, hMb, e2, esp, enp, exp, ed, ec, fr⟩ := lm8_s2_iter (i := i) s hc hb hP hi hF hnp hxp hD
      sFB sFC (sDC.sub (by omega)) rsp rnp rxp rd rc rb
    have eA : memLoad32 M (np + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (np + BitVec.ofNat 32 (4 * i)) :=
      load_frame2 hfr (sFN.subR (by omega)) (sDN.subR (by omega))
    have eN : memLoad32 M (xp + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i)) :=
      load_frame2 hfr (sFX.subR (by omega)) (sDX.subR (by omega))
    rw [eA, eN] at u1 e2
    obtain ⟨bv, bm⟩ := bsub_val (memLoad32 M0 (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i)))
      b hbm
    have hDb : CodeIn Mb (lm8Bsub P) borrowingSubCode := fun j hj => by
      rw [hMb _ (sFB.subR (c := j) (l := 1) (by omega))]; exact hb j hj
    have hCb : CodeIn Mb P lincombShiftMod8Code := fun j hj => by
      rw [hMb _ (sFC.subR (c := j) (l := 1) (by omega))]; exact hc j hj
    refine ⟨n1, _, c1, u1, CodeIn.store32 hCb (sDC.sub (by omega)), CodeIn.store32 hDb (sDB.sub (by omega)),
      fun x hx hd => ?_, by rw [e2]; exact bm, ?_, esp, enp, exp, ed, ec, fr⟩
    · rw [memStore32_get_sep (hd.sub (c := 4 * i) (l := 4) (by omega)), hMb x hx, hfr x hx hd]
    · have hA : accV (memStore32 Mb (D + BitVec.ofNat 32 (4 * i)) (bsubD (memLoad32 M0 (np + BitVec.ofNat 32 (4 * i)))
          (memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i))) b)) D (i + 1) = accV M D i +
          (bsubD (memLoad32 M0 (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i))) b).toNat *
            2 ^ (32 * i) := by
        rw [accV_succ1, accV_store_above (by omega) i (Nat.le_refl i), memLoad32_store32_same]
        congr 1
        exact accV_congr i fun j hj => memLoad32_congr fun q hq =>
          hMb _ ((sFD.subR (c := 4 * j) (l := 4) (by omega)).subR (c := q) (l := 1) (by omega))
      rw [hA, accV_succ1, accV_succ1, pow32_succ, e2]
      exact sub_arith_z hv bv
  intro m
  induction m with
  | zero =>
    intro i hi M n b s hc hb hfr hbm hv rsp rnp rxp rd rc rb
    have i11 : i = 1 := Nat.succ.inj hi
    subst i11
    obtain ⟨n1, M1, c1, u1, hc1, _, hf1, hm1, hv1, sp1, _, _, _, _, fr⟩ :=
      step 1 (by decide) s hc hb hfr hbm hv rsp rnp rxp rd rc rb
    exact ⟨n1, M1, c1, u1, hc1, hf1, hm1, hv1, sp1, fr⟩
  | succ m ih =>
    intro i hi M n b s hc hb hfr hbm hv rsp rnp rxp rd rc rb
    have hl : i + 1 < 2 := sel_lt1 hi
    obtain ⟨n1, M1, c1, u1, hc1, hb1, hf1, hm1, hv1, sp1, enp, exp, ed, ec, fr⟩ :=
      step i (Nat.lt_trans (Nat.lt_succ_self i) hl) s hc hb hfr hbm hv rsp rnp rxp rd rc rb
    rw [ite_eq_left hl] at u1
    obtain ⟨n', M', c', u', hc', hf', hm', hv', sp', fr'⟩ :=
      ih (i + 1) (sel_succ hi) u1 hc1 hb1 hf1 hm1 hv1 sp1 enp exp ed ec rfl
    exact ⟨n', M', c1.trans c', u', hc', hf', hm', hv', sp', fun q q0 q1 q2 q20 q3 q4 qr qnp qxp qd qc => by
      rw [fr' q q0 q1 q2 q20 q3 q4 qr qnp qxp qd qc, fr q q0 q1 q2 q20 q3 q4 qr qnp qxp qd qc]⟩


theorem lm8Pro_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base F : Word} {len : Nat}
    (hF : f sp + 0xFFFFFF00 = F)
    (h : ∀ c : Nat, 0xD4 ≤ c → c + 4 ≤ 0x100 → c % 4 = 0 →
      (F + BitVec.ofNat 32 c).toNat % 4 = 0 ∧ Sep (F + BitVec.ofNat 32 c) 4 base len) :
    BlockOk base len lm8Pro (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, lm8Pro, upd, ↓reduceIte, and_true, true_and, ev_add]
  rw [hF]
  exact ⟨h 0xFC (by decide) (by decide) (by decide), h 0xF8 (by decide) (by decide) (by decide), h 0xF4 (by decide) (by decide) (by decide), h 0xF0 (by decide) (by decide) (by decide), h 0xEC (by decide) (by decide) (by decide), h 0xE8 (by decide) (by decide) (by decide), h 0xE4 (by decide) (by decide) (by decide), h 0xE0 (by decide) (by decide) (by decide), h 0xDC (by decide) (by decide) (by decide), h 0xD8 (by decide) (by decide) (by decide), h 0xD4 (by decide) (by decide) (by decide)⟩


/-- From 0x54 to `to_uint_resize`'s call at 0x4E: the high limbs to
`sp + 0x20`, the sign to `s6`, and the call's arguments. -/
def lm8B1 : List BInstr :=
  [.lw a0 sp 0x48, .lw a1 sp 0x4C, .lbu (22 : Fin 32) sp 0x50, .sw sp a0 0x20, .sw sp a1 0x24,
   .aluImm .add a0 sp 0x28, .alu .add a1 x0 sp]

section
set_option maxRecDepth 20000
theorem lm8B1_end : blockEnd lincombShiftMod8Code 0x3E lm8B1 = some 0x4E := by decide
end

set_option maxRecDepth 20000 in
theorem lm8B1_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lm8B1 (M, f)).1 = memStore32 (memStore32 M (f sp + 0x20) (memLoad32 M (f sp + 0x48)))
      (f sp + 0x24) (memLoad32 M (f sp + 0x4C)) ∧
    (runBlock lm8B1 (M, f)).2 (22 : Fin 32) = (M (f sp + 0x50)).zeroExtend 32 ∧
    (runBlock lm8B1 (M, f)).2 a0 = f sp + 0x28 ∧ (runBlock lm8B1 (M, f)).2 a1 = f sp ∧
    ∀ q : Fin 32, q.val ∉ [10, 11, 22] → (runBlock lm8B1 (M, f)).2 q = f q := by
  refine ⟨?_, ?_, ?_, ?_, fun q hq => runBlock_keepL (by decide) hz hq⟩ <;>
    simp only [runBlock, BInstr.run, lm8B1] <;> simp +decide only [upd, ↓reduceIte, ev_add, hz] <;>
    first | rfl | exact BitVec.zero_add _ | skip

theorem lm8B1_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h68 : (f sp + 0x48).toNat % 4 = 0) (h6c : (f sp + 0x4C).toNat % 4 = 0) (h30 : (f sp + 0x20).toNat % 4 = 0)
    (h34 : (f sp + 0x24).toNat % 4 = 0) (s30 : Sep (f sp + 0x20) 4 base len) (s34 : Sep (f sp + 0x24) 4 base len) :
    BlockOk base len lm8B1 (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, lm8B1, upd, ↓reduceIte, and_true, true_and]
  exact ⟨h68, h6c, ⟨h30, s30⟩, h34, s34⟩

/-- The memory and registers at 0x56, after `lincomb_int`, the copy of its
result down to `F`, and `to_uint_resize`: what the rest of the proof uses. -/
structure Lm8At6C (m : Machine) (M : Word → BitVec 8) (n : Machine) (G : Word) : Prop where
  frame : ∀ x, Sep G 0x280 x 1 → M x = m.mem x
  slots : ∀ r o, (r, o) ∈ lm8Ps → memLoad32 M (G + 0x180 + o) = reg m r
  sp : reg n sp = G + 0x180
  s2 : reg n 18 = reg m a0
  s3 : reg n 19 = reg m a5
  s5 : reg n 21 = reg m 17
  s7 : reg n 23 = reg m a6
  s4 : reg n 20 = G + 0x180 + 0x28
  keep : ∀ q : Fin 32, q.val ∈ [3, 4, 26, 27] → reg n q = reg m q
  lo2 : memLoad32 M (G + 0x180 + 0x28) = memLoad32 M (G + 0x180) ∧
    memLoad32 M (G + 0x180 + 0x2C) = memLoad32 M (G + 0x180 + 4)

set_option exponentiation.threshold 128 in
set_option maxRecDepth 60000 in
set_option maxHeartbeats 16000000 in
/-- **Phase 1**, from entry to 0x56: the frame, `lincomb_int(a, b, c, d)`,
its magnitude copied to `F = sp - 0x100` (8 limbs, then 2 at `F + 0x20`),
its sign in `s6`, and the low two limbs again at `F + 0x28`. -/
theorem lm8_ph1 (m : Machine) {P G res ap bp cp dp mp mip : Word} (env : LMEnv8 m.mem P G res ap bp cp dp mp mip)
    (hpc : m.pc = P) (hsp : reg m sp = G + 0x280) (ha0 : reg m a0 = res) (ha1 : reg m a1 = ap)
    (ha2 : reg m a2 = bp) (ha3 : reg m a3 = cp) (ha4 : reg m a4 = dp)
    (hsa : (m.mem (ap + 0x20)).toNat ≤ 1) (hsb : (m.mem (bp + 0x20)).toNat ≤ 1) :
    ∃ n M σ, Steps m n ∧ St M P n 0x56 (reg n) ∧ Lm8At6C m M n G ∧ σ ≤ 1 ∧ reg n 22 = BitVec.ofNat 32 σ ∧
      sgnVal σ (accV M (G + 0x180) 8 + 2 ^ 256 * accV M (G + 0x180 + 0x20) 2) =
        sgnVal (m.mem (ap + 0x20)).toNat (accV m.mem ap 8) * i64Val (accV m.mem cp 2) +
        sgnVal (m.mem (bp + 0x20)).toNat (accV m.mem bp 8) * i64Val (accV m.mem dp 2) := by
  obtain ⟨F, hF⟩ : ∃ F, G + 0x180 = F := ⟨_, rfl⟩
  have hGt := env.hGt
  have tG : ∀ c, c < 0x280 → (G + BitVec.ofNat 32 c).toNat = G.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show c < 2 ^ 32 by omega),
      Nat.mod_eq_of_lt (show G.toNat + c < 2 ^ 32 by omega)]
  have fG : ∀ c, F + BitVec.ofNat 32 c = G + BitVec.ofNat 32 (0x180 + c) := fun c => by
    rw [← hF, show (0x180 : Word) = BitVec.ofNat 32 0x180 from rfl, add_ofNat_assoc]
  have eF : F = G + BitVec.ofNat 32 0x180 := hF.symm
  have hFn : F.toNat = G.toNat + 0x180 := by rw [eF, tG _ (by decide)]
  have hFa : F.toNat % 4 = 0 := by rw [hFn]; have := env.hG; omega
  have aG : ∀ c, c % 4 = 0 → c < 0x280 → (G + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h1 h2 => by
    rw [tG c h2]; have := env.hG; omega
  have sub : ∀ {b : Word} {k : Nat} (c l : Nat), c + l ≤ 0x280 → Sep G 0x280 b k → Sep (G + BitVec.ofNat 32 c) l b k :=
    fun c l h hs => hs.sub h
  have sG : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x280 → d + k ≤ 0x280 →
      Sep (G + BitVec.ofNat 32 c) n (G + BitVec.ofNat 32 d) k := fun h h1 h2 =>
    sep_offsets G h (by omega) (by omega)
  have g0 : ∀ {b : Word} {k : Nat} (l : Nat), l ≤ 0x280 → Sep G 0x280 b k → Sep G l b k := fun l h hs => by
    have := hs.sub (c := 0) (l := l) (by omega); rwa [add_ofNat_zero] at this
  have cOf : ∀ {M : Word → BitVec 8}, (∀ x, Sep G 0x280 x 1 → M x = m.mem x) →
      ∀ {b : Word} {code : List Nat}, CodeIn m.mem b code → Sep G 0x280 b code.length → CodeIn M b code :=
    fun hM _ _ hc hs i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have opG : ∀ {M : Word → BitVec 8}, (∀ x, Sep G 0x280 x 1 → M x = m.mem x) →
      ∀ {b : Word} {n : Nat}, Sep b (4 * n) G 0x280 → accV M b n = accV m.mem b n := fun hM _ n hb =>
    accV_congr n fun i hi => memLoad32_congr fun j hj => hM _ (by
      have := hb.symm.subR (c := 4 * i + j) (l := 1) (by omega)
      rwa [← add_ofNat_assoc] at this)
  have byG : ∀ {M : Word → BitVec 8}, (∀ x, Sep G 0x280 x 1 → M x = m.mem x) →
      ∀ {b : Word}, Sep b 33 G 0x280 → M (b + 0x20) = m.mem (b + 0x20) := fun hM _ hb =>
    hM _ (hb.symm.subR (c := 0x20) (l := 1) (by omega))
  have hz : reg m 0 = 0 := rfl
  -- the prologue
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have eSp : reg m sp + 0xFFFFFF00 = F := by rw [hsp, ← hF, BitVec.add_assoc]; rfl
  obtain ⟨n1, c1, u1⟩ := St.block lm8Pro s0 env.code lm8Pro_end (lm8Pro_ok eSp fun c h1 h2 h3 => by
    rw [fG]; exact ⟨aG _ (by omega) (by omega), sub _ 4 (by omega) env.sC⟩)
  obtain ⟨pm, psp, ps5, ps7, ps3, ps2, pa0, ps4, pk⟩ := lm8Pro_run (M := m.mem) (f := reg m) hz
  rw [pm, eSp] at u1
  obtain ⟨M1, hM1⟩ : ∃ M1, saveMem m.mem F (reg m) lm8Ps = M1 := ⟨_, rfl⟩
  rw [hM1] at u1
  have fr1 : ∀ x, Sep G 0x280 x 1 → M1 x = m.mem x := fun x hx => by
    rw [← hM1]
    exact saveMem_outside lm8Ps fun p hp => by
      obtain ⟨h1, h2, h3⟩ := lm8Ps_range p hp
      have e : F + p.2 = G + BitVec.ofNat 32 (0x180 + p.2.toNat) := by rw [← fG, ofNat_toNat_self]
      rw [e]; exact sub _ 4 (by omega) hx
  have eLc : lcR8 F = G := by
    show F + 0xFFFFFE80 = G
    rw [eF, BitVec.add_assoc, show BitVec.ofNat 32 0x180 + 0xFFFFFE80 = BitVec.ofNat 32 0 from rfl, add_ofNat_zero]
  have e38 : F + 0x28 = G + BitVec.ofNat 32 0x1A8 := fG 0x28
  have r1 : ∀ q, reg n1 q = (runBlock lm8Pro (m.mem, reg m)).2 q := u1.regs
  obtain ⟨t1, ct1, pct1, memt1, regst1⟩ := u1.self.callRa (cOf fr1 env.code env.sC) lsm8_at_26 lsm8_at_2a
    (cb := lm8Lc P) (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFFA70 (by decide))
  have rt1 := PEnv.reg1 regst1 u1.self.zero
  have LE : LCEnv8 t1.mem (lm8Lc P) F (F + 0x28) ap bp cp dp := by
    rw [memt1]
    exact {
      hP := even_at P env.hP 0xFFFFFA70 (by decide)
      code := cOf fr1 env.lc env.sL
      abs := cOf fr1 env.abs env.sA
      wide := cOf fr1 env.wide env.sW
      neg := cOf fr1 env.neg env.sN
      mset := cOf fr1 env.mset env.sM
      stub := cOf fr1 env.stub env.sU
      body := cOf fr1 env.body env.sB
      bsub := cOf fr1 env.bsub env.sBs
      sel2 := cOf fr1 env.sel2 env.s2
      sel12 := cOf fr1 env.sel12 env.s12
      zero := cOf fr1 env.zero env.sZ
      one := cOf fr1 env.one env.sO
      hsp := hFa
      hS := by omega
      hout := by rw [e38]; exact aG _ (by decide) (by decide)
      hap := env.hap
      hbp := env.hbp
      hcp := env.hcp
      hdp := env.hdp
      hwo := by rw [e38, tG _ (by decide)]; omega
      hwa := env.hwa
      hwb := env.hwb
      sC := by rw [eLc]; exact g0 0x180 (by decide) env.sL
      sA := by rw [eLc]; exact g0 0x180 (by decide) env.sA
      sW := by rw [eLc]; exact g0 0x180 (by decide) env.sW
      sN := by rw [eLc]; exact g0 0x180 (by decide) env.sN
      sM := by rw [eLc]; exact g0 0x180 (by decide) env.sM
      sU := by rw [eLc]; exact g0 0x180 (by decide) env.sU
      sB := by rw [eLc]; exact g0 0x180 (by decide) env.sB
      sBs := by rw [eLc]; exact g0 0x180 (by decide) env.sBs
      s2 := by rw [eLc]; exact g0 0x180 (by decide) env.s2
      s12 := by rw [eLc]; exact g0 0x180 (by decide) env.s12
      sZ := by rw [eLc]; exact g0 0x180 (by decide) env.sZ
      sO := by rw [eLc]; exact g0 0x180 (by decide) env.sO
      oR := by
        rw [eLc, e38]
        have := sG (c := 0x1A8) (n := 41) (d := 0) (k := 0x180) (.inr (by decide)) (by decide) (by decide)
        rwa [add_ofNat_zero] at this
      aR := by rw [eLc]; exact (g0 0x180 (by decide) env.aG.symm).symm
      bR := by rw [eLc]; exact (g0 0x180 (by decide) env.bG.symm).symm
      cR := by rw [eLc]; exact (g0 0x180 (by decide) env.cG.symm).symm
      dR := by rw [eLc]; exact (g0 0x180 (by decide) env.dG.symm).symm
      oC := by rw [e38]; exact sub 0x1A8 41 (by decide) env.sL
      oB := by rw [e38]; exact sub 0x1A8 41 (by decide) env.sB }
  have rspF : reg n1 sp = F := by rw [r1, psp, eSp]
  obtain ⟨t2, ct2, pct2, spt2, kt2, sgt2, valt2, frt2⟩ := lincomb8_correct t1 LE pct1
    (by rw [rt1 _ (by decide), rspF]) (by rw [rt1 _ (by decide), r1, pa0, eSp])
    (by rw [rt1 _ (by decide), r1, pk a1 (by decide), ha1]) (by rw [rt1 _ (by decide), r1, pk a2 (by decide), ha2])
    (by rw [rt1 _ (by decide), r1, pk a3 (by decide), ha3]) (by rw [rt1 _ (by decide), r1, pk a4 (by decide), ha4])
    (by rw [regst1]; simp [upd]) (even_clear _ (even_at P env.hP (0x26 + 8) (by decide)))
    (by rw [memt1, byG fr1 env.aG]; exact hsa) (by rw [memt1, byG fr1 env.bG]; exact hsb)
  rw [memt1, byG fr1 env.aG, byG fr1 env.bG, opG fr1 (n := 8) (sep_pre env.aG (by decide)),
    opG fr1 (n := 8) (sep_pre env.bG (by decide)), opG fr1 (n := 2) (by exact sep_pre env.cG (by decide)),
    opG fr1 (n := 2) (by exact sep_pre env.dG (by decide))] at valt2
  rw [memt1] at frt2
  have frG2 : ∀ x, Sep G 0x280 x 1 → t2.mem x = m.mem x := fun x hx => by
    rw [frt2 x (by rw [eLc]; exact g0 0x180 (by decide) hx) (by rw [e38]; exact sub 0x1A8 41 (by decide) hx), fr1 x hx]
  have frS2 : ∀ x, Sep G 0x180 x 1 → Sep (G + BitVec.ofNat 32 0x1A8) 41 x 1 → t2.mem x = M1 x := fun x h1 h2 => by
    rw [frt2 x (by rw [eLc]; exact h1) (by rw [e38]; exact h2)]
  -- `memcpy(F, F + 0x28, 32)`
  have st2 : St t2.mem P t2 0x2E (reg t2) := ⟨pct2, rfl, fun _ => rfl⟩
  have hc2 := cOf frG2 env.code env.sC
  obtain ⟨u1', du1, vu1⟩ := st2.alu hc2 lsm8_at_2e (off' := 0x30) (by decide)
  have ku1 := vu1.oldReg st2.zero
  obtain ⟨u2', du2, vu2⟩ := vu1.self.aluImm hc2 lsm8_at_30 (off' := 0x32) (by decide)
  have ku2 := vu2.oldReg vu1.self.zero
  obtain ⟨u3', du3, vu3⟩ := vu2.self.aluImm hc2 lsm8_at_32 (off' := 0x36) (by decide)
  have ku3 := vu3.oldReg vu2.self.zero
  have spu3 : reg u3' sp = F := by rw [ku3 _ (by decide), ku2 _ (by decide), ku1 _ (by decide), spt2]
  have a0u3 : reg u3' a0 = F := by
    rw [ku3 _ (by decide), ku2 _ (by decide), vu1.newReg (by decide)]
    show reg t2 x0 + reg t2 sp = _; rw [st2.zero, spt2]; exact BitVec.zero_add _
  have a1u3 : reg u3' a1 = F + 0x28 := by
    rw [ku3 _ (by decide), vu2.newReg (by decide)]; show reg u1' sp + 0x28 = _; rw [ku1 _ (by decide), spt2]
  have a2u3 : reg u3' a2 = BitVec.ofNat 32 32 := by
    rw [vu3.newReg (by decide)]; show reg u2' x0 + 0x20 = _; rw [vu2.self.zero]; rfl
  have hev1 : (lm8Lc P + 0x3AAC : Word).toNat % 2 = 0 := even_at (lm8Lc P) (even_at P env.hP 0xFFFFFA70 (by decide)) 0x3AAC (by decide)
  obtain ⟨t3, ct3, pct3, memt3, regst3⟩ := vu3.self.callRa hc2 lsm8_at_36 lsm8_at_3a (cb := lm8Lc P + 0x3AAC)
    (by simp only [BitVec.add_assoc] <;> rfl) hev1
  have rt3 := PEnv.reg1 regst3 vu3.self.zero
  have spt3 : reg t3 sp = F := by rw [rt3 _ (by decide), spu3]
  have eS : F + 0xFFFFFFF0 = G + BitVec.ofNat 32 0x170 := by rw [eF, BitVec.add_assoc]; rfl
  have scr : ∀ c, 0x180 ≤ c → c < 0x280 → Sep (G + BitVec.ofNat 32 0x170) 16 (G + BitVec.ofNat 32 c) 1 :=
    fun c h1 h2 => sG (.inl (by omega)) (by decide) (by omega)
  have eF0 : F = G + BitVec.ofNat 32 0x180 := eF
  obtain ⟨t4, ct4, pct4, spt4, -, memt4, kt4⟩ := memcpy_correct t3 (lm8Lc P + 0x3AAC) (P + BitVec.ofNat 32 (0x36 + 8))
    F (F + 0x28) 32 (fun i hi => by rw [memt3]; exact cOf frG2 env.stub env.sU i hi) hev1 pct3
    (by rw [rt3 _ (by decide), a0u3]) (by rw [rt3 _ (by decide), a1u3]) (by rw [rt3 _ (by decide), a2u3])
    (by rw [regst3]; simp [upd]) (even_clear _ (even_at P env.hP (0x36 + 8) (by decide)))
    (by
      rw [memt3, spt3, show lm8Lc P + 0x3AAC + 8 = lm8Lc P + 0x3AB4 by rw [BitVec.add_assoc]; rfl, eS, e38, eF0]
      exact {
        code := cOf frG2 env.body env.sB
        hDC := sub 0x180 32 (by decide) env.sB
        hFC := sub 0x170 16 (by decide) env.sB
        hdF := sG (.inr (by decide)) (by decide) (by decide)
        hsF := sG (.inr (by decide)) (by decide) (by decide)
        hsep := sG (.inl (by decide)) (by decide) (by decide)
        hF := aG _ (by decide) (by decide)
        hFw := by rw [tG _ (by decide)]; omega
        hdw := by rw [tG _ (by decide)]; omega
        hsw := by rw [tG _ (by decide)]; omega })
  rw [spt3, eS, memt3] at memt4
  have frG4 : ∀ x, Sep G 0x280 x 1 → t4.mem x = m.mem x := fun x hx => by
    rw [memt4 x (sub 0x170 16 (by decide) hx), copyBytes_sep (by rw [eF0]; exact sub 0x180 32 (by decide) hx) (Nat.le_refl _),
      frG2 x hx]
  have up4 : ∀ c, 0x30 ≤ c → c < 0x100 → t4.mem (F + BitVec.ofNat 32 c) = t2.mem (F + BitVec.ofNat 32 c) :=
    fun c h1 h2 => by
      rw [memt4 _ (by rw [fG]; exact sG (.inl (by omega)) (by decide) (by omega)),
        copyBytes_sep (by rw [fG, eF0]; exact sG (.inl (by omega)) (by decide) (by omega)) (Nat.le_refl _)]
  have upw4 : ∀ c, 0x30 ≤ c → c + 4 ≤ 0x100 →
      memLoad32 t4.mem (F + BitVec.ofNat 32 c) = memLoad32 t2.mem (F + BitVec.ofNat 32 c) := fun c h1 h2 =>
    memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact up4 _ (by omega) (by omega)
  have lo4 : ∀ i, i < 8 → memLoad32 t4.mem (F + BitVec.ofNat 32 (4 * i)) =
      memLoad32 t2.mem (F + 0x28 + BitVec.ofNat 32 (4 * i)) := fun i hi => by
    have h1 : memLoad32 t4.mem (F + BitVec.ofNat 32 (4 * i)) =
        memLoad32 (copyBytes t2.mem F (F + 0x28) 32) (F + BitVec.ofNat 32 (4 * i)) :=
      memLoad32_congr fun j hj => memt4 _ (by rw [add_ofNat_assoc, fG]; exact scr _ (by omega) (by omega))
    rw [h1, cb_load (by omega) (by decide)]
  -- the high limbs and the sign
  have st4 : St t4.mem P t4 0x3E (reg t4) := ⟨pct4, rfl, fun _ => rfl⟩
  have hc4 := cOf frG4 env.code env.sC
  have aF : ∀ c, c % 4 = 0 → 0x180 + c < 0x280 → (F + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h1 h2 => by
    rw [fG]; exact aG _ (by omega) h2
  have sF : ∀ {b : Word} {k : Nat} (c l : Nat), 0x180 + c + l ≤ 0x280 → Sep G 0x280 b k →
      Sep (F + BitVec.ofNat 32 c) l b k := fun c l h hs => by rw [fG]; exact sub _ l h hs
  have sp4 : reg t4 sp = F := by rw [spt4, spt3]
  obtain ⟨n5, c5, u5⟩ := St.block lm8B1 st4 hc4 lm8B1_end (lm8B1_ok
    (by rw [sp4]; exact aF 0x48 rfl (by decide)) (by rw [sp4]; exact aF 0x4C rfl (by decide))
    (by rw [sp4]; exact aF 0x20 rfl (by decide)) (by rw [sp4]; exact aF 0x24 rfl (by decide))
    (by rw [sp4]; exact sF 0x20 4 (by decide) env.sC) (by rw [sp4]; exact sF 0x24 4 (by decide) env.sC))
  obtain ⟨b1m, b1s6, b1a0, b1a1, b1k⟩ := lm8B1_run (M := t4.mem) (f := reg t4) st4.zero
  rw [b1m, sp4] at u5
  obtain ⟨M5, hM5⟩ : ∃ M5, memStore32 (memStore32 t4.mem (F + 0x20) (memLoad32 t4.mem (F + 0x48))) (F + 0x24)
      (memLoad32 t4.mem (F + 0x4C)) = M5 := ⟨_, rfl⟩
  rw [hM5] at u5
  have fr5 : ∀ x, Sep (F + 0x20) 8 x 1 → M5 x = t4.mem x := fun x hx => by
    have h4 : Sep (F + 0x24) 4 x 1 := by
      have := hx.sub (c := 4) (l := 4) (by decide); rw [BitVec.add_assoc] at this; exact this
    have h0 : Sep (F + 0x20) 4 x 1 := by
      have := hx.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    rw [← hM5, memStore32_get_sep h4, memStore32_get_sep h0]
  have frG5 : ∀ x, Sep G 0x280 x 1 → M5 x = m.mem x := fun x hx => by
    rw [fr5 x (sF 0x20 8 (by decide) hx), frG4 x hx]
  have hc5 := cOf frG5 env.code env.sC
  have g5 : ∀ q, reg n5 q = (runBlock lm8B1 (t4.mem, reg t4)).2 q := u5.regs
  have hevT : (P + 0xFFFFBFB6 : Word).toNat % 2 = 0 := even_at P env.hP 0xFFFFBFB6 (by decide)
  obtain ⟨t6, ct6, pct6, memt6, regst6⟩ := u5.self.callRa hc5 lsm8_at_4e lsm8_at_52 (cb := P + 0xFFFFBFB6)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) hevT
  have rt6 := PEnv.reg1 regst6 u5.self.zero
  obtain ⟨t7, ct7, pct7, kt7, w0, w1, fr7⟩ := toUintResize2_correct t6 (out := F + 0x28) (src := F)
    (by rw [memt6]; exact cOf frG5 env.tur env.sT) pct6 (by rw [rt6 _ (by decide), g5, b1a0, sp4])
    (by rw [rt6 _ (by decide), g5, b1a1, sp4]) (aF 0x28 rfl (by decide)) hFa
    (by have := sG (c := 0x1A8) (n := 8) (d := 0x180) (k := 8) (.inr (by decide)) (by decide) (by decide)
        rw [e38, eF0]; exact this)
    (by rw [e38]; exact sub 0x1A8 8 (by decide) env.sT) (by rw [regst6]; simp [upd])
    (even_clear _ (even_at P env.hP (0x4E + 8) (by decide)))
  rw [memt6] at w0 w1 fr7
  have hslv : ∀ r o, (r, o) ∈ lm8Ps → memLoad32 M1 (F + o) = reg m r := fun r o h => by
    rw [← hM1]
    simp only [lm8Ps, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
  have fr7' : ∀ x, Sep (F + 0x28) 8 x 1 → Sep (F + 0x20) 8 x 1 → t7.mem x = t4.mem x := fun x h1 h2 => by
    rw [fr7 x h1, fr5 x h2]
  have hiF : ∀ c, 0x30 ≤ c → c < 0x100 → t7.mem (F + BitVec.ofNat 32 c) = t2.mem (F + BitVec.ofNat 32 c) :=
    fun c h1 h2 => by
      have h38 : Sep (F + 0x28) 8 (F + BitVec.ofNat 32 c) 1 := by
        rw [e38, fG]; exact sG (.inl (by omega)) (by decide) (by omega)
      have h30 : Sep (F + 0x20) 8 (F + BitVec.ofNat 32 c) 1 := by
        rw [show F + 0x20 = G + BitVec.ofNat 32 0x1A0 from fG 0x20, fG]; exact sG (.inl (by omega)) (by decide) (by omega)
      rw [fr7' _ h38 h30, up4 c (by omega) h2]
  have mdisj : ∀ {q : Nat} {L1 L2 : List Nat}, q ∈ L1 → (∀ x ∈ L1, x ∉ L2) → q ∉ L2 := fun h1 h2 => h2 _ h1
  have chain : ∀ q : Fin 32, q.val ∈ [3, 4, 18, 19, 20, 21, 23, 26, 27] → reg t7 q = reg n1 q := fun q hq => by
    have ne : ∀ w : Fin 32, w.val ∉ [3, 4, 18, 19, 20, 21, 23, 26, 27] → q ≠ w := fun w hw e => hw (e ▸ hq)
    rw [kt7 q (ne a0 (by decide)) (ne a1 (by decide)) (ne a2 (by decide)) (ne a3 (by decide)), rt6 q (ne ra (by decide)),
      g5, b1k q (mdisj hq (by decide)),
      kt4 q (ne a1 (by decide)) (ne a2 (by decide)) (ne a3 (by decide)) (ne a4 (by decide)) (ne a5 (by decide))
        (ne a6 (by decide)) (ne a7 (by decide)) (ne (5 : Fin 32) (by decide)) (ne (6 : Fin 32) (by decide)) (ne 7 (by decide))
        (ne 28 (by decide)) (ne 29 (by decide)) (ne 30 (by decide)) (ne sp (by decide)),
      rt3 q (ne ra (by decide)), ku3 q (ne a2 (by decide)), ku2 q (ne a1 (by decide)), ku1 q (ne a0 (by decide)),
      kt2 q (mdisj hq (by decide)), rt1 q (ne ra (by decide))]
  have r1k : ∀ q : Fin 32, q.val ∈ [3, 4, 26, 27] → reg n1 q = reg m q := fun q hq => by
    rw [r1, pk q (mdisj hq (by decide))]
  have sp7 : reg t7 sp = F := by
    rw [kt7 sp (by decide) (by decide) (by decide) (by decide), rt6 sp (by decide), g5, b1k sp (by decide), sp4]
  have slotW : ∀ c, 0xD4 ≤ c → c + 4 ≤ 0x100 → memLoad32 t7.mem (F + BitVec.ofNat 32 c) = memLoad32 M1 (F + BitVec.ofNat 32 c) :=
    fun c h1 h2 => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc, hiF (c + j) (by omega) (by omega)]
      apply frS2
      · rw [fG]; have := sG (c := 0) (n := 0x180) (d := 0x180 + (c + j)) (k := 1) (.inl (by omega)) (by decide) (by omega)
        rwa [add_ofNat_zero] at this
      · rw [fG]; exact sG (.inl (by omega)) (by decide) (by omega)
  have zx : ∀ b : BitVec 8, b.zeroExtend 32 = BitVec.ofNat 32 b.toNat := fun b => by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have s6v : reg t7 22 = BitVec.ofNat 32 (t2.mem (F + 0x50)).toNat := by
    rw [kt7 22 (by decide) (by decide) (by decide) (by decide), rt6 22 (by decide), g5, b1s6, sp4,
      show F + 0x50 = F + BitVec.ofNat 32 0x50 from rfl, up4 0x50 (by decide) (by decide), zx]
  have e70 : F + 0x28 + 0x28 = F + 0x50 := by rw [BitVec.add_assoc]; rfl
  have e68 : F + 0x28 + 0x20 = F + 0x48 := by rw [BitVec.add_assoc]; rfl
  rw [e70, e68] at valt2
  rw [e70] at sgt2
  have lo12 : accV t7.mem F 8 = accV t2.mem (F + 0x28) 8 := by
    apply accV_congr2 8; intro i hi
    rw [← lo4 i hi]
    exact memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]
      have h38 : Sep (F + 0x28) 8 (F + BitVec.ofNat 32 (4 * i + j)) 1 := by
        rw [e38, fG]; exact sG (.inr (by omega)) (by decide) (by omega)
      have h30 : Sep (F + 0x20) 8 (F + BitVec.ofNat 32 (4 * i + j)) 1 := by
        rw [show F + 0x20 = G + BitVec.ofNat 32 0x1A0 from fG 0x20, fG]; exact sG (.inr (by omega)) (by decide) (by omega)
      exact fr7' _ h38 h30
  have hi2 : accV t7.mem (F + 0x20) 2 = accV t2.mem (F + 0x48) 2 := by
    apply accV_congr2 2; intro i hi
    have e : memLoad32 t7.mem (F + 0x20 + BitVec.ofNat 32 (4 * i)) = memLoad32 M5 (F + 0x20 + BitVec.ofNat 32 (4 * i)) :=
      memLoad32_congr fun j hj => fr7 _ (by
        rw [add_ofNat_assoc, show F + 0x20 = G + BitVec.ofNat 32 0x1A0 from fG 0x20, add_ofNat_assoc, e38]
        exact sG (.inr (by omega)) (by omega) (by omega))
    rw [e]
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · rw [← hM5, add_ofNat_zero, memLoad32_store32_sep (by
          have := sep_offsets F (c := 0x24) (n := 4) (d := 0x20) (k := 4) (.inr (by decide)) (by decide) (by decide)
          exact this), memLoad32_store32_same, add_ofNat_zero]
      exact upw4 0x48 (by decide) (by decide)
    · rw [← hM5, show F + 0x20 + BitVec.ofNat 32 (4 * 1) = F + 0x24 by rw [BitVec.add_assoc]; rfl,
        memLoad32_store32_same, show F + 0x48 + BitVec.ofNat 32 (4 * 1) = F + BitVec.ofNat 32 0x4C by rw [BitVec.add_assoc]; rfl]
      exact upw4 0x4C (by decide) (by decide)
  refine ⟨t7, t7.mem, (t2.mem (F + 0x50)).toNat,
    c1.trans (ct1.trans (ct2.trans (.cons du1 (.cons du2 (.cons du3 (ct3.trans (ct4.trans (c5.trans (ct6.trans ct7))))))))),
    ⟨pct7, rfl, fun _ => rfl⟩, ?_, sgt2, s6v, ?_⟩
  · have m38 : ∀ k, k = 0 ∨ k = 4 → memLoad32 t7.mem (F + BitVec.ofNat 32 k) = memLoad32 M5 (F + BitVec.ofNat 32 k) :=
      fun k hk => memLoad32_congr fun j hj => fr7 _ (by
        rw [add_ofNat_assoc, e38, fG]; exact sG (.inr (by omega)) (by decide) (by omega))
    exact {
      frame := fun x hx => by rw [fr7' x (sF 0x28 8 (by decide) hx) (sF 0x20 8 (by decide) hx), frG4 x hx]
      slots := fun r o h => by
        obtain ⟨_, h2, h3⟩ := lm8Ps_range (r, o) h
        have := slotW o.toNat h2 h3
        rw [ofNat_toNat_self] at this
        rw [hF, this, hslv r o h]
      sp := by rw [sp7]; exact hF.symm
      s2 := by rw [chain 18 (by decide), r1, ps2]
      s3 := by rw [chain 19 (by decide), r1, ps3]
      s5 := by rw [chain 21 (by decide), r1, ps5]
      s7 := by rw [chain 23 (by decide), r1, ps7]
      s4 := by rw [chain 20 (by decide), r1, ps4, eSp, hF]
      keep := fun q hq => by rw [chain q (by simp at hq ⊢; omega), r1k q hq]
      lo2 := by
        rw [hF]
        refine ⟨?_, ?_⟩
        · rw [w0]; have := m38 0 (.inl rfl); rw [add_ofNat_zero] at this; exact this.symm
        · have e3c : F + 0x28 + 4 = F + 0x2C := by rw [BitVec.add_assoc]; rfl
          rw [← e3c, w1]; exact (m38 4 (.inr rfl)).symm }
  · rw [hF, lo12, hi2]; exact valt2


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **Phase 2**, from 0x56 to 0x160: `mf`, the low 64 bits of `x` times
`mi`, masked to `shift` bits, at `F + 0xC8`. -/
theorem lm8_ph2 {M : Word → BitVec 8} {P F mip : Word} {n : Machine} {sh : Nat} (hP : P.toNat % 2 = 0)
    (s : St M P n 0x56 (reg n)) (hc : CodeIn M P lincombShiftMod8Code)
    (hl : CodeIn M (lm8Shr P + 0x1EE) leadMut8Code) (ht : CodeIn M (lm8Shr P + 0x1FE) trailing8Code)
    (hmax : CodeIn M (BitVec.ofNat 32 u2MaxAddress) u2MaxData)
    (rsp : reg n sp = F) (r19 : reg n 19 = BitVec.ofNat 32 sh) (r20 : reg n 20 = F + 0x28) (r21 : reg n 21 = mip)
    (hs1 : 1 ≤ sh) (hs2 : sh ≤ 63) (hF : F.toNat % 4 = 0) (hmip : mip.toNat % 4 = 0)
    (sC1 : Sep (F + 0x28) 8 P lincombShiftMod8Code.length)
    (sC2 : Sep (F + 0x58) 8 P lincombShiftMod8Code.length) (sC3 : Sep (F + 0xC8) 8 P lincombShiftMod8Code.length)
    (sLm : Sep (F + 0x28) 8 (lm8Shr P + 0x1EE) leadMut8Code.length)
    (sTr : Sep (F + 0x28) 8 (lm8Shr P + 0x1FE) trailing8Code.length)
    (sMX : Sep (F + 0x28) 8 (BitVec.ofNat 32 u2MaxAddress) 8) (sX : Sep (F + 0xC8) 8 (F + 0x28) 8)
    (sI : Sep (F + 0xC8) 8 mip 8) (sL : Sep (F + 0xC8) 8 (lm8Shr P + 0x1EE) leadMut8Code.length)
    (sT : Sep (F + 0xC8) 8 (lm8Shr P + 0x1FE) trailing8Code.length)
    (sM : Sep (F + 0xC8) 8 (BitVec.ofNat 32 u2MaxAddress) 8) :
    ∃ n' M', Steps n n' ∧ St M' P n' 0x160 (reg n') ∧ CodeIn M' P lincombShiftMod8Code ∧
      (∀ x, Sep (F + 0x28) 8 x 1 → Sep (F + 0x58) 8 x 1 → Sep (F + 0xC8) 8 x 1 → M' x = M x) ∧
      (memLoad32 M' (F + 0xC8)).toNat + 2 ^ 32 * (memLoad32 M' (F + 0xCC)).toNat =
        ((memLoad32 M (F + 0x28)).toNat + 2 ^ 32 * (memLoad32 M (F + 0x2C)).toNat) *
          ((memLoad32 M mip).toNat + 2 ^ 32 * (memLoad32 M (mip + 4)).toNat) % 2 ^ 64 % 2 ^ sh ∧
      reg n' 21 = F + 0x80 ∧ reg n' sp = F ∧
      ∀ q : Fin 32, q.val ∉ [1, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 20, 21, 24] → reg n' q = reg n q := by
  obtain ⟨n1, M1, c1, u1, hc1, fr1, v1, k1⟩ := lm8_mul s hc rsp r20 r21 hF hmip sC3 sX sI
  have cM : ∀ {b : Word} {code : List Nat}, CodeIn M b code → Sep (F + 0xC8) 8 b code.length → CodeIn M1 b code :=
    fun h hs i hi => by rw [fr1 _ (hs.subR (c := i) (l := 1) (by omega))]; exact h i hi
  obtain ⟨n2, M2, c2, u2, hc2, fr2, v2, r21', sp2, k2⟩ := lm8_mask hP u1 hc1 (cM hl sL) (cM ht sT) (cM hmax sM)
    (by rw [k1 sp (by decide), rsp]) (by rw [k1 19 (by decide), r19]) hs1 hs2 hF sC1 sC2 sC3 sLm sTr sMX
  refine ⟨n2, M2, c1.trans c2, u2, hc2, fun x h1 h2 h3 => by rw [fr2 x h1 h2 h3, fr1 x h3], ?_, r21', sp2,
    fun q hq => by rw [k2 q (nmem_of (by decide) hq), k1 q (nmem_of (by decide) hq)]⟩
  rw [v2, v1]


/-! ## Phase 3: `x - m·mf`, from 0x160 to 0x1FE -/

def lm8W0 : List BInstr :=
  [.aluImm .add a0 sp 0x60, .aluImm .add a2 sp 0xC8, .alu .add a1 x0 (23 : Fin 32), .aluImm .add (24 : Fin 32) sp 0x60]
def lm8W1 : List BInstr :=
  [.aluImm .add a0 sp 0x88, .aluImm .add a2 x0 0x20, .aluImm .add a1 x0 0, .aluImm .add (25 : Fin 32) sp 0x88]
def lm8W2 : List BInstr :=
  [.aluImm .add (20 : Fin 32) x0 0, .alu .add (9 : Fin 32) x0 sp, .aluImm .add (8 : Fin 32) x0 0x8]
def lm8W3 : List BInstr := [.alu .add a0 x0 sp, .aluImm .add a1 sp 0x88, .aluImm .add a2 x0 0x20]
def lm8W4 : List BInstr :=
  [.sw sp x0 0x28, .sw sp x0 0x2C, .aluImm .add (24 : Fin 32) sp 0x20, .aluImm .add (9 : Fin 32) sp 0x28,
   .aluImm .add (8 : Fin 32) x0 2]
/-- From 0x20A to 0x1FE: the high limbs of the difference to `sp + 0x20`,
and the borrow, through `black_box`, as 0 or 1 in `s4`. -/
def lm8W5 : List BInstr :=
  [.lw a0 sp 0x28, .lw a1 sp 0x2C, .sw sp a0 0x20, .sw sp a1 0x24, .sw sp (20 : Fin 32) 0x28, .aluImm .add a0 sp 0x28,
   .lw a0 sp 0x28, .alu .sltu (20 : Fin 32) x0 a0]

section
set_option maxRecDepth 20000
theorem lm8W0_end : blockEnd lincombShiftMod8Code 0x160 lm8W0 = some 0x16A := by decide
theorem lm8W1_end : blockEnd lincombShiftMod8Code 0x172 lm8W1 = some 0x17E := by decide
theorem lm8W2_end : blockEnd lincombShiftMod8Code 0x186 lm8W2 = some 0x18C := by decide
theorem lm8W3_end : blockEnd lincombShiftMod8Code 0x1AE lm8W3 = some 0x1B6 := by decide
theorem lm8W4_end : blockEnd lincombShiftMod8Code 0x1BE lm8W4 = some 0x1CA := by decide
theorem lm8W5_end : blockEnd lincombShiftMod8Code 0x1EC lm8W5 = some 0x1FE := by decide
end

set_option maxRecDepth 20000 in
theorem lm8W0_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lm8W0 (M, f)).1 = M ∧ (runBlock lm8W0 (M, f)).2 a0 = f sp + 0x60 ∧
    (runBlock lm8W0 (M, f)).2 a2 = f sp + 0xC8 ∧ (runBlock lm8W0 (M, f)).2 a1 = f 23 ∧
    (runBlock lm8W0 (M, f)).2 (24 : Fin 32) = f sp + 0x60 ∧
    ∀ q : Fin 32, q.val ∉ [10, 11, 12, 24] → (runBlock lm8W0 (M, f)).2 q = f q := by
  refine ⟨?_, ?_, ?_, ?_, ?_, fun q hq => runBlock_keepL (by decide) hz hq⟩ <;>
    simp only [runBlock, BInstr.run, lm8W0] <;> simp +decide only [upd, ↓reduceIte, ev_add, hz] <;>
    first | rfl | exact BitVec.zero_add _ | skip

set_option maxRecDepth 20000 in
theorem lm8W1_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lm8W1 (M, f)).1 = M ∧ (runBlock lm8W1 (M, f)).2 a0 = f sp + 0x88 ∧
    (runBlock lm8W1 (M, f)).2 a2 = 0x20 ∧ (runBlock lm8W1 (M, f)).2 a1 = 0 ∧
    (runBlock lm8W1 (M, f)).2 (25 : Fin 32) = f sp + 0x88 ∧
    ∀ q : Fin 32, q.val ∉ [10, 11, 12, 25] → (runBlock lm8W1 (M, f)).2 q = f q := by
  refine ⟨?_, ?_, ?_, ?_, ?_, fun q hq => runBlock_keepL (by decide) hz hq⟩ <;>
    simp only [runBlock, BInstr.run, lm8W1] <;> simp +decide only [upd, ↓reduceIte, ev_add, hz] <;>
    first | rfl | exact BitVec.zero_add _ | skip

set_option maxRecDepth 20000 in
theorem lm8W2_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lm8W2 (M, f)).1 = M ∧ (runBlock lm8W2 (M, f)).2 (20 : Fin 32) = 0 ∧
    (runBlock lm8W2 (M, f)).2 (9 : Fin 32) = f sp ∧ (runBlock lm8W2 (M, f)).2 (8 : Fin 32) = 0x8 ∧
    ∀ q : Fin 32, q.val ∉ [8, 9, 20] → (runBlock lm8W2 (M, f)).2 q = f q := by
  refine ⟨?_, ?_, ?_, ?_, fun q hq => runBlock_keepL (by decide) hz hq⟩ <;>
    simp only [runBlock, BInstr.run, lm8W2] <;> simp +decide only [upd, ↓reduceIte, ev_add, hz] <;>
    first | rfl | exact BitVec.zero_add _ | skip

set_option maxRecDepth 20000 in
theorem lm8W3_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lm8W3 (M, f)).1 = M ∧ (runBlock lm8W3 (M, f)).2 a0 = f sp ∧
    (runBlock lm8W3 (M, f)).2 a1 = f sp + 0x88 ∧ (runBlock lm8W3 (M, f)).2 a2 = 0x20 ∧
    ∀ q : Fin 32, q.val ∉ [10, 11, 12] → (runBlock lm8W3 (M, f)).2 q = f q := by
  refine ⟨?_, ?_, ?_, ?_, fun q hq => runBlock_keepL (by decide) hz hq⟩ <;>
    simp only [runBlock, BInstr.run, lm8W3] <;> simp +decide only [upd, ↓reduceIte, ev_add, hz] <;>
    first | rfl | exact BitVec.zero_add _ | skip

set_option maxRecDepth 20000 in
theorem lm8W4_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lm8W4 (M, f)).1 = memStore32 (memStore32 M (f sp + 0x28) 0) (f sp + 0x2C) 0 ∧
    (runBlock lm8W4 (M, f)).2 (24 : Fin 32) = f sp + 0x20 ∧ (runBlock lm8W4 (M, f)).2 (9 : Fin 32) = f sp + 0x28 ∧
    (runBlock lm8W4 (M, f)).2 (8 : Fin 32) = 2 ∧
    ∀ q : Fin 32, q.val ∉ [8, 9, 24] → (runBlock lm8W4 (M, f)).2 q = f q := by
  refine ⟨?_, ?_, ?_, ?_, fun q hq => runBlock_keepL (by decide) hz hq⟩ <;>
    simp only [runBlock, BInstr.run, lm8W4] <;> simp +decide only [upd, ↓reduceIte, ev_add, hz] <;>
    first | rfl | exact BitVec.zero_add _ | skip

set_option maxRecDepth 20000 in
theorem lm8W5_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lm8W5 (M, f)).1 = memStore32 (memStore32 (memStore32 M (f sp + 0x20) (memLoad32 M (f sp + 0x28)))
      (f sp + 0x24) (memLoad32 M (f sp + 0x2C))) (f sp + 0x28) (f 20) ∧
    (runBlock lm8W5 (M, f)).2 (20 : Fin 32) = aluEval .sltu 0 (memLoad32 (memStore32 (memStore32 (memStore32 M
      (f sp + 0x20) (memLoad32 M (f sp + 0x28))) (f sp + 0x24) (memLoad32 M (f sp + 0x2C))) (f sp + 0x28) (f 20))
      (f sp + 0x28)) ∧
    ∀ q : Fin 32, q.val ∉ [10, 11, 20] → (runBlock lm8W5 (M, f)).2 q = f q := by
  refine ⟨?_, ?_, fun q hq => runBlock_keepL (by decide) hz hq⟩ <;>
    simp only [runBlock, BInstr.run, lm8W5] <;> simp +decide only [upd, ↓reduceIte, ev_add, hz] <;>
    first | rfl | exact BitVec.zero_add _ | skip


set_option exponentiation.threshold 128 in
theorem ph3_arith'8 {a x d1 b y d2 m1 m2 : Nat} (v7 : a + 2 ^ (32 * 8) * m1 = x + d1 + 0)
    (v13 : b + 2 ^ (32 * 2) * m2 = y + d2 + m1) :
    d1 + 2 ^ 256 * d2 + (x + 2 ^ 256 * y) = a + 2 ^ 256 * b + 2 ^ 320 * m2 := by
  rw [show (320 : Nat) = 256 + 64 from rfl, Nat.pow_add]
  rw [Nat.add_zero, show 32 * 8 = 256 from rfl] at v7
  rw [show 32 * 2 = 64 from rfl] at v13
  generalize (2 : Nat) ^ 256 = K at v7 ⊢
  generalize (2 : Nat) ^ 64 = L at v13 ⊢
  exact ph3_arith v7 v13

set_option exponentiation.threshold 128 in
set_option maxRecDepth 60000 in
set_option maxHeartbeats 16000000 in
/-- **Phase 3**, from 0x160 to 0x1FE: the 10 limbs at `F` and `F + 0x20`
become `x - m·mf` modulo 2^320, and `s4` the borrow out, 0 or 1. -/
theorem lm8_ph3 {M0 M : Word → BitVec 8} {P G res ap bp cp dp mp mip : Word} {n : Machine}
    (env : LMEnv8 M0 P G res ap bp cp dp mp mip) (hM : ∀ x, Sep G 0x280 x 1 → M x = M0 x)
    (s : St M P n 0x160 (reg n)) (rsp : reg n sp = G + 0x180) (r23 : reg n 23 = mp)
    (r21 : reg n 21 = G + 0x180 + 0x80) :
    ∃ n' M' sw, Steps n n' ∧ St M' P n' 0x1FE (reg n') ∧ (∀ x, Sep G 0x254 x 1 → M' x = M x) ∧ sw ≤ 1 ∧
      reg n' 20 = BitVec.ofNat 32 sw ∧
      accV M' (G + 0x180) 8 + 2 ^ 256 * accV M' (G + 0x180 + 0x20) 2 +
          accV M0 mp 8 * accV M (G + 0x180 + 0xC8) 2 =
        accV M (G + 0x180) 8 + 2 ^ 256 * accV M (G + 0x180 + 0x20) 2 + 2 ^ 320 * sw ∧
      reg n' sp = G + 0x180 ∧ ∀ q : Fin 32, q.val ∈ [3, 4, 18, 19, 22, 23, 26, 27] → reg n' q = reg n q := by
  obtain ⟨F, hF⟩ : ∃ F, G + 0x180 = F := ⟨_, rfl⟩
  rw [hF] at rsp r21 ⊢
  have hGt := env.hGt
  have tG : ∀ c, c < 0x280 → (G + BitVec.ofNat 32 c).toNat = G.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show c < 2 ^ 32 by omega),
      Nat.mod_eq_of_lt (show G.toNat + c < 2 ^ 32 by omega)]
  have fG : ∀ c, F + BitVec.ofNat 32 c = G + BitVec.ofNat 32 (0x180 + c) := fun c => by
    rw [← hF, show (0x180 : Word) = BitVec.ofNat 32 0x180 from rfl, add_ofNat_assoc]
  have eF : F = G + BitVec.ofNat 32 0x180 := hF.symm
  have hFn : F.toNat = G.toNat + 0x180 := by rw [eF, tG _ (by decide)]
  have hFa : F.toNat % 4 = 0 := by rw [hFn]; have := env.hG; omega
  have aG : ∀ c, c % 4 = 0 → c < 0x280 → (G + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h1 h2 => by
    rw [tG c h2]; have := env.hG; omega
  have sub : ∀ {b : Word} {k : Nat} (c l : Nat), c + l ≤ 0x280 → Sep G 0x280 b k → Sep (G + BitVec.ofNat 32 c) l b k :=
    fun c l h hs => hs.sub h
  have sG : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x280 → d + k ≤ 0x280 →
      Sep (G + BitVec.ofNat 32 c) n (G + BitVec.ofNat 32 d) k := fun h h1 h2 =>
    sep_offsets G h (by omega) (by omega)
  have aF : ∀ c, c % 4 = 0 → 0x180 + c < 0x280 → (F + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h1 h2 => by
    rw [fG]; exact aG _ (by omega) h2
  have sF : ∀ {b : Word} {k : Nat} (c l : Nat), 0x180 + c + l ≤ 0x280 → Sep G 0x280 b k →
      Sep (F + BitVec.ofNat 32 c) l b k := fun c l h hs => by rw [fG]; exact sub _ l h hs
  have cOf : ∀ {M' : Word → BitVec 8}, (∀ x, Sep G 0x280 x 1 → M' x = M0 x) →
      ∀ {b : Word} {code : List Nat}, CodeIn M0 b code → Sep G 0x280 b code.length → CodeIn M' b code :=
    fun hM' _ _ hc hs i hi => by rw [hM' _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have hz := s.zero
  have hc := cOf hM env.code env.sC
  -- `widening_mul_fixed::<8, 2>(F + 0x60, m, F + 0xC8)`
  obtain ⟨n1, c1, u1⟩ := St.block lm8W0 s hc lm8W0_end (by simp [BlockOk, BInstr.ok, lm8W0])
  obtain ⟨w0e, w0a0, w0a2, w0a1, w0s8, w0k⟩ := lm8W0_run (M := M) (f := reg n) hz
  rw [w0e] at u1
  have g1 : ∀ q, reg n1 q = (runBlock lm8W0 (M, reg n)).2 q := u1.regs
  have eW : lm8Lc P + 0x398 = P + 0xFFFFFE08 := by rw [BitVec.add_assoc]; rfl
  have hevW : (lm8Lc P + 0x398).toNat % 2 = 0 := by rw [eW]; exact even_at P env.hP 0xFFFFFE08 (by decide)
  obtain ⟨t1, ct1, pct1, memt1, regst1⟩ := u1.self.callRa hc lsm8_at_16a lsm8_at_16e (cb := lm8Lc P + 0x398)
    (by rw [eW, BitVec.add_assoc, BitVec.add_assoc]; rfl) hevW
  have rt1 := PEnv.reg1 regst1 u1.self.zero
  have eGW : F + 0xFFFFFFA0 = G + BitVec.ofNat 32 0x120 := by rw [eF, BitVec.add_assoc]; rfl
  have e80 : F + 0x60 = G + BitVec.ofNat 32 0x1E0 := fG 0x60
  have e118 : F + 0xC8 = G + BitVec.ofNat 32 0x248 := fG 0xC8
  have KE : K8Env t1.mem (lm8Lc P + 0x398) (F + 0xFFFFFFA0) (F + 0x60) mp (F + 0xC8) := by
    rw [memt1, eGW, e80, e118]
    exact {
      hP := hevW
      code := cOf hM env.wide env.sW
      ms := by rw [show lm8Lc P + 0x398 + 0x36AC = lm8Lc P + 0x3A44 by rw [BitVec.add_assoc]; rfl]; exact cOf hM env.mset env.sM
      mcS := by rw [show lm8Lc P + 0x398 + 0x3714 = lm8Lc P + 0x3AAC by rw [BitVec.add_assoc]; rfl]; exact cOf hM env.stub env.sU
      mcB := by rw [show lm8Lc P + 0x398 + 0x371C = lm8Lc P + 0x3AB4 by rw [BitVec.add_assoc]; rfl]; exact cOf hM env.body env.sB
      hG := aG _ (by decide) (by decide)
      hGt := by rw [tG _ (by decide)]; omega
      hx := env.hmp
      hy := aG _ (by decide) (by decide)
      hout := aG _ (by decide) (by decide)
      hot := by rw [tG _ (by decide)]; omega
      sGC := sub _ _ (by decide) env.sW
      sGM := by rw [show lm8Lc P + 0x398 + 0x36AC = lm8Lc P + 0x3A44 by rw [BitVec.add_assoc]; rfl]; exact sub _ _ (by decide) env.sM
      sGS := by rw [show lm8Lc P + 0x398 + 0x3714 = lm8Lc P + 0x3AAC by rw [BitVec.add_assoc]; rfl]; exact sub _ _ (by decide) env.sU
      sGB := by rw [show lm8Lc P + 0x398 + 0x371C = lm8Lc P + 0x3AB4 by rw [BitVec.add_assoc]; rfl]; exact sub _ _ (by decide) env.sB
      sOC := sub _ _ (by decide) env.sW
      sOB := by rw [show lm8Lc P + 0x398 + 0x371C = lm8Lc P + 0x3AB4 by rw [BitVec.add_assoc]; rfl]; exact sub _ _ (by decide) env.sB
      sOG := sG (.inr (by decide)) (by decide) (by decide)
      sXG := (sub _ _ (by decide) env.mG.symm).symm
      sYG := sG (.inr (by decide)) (by decide) (by decide) }
  have r1sp : reg n1 sp = F := by rw [g1, w0k sp (by decide), rsp]
  obtain ⟨t2, ct2, pct2, spt2, kt2, valt2, frt2⟩ := wideMul8x2_correct t1 KE pct1
    (by rw [rt1 _ (by decide), g1, w0a0, rsp]) (by rw [rt1 _ (by decide), g1, w0a1, r23])
    (by rw [rt1 _ (by decide), g1, w0a2, rsp]) (by rw [regst1]; simp [upd])
    (even_clear _ (even_at P env.hP (0x16A + 8) (by decide)))
    (by rw [rt1 _ (by decide), r1sp, BitVec.add_assoc, show (0xFFFFFFA0 : Word) + 0x60 = 0 by decide, add_lit_zero])
  rw [memt1] at valt2 frt2
  have frW : ∀ x, Sep (G + BitVec.ofNat 32 0x120) 0x60 x 1 → Sep (G + BitVec.ofNat 32 0x1E0) 40 x 1 →
      t2.mem x = M x := fun x h1 h2 => by rw [frt2 x (by rw [eGW]; exact h1) (by rw [e80]; exact h2)]
  have frG2 : ∀ x, Sep G 0x280 x 1 → t2.mem x = M0 x := fun x hx => by
    rw [frW x (sub _ _ (by decide) hx) (sub _ _ (by decide) hx), hM x hx]
  have sp2 : reg t2 sp = F := by
    rw [spt2, BitVec.add_assoc, show (0xFFFFFFA0 : Word) + 0x60 = 0 by decide, add_lit_zero]
  have k2 : ∀ q : Fin 32, q.val ∈ [3, 4, 18, 19, 20, 21, 22, 23, 26, 27] → reg t2 q = reg n q := fun q hq => by
    rw [kt2 q (by revert hq; revert q; decide), rt1 q (fun e => by subst e; revert hq; decide), g1,
      w0k q (nmem_disj hq (by decide))]
  -- `memset(F + 0x88, 0, 32)`
  have hc2 := cOf frG2 env.code env.sC
  have st2 : St t2.mem P t2 0x172 (reg t2) := ⟨pct2, rfl, fun _ => rfl⟩
  obtain ⟨n3, c3, u3⟩ := St.block lm8W1 st2 hc2 lm8W1_end (by simp [BlockOk, BInstr.ok, lm8W1])
  obtain ⟨w1e, w1a0, w1a2, w1a1, w1s9, w1k⟩ := lm8W1_run (M := t2.mem) (f := reg t2) st2.zero
  rw [w1e] at u3
  have g3 : ∀ q, reg n3 q = (runBlock lm8W1 (t2.mem, reg t2)).2 q := u3.regs
  have eMs : lm8Lc P + 0x3A44 = P + 0x34B4 := by rw [BitVec.add_assoc]; rfl
  have hevM : (lm8Lc P + 0x3A44).toNat % 2 = 0 := by rw [eMs]; exact even_at P env.hP 0x34B4 (by decide)
  obtain ⟨t3, ct3, pct3, memt3, regst3⟩ := u3.self.callRa hc2 lsm8_at_17e lsm8_at_182 (cb := lm8Lc P + 0x3A44)
    (by rw [eMs, BitVec.add_assoc, BitVec.add_assoc]; rfl) hevM
  have rt3 := PEnv.reg1 regst3 u3.self.zero
  obtain ⟨t4, ct4, pct4, memt4, -, kt4⟩ := memset_correct t3 (lm8Lc P + 0x3A44) (P + BitVec.ofNat 32 (0x17E + 8))
    (F + 0x88) 0 32 (fun i hi => by show t3.mem _ = _; rw [memt3]; exact cOf frG2 env.mset env.sM i hi) hevM
    pct3 (by rw [rt3 _ (by decide), g3, w1a0, sp2]) (by rw [rt3 _ (by decide), g3, w1a1])
    (by rw [rt3 _ (by decide), g3, w1a2]; rfl) (by rw [regst3]; simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at P env.hP (0x17E + 8) (by decide)))
    (by rw [show F + 0x88 = F + BitVec.ofNat 32 0x88 from rfl, fG, tG _ (by decide)]; omega)
    (sF 0x88 32 (by decide) env.sM)
  rw [memt3] at memt4
  have frM4 : ∀ x, Sep (F + 0x88) 32 x 1 → t4.mem x = t2.mem x := fun x hx => by
    rw [memt4]; exact fillBytes_sep hx (Nat.le_refl _)
  have frG4 : ∀ x, Sep G 0x280 x 1 → t4.mem x = M0 x := fun x hx => by
    rw [frM4 x (sF 0x88 32 (by decide) hx), frG2 x hx]
  have hc4 := cOf frG4 env.code env.sC
  have eB : lm8Bsub P = lcBsub8 (lm8Lc P) := by show P + 0xFFFF0FEE = P + 0xFFFFFA70 + 0xFFFF157E; rw [BitVec.add_assoc]; rfl
  have hb4 : CodeIn t4.mem (lm8Bsub P) borrowingSubCode := by rw [eB]; exact cOf frG4 env.bsub env.sBs
  have sBs : Sep G 0x280 (lm8Bsub P) borrowingSubCode.length := by rw [eB]; exact env.sBs
  have st4 : St t4.mem P t4 0x186 (reg t4) := ⟨pct4, rfl, fun _ => rfl⟩
  obtain ⟨n5, c5, u5⟩ := St.block lm8W2 st4 hc4 lm8W2_end (by simp [BlockOk, BInstr.ok, lm8W2])
  obtain ⟨w2e, w2s4, w2s1, w2s0, w2k⟩ := lm8W2_run (M := t4.mem) (f := reg t4) st4.zero
  rw [w2e] at u5
  have g5 : ∀ q, reg n5 q = (runBlock lm8W2 (t4.mem, reg t4)).2 q := u5.regs
  have k4 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ ra →
      reg t4 q = reg n3 q := fun q q0 q1 q2 q3 q4 q5 q6 qr => by
    rw [kt4 q q2 q3 q4 q5 q6, rt3 q qr]
  have sp4 : reg t4 sp = F := by
    rw [k4 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g3,
      w1k sp (by decide), sp2]
  have s8v : reg t4 24 = F + 0x60 := by
    rw [k4 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g3,
      w1k 24 (by decide), kt2 24 (by decide), rt1 24 (by decide), g1, w0s8, rsp]
  have s9v : reg t4 25 = F + 0x88 := by
    rw [k4 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g3,
      w1s9, sp2]
  obtain ⟨n6, d6, u6⟩ := u5.self.notTaken hc4 0x18E lsm8_at_18c (by decide) (by rw [g5, w2s0, u5.self.zero]; decide)
  have g6 : ∀ q, reg n6 q = reg n5 q := u6.regs
  have eM4 : F + 0xFFFFFFFC = G + BitVec.ofNat 32 0x17C := by rw [eF, BitVec.add_assoc]; rfl
  have e0 : F = G + BitVec.ofNat 32 0x180 := eF
  have eB8 : F + 0x88 = G + BitVec.ofNat 32 0x208 := fG 0x88
  have z0 : ∀ b : Word, b + BitVec.ofNat 32 (4 * 0) = b := fun b => add_ofNat_zero b
  obtain ⟨n7, M7, c7, u7, hc7, fr7, bm7, v7, sp7, k7⟩ := lm8_s1_loop (z := 0) (np := F) (xp := F + 0x60) (D := F + 0x88) env.hP hFa hFa
    (by exact aF 0x60 rfl (by decide)) (by exact aF 0x88 rfl (by decide)) (by rw [eB8, tG _ (by decide)]; omega)
    (by rw [eM4, e0]; exact sG (.inl (by decide)) (by decide) (by decide))
    (by rw [eM4, e80]; exact sG (.inl (by decide)) (by decide) (by decide))
    (by rw [eM4, eB8]; exact sG (.inl (by decide)) (by decide) (by decide))
    (by rw [eB8, e0]; exact sG (.inr (by decide)) (by decide) (by decide))
    (by rw [eB8, e80]; exact sG (.inr (by decide)) (by decide) (by decide))
    (by rw [eM4]; exact sub _ _ (by decide) sBs) (by rw [eM4]; exact sub _ _ (by decide) env.sC)
    (by rw [eB8]; exact sub _ _ (by decide) sBs) (by rw [eB8]; exact sub _ _ (by decide) env.sC)
    7 0 rfl u6.self hc4 hb4 (fun _ _ _ => rfl) (.inl rfl) (by show 0 + 2 ^ (32 * 0) * maskBit 0 = 0 + 0 + 0; rfl)
    (by rw [g6, g5, w2k sp (by decide), sp4]) (by rw [g6, g5, w2s1, sp4, z0])
    (by rw [g6, g5, w2k 24 (by decide), s8v, z0]) (by rw [g6, g5, w2k 25 (by decide), s9v, z0])
    (by rw [g6, g5, w2s0]; rfl) (by rw [g6, g5, w2s4])
  -- `memcpy(F, F + 0x88, 32)`
  have frG7 : ∀ x, Sep G 0x280 x 1 → M7 x = M0 x := fun x hx => by
    rw [fr7 x (by rw [eM4]; exact sub _ _ (by decide) hx) (by rw [eB8]; exact sub _ _ (by decide) hx), frG4 x hx]
  obtain ⟨n8, c8, u8⟩ := St.block lm8W3 u7 hc7 lm8W3_end (by simp [BlockOk, BInstr.ok, lm8W3])
  obtain ⟨w3e, w3a0, w3a1, w3a2, w3k⟩ := lm8W3_run (M := M7) (f := reg n7) u7.zero
  rw [w3e] at u8
  have g8 : ∀ q, reg n8 q = (runBlock lm8W3 (M7, reg n7)).2 q := u8.regs
  have eU : lm8Lc P + 0x3AAC = P + 0x351C := by rw [BitVec.add_assoc]; rfl
  have hevU : (lm8Lc P + 0x3AAC).toNat % 2 = 0 := by rw [eU]; exact even_at P env.hP 0x351C (by decide)
  obtain ⟨t9, ct9, pct9, memt9, regst9⟩ := u8.self.callRa hc7 lsm8_at_1b6 lsm8_at_1ba (cb := lm8Lc P + 0x3AAC)
    (by rw [eU, BitVec.add_assoc, BitVec.add_assoc]; rfl) hevU
  have rt9 := PEnv.reg1 regst9 u8.self.zero
  have sp8 : reg n8 sp = F := by rw [g8, w3k sp (by decide), sp7]
  have eS : F + 0xFFFFFFF0 = G + BitVec.ofNat 32 0x170 := by rw [eF, BitVec.add_assoc]; rfl
  obtain ⟨t10, ct10, pct10, spt10, -, memt10, kt10⟩ := memcpy_correct t9 (lm8Lc P + 0x3AAC)
    (P + BitVec.ofNat 32 (0x1B6 + 8)) F (F + 0x88) 32 (fun i hi => by rw [memt9]; exact cOf frG7 env.stub env.sU i hi)
    hevU pct9 (by rw [rt9 _ (by decide), g8, w3a0, sp7]) (by rw [rt9 _ (by decide), g8, w3a1, sp7])
    (by rw [rt9 _ (by decide), g8, w3a2]; rfl) (by rw [regst9]; simp [upd])
    (even_clear _ (even_at P env.hP (0x1B6 + 8) (by decide)))
    (by
      rw [memt9, rt9 _ (by decide), sp8, show lm8Lc P + 0x3AAC + 8 = lm8Lc P + 0x3AB4 by rw [BitVec.add_assoc]; rfl, eS,
        eB8, e0]
      exact {
        code := cOf frG7 env.body env.sB
        hDC := sub 0x180 32 (by decide) env.sB
        hFC := sub 0x170 16 (by decide) env.sB
        hdF := sG (.inr (by decide)) (by decide) (by decide)
        hsF := sG (.inr (by decide)) (by decide) (by decide)
        hsep := sG (.inl (by decide)) (by decide) (by decide)
        hF := aG _ (by decide) (by decide)
        hFw := by rw [tG _ (by decide)]; omega
        hdw := by rw [tG _ (by decide)]; omega
        hsw := by rw [tG _ (by decide)]; omega })
  rw [rt9 _ (by decide), sp8, eS, memt9] at memt10
  have kA : ∀ q : Fin 32, q.val ∈ [3, 4, 18, 19, 21, 22, 23, 26, 27] → reg t10 q = reg n q := fun q hq => by
    have ne : ∀ w : Fin 32, w.val ∉ [3, 4, 18, 19, 21, 22, 23, 26, 27] → q ≠ w := fun w hw e => hw (e ▸ hq)
    rw [kt10 q (ne a1 (by decide)) (ne a2 (by decide)) (ne a3 (by decide)) (ne a4 (by decide)) (ne a5 (by decide))
        (ne a6 (by decide)) (ne a7 (by decide)) (ne (5 : Fin 32) (by decide)) (ne (6 : Fin 32) (by decide))
        (ne 7 (by decide)) (ne 28 (by decide)) (ne 29 (by decide)) (ne 30 (by decide)) (ne sp (by decide)),
      rt9 q (ne ra (by decide)), g8, w3k q (nmem_disj hq (by decide)),
      k7 q (ne a0 (by decide)) (ne a1 (by decide)) (ne a2 (by decide)) (ne 20 (by decide)) (ne a3 (by decide))
        (ne a4 (by decide)) (ne ra (by decide)) (ne 9 (by decide)) (ne 24 (by decide)) (ne 25 (by decide))
        (ne 8 (by decide)),
      g6, g5, w2k q (nmem_disj hq (by decide)),
      k4 q (ne a0 (by decide)) (ne a1 (by decide)) (ne a2 (by decide)) (ne a3 (by decide)) (ne a4 (by decide))
        (ne a5 (by decide)) (ne a6 (by decide)) (ne ra (by decide)),
      g3, w1k q (nmem_disj hq (by decide))]
    exact k2 q (by revert hq; revert q; decide)
  have sp10 : reg t10 sp = F := by rw [spt10, rt9 _ (by decide), sp8]
  have b10 : reg t10 20 = reg n7 20 := by
    rw [kt10 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rt9 _ (by decide), g8, w3k 20 (by decide)]
  have frG10 : ∀ x, Sep G 0x280 x 1 → t10.mem x = M0 x := fun x hx => by
    rw [memt10 x (sub 0x170 16 (by decide) hx), copyBytes_sep (by rw [e0]; exact sub 0x180 32 (by decide) hx)
      (Nat.le_refl _), frG7 x hx]
  have hc10 := cOf frG10 env.code env.sC
  have st10 : St t10.mem P t10 0x1BE (reg t10) := ⟨pct10, rfl, fun _ => rfl⟩
  have e38 : F + 0x28 = G + BitVec.ofNat 32 0x1A8 := fG 0x28
  have e3c : F + 0x2C = G + BitVec.ofNat 32 0x1AC := fG 0x2C
  obtain ⟨n11, c11, u11⟩ := St.block lm8W4 st10 hc10 lm8W4_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, lm8W4, upd, ↓reduceIte, and_true, true_and]
    rw [sp10, e38, e3c]
    exact ⟨⟨aG _ (by decide) (by decide), sub _ _ (by decide) env.sC⟩, aG _ (by decide) (by decide),
      sub _ _ (by decide) env.sC⟩)
  obtain ⟨w4e, w4s8, w4s1, w4s0, w4k⟩ := lm8W4_run (M := t10.mem) (f := reg t10) st10.zero
  rw [w4e, sp10] at u11
  obtain ⟨M11, hM11⟩ : ∃ M11, memStore32 (memStore32 t10.mem (F + 0x28) 0) (F + 0x2C) 0 = M11 := ⟨_, rfl⟩
  rw [hM11] at u11
  have fr11 : ∀ x, Sep (F + 0x28) 8 x 1 → M11 x = t10.mem x := fun x hx => by
    have h4 : Sep (F + 0x2C) 4 x 1 := by
      have := hx.sub (c := 4) (l := 4) (by decide); rw [BitVec.add_assoc] at this; exact this
    have h0 : Sep (F + 0x28) 4 x 1 := by
      have := hx.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    rw [← hM11, memStore32_get_sep h4, memStore32_get_sep h0]
  have frG11 : ∀ x, Sep G 0x280 x 1 → M11 x = M0 x := fun x hx => by
    rw [fr11 x (by rw [e38]; exact sub _ _ (by decide) hx), frG10 x hx]
  have hc11 := cOf frG11 env.code env.sC
  have hb11 : CodeIn M11 (lm8Bsub P) borrowingSubCode := by rw [eB]; exact cOf frG11 env.bsub env.sBs
  have g11 : ∀ q, reg n11 q = (runBlock lm8W4 (t10.mem, reg t10)).2 q := u11.regs
  obtain ⟨n12, d12, u12⟩ := u11.self.notTaken hc11 0x1CC lsm8_at_1ca (by decide) (by rw [g11, w4s0, u11.self.zero]; decide)
  have g12 : ∀ q, reg n12 q = reg n11 q := u12.regs
  have e30 : F + 0x20 = G + BitVec.ofNat 32 0x1A0 := fG 0x20
  have eB0 : F + 0x80 = G + BitVec.ofNat 32 0x200 := fG 0x80
  obtain ⟨n13, M13, c13, u13, hc13, fr13, bm13, v13, sp13, k13⟩ := lm8_s2_loop (z := maskBit (reg n7 20))
    (np := F + 0x20) (xp := F + 0x80) (D := F + 0x28) env.hP hFa
    (by exact aF 0x20 rfl (by decide)) (by exact aF 0x80 rfl (by decide)) (by exact aF 0x28 rfl (by decide))
    (by rw [e38, tG _ (by decide)]; omega)
    (by rw [eM4, e30]; exact sG (.inl (by decide)) (by decide) (by decide))
    (by rw [eM4, eB0]; exact sG (.inl (by decide)) (by decide) (by decide))
    (by rw [eM4, e38]; exact sG (.inl (by decide)) (by decide) (by decide))
    (by rw [e38, e30]; exact sG (.inr (by decide)) (by decide) (by decide))
    (by rw [e38, eB0]; exact sG (.inl (by decide)) (by decide) (by decide))
    (by rw [eM4]; exact sub _ _ (by decide) sBs) (by rw [eM4]; exact sub _ _ (by decide) env.sC)
    (by rw [e38]; exact sub _ _ (by decide) sBs) (by rw [e38]; exact sub _ _ (by decide) env.sC)
    1 0 rfl u12.self hc11 hb11 (fun _ _ _ => rfl) (by rw [g12, g11, w4k 20 (by decide), b10]; exact bm7)
    (by show 0 + 1 * maskBit (reg n12 20) = 0 + 0 + maskBit (reg n7 20)
        rw [g12, g11, w4k 20 (by decide), b10]; omega)
    (by rw [g12, g11, w4k sp (by decide), sp10]) (by rw [g12, g11, w4s8, sp10, z0])
    (by rw [g12, g11, w4k 21 (by decide), kA 21 (by decide), r21, z0])
    (by rw [g12, g11, w4s1, sp10, z0]) (by rw [g12, g11, w4s0]; rfl) rfl
  -- the high limbs down, and the borrow as 0 or 1
  have e34 : F + 0x24 = G + BitVec.ofNat 32 0x1A4 := fG 0x24
  obtain ⟨n14, c14, u14⟩ := St.block lm8W5 u13 hc13 lm8W5_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, lm8W5, upd, ↓reduceIte, and_true, true_and]
    rw [sp13, e38, e3c, e30, e34]
    exact ⟨aG _ (by decide) (by decide), aG _ (by decide) (by decide),
      ⟨aG _ (by decide) (by decide), sub _ _ (by decide) env.sC⟩, ⟨aG _ (by decide) (by decide), sub _ _ (by decide) env.sC⟩,
      ⟨aG _ (by decide) (by decide), sub _ _ (by decide) env.sC⟩, aG _ (by decide) (by decide)⟩)
  obtain ⟨w5e, w5s4, w5k⟩ := lm8W5_run (M := M13) (f := reg n13) u13.zero
  rw [w5e, sp13] at u14
  rw [sp13] at w5s4
  obtain ⟨b1, hb1⟩ : ∃ b1, reg n7 20 = b1 := ⟨_, rfl⟩
  obtain ⟨b2, hb2⟩ : ∃ b2, reg n13 20 = b2 := ⟨_, rfl⟩
  rw [hb1] at bm7 v7 v13
  rw [hb2] at bm13 v13 u14 w5s4
  -- limbs, compared byte by byte inside the region
  have accF : ∀ {M1 M2 : Word → BitVec 8} (c k : Nat), 0x180 + c + 4 * k ≤ 0x280 →
      (∀ d, 0x180 + c ≤ d → d < 0x180 + c + 4 * k → M1 (G + BitVec.ofNat 32 d) = M2 (G + BitVec.ofNat 32 d)) →
      accV M1 (F + BitVec.ofNat 32 c) k = accV M2 (F + BitVec.ofNat 32 c) k := fun c k hb h =>
    accV_congr k fun i hi => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc, add_ofNat_assoc, fG]; exact h _ (by omega) (by omega)
  have gS : ∀ {c l d : Nat}, c + l ≤ d ∨ d + 1 ≤ c → c + l ≤ 0x280 → d < 0x280 →
      Sep (G + BitVec.ofNat 32 c) l (G + BitVec.ofNat 32 d) 1 := fun h h1 h2 => sG h h1 (by omega)
  have bt2 : ∀ d, d < 0x280 → d < 0x120 ∨ (0x180 ≤ d ∧ d < 0x1E0) ∨ 0x208 ≤ d →
      t2.mem (G + BitVec.ofNat 32 d) = M (G + BitVec.ofNat 32 d) := fun d hd h => by
    apply frW
    · rcases h with h | h | h
      · exact gS (.inr (by omega)) (by decide) hd
      · exact gS (.inl (by omega)) (by decide) hd
      · exact gS (.inl (by omega)) (by decide) hd
    · rcases h with h | h | h
      · exact gS (.inr (by omega)) (by decide) hd
      · exact gS (.inr (by omega)) (by decide) hd
      · exact gS (.inl (by omega)) (by decide) hd
  have bt4 : ∀ d, d < 0x280 → d < 0x208 ∨ 0x228 ≤ d → t4.mem (G + BitVec.ofNat 32 d) = t2.mem (G + BitVec.ofNat 32 d) :=
    fun d hd h => by
      rcases h with h | h
      · exact frM4 _ (by rw [eB8]; exact gS (.inr (by omega)) (by decide) hd)
      · exact frM4 _ (by rw [eB8]; exact gS (.inl (by omega)) (by decide) hd)
  have b7 : ∀ d, d < 0x280 → d < 0x17C ∨ (0x180 ≤ d ∧ d < 0x208) ∨ 0x228 ≤ d →
      M7 (G + BitVec.ofNat 32 d) = t4.mem (G + BitVec.ofNat 32 d) := fun d hd h => by
    apply fr7
    · rw [eM4]; rcases h with h | h | h
      · exact gS (.inr (by omega)) (by decide) hd
      · exact gS (.inl (by omega)) (by decide) hd
      · exact gS (.inl (by omega)) (by decide) hd
    · rw [eB8]; rcases h with h | h | h
      · exact gS (.inr (by omega)) (by decide) hd
      · exact gS (.inr (by omega)) (by decide) hd
      · exact gS (.inl (by omega)) (by decide) hd
  have b10 : ∀ d, d < 0x280 → d < 0x170 ∨ 0x1A0 ≤ d → t10.mem (G + BitVec.ofNat 32 d) = M7 (G + BitVec.ofNat 32 d) :=
    fun d hd h => by
      rcases h with h | h
      · rw [memt10 _ (gS (.inr (by omega)) (by decide) hd)]
        exact copyBytes_sep (by rw [e0]; exact gS (.inr (by omega)) (by decide) hd) (Nat.le_refl _)
      · rw [memt10 _ (gS (.inl (by omega)) (by decide) hd)]
        exact copyBytes_sep (by rw [e0]; exact gS (.inl (by omega)) (by decide) hd) (Nat.le_refl _)
  have b11 : ∀ d, d < 0x280 → d < 0x1A8 ∨ 0x1B0 ≤ d → M11 (G + BitVec.ofNat 32 d) = t10.mem (G + BitVec.ofNat 32 d) :=
    fun d hd h => by
      rcases h with h | h
      · exact fr11 _ (by rw [e38]; exact gS (.inr (by omega)) (by decide) hd)
      · exact fr11 _ (by rw [e38]; exact gS (.inl (by omega)) (by decide) hd)
  have b13 : ∀ d, d < 0x280 → d < 0x17C ∨ (0x180 ≤ d ∧ d < 0x1A8) ∨ 0x1B0 ≤ d →
      M13 (G + BitVec.ofNat 32 d) = M11 (G + BitVec.ofNat 32 d) := fun d hd h => by
    apply fr13
    · rw [eM4]; rcases h with h | h | h
      · exact gS (.inr (by omega)) (by decide) hd
      · exact gS (.inl (by omega)) (by decide) hd
      · exact gS (.inl (by omega)) (by decide) hd
    · rw [e38]; rcases h with h | h | h
      · exact gS (.inr (by omega)) (by decide) hd
      · exact gS (.inr (by omega)) (by decide) hd
      · exact gS (.inl (by omega)) (by decide) hd
  obtain ⟨M14, hM14⟩ : ∃ M14, memStore32 (memStore32 (memStore32 M13 (F + 0x20) (memLoad32 M13 (F + 0x28)))
      (F + 0x24) (memLoad32 M13 (F + 0x2C))) (F + 0x28) b2 = M14 := ⟨_, rfl⟩
  rw [hM14] at u14 w5s4
  have s30 : ∀ {x : Word}, Sep (F + 0x20) 12 x 1 → M14 x = M13 x := fun {x} hx => by
    have h8 : Sep (F + 0x28) 4 x 1 := by
      have := hx.sub (c := 8) (l := 4) (by decide); rw [BitVec.add_assoc] at this; exact this
    have h4 : Sep (F + 0x24) 4 x 1 := by
      have := hx.sub (c := 4) (l := 4) (by decide); rw [BitVec.add_assoc] at this; exact this
    have h0 : Sep (F + 0x20) 4 x 1 := by
      have := hx.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    rw [← hM14, memStore32_get_sep h8, memStore32_get_sep h4, memStore32_get_sep h0]
  have b14 : ∀ d, d < 0x280 → d < 0x1A0 ∨ 0x1AC ≤ d → M14 (G + BitVec.ofNat 32 d) = M13 (G + BitVec.ofNat 32 d) :=
    fun d hd h => by
      rcases h with h | h
      · exact s30 (by rw [e30]; exact gS (.inr (by omega)) (by decide) hd)
      · exact s30 (by rw [e30]; exact gS (.inl (by omega)) (by decide) hd)
  have z0' : ∀ b : Word, b = b + BitVec.ofNat 32 0 := fun b => (add_ofNat_zero b).symm
  -- the value
  have E1 : accV M14 F 8 = accV M7 (F + 0x88) 8 := by
    have h1 : accV M14 (F + BitVec.ofNat 32 0) 8 = accV t10.mem (F + BitVec.ofNat 32 0) 8 :=
      accF 0 8 (by decide) fun d h1 h2 => by
        rw [b14 d (by omega) (by dis), b13 d (by omega) (by dis), b11 d (by omega) (by dis)]
    rw [add_ofNat_zero] at h1
    rw [h1]
    apply accV_congr2 8; intro i hi
    have e : memLoad32 t10.mem (F + BitVec.ofNat 32 (4 * i)) =
        memLoad32 (copyBytes M7 F (F + 0x88) 32) (F + BitVec.ofNat 32 (4 * i)) :=
      memLoad32_congr fun j hj => memt10 _ (by
        rw [add_ofNat_assoc, fG]; exact gS (.inl (by omega)) (by decide) (by omega))
    rw [e, cb_load (by omega) (by decide)]
  have E2 : accV M14 (F + 0x20) 2 = accV M13 (F + 0x28) 2 := by
    apply accV_congr2 2; intro i hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · rw [← z0', ← z0', ← hM14]; simp (disch := decide) only [ls_lit, ls_same]
    · rw [show F + 0x20 + BitVec.ofNat 32 (4 * 1) = F + 0x24 by rw [BitVec.add_assoc]; rfl,
        show F + 0x28 + BitVec.ofNat 32 (4 * 1) = F + 0x2C by rw [BitVec.add_assoc]; rfl, ← hM14]
      simp (disch := decide) only [ls_lit, ls_same]
  have E3 : accV t4.mem F 8 = accV M F 8 := by
    have := accF (M1 := t4.mem) (M2 := M) 0 8 (by decide) fun d h1 h2 => by
      rw [bt4 d (by omega) (by dis), bt2 d (by omega) (by dis)]
    rwa [add_ofNat_zero] at this
  have E4 : accV M11 (F + 0x20) 2 = accV M (F + 0x20) 2 :=
    accF 0x20 2 (by decide) fun d h1 h2 => by
      rw [b11 d (by omega) (by dis), b10 d (by omega) (by dis), b7 d (by omega) (by dis),
        bt4 d (by omega) (by dis), bt2 d (by omega) (by dis)]
  have E5 : accV t2.mem (F + 0x60) 10 = accV t4.mem (F + 0x60) 8 + 2 ^ 256 * accV M11 (F + 0x80) 2 := by
    rw [show (10 : Nat) = 8 + 2 from rfl, accV_split,
      show F + 0x60 + BitVec.ofNat 32 (4 * 8) = F + 0x80 by rw [BitVec.add_assoc]; rfl,
      show 32 * 8 = 256 from rfl]
    have h1 : accV t2.mem (F + 0x60) 8 = accV t4.mem (F + 0x60) 8 :=
      accF 0x60 8 (by decide) fun d h1 h2 => (bt4 d (by omega) (by dis)).symm
    have h2 : accV t2.mem (F + 0x80) 2 = accV M11 (F + 0x80) 2 :=
      accF 0x80 2 (by decide) fun d h1 h2 => by
        rw [b11 d (by omega) (by dis), b10 d (by omega) (by dis), b7 d (by omega) (by dis),
          bt4 d (by omega) (by dis)]
    rw [h1, h2]
  have E7 : accV M mp 8 = accV M0 mp 8 :=
    accV_congr 8 fun i hi => memLoad32_congr fun j hj => hM _ (by
      have := env.mG.symm.subR (c := 4 * i + j) (l := 1) (by omega); rwa [← add_ofNat_assoc] at this)
  have mb01 : ∀ {b : Word}, b = 0 ∨ b = 0xFFFFFFFF → maskBit b ≤ 1 := fun h => by rcases h with rfl | rfl <;> decide
  refine ⟨n14, M14, maskBit b2, c1.trans (ct1.trans (ct2.trans (c3.trans (ct3.trans (ct4.trans (c5.trans (.cons d6
    (c7.trans (c8.trans (ct9.trans (ct10.trans (c11.trans (.cons d12 (c13.trans c14)))))))))))))),
    u14.self, fun x hx => ?_, mb01 bm13, ?_, ?_, ?_, fun q hq => ?_⟩
  · have hs : ∀ c l, c + l ≤ 0x254 → Sep (G + BitVec.ofNat 32 c) l x 1 := fun c l h => hx.sub h
    rw [s30 (by rw [e30]; exact hs _ _ (by decide)), fr13 x (by rw [eM4]; exact hs _ _ (by decide))
        (by rw [e38]; exact hs _ _ (by decide)), fr11 x (by rw [e38]; exact hs _ _ (by decide)),
      memt10 x (hs _ _ (by decide)), copyBytes_sep (by rw [e0]; exact hs _ _ (by decide)) (Nat.le_refl _),
      fr7 x (by rw [eM4]; exact hs _ _ (by decide)) (by rw [eB8]; exact hs _ _ (by decide)),
      frM4 x (by rw [eB8]; exact hs _ _ (by decide)), frW x (hs _ _ (by decide)) (hs _ _ (by decide))]
  · rw [u14.regs, w5s4]
    have : memLoad32 M14 (F + 0x28) = b2 := by rw [← hM14]; simp (disch := decide) only [ls_lit, ls_same]
    rw [this]
    rcases bm13 with rfl | rfl <;> decide
  · rw [E1, E2, ← E7, ← valt2, E5, ← E3, ← E4]
    exact ph3_arith'8 v7 v13
  · rw [u14.regs, w5k sp (by decide), sp13]
  · have ne : ∀ w : Fin 32, w.val ∉ [3, 4, 18, 19, 22, 23, 26, 27] → q ≠ w := fun w hw e => hw (e ▸ hq)
    rw [u14.regs, w5k q (nmem_disj hq (by decide)),
      k13 q (ne a0 (by decide)) (ne a1 (by decide)) (ne a2 (by decide)) (ne 20 (by decide)) (ne a3 (by decide))
        (ne a4 (by decide)) (ne ra (by decide)) (ne 24 (by decide)) (ne 21 (by decide)) (ne 9 (by decide))
        (ne 8 (by decide)),
      g12, g11, w4k q (nmem_disj hq (by decide)), kA q (by revert hq; revert q; decide)]


/-! ## Phase 4: the conditional negation and the shift, from 0x1FE to 0x21C -/

def lm8N0 : List BInstr := [.alu .add a0 x0 sp, .aluImm .add a1 sp 0x20, .alu .add a2 x0 (20 : Fin 32),
  .alu .add (21 : Fin 32) x0 sp]
def lm8N1 : List BInstr := [.alu .add a0 x0 sp, .aluImm .add a1 sp 0x20, .alu .add a2 x0 (19 : Fin 32)]

section
set_option maxRecDepth 20000
theorem lm8N0_end : blockEnd lincombShiftMod8Code 0x1FE lm8N0 = some 0x206 := by decide
theorem lm8N1_end : blockEnd lincombShiftMod8Code 0x20E lm8N1 = some 0x214 := by decide
end

set_option maxRecDepth 20000 in
theorem lm8N0_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lm8N0 (M, f)).1 = M ∧ (runBlock lm8N0 (M, f)).2 a0 = f sp ∧ (runBlock lm8N0 (M, f)).2 a1 = f sp + 0x20 ∧
    (runBlock lm8N0 (M, f)).2 a2 = f 20 ∧ (runBlock lm8N0 (M, f)).2 (21 : Fin 32) = f sp ∧
    ∀ q : Fin 32, q.val ∉ [10, 11, 12, 21] → (runBlock lm8N0 (M, f)).2 q = f q := by
  refine ⟨?_, ?_, ?_, ?_, ?_, fun q hq => runBlock_keepL (by decide) hz hq⟩ <;>
    simp only [runBlock, BInstr.run, lm8N0] <;> simp +decide only [upd, ↓reduceIte, ev_add, hz] <;>
    first | rfl | exact BitVec.zero_add _ | skip

set_option maxRecDepth 20000 in
theorem lm8N1_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lm8N1 (M, f)).1 = M ∧ (runBlock lm8N1 (M, f)).2 a0 = f sp ∧ (runBlock lm8N1 (M, f)).2 a1 = f sp + 0x20 ∧
    (runBlock lm8N1 (M, f)).2 a2 = f 19 ∧
    ∀ q : Fin 32, q.val ∉ [10, 11, 12] → (runBlock lm8N1 (M, f)).2 q = f q := by
  refine ⟨?_, ?_, ?_, ?_, fun q hq => runBlock_keepL (by decide) hz hq⟩ <;>
    simp only [runBlock, BInstr.run, lm8N1] <;> simp +decide only [upd, ↓reduceIte, ev_add, hz] <;>
    first | rfl | exact BitVec.zero_add _ | skip

set_option exponentiation.threshold 128 in
set_option maxRecDepth 60000 in
set_option maxHeartbeats 16000000 in
/-- **Phase 4**, from 0x1FE to 0x21C: negate the 320-bit value at `F` and
`F + 0x20` when the borrow is set, then shift it right by `shift`. -/
theorem lm8_ph4 {M0 M : Word → BitVec 8} {P G res ap bp cp dp mp mip : Word} {n : Machine} {sw sh : Nat}
    (env : LMEnv8 M0 P G res ap bp cp dp mp mip) (hM : ∀ x, Sep G 0x280 x 1 → M x = M0 x)
    (s : St M P n 0x1FE (reg n)) (rsp : reg n sp = G + 0x180) (r20 : reg n 20 = BitVec.ofNat 32 sw) (hsw : sw ≤ 1)
    (r19 : reg n 19 = BitVec.ofNat 32 sh) (hs1 : 1 ≤ sh) (hs2 : sh ≤ 63) :
    ∃ n' M', Steps n n' ∧ St M' P n' 0x21C (reg n') ∧ (∀ x, Sep G 0x254 x 1 → M' x = M x) ∧
      accV M' (G + 0x180) 8 + 2 ^ 256 * accV M' (G + 0x180 + 0x20) 2 =
        (if sw = 1 then (2 ^ 320 - (accV M (G + 0x180) 8 + 2 ^ 256 * accV M (G + 0x180 + 0x20) 2)) % 2 ^ 320
          else accV M (G + 0x180) 8 + 2 ^ 256 * accV M (G + 0x180 + 0x20) 2) / 2 ^ sh ∧
      reg n' sp = G + 0x180 ∧ reg n' 21 = G + 0x180 ∧
      ∀ q : Fin 32, q.val ∈ [3, 4, 18, 19, 20, 22, 23, 26, 27] → reg n' q = reg n q := by
  obtain ⟨F, hF⟩ : ∃ F, G + 0x180 = F := ⟨_, rfl⟩
  rw [hF] at rsp ⊢
  have hGt := env.hGt
  have tG : ∀ c, c < 0x280 → (G + BitVec.ofNat 32 c).toNat = G.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show c < 2 ^ 32 by omega),
      Nat.mod_eq_of_lt (show G.toNat + c < 2 ^ 32 by omega)]
  have fG : ∀ c, F + BitVec.ofNat 32 c = G + BitVec.ofNat 32 (0x180 + c) := fun c => by
    rw [← hF, show (0x180 : Word) = BitVec.ofNat 32 0x180 from rfl, add_ofNat_assoc]
  have eF : F = G + BitVec.ofNat 32 0x180 := hF.symm
  have hFn : F.toNat = G.toNat + 0x180 := by rw [eF, tG _ (by decide)]
  have hFa : F.toNat % 4 = 0 := by rw [hFn]; have := env.hG; omega
  have aG : ∀ c, c % 4 = 0 → c < 0x280 → (G + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h1 h2 => by
    rw [tG c h2]; have := env.hG; omega
  have sub : ∀ {b : Word} {k : Nat} (c l : Nat), c + l ≤ 0x280 → Sep G 0x280 b k → Sep (G + BitVec.ofNat 32 c) l b k :=
    fun c l h hs => hs.sub h
  have sG : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x280 → d + k ≤ 0x280 →
      Sep (G + BitVec.ofNat 32 c) n (G + BitVec.ofNat 32 d) k := fun h h1 h2 =>
    sep_offsets G h (by omega) (by omega)
  have aF : ∀ c, c % 4 = 0 → 0x180 + c < 0x280 → (F + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h1 h2 => by
    rw [fG]; exact aG _ (by omega) h2
  have sF : ∀ {b : Word} {k : Nat} (c l : Nat), 0x180 + c + l ≤ 0x280 → Sep G 0x280 b k →
      Sep (F + BitVec.ofNat 32 c) l b k := fun c l h hs => by rw [fG]; exact sub _ l h hs
  have cOf : ∀ {M' : Word → BitVec 8}, (∀ x, Sep G 0x280 x 1 → M' x = M0 x) →
      ∀ {b : Word} {code : List Nat}, CodeIn M0 b code → Sep G 0x280 b code.length → CodeIn M' b code :=
    fun hM' _ _ hc hs i hi => by rw [hM' _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have hz := s.zero
  have hc := cOf hM env.code env.sC
  obtain ⟨n1, c1, u1⟩ := St.block lm8N0 s hc lm8N0_end (by simp [BlockOk, BInstr.ok, lm8N0])
  obtain ⟨n0e, n0a0, n0a1, n0a2, n0s5, n0k⟩ := lm8N0_run (M := M) (f := reg n) hz
  rw [n0e] at u1
  have g1 : ∀ q, reg n1 q = (runBlock lm8N0 (M, reg n)).2 q := u1.regs
  have eN : lm8Lc P + 0x480 = P + 0xFFFFFEF0 := by rw [BitVec.add_assoc]; rfl
  have hevN : (lm8Lc P + 0x480).toNat % 2 = 0 := by rw [eN]; exact even_at P env.hP 0xFFFFFEF0 (by decide)
  obtain ⟨t1, ct1, pct1, memt1, regst1⟩ := u1.self.callRa hc lsm8_at_206 lsm8_at_20a (cb := lm8Lc P + 0x480)
    (by rw [eN, BitVec.add_assoc, BitVec.add_assoc]; rfl) hevN
  have rt1 := PEnv.reg1 regst1 u1.self.zero
  have eR : c8R F = G + BitVec.ofNat 32 0xD0 := by show F + 0xFFFFFF50 = _; rw [eF, BitVec.add_assoc]; rfl
  have e0 : F = G + BitVec.ofNat 32 0x180 := eF
  have e30 : F + 0x20 = G + BitVec.ofNat 32 0x1A0 := fG 0x20
  have eo : ∀ c : Nat, lm8Lc P + 0x480 + BitVec.ofNat 32 c = lm8Lc P + BitVec.ofNat 32 (0x480 + c) := fun c => by
    rw [show (0x480 : Word) = BitVec.ofNat 32 0x480 from rfl, add_ofNat_assoc]
  have CE : C8Env t1.mem (lm8Lc P + 0x480) F F (F + 0x20) := by
    rw [memt1]
    have e2 : lm8Lc P + 0x480 + 0xFFFFFAAA = lm8Lc P + 0xFFFFFF2A := by rw [BitVec.add_assoc]; rfl
    exact {
      hP := hevN
      code := cOf hM env.neg env.sN
      mset := by rw [show (0x35C4 : Word) = BitVec.ofNat 32 0x35C4 from rfl, eo]; exact cOf hM env.mset env.sM
      stub := by rw [show (0x362C : Word) = BitVec.ofNat 32 0x362C from rfl, eo]; exact cOf hM env.stub env.sU
      body := by rw [show (0x3634 : Word) = BitVec.ofNat 32 0x3634 from rfl, eo]; exact cOf hM env.body env.sB
      sel2 := by rw [show (0x22AE : Word) = BitVec.ofNat 32 0x22AE from rfl, eo]; exact cOf hM env.sel2 env.s2
      sel12 := by rw [e2]; exact cOf hM env.sel12 env.s12
      zero := cOf hM env.zero env.sZ
      one := cOf hM env.one env.sO
      hsp := hFa
      hS := by omega
      hlo := hFa
      hhi := by rw [e30]; exact aG _ (by decide) (by decide)
      hwl := by omega
      hwh := by rw [e30, tG _ (by decide)]; omega
      sRC := by rw [eR]; exact sub _ _ (by decide) env.sN
      sRM := by rw [eR, show (0x35C4 : Word) = BitVec.ofNat 32 0x35C4 from rfl, eo]; exact sub _ _ (by decide) env.sM
      sRU := by rw [eR, show (0x362C : Word) = BitVec.ofNat 32 0x362C from rfl, eo]; exact sub _ _ (by decide) env.sU
      sRB := by rw [eR, show (0x3634 : Word) = BitVec.ofNat 32 0x3634 from rfl, eo]; exact sub _ _ (by decide) env.sB
      sR2 := by rw [eR, show (0x22AE : Word) = BitVec.ofNat 32 0x22AE from rfl, eo]; exact sub _ _ (by decide) env.s2
      sRL := by rw [eR, e2]; exact sub _ _ (by decide) env.s12
      sRZ := by rw [eR]; exact sub _ _ (by decide) env.sZ
      sRO := by rw [eR]; exact sub _ _ (by decide) env.sO
      sLR := by rw [eR, e0]; exact sG (.inr (by decide)) (by decide) (by decide)
      sHR := by rw [eR, e30]; exact sG (.inr (by decide)) (by decide) (by decide)
      sLH := by rw [e30, e0]; exact sG (.inl (by decide)) (by decide) (by decide)
      sLC := by rw [e0]; exact sub _ _ (by decide) env.sN
      sLB := by rw [e0, show (0x3634 : Word) = BitVec.ofNat 32 0x3634 from rfl, eo]; exact sub _ _ (by decide) env.sB
      sL2 := by rw [e0, show (0x22AE : Word) = BitVec.ofNat 32 0x22AE from rfl, eo]; exact sub _ _ (by decide) env.s2
      sHC := by rw [e30]; exact sub _ _ (by decide) env.sN }
  have hfl : BitVec.ofNat 32 sw = 0 ∨ BitVec.ofNat 32 sw = 1 := by
    rcases (by omega : sw = 0 ∨ sw = 1) with h | h <;> rw [h] <;> decide
  obtain ⟨t2, ct2, pct2, spt2, kt2, valt2, frt2⟩ := condNeg8_correct t1 CE pct1
    (by rw [rt1 _ (by decide), g1, n0k sp (by decide), rsp]) (by rw [rt1 _ (by decide), g1, n0a0, rsp])
    (by rw [rt1 _ (by decide), g1, n0a1, rsp]) (by rw [rt1 _ (by decide), g1, n0a2, r20]) hfl
    (by rw [regst1]; simp [upd]) (even_clear _ (even_at P env.hP (0x206 + 8) (by decide)))
  rw [memt1] at valt2 frt2
  have frN : ∀ x, Sep (G + BitVec.ofNat 32 0xD0) 0xB0 x 1 → Sep (G + BitVec.ofNat 32 0x180) 0x38 x 1 →
      t2.mem x = M x := fun x h1 h2 => by
    apply frt2 x (by rw [eR]; exact h1)
    · rw [e0]; have := h2.sub (c := 0) (l := 32) (by decide); rwa [add_ofNat_zero] at this
    · rw [e30, show (0x1A0 : Nat) = 0x180 + 0x20 from rfl, ← add_ofNat_assoc]; exact h2.sub (c := 0x20) (l := 8) (by decide)
  have frG2 : ∀ x, Sep G 0x280 x 1 → t2.mem x = M0 x := fun x hx => by
    rw [frN x (sub _ _ (by decide) hx) (sub _ _ (by decide) hx), hM x hx]
  have hc2 := cOf frG2 env.code env.sC
  have st2 : St t2.mem P t2 0x20E (reg t2) := ⟨pct2, rfl, fun _ => rfl⟩
  obtain ⟨n3, c3, u3⟩ := St.block lm8N1 st2 hc2 lm8N1_end (by simp [BlockOk, BInstr.ok, lm8N1])
  obtain ⟨n1e, n1a0, n1a1, n1a2, n1k⟩ := lm8N1_run (M := t2.mem) (f := reg t2) st2.zero
  rw [n1e] at u3
  have g3 : ∀ q, reg n3 q = (runBlock lm8N1 (t2.mem, reg t2)).2 q := u3.regs
  have eS : lm8Shr P = P + 0xFFFFFBF4 := rfl
  have hevS : (lm8Shr P).toNat % 2 = 0 := even_at P env.hP 0xFFFFFBF4 (by decide)
  obtain ⟨t3, ct3, pct3, memt3, regst3⟩ := u3.self.callRa hc2 lsm8_at_214 lsm8_at_218 (cb := lm8Shr P)
    (by rw [eS, BitVec.add_assoc, BitVec.add_assoc]; rfl) hevS
  have rt3 := PEnv.reg1 regst3 u3.self.zero
  have eF' : shF8 F = G + BitVec.ofNat 32 0x110 := by show F + 0xFFFFFF90 = _; rw [eF, BitVec.add_assoc]; rfl
  have m1 : lm8Shr P + 0x38C0 = lm8Lc P + 0x3A44 := by
    show P + 0xFFFFFBF4 + 0x38C0 = P + 0xFFFFFA70 + 0x3A44; rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  have m2 : lm8Shr P + 0x3928 = lm8Lc P + 0x3AAC := by
    show P + 0xFFFFFBF4 + 0x3928 = P + 0xFFFFFA70 + 0x3AAC; rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  have m3 : lm8Shr P + 0x3930 = lm8Lc P + 0x3AB4 := by
    show P + 0xFFFFFBF4 + 0x3930 = P + 0xFFFFFA70 + 0x3AB4; rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  have SE : SHEnv8 t3.mem (lm8Shr P) F F (F + 0x20) := by
    rw [memt3]
    exact {
      hP := hevS
      code := cOf frG2 env.shr env.sS
      lm := cOf frG2 env.lm env.sLm
      tr := cOf frG2 env.tr env.sTr
      mset := by rw [m1]; exact cOf frG2 env.mset env.sM
      stub := by rw [m2]; exact cOf frG2 env.stub env.sU
      body := by rw [m3]; exact cOf frG2 env.body env.sB
      hsp := hFa
      hS := by omega
      hlo := hFa
      hhi := by rw [e30]; exact aG _ (by decide) (by decide)
      hwl := by omega
      hwh := by rw [e30, tG _ (by decide)]; omega
      sC := by rw [eF']; exact sub _ _ (by decide) env.sS
      sLm := by rw [eF']; exact sub _ _ (by decide) env.sLm
      sTr := by rw [eF']; exact sub _ _ (by decide) env.sTr
      sMs := by rw [eF', m1]; exact sub _ _ (by decide) env.sM
      sU := by rw [eF', m2]; exact sub _ _ (by decide) env.sU
      sB := by rw [eF', m3]; exact sub _ _ (by decide) env.sB
      sL := by rw [eF', e0]; exact sG (.inr (by decide)) (by decide) (by decide)
      sH := by rw [eF', e30]; exact sG (.inr (by decide)) (by decide) (by decide)
      sLH := by rw [e30, e0]; exact sG (.inl (by decide)) (by decide) (by decide)
      lC := by rw [e0]; exact sub _ _ (by decide) env.sS
      lB := by rw [e0, m3]; exact sub _ _ (by decide) env.sB
      hC := by rw [e30]; exact sub _ _ (by decide) env.sS
      hLm := by rw [e30]; exact sub _ _ (by decide) env.sLm
      hTr := by rw [e30]; exact sub _ _ (by decide) env.sTr
      hMs := by rw [e30, m1]; exact sub _ _ (by decide) env.sM
      hU := by rw [e30, m2]; exact sub _ _ (by decide) env.sU
      hB := by rw [e30, m3]; exact sub _ _ (by decide) env.sB }
  have sp2 : reg t2 sp = F := spt2
  obtain ⟨t4, ct4, pct4, spt4, kt4, valt4, frt4⟩ := shr8_correct t3 SE pct3
    (by rw [rt3 _ (by decide), g3, n1k sp (by decide), sp2]) (by rw [rt3 _ (by decide), g3, n1a0, sp2])
    (by rw [rt3 _ (by decide), g3, n1a1, sp2])
    (by rw [rt3 _ (by decide), g3, n1a2, kt2 19 (by decide), rt1 _ (by decide), g1, n0k 19 (by decide), r19])
    (by rw [regst3]; simp [upd]) (even_clear _ (even_at P env.hP (0x214 + 8) (by decide))) hs1 hs2
  rw [memt3] at valt4 frt4
  rw [limbVal_wordsAt, limbVal_wordsAt, limbVal_wordsAt, limbVal_wordsAt] at valt2
  have hif : ∀ A B : Nat, (if BitVec.ofNat 32 sw = 1 then A else B) = (if sw = 1 then A else B) := fun A B => by
    rcases (by omega : sw = 0 ∨ sw = 1) with h | h <;> subst h <;> rfl
  have chain : ∀ q : Fin 32, q.val ∉ [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 21] → reg t4 q = reg n q := fun q hq => by
    rw [kt4 q (nmem_of (by decide) hq), rt3 q (fun e => hq (by rw [e]; decide)), g3, n1k q (nmem_of (by decide) hq),
      kt2 q (nmem_of (by decide) hq), rt1 q (fun e => hq (by rw [e]; decide)), g1, n0k q (nmem_of (by decide) hq)]
  refine ⟨t4, t4.mem, c1.trans (ct1.trans (ct2.trans (c3.trans (ct3.trans ct4)))), ⟨pct4, rfl, fun _ => rfl⟩,
    fun x hx => ?_, ?_, spt4, ?_, fun q hq => chain q (nmem_disj hq (by decide))⟩
  · have hs : ∀ c l, c + l ≤ 0x254 → Sep (G + BitVec.ofNat 32 c) l x 1 := fun c l h => hx.sub h
    rw [frt4 x (by rw [eF']; exact hs _ _ (by decide)) (by rw [e0]; exact hs _ _ (by decide))
      (by rw [e30]; exact hs _ _ (by decide)), frN x (hs _ _ (by decide)) (hs _ _ (by decide))]
  · rw [valt4, valt2, hif]
  · rw [kt4 21 (by decide), rt3 _ (by decide), g3, n1k 21 (by decide), kt2 21 (by decide), rt1 _ (by decide), g1,
      n0s5, rsp]


/-! ## Phase 5: the final reduction, from 0x21C to 0x2B2 -/

def lm8F0 : List BInstr :=
  [.lw (19 : Fin 32) sp 0x20, .aluImm .add a0 sp 0xA8, .aluImm .add a2 x0 0x20, .aluImm .add a1 x0 0,
   .aluImm .add (8 : Fin 32) sp 0xA8]
def lm8F1 : List BInstr := [.aluImm .add a2 x0 0, .aluImm .add (9 : Fin 32) x0 0x8]
/-- From 0x272 to the `borrowing_sub` call at 0x276: the choice bit in `s1`
(the high word is zero and `x < m`), through `black_box` twice, and the
result's sign `s6 ^ s4` in `s0`. -/
def lm8F2 : List BInstr :=
  [.sw sp (19 : Fin 32) 0x28, .aluImm .add a0 sp 0x28, .lw a0 sp 0x28, .aluImm .sltu (9 : Fin 32) a0 1,
   .alu .and (9 : Fin 32) (9 : Fin 32) a2, .sb sp (9 : Fin 32) 0x28, .aluImm .add a0 sp 0x28, .lbu a0 sp 0x28,
   .aluImm .add a0 a0 0xFFFFFFFF, .alu .xor (8 : Fin 32) (22 : Fin 32) (20 : Fin 32), .alu .and a2 a2 a0,
   .alu .add a0 x0 (19 : Fin 32), .aluImm .add a1 x0 0]
def lm8F3 : List BInstr := [.aluImm .add a0 sp 0x28, .aluImm .add a1 sp 0xA8, .alu .add a2 x0 sp, .alu .add a3 x0 (9 : Fin 32)]
def lm8F4 : List BInstr := [.alu .add a0 x0 sp, .aluImm .add a1 sp 0x28, .aluImm .add a2 x0 0x20]
def lm8F5 : List BInstr := [.alu .add a1 x0 sp, .aluImm .add a2 x0 0x20, .alu .add a0 x0 (18 : Fin 32)]

section
set_option maxRecDepth 20000
theorem lm8F0_end : blockEnd lincombShiftMod8Code 0x21C lm8F0 = some 0x228 := by decide
theorem lm8F1_end : blockEnd lincombShiftMod8Code 0x230 lm8F1 = some 0x234 := by decide
theorem lm8F2_end : blockEnd lincombShiftMod8Code 0x254 lm8F2 = some 0x276 := by decide
theorem lm8F3_end : blockEnd lincombShiftMod8Code 0x27E lm8F3 = some 0x286 := by decide
theorem lm8F4_end : blockEnd lincombShiftMod8Code 0x28E lm8F4 = some 0x296 := by decide
theorem lm8F5_end : blockEnd lincombShiftMod8Code 0x29E lm8F5 = some 0x2A6 := by decide
end

set_option maxRecDepth 20000 in
theorem lm8F0_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lm8F0 (M, f)).1 = M ∧ (runBlock lm8F0 (M, f)).2 (19 : Fin 32) = memLoad32 M (f sp + 0x20) ∧
    (runBlock lm8F0 (M, f)).2 a0 = f sp + 0xA8 ∧ (runBlock lm8F0 (M, f)).2 a2 = 0x20 ∧ (runBlock lm8F0 (M, f)).2 a1 = 0 ∧
    (runBlock lm8F0 (M, f)).2 (8 : Fin 32) = f sp + 0xA8 ∧
    ∀ q : Fin 32, q.val ∉ [8, 10, 11, 12, 19] → (runBlock lm8F0 (M, f)).2 q = f q := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun q hq => runBlock_keepL (by decide) hz hq⟩ <;>
    simp only [runBlock, BInstr.run, lm8F0] <;> simp +decide only [upd, ↓reduceIte, ev_add, hz] <;>
    first | rfl | exact BitVec.zero_add _ | skip

set_option maxRecDepth 20000 in
theorem lm8F1_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lm8F1 (M, f)).1 = M ∧ (runBlock lm8F1 (M, f)).2 a2 = 0 ∧ (runBlock lm8F1 (M, f)).2 (9 : Fin 32) = 0x8 ∧
    ∀ q : Fin 32, q.val ∉ [9, 12] → (runBlock lm8F1 (M, f)).2 q = f q := by
  refine ⟨?_, ?_, ?_, fun q hq => runBlock_keepL (by decide) hz hq⟩ <;>
    simp only [runBlock, BInstr.run, lm8F1] <;> simp +decide only [upd, ↓reduceIte, ev_add, hz] <;>
    first | rfl | exact BitVec.zero_add _ | skip

set_option maxRecDepth 20000 in
theorem lm8F2_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lm8F2 (M, f)).1 = memStore8 (memStore32 M (f sp + 0x28) (f 19)) (f sp + 0x28)
      ((aluEval .and (aluEval .sltu (memLoad32 (memStore32 M (f sp + 0x28) (f 19)) (f sp + 0x28)) 1) (f a2)).extractLsb' 0 8) ∧
    (runBlock lm8F2 (M, f)).2 (9 : Fin 32) =
      aluEval .and (aluEval .sltu (memLoad32 (memStore32 M (f sp + 0x28) (f 19)) (f sp + 0x28)) 1) (f a2) ∧
    (runBlock lm8F2 (M, f)).2 (8 : Fin 32) = aluEval .xor (f 22) (f 20) ∧
    (runBlock lm8F2 (M, f)).2 a0 = f 19 ∧ (runBlock lm8F2 (M, f)).2 a1 = 0 ∧
    ∀ q : Fin 32, q.val ∉ [8, 9, 10, 11, 12] → (runBlock lm8F2 (M, f)).2 q = f q := by
  refine ⟨?_, ?_, ?_, ?_, ?_, fun q hq => runBlock_keepL (by decide) hz hq⟩ <;>
    simp only [runBlock, BInstr.run, lm8F2] <;> simp +decide only [upd, ↓reduceIte, ev_add, hz] <;>
    first | rfl | exact BitVec.zero_add _ | skip

set_option maxRecDepth 20000 in
theorem lm8F3_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lm8F3 (M, f)).1 = M ∧ (runBlock lm8F3 (M, f)).2 a0 = f sp + 0x28 ∧ (runBlock lm8F3 (M, f)).2 a1 = f sp + 0xA8 ∧
    (runBlock lm8F3 (M, f)).2 a2 = f sp ∧ (runBlock lm8F3 (M, f)).2 a3 = f 9 ∧
    ∀ q : Fin 32, q.val ∉ [10, 11, 12, 13] → (runBlock lm8F3 (M, f)).2 q = f q := by
  refine ⟨?_, ?_, ?_, ?_, ?_, fun q hq => runBlock_keepL (by decide) hz hq⟩ <;>
    simp only [runBlock, BInstr.run, lm8F3] <;> simp +decide only [upd, ↓reduceIte, ev_add, hz] <;>
    first | rfl | exact BitVec.zero_add _ | skip

set_option maxRecDepth 20000 in
theorem lm8F4_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lm8F4 (M, f)).1 = M ∧ (runBlock lm8F4 (M, f)).2 a0 = f sp ∧ (runBlock lm8F4 (M, f)).2 a1 = f sp + 0x28 ∧
    (runBlock lm8F4 (M, f)).2 a2 = 0x20 ∧
    ∀ q : Fin 32, q.val ∉ [10, 11, 12] → (runBlock lm8F4 (M, f)).2 q = f q := by
  refine ⟨?_, ?_, ?_, ?_, fun q hq => runBlock_keepL (by decide) hz hq⟩ <;>
    simp only [runBlock, BInstr.run, lm8F4] <;> simp +decide only [upd, ↓reduceIte, ev_add, hz] <;>
    first | rfl | exact BitVec.zero_add _ | skip

set_option maxRecDepth 20000 in
theorem lm8F5_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lm8F5 (M, f)).1 = M ∧ (runBlock lm8F5 (M, f)).2 a1 = f sp ∧ (runBlock lm8F5 (M, f)).2 a2 = 0x20 ∧
    (runBlock lm8F5 (M, f)).2 a0 = f 18 ∧
    ∀ q : Fin 32, q.val ∉ [10, 11, 12] → (runBlock lm8F5 (M, f)).2 q = f q := by
  refine ⟨?_, ?_, ?_, ?_, fun q hq => runBlock_keepL (by decide) hz hq⟩ <;>
    simp only [runBlock, BInstr.run, lm8F5] <;> simp +decide only [upd, ↓reduceIte, ev_add, hz] <;>
    first | rfl | exact BitVec.zero_add _ | skip


set_option exponentiation.threshold 128 in
/-- The final reduction's value: the subtraction `x - m` borrowed exactly
when `x < m`, and the select keeps `x` exactly when the high word `s3` is
zero and it borrowed. -/
theorem ph5_val8 {x m D : Nat} {B s3 : Word} (hB : B = 0 ∨ B = 0xFFFFFFFF) (hm : m < 2 ^ 256) (hD : D < 2 ^ 256)
    (h : x + 2 ^ (32 * 8) * maskBit B = m + D) :
    (if aluEval .and (aluEval .sltu s3 1) B = 1 then x else D) =
      (if s3.toNat = 0 ∧ x < m then x else (x + 2 ^ 256 - m) % 2 ^ 256) := by
  rw [show 32 * 8 = 256 from rfl] at h
  rcases hB with rfl | rfl
  · rw [show aluEval .and (aluEval .sltu s3 1) 0 = 0 from BitVec.and_zero,
      show maskBit (0 : Word) = 0 from rfl, Nat.mul_zero, Nat.add_zero] at *
    rw [ite_eq_right (by decide), ite_eq_right (fun hc => by omega)]
    generalize (2 : Nat) ^ 256 = K at hm hD ⊢
    rw [show x + K - m = D + K by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hD]
  · rw [show aluEval .and (aluEval .sltu s3 1) 0xFFFFFFFF = aluEval .sltu s3 1 from ng_and_ones _,
      show maskBit (0xFFFFFFFF : Word) = 1 from rfl, Nat.mul_one] at *
    have hs := sltu_tn s3 1
    generalize (2 : Nat) ^ 256 = K at hm hD h ⊢
    have hxm : x < m := by omega
    rw [show x + K - m = D by omega, Nat.mod_eq_of_lt hD]
    by_cases h0 : s3.toNat = 0
    · have : aluEval .sltu s3 1 = 1 := by
        apply BitVec.eq_of_toNat_eq; rw [hs, ite_eq_left (by rw [h0]; exact Nat.one_pos)]; rfl
      rw [this, ite_eq_left rfl, ite_eq_left ⟨h0, hxm⟩]
    · have : aluEval .sltu s3 1 ≠ 1 := fun e => by
        have := congrArg BitVec.toNat e; rw [hs] at this
        split at this
        · omega
        · exact absurd this (by decide)
      rw [ite_eq_right this, ite_eq_right (fun hc => h0 hc.1)]

set_option exponentiation.threshold 128 in
theorem ph5_val'8 {x x' m m' D : Nat} {B s3 : Word} (hB : B = 0 ∨ B = 0xFFFFFFFF) (hm : m < 2 ^ 256)
    (hD : D < 2 ^ 256) (h : x' + 2 ^ (32 * 8) * maskBit B = m' + D) (hx : x' = x) (hm' : m' = m) :
    (if aluEval .and (aluEval .sltu s3 1) B = 1 then x else D) =
      (if s3.toNat = 0 ∧ x < m then x else (x + 2 ^ 256 - m) % 2 ^ 256) := by
  subst hx hm'; exact ph5_val8 hB hm hD h

set_option exponentiation.threshold 128 in
set_option maxRecDepth 60000 in
set_option maxHeartbeats 16000000 in
/-- **Phase 5**, from 0x21C to 0x2B2: subtract `m` from the low 8 limbs,
keep the difference unless the high word is zero and the subtraction
borrowed, copy the result to `res`, and store the sign `σ ^ sw` after it. -/
theorem lm8_ph5 {M0 M : Word → BitVec 8} {P G res ap bp cp dp mp mip : Word} {n : Machine} {σ sw : Nat}
    (env : LMEnv8 M0 P G res ap bp cp dp mp mip) (hM : ∀ x, Sep G 0x280 x 1 → M x = M0 x)
    (s : St M P n 0x21C (reg n)) (rsp : reg n sp = G + 0x180) (r21 : reg n 21 = G + 0x180) (r23 : reg n 23 = mp)
    (r22 : reg n 22 = BitVec.ofNat 32 σ) (hσ : σ ≤ 1) (r20 : reg n 20 = BitVec.ofNat 32 sw) (hsw : sw ≤ 1)
    (r18 : reg n 18 = res) :
    ∃ n' M', Steps n n' ∧ St M' P n' 0x2B2 (reg n') ∧ (∀ x, Sep G 0x254 x 1 → Sep res 33 x 1 → M' x = M x) ∧
      (M' (res + 0x20)).toNat = (if sw = 1 then 1 - σ else σ) ∧
      accV M' res 8 =
        (if (memLoad32 M (G + 0x180 + 0x20)).toNat = 0 ∧ accV M (G + 0x180) 8 < accV M0 mp 8 then
          accV M (G + 0x180) 8
        else (accV M (G + 0x180) 8 + 2 ^ 256 - accV M0 mp 8) % 2 ^ 256) ∧
      reg n' sp = G + 0x180 ∧ ∀ q : Fin 32, q.val ∈ [3, 4, 26, 27] → reg n' q = reg n q := by
  obtain ⟨F, hF⟩ : ∃ F, G + 0x180 = F := ⟨_, rfl⟩
  rw [hF] at rsp r21 ⊢
  have hGt := env.hGt
  have tG : ∀ c, c < 0x280 → (G + BitVec.ofNat 32 c).toNat = G.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show c < 2 ^ 32 by omega),
      Nat.mod_eq_of_lt (show G.toNat + c < 2 ^ 32 by omega)]
  have fG : ∀ c, F + BitVec.ofNat 32 c = G + BitVec.ofNat 32 (0x180 + c) := fun c => by
    rw [← hF, show (0x180 : Word) = BitVec.ofNat 32 0x180 from rfl, add_ofNat_assoc]
  have eF : F = G + BitVec.ofNat 32 0x180 := hF.symm
  have hFn : F.toNat = G.toNat + 0x180 := by rw [eF, tG _ (by decide)]
  have hFa : F.toNat % 4 = 0 := by rw [hFn]; have := env.hG; omega
  have aG : ∀ c, c % 4 = 0 → c < 0x280 → (G + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h1 h2 => by
    rw [tG c h2]; have := env.hG; omega
  have sub : ∀ {b : Word} {k : Nat} (c l : Nat), c + l ≤ 0x280 → Sep G 0x280 b k → Sep (G + BitVec.ofNat 32 c) l b k :=
    fun c l h hs => hs.sub h
  have sG : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x280 → d + k ≤ 0x280 →
      Sep (G + BitVec.ofNat 32 c) n (G + BitVec.ofNat 32 d) k := fun h h1 h2 =>
    sep_offsets G h (by omega) (by omega)
  have aF : ∀ c, c % 4 = 0 → 0x180 + c < 0x280 → (F + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h1 h2 => by
    rw [fG]; exact aG _ (by omega) h2
  have sF : ∀ {b : Word} {k : Nat} (c l : Nat), 0x180 + c + l ≤ 0x280 → Sep G 0x280 b k →
      Sep (F + BitVec.ofNat 32 c) l b k := fun c l h hs => by rw [fG]; exact sub _ l h hs
  have cOf : ∀ {M' : Word → BitVec 8}, (∀ x, Sep G 0x280 x 1 → M' x = M0 x) →
      ∀ {b : Word} {code : List Nat}, CodeIn M0 b code → Sep G 0x280 b code.length → CodeIn M' b code :=
    fun hM' _ _ hc hs i hi => by rw [hM' _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have hz := s.zero
  have hc := cOf hM env.code env.sC
  have e0 : F = G + BitVec.ofNat 32 0x180 := eF
  have e30 : F + 0x20 = G + BitVec.ofNat 32 0x1A0 := fG 0x20
  have e38 : F + 0x28 = G + BitVec.ofNat 32 0x1A8 := fG 0x28
  have eE8 : F + 0xA8 = G + BitVec.ofNat 32 0x228 := fG 0xA8
  have eM4 : F + 0xFFFFFFFC = G + BitVec.ofNat 32 0x17C := by rw [eF, BitVec.add_assoc]; rfl
  have eB : lm8Bsub P = lcBsub8 (lm8Lc P) := by show P + 0xFFFF0FEE = P + 0xFFFFFA70 + 0xFFFF157E; rw [BitVec.add_assoc]; rfl
  have sBs : Sep G 0x280 (lm8Bsub P) borrowingSubCode.length := by rw [eB]; exact env.sBs
  -- `s3` = the high word, and `memset(F + 0xA8, 0, 32)`
  obtain ⟨n1, c1, u1⟩ := St.block lm8F0 s hc lm8F0_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, lm8F0, upd, ↓reduceIte, and_true, true_and]
    rw [rsp, e30]; exact aG _ (by decide) (by decide))
  obtain ⟨f0e, f0s3, f0a0, f0a2, f0a1, f0s0, f0k⟩ := lm8F0_run (M := M) (f := reg n) hz
  rw [f0e] at u1
  have g1 : ∀ q, reg n1 q = (runBlock lm8F0 (M, reg n)).2 q := u1.regs
  have eMs : lm8Lc P + 0x3A44 = P + 0x34B4 := by rw [BitVec.add_assoc]; rfl
  have hevM : (lm8Lc P + 0x3A44).toNat % 2 = 0 := by rw [eMs]; exact even_at P env.hP 0x34B4 (by decide)
  obtain ⟨t1, ct1, pct1, memt1, regst1⟩ := u1.self.callRa hc lsm8_at_228 lsm8_at_22c (cb := lm8Lc P + 0x3A44)
    (by rw [eMs, BitVec.add_assoc, BitVec.add_assoc]; rfl) hevM
  have rt1 := PEnv.reg1 regst1 u1.self.zero
  obtain ⟨t2, ct2, pct2, memt2, -, kt2⟩ := memset_correct t1 (lm8Lc P + 0x3A44) (P + BitVec.ofNat 32 (0x228 + 8))
    (F + 0xA8) 0 32 (fun i hi => by show t1.mem _ = _; rw [memt1]; exact cOf hM env.mset env.sM i hi) hevM
    pct1 (by rw [rt1 _ (by decide), g1, f0a0, rsp]) (by rw [rt1 _ (by decide), g1, f0a1])
    (by rw [rt1 _ (by decide), g1, f0a2]; rfl) (by rw [regst1]; simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at P env.hP (0x228 + 8) (by decide)))
    (by rw [eE8, tG _ (by decide)]; omega) (by rw [eE8]; exact sub _ _ (by decide) env.sM)
  rw [memt1] at memt2
  have frM2 : ∀ x, Sep (F + 0xA8) 32 x 1 → t2.mem x = M x := fun x hx => by
    rw [memt2]; exact fillBytes_sep hx (Nat.le_refl _)
  have frG2 : ∀ x, Sep G 0x280 x 1 → t2.mem x = M0 x := fun x hx => by
    rw [frM2 x (by rw [eE8]; exact sub _ _ (by decide) hx), hM x hx]
  have hc2 := cOf frG2 env.code env.sC
  have hb2 : CodeIn t2.mem (lm8Bsub P) borrowingSubCode := by rw [eB]; exact cOf frG2 env.bsub env.sBs
  have k2 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ ra →
      reg t2 q = reg n1 q := fun q q0 q1 q2 q3 q4 q5 q6 qr => by rw [kt2 q q2 q3 q4 q5 q6, rt1 q qr]
  have st2 : St t2.mem P t2 0x230 (reg t2) := ⟨pct2, rfl, fun _ => rfl⟩
  obtain ⟨n3, c3, u3⟩ := St.block lm8F1 st2 hc2 lm8F1_end (by simp [BlockOk, BInstr.ok, lm8F1])
  obtain ⟨f1e, f1a2, f1s1, f1k⟩ := lm8F1_run (M := t2.mem) (f := reg t2) st2.zero
  rw [f1e] at u3
  have g3 : ∀ q, reg n3 q = (runBlock lm8F1 (t2.mem, reg t2)).2 q := u3.regs
  obtain ⟨n4, d4, u4⟩ := u3.self.notTaken hc2 0x236 lsm8_at_234 (by decide) (by rw [g3, f1s1, u3.self.zero]; decide)
  have g4 : ∀ q, reg n4 q = reg n3 q := u4.regs
  have K8 : ∀ q : Fin 32, q.val ∈ [3, 4, 18, 19, 20, 21, 22, 23, 26, 27] → reg n4 q = reg n1 q := fun q hq => by
    have ne : ∀ w : Fin 32, w.val ∉ [3, 4, 18, 19, 20, 21, 22, 23, 26, 27] → q ≠ w := fun w hw e => hw (e ▸ hq)
    rw [g4, g3, f1k q (nmem_disj hq (by decide)), k2 q (ne a0 (by decide)) (ne a1 (by decide)) (ne a2 (by decide))
      (ne a3 (by decide)) (ne a4 (by decide)) (ne a5 (by decide)) (ne a6 (by decide)) (ne ra (by decide))]
  have sp4 : reg n4 sp = F := by
    rw [g4, g3, f1k sp (by decide), k2 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), g1, f0k sp (by decide), rsp]
  have s0v : reg n4 8 = F + 0xA8 := by
    rw [g4, g3, f1k 8 (by decide), k2 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), g1, f0s0, rsp]
  have z0 : ∀ b : Word, b + BitVec.ofNat 32 (4 * 0) = b := fun b => add_ofNat_zero b
  obtain ⟨n5, M5, c5, u5, hc5, fr5, bm5, v5, sp5, k5⟩ := lm8_sub_loop (np := F) (xp := mp) (D := F + 0xA8)
    env.hP hFa hFa env.hmp (by exact aF 0xA8 rfl (by decide)) (by rw [eE8, tG _ (by decide)]; omega)
    (by rw [eM4, e0]; exact sG (.inl (by decide)) (by decide) (by decide))
    (by rw [eM4]; exact (sub _ _ (by decide) env.mG.symm))
    (by rw [eM4, eE8]; exact sG (.inl (by decide)) (by decide) (by decide))
    (by rw [eE8, e0]; exact sG (.inr (by decide)) (by decide) (by decide))
    (by rw [eE8]; exact (sub _ _ (by decide) env.mG.symm))
    (by rw [eM4]; exact sub _ _ (by decide) sBs) (by rw [eM4]; exact sub _ _ (by decide) env.sC)
    (by rw [eE8]; exact sub _ _ (by decide) sBs) (by rw [eE8]; exact sub _ _ (by decide) env.sC)
    7 0 rfl u4.self hc2 hb2 (fun _ _ _ => rfl) (.inl rfl) (by show 0 + 2 ^ (32 * 0) * maskBit 0 = 0 + 0; rfl)
    sp4 (by rw [K8 21 (by decide), g1, f0k 21 (by decide), r21, z0])
    (by rw [K8 23 (by decide), g1, f0k 23 (by decide), r23, z0]) (by rw [s0v, z0])
    (by rw [g4, g3, f1s1]; rfl) (by rw [g4, g3, f1a2])
  -- the choice bit and the sign
  have frG5 : ∀ x, Sep G 0x280 x 1 → M5 x = M0 x := fun x hx => by
    rw [fr5 x (by rw [eM4]; exact sub _ _ (by decide) hx) (by rw [eE8]; exact sub _ _ (by decide) hx), frG2 x hx]
  obtain ⟨n6, c6, u6⟩ := St.block lm8F2 u5 hc5 lm8F2_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, lm8F2, upd, ↓reduceIte, and_true, true_and]
    rw [sp5, e38]
    exact ⟨⟨aG _ (by decide) (by decide), sub _ _ (by decide) env.sC⟩, aG _ (by decide) (by decide),
      sub _ _ (by decide) env.sC⟩)
  obtain ⟨f2e, f2s1, f2s0, f2a0, f2a1, f2k⟩ := lm8F2_run (M := M5) (f := reg n5) u5.zero
  rw [f2e, sp5] at u6
  rw [sp5] at f2s1
  have g6 : ∀ q, reg n6 q = (runBlock lm8F2 (M5, reg n5)).2 q := u6.regs
  obtain ⟨M6, hM6⟩ : ∃ M6, memStore8 (memStore32 M5 (F + 0x28) (reg n5 19)) (F + 0x28)
      ((aluEval .and (aluEval .sltu (memLoad32 (memStore32 M5 (F + 0x28) (reg n5 19)) (F + 0x28)) 1)
        (reg n5 a2)).extractLsb' 0 8) = M6 := ⟨_, rfl⟩
  rw [hM6] at u6
  have fr6 : ∀ x, Sep (F + 0x28) 4 x 1 → M6 x = M5 x := fun x hx => by
    rw [← hM6, memStore8_ne (fun e => hx 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)),
      memStore32_get_sep hx]
  have frG6 : ∀ x, Sep G 0x280 x 1 → M6 x = M0 x := fun x hx => by
    rw [fr6 x (by rw [e38]; exact sub _ _ (by decide) hx), frG5 x hx]
  have hc6 := cOf frG6 env.code env.sC
  have hb6 : CodeIn M6 (lm8Bsub P) borrowingSubCode := by rw [eB]; exact cOf frG6 env.bsub env.sBs
  have sp6 : reg n6 sp = F := by rw [g6, f2k sp (by decide), sp5]
  obtain ⟨n7, c7, u7, -, -, sp7, k7, fr7⟩ := u6.self.bsubCall hc6 hb6 (even_at P env.hP 0xFFFF0FEE (by decide))
    lsm8_at_276 lsm8_at_27a (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP (0x276 + 8) (by decide))
    sp6 hFa (by rw [eM4]; exact sub _ _ (by decide) sBs)
  have frG7 : ∀ x, Sep G 0x280 x 1 → n7.mem x = M0 x := fun x hx => by
    rw [fr7 x (by rw [eM4]; exact sub _ _ (by decide) hx), frG6 x hx]
  have hc7 := cOf frG7 env.code env.sC
  have r7 : ∀ q : Fin 32, q.val ∉ [1, 10, 11, 12, 13, 14] → reg n7 q = reg n6 q := fun q hq =>
    k7 q (fun e => hq (by rw [e]; decide)) (fun e => hq (by rw [e]; decide)) (fun e => hq (by rw [e]; decide))
      (fun e => hq (by rw [e]; decide)) (fun e => hq (by rw [e]; decide)) (fun e => hq (by rw [e]; decide))
  obtain ⟨n8, c8, u8⟩ := St.block lm8F3 u7 hc7 lm8F3_end (by simp [BlockOk, BInstr.ok, lm8F3])
  obtain ⟨f3e, f3a0, f3a1, f3a2, f3a3, f3k⟩ := lm8F3_run (M := n7.mem) (f := reg n7) u7.zero
  rw [f3e] at u8
  have g8 : ∀ q, reg n8 q = (runBlock lm8F3 (n7.mem, reg n7)).2 q := u8.regs
  have eSel : lm8Lc P + 0xFFFFFF2A = P + 0xFFFFF99A := by rw [BitVec.add_assoc]; rfl
  have hevS : (lm8Lc P + 0xFFFFFF2A).toNat % 2 = 0 := by rw [eSel]; exact even_at P env.hP 0xFFFFF99A (by decide)
  obtain ⟨t9, ct9, pct9, memt9, regst9⟩ := u8.self.callRa hc7 lsm8_at_286 lsm8_at_28a (cb := lm8Lc P + 0xFFFFFF2A)
    (by rw [eSel, BitVec.add_assoc, BitVec.add_assoc]; rfl) hevS
  have rt9 := PEnv.reg1 regst9 u8.self.zero
  have sp9 : reg t9 sp = F := by rw [rt9 _ (by decide), g8, f3k sp (by decide), sp7]
  have eSR : F + 0xFFFFFFC0 = G + BitVec.ofNat 32 0x140 := by rw [eF, BitVec.add_assoc]; rfl
  have q1 : lm8Lc P + 0xFFFFFF2A + 0x3B1A = lm8Lc P + 0x3A44 := by rw [BitVec.add_assoc]; rfl
  have q2 : lm8Lc P + 0xFFFFFF2A + 0x3B82 = lm8Lc P + 0x3AAC := by rw [BitVec.add_assoc]; rfl
  have q3 : lm8Lc P + 0xFFFFFF2A + 0x3B8A = lm8Lc P + 0x3AB4 := by rw [BitVec.add_assoc]; rfl
  have SE : Sel8Env t9.mem (lm8Lc P + 0xFFFFFF2A) (reg t9 sp) (F + 0x28) (F + 0xA8) F := by
    rw [memt9, sp9]
    exact {
      hS := hevS
      code := cOf frG7 env.sel12 env.s12
      mset := by rw [q1]; exact cOf frG7 env.mset env.sM
      stub := by rw [q2]; exact cOf frG7 env.stub env.sU
      body := by rw [q3]; exact cOf frG7 env.body env.sB
      hsp := hFa
      h40 := by omega
      hout := by rw [e38]; exact aG _ (by decide) (by decide)
      hap := by rw [eE8]; exact aG _ (by decide) (by decide)
      hbp := hFa
      hwo := by rw [e38, tG _ (by decide)]; omega
      sFC := by rw [eSR]; exact sub _ _ (by decide) env.s12
      sFM := by rw [eSR, q1]; exact sub _ _ (by decide) env.sM
      sFU := by rw [eSR, q2]; exact sub _ _ (by decide) env.sU
      sFB := by rw [eSR, q3]; exact sub _ _ (by decide) env.sB
      sOF := by rw [eSR, e38]; exact sG (.inr (by decide)) (by decide) (by decide)
      sOC := by rw [e38]; exact sub _ _ (by decide) env.s12
      sOB := by rw [e38, q3]; exact sub _ _ (by decide) env.sB
      sAF := by rw [eSR, eE8]; exact sG (.inr (by decide)) (by decide) (by decide)
      sBF := by rw [eSR, e0]; exact sG (.inr (by decide)) (by decide) (by decide) }
  -- the choice is 0 or 1
  have hB : reg n5 a2 = 0 ∨ reg n5 a2 = 0xFFFFFFFF := bm5
  obtain ⟨cv, hcv⟩ : ∃ cv, aluEval .and (aluEval .sltu (memLoad32 (memStore32 M5 (F + 0x28) (reg n5 19)) (F + 0x28)) 1)
      (reg n5 a2) = cv := ⟨_, rfl⟩
  rw [hcv] at f2s1
  have hc01 : cv = 0 ∨ cv = 1 := by
    rw [← hcv, memLoad32_store32_same]
    have : aluEval .sltu (reg n5 19) 1 = 0 ∨ aluEval .sltu (reg n5 19) 1 = 1 := by
      simp only [aluEval]; split <;> simp
    rcases hB with h | h <;> rw [h]
    · left; exact BitVec.and_zero
    · rw [show aluEval .and (aluEval .sltu (reg n5 19) 1) 0xFFFFFFFF = aluEval .sltu (reg n5 19) 1 from ng_and_ones _]
      exact this
  have r9c : reg t9 a3 = cv := by
    rw [rt9 _ (by decide), g8, f3a3, r7 9 (by decide), g6, f2s1]
  obtain ⟨t10, ct10, pct10, spt10, w10, fr10, k10⟩ := uintSelect8_correct t9 SE pct9
    (by rw [rt9 _ (by decide), g8, f3a0, sp7]) (by rw [rt9 _ (by decide), g8, f3a1, sp7])
    (by rw [rt9 _ (by decide), g8, f3a2, sp7]) r9c hc01 (by rw [regst9]; simp [upd])
    (even_clear _ (even_at P env.hP (0x286 + 8) (by decide)))
  rw [memt9, sp9] at fr10
  rw [memt9] at w10
  have e1E0 : F = G + BitVec.ofNat 32 0x180 := eF
  have eS16 : F + 0xFFFFFFF0 = G + BitVec.ofNat 32 0x170 := by rw [eF, BitVec.add_assoc]; rfl
  have frG10 : ∀ x, Sep G 0x280 x 1 → t10.mem x = M0 x := fun x hx => by
    rw [fr10 x (by rw [eSR]; exact sub _ _ (by decide) hx) (by rw [e38]; exact sub _ _ (by decide) hx), frG7 x hx]
  have hc10 := cOf frG10 env.code env.sC
  have st10 : St t10.mem P t10 0x28E (reg t10) := ⟨pct10, rfl, fun _ => rfl⟩
  have sp10 : reg t10 sp = F := by rw [spt10, sp9]
  -- `memcpy(F, F + 0x28, 32)`
  obtain ⟨n11, c11, u11⟩ := St.block lm8F4 st10 hc10 lm8F4_end (by simp [BlockOk, BInstr.ok, lm8F4])
  obtain ⟨f4e, f4a0, f4a1, f4a2, f4k⟩ := lm8F4_run (M := t10.mem) (f := reg t10) st10.zero
  rw [f4e] at u11
  have g11 : ∀ q, reg n11 q = (runBlock lm8F4 (t10.mem, reg t10)).2 q := u11.regs
  have eU : lm8Lc P + 0x3AAC = P + 0x351C := by rw [BitVec.add_assoc]; rfl
  have hevU : (lm8Lc P + 0x3AAC).toNat % 2 = 0 := by rw [eU]; exact even_at P env.hP 0x351C (by decide)
  obtain ⟨t12, ct12, pct12, memt12, regst12⟩ := u11.self.callRa hc10 lsm8_at_296 lsm8_at_29a (cb := lm8Lc P + 0x3AAC)
    (by rw [eU, BitVec.add_assoc, BitVec.add_assoc]; rfl) hevU
  have rt12 := PEnv.reg1 regst12 u11.self.zero
  have sp11 : reg n11 sp = F := by rw [g11, f4k sp (by decide), sp10]
  obtain ⟨t13, ct13, pct13, spt13, -, memt13, kt13⟩ := memcpy_correct t12 (lm8Lc P + 0x3AAC)
    (P + BitVec.ofNat 32 (0x296 + 8)) F (F + 0x28) 32 (fun i hi => by rw [memt12]; exact cOf frG10 env.stub env.sU i hi)
    hevU pct12 (by rw [rt12 _ (by decide), g11, f4a0, sp10]) (by rw [rt12 _ (by decide), g11, f4a1, sp10])
    (by rw [rt12 _ (by decide), g11, f4a2]; rfl) (by rw [regst12]; simp [upd])
    (even_clear _ (even_at P env.hP (0x296 + 8) (by decide)))
    (by
      rw [memt12, rt12 _ (by decide), sp11, show lm8Lc P + 0x3AAC + 8 = lm8Lc P + 0x3AB4 by rw [BitVec.add_assoc]; rfl,
        eS16, e38, e1E0]
      exact {
        code := cOf frG10 env.body env.sB
        hDC := sub 0x180 32 (by decide) env.sB
        hFC := sub 0x170 16 (by decide) env.sB
        hdF := sG (.inr (by decide)) (by decide) (by decide)
        hsF := sG (.inr (by decide)) (by decide) (by decide)
        hsep := sG (.inl (by decide)) (by decide) (by decide)
        hF := aG _ (by decide) (by decide)
        hFw := by rw [tG _ (by decide)]; omega
        hdw := by rw [tG _ (by decide)]; omega
        hsw := by rw [tG _ (by decide)]; omega })
  rw [rt12 _ (by decide), sp11, eS16, memt12] at memt13
  have frG13 : ∀ x, Sep G 0x280 x 1 → t13.mem x = M0 x := fun x hx => by
    rw [memt13 x (sub 0x170 16 (by decide) hx), copyBytes_sep (by rw [e1E0]; exact sub 0x180 32 (by decide) hx)
      (Nat.le_refl _), frG10 x hx]
  have hc13 := cOf frG13 env.code env.sC
  have st13 : St t13.mem P t13 0x29E (reg t13) := ⟨pct13, rfl, fun _ => rfl⟩
  have sp13 : reg t13 sp = F := by rw [spt13, rt12 _ (by decide), sp11]
  -- `memcpy(res, F, 32)`
  obtain ⟨n14, c14, u14⟩ := St.block lm8F5 st13 hc13 lm8F5_end (by simp [BlockOk, BInstr.ok, lm8F5])
  obtain ⟨f5e, f5a1, f5a2, f5a0, f5k⟩ := lm8F5_run (M := t13.mem) (f := reg t13) st13.zero
  rw [f5e] at u14
  have g14 : ∀ q, reg n14 q = (runBlock lm8F5 (t13.mem, reg t13)).2 q := u14.regs
  obtain ⟨t15, ct15, pct15, memt15, regst15⟩ := u14.self.callRa hc13 lsm8_at_2a6 lsm8_at_2aa (cb := lm8Lc P + 0x3AAC)
    (by rw [eU, BitVec.add_assoc, BitVec.add_assoc]; rfl) hevU
  have rt15 := PEnv.reg1 regst15 u14.self.zero
  have sp14 : reg n14 sp = F := by rw [g14, f5k sp (by decide), sp13]
  -- `s2` is still `res`
  have chainR : ∀ q : Fin 32, q.val ∈ [3, 4, 8, 18, 26, 27] → reg t13 q = reg n6 q := fun q hq => by
    have ne : ∀ w : Fin 32, w.val ∉ [3, 4, 8, 18, 26, 27] → q ≠ w := fun w hw e => hw (e ▸ hq)
    rw [kt13 q (ne a1 (by decide)) (ne a2 (by decide)) (ne a3 (by decide)) (ne a4 (by decide)) (ne a5 (by decide))
        (ne a6 (by decide)) (ne a7 (by decide)) (ne (5 : Fin 32) (by decide)) (ne (6 : Fin 32) (by decide))
        (ne 7 (by decide)) (ne 28 (by decide)) (ne 29 (by decide)) (ne 30 (by decide)) (ne sp (by decide)),
      rt12 q (ne ra (by decide)), g11, f4k q (nmem_disj hq (by decide)), k10 q (by revert hq; revert q; decide),
      rt9 q (ne ra (by decide)), g8, f3k q (nmem_disj hq (by decide)), r7 q (nmem_disj hq (by decide))]
  have chain6 : ∀ q : Fin 32, q.val ∈ [3, 4, 18, 20, 22, 26, 27] → reg n6 q = reg n q := fun q hq => by
    have ne : ∀ w : Fin 32, w.val ∉ [3, 4, 18, 20, 22, 26, 27] → q ≠ w := fun w hw e => hw (e ▸ hq)
    rw [g6, f2k q (nmem_disj hq (by decide)),
      k5 q (ne a0 (by decide)) (ne a1 (by decide)) (ne a2 (by decide)) (ne a3 (by decide)) (ne a4 (by decide))
        (ne ra (by decide)) (ne 21 (by decide)) (ne 23 (by decide)) (ne 8 (by decide)) (ne 9 (by decide)),
      K8 q (by revert hq; revert q; decide), g1, f0k q (nmem_disj hq (by decide))]
  have r18 : reg t13 18 = res := by rw [chainR 18 (by decide), chain6 18 (by decide), r18]
  have hdw : res.toNat + 32 < 2 ^ 32 := by have := env.hwr; omega
  have rG48 : ∀ {c l : Nat}, c + l ≤ 0x280 → Sep res 32 (G + BitVec.ofNat 32 c) l := fun {c l} h => by
    have := (env.rG.subR (c := c) (l := l) h).sub (c := 0) (l := 32) (by decide)
    rwa [add_ofNat_zero] at this
  obtain ⟨t16, ct16, pct16, spt16, -, memt16, kt16⟩ := memcpy_correct t15 (lm8Lc P + 0x3AAC)
    (P + BitVec.ofNat 32 (0x2A6 + 8)) res F 32 (fun i hi => by rw [memt15]; exact cOf frG13 env.stub env.sU i hi)
    hevU pct15 (by rw [rt15 _ (by decide), g14, f5a0, r18]) (by rw [rt15 _ (by decide), g14, f5a1, sp13])
    (by rw [rt15 _ (by decide), g14, f5a2]; rfl) (by rw [regst15]; simp [upd])
    (even_clear _ (even_at P env.hP (0x2A6 + 8) (by decide)))
    (by
      rw [memt15, rt15 _ (by decide), sp14, show lm8Lc P + 0x3AAC + 8 = lm8Lc P + 0x3AB4 by rw [BitVec.add_assoc]; rfl,
        eS16, e1E0]
      exact {
        code := cOf frG13 env.body env.sB
        hDC := by have := env.rB.sub (c := 0) (l := 32) (by decide); rwa [add_ofNat_zero] at this
        hFC := sub 0x170 16 (by decide) env.sB
        hdF := rG48 (by decide)
        hsF := sG (.inr (by decide)) (by decide) (by decide)
        hsep := rG48 (by decide)
        hF := aG _ (by decide) (by decide)
        hFw := by rw [tG _ (by decide)]; omega
        hdw := hdw
        hsw := by rw [tG _ (by decide)]; omega })
  rw [rt15 _ (by decide), sp14, eS16, memt15] at memt16
  have sC16 : ∀ i, i < lincombShiftMod8Code.length → Sep (G + BitVec.ofNat 32 0x170) 16 (P + BitVec.ofNat 32 i) 1 :=
    fun i hi => (sub 0x170 16 (by decide) env.sC).subR (c := i) (l := 1) (by omega)
  have hc16 : CodeIn t16.mem P lincombShiftMod8Code := fun i hi => by
    rw [memt16 _ (sC16 i hi), copyBytes_sep (by
        have := (env.rC.subR (c := i) (l := 1) (by omega)).sub (c := 0) (l := 32) (by decide)
        rwa [add_ofNat_zero] at this) (Nat.le_refl _)]
    exact hc13 i hi
  have st16 : St t16.mem P t16 0x2AE (reg t16) := ⟨pct16, rfl, fun _ => rfl⟩
  have k16 : ∀ q : Fin 32, q.val ∈ [3, 4, 8, 18, 26, 27] → reg t16 q = reg t13 q := fun q hq => by
    have ne : ∀ w : Fin 32, w.val ∉ [3, 4, 8, 18, 26, 27] → q ≠ w := fun w hw e => hw (e ▸ hq)
    rw [kt16 q (ne a1 (by decide)) (ne a2 (by decide)) (ne a3 (by decide)) (ne a4 (by decide)) (ne a5 (by decide))
        (ne a6 (by decide)) (ne a7 (by decide)) (ne (5 : Fin 32) (by decide)) (ne (6 : Fin 32) (by decide))
        (ne 7 (by decide)) (ne 28 (by decide)) (ne 29 (by decide)) (ne 30 (by decide)) (ne sp (by decide)),
      rt15 q (ne ra (by decide)), g14, f5k q (nmem_disj hq (by decide))]
  have r16s2 : reg t16 18 = res := by rw [k16 18 (by decide), r18]
  obtain ⟨n17, d17, u17⟩ := st16.sb hc16 lsm8_at_2ae (off' := 0x2B2) (by decide)
  rw [r16s2] at u17
  have xs : reg t16 8 = aluEval .xor (BitVec.ofNat 32 σ) (BitVec.ofNat 32 sw) := by
    rw [k16 8 (by decide), chainR 8 (by decide), g6, f2s0, k5 22 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k5 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), K8 22 (by decide), K8 20 (by decide), g1, f0k 22 (by decide), g1, f0k 20 (by decide), r22, r20]
  obtain ⟨M', hM'⟩ : ∃ M', memStore8 t16.mem (res + 0x20) ((reg t16 8).extractLsb' 0 8) = M' := ⟨_, rfl⟩
  rw [hM'] at u17
  refine ⟨n17, M', c1.trans (ct1.trans (ct2.trans (c3.trans (.cons d4 (c5.trans (c6.trans (c7.trans (c8.trans (ct9.trans
    (ct10.trans (c11.trans (ct12.trans (ct13.trans (c14.trans (ct15.trans (ct16.trans (.single d17))))))))))))))))),
    u17.self, ?_, ?_, ?_, ?_, ?_⟩
  · intro x h1 h2
    have hs : ∀ c l, c + l ≤ 0x254 → Sep (G + BitVec.ofNat 32 c) l x 1 := fun c l h => h1.sub h
    have hr : Sep res 32 x 1 := by have := h2.sub (c := 0) (l := 32) (by decide); rwa [add_ofNat_zero] at this
    have hne : x ≠ res + 0x20 := fun e => h2 32 (by decide) 0 (by decide) (by
      rw [add_ofNat_zero, e]; rfl)
    rw [← hM', memStore8_ne hne, memt16 x (hs 0x170 16 (by decide)), copyBytes_sep hr (Nat.le_refl _),
      memt13 x (hs 0x170 16 (by decide)), copyBytes_sep (by rw [e1E0]; exact hs 0x180 32 (by decide)) (Nat.le_refl _),
      fr10 x (by rw [eSR]; exact hs _ _ (by decide)) (by rw [e38]; exact hs _ _ (by decide)),
      fr7 x (by rw [eM4]; exact hs _ _ (by decide)), fr6 x (by rw [e38]; exact hs _ _ (by decide)),
      fr5 x (by rw [eM4]; exact hs _ _ (by decide)) (by rw [eE8]; exact hs _ _ (by decide)),
      frM2 x (by rw [eE8]; exact hs _ _ (by decide))]
  · rw [← hM', memStore8_same, xs]
    rcases (by omega : σ = 0 ∨ σ = 1) with h1 | h1 <;> rcases (by omega : sw = 0 ∨ sw = 1) with h2 | h2 <;>
      subst h1 h2 <;> decide
  · have accF : ∀ {M1 M2 : Word → BitVec 8} (c k : Nat), 0x180 + c + 4 * k ≤ 0x280 →
        (∀ d, 0x180 + c ≤ d → d < 0x180 + c + 4 * k → M1 (G + BitVec.ofNat 32 d) = M2 (G + BitVec.ofNat 32 d)) →
        accV M1 (F + BitVec.ofNat 32 c) k = accV M2 (F + BitVec.ofNat 32 c) k := fun c k hb h =>
      accV_congr k fun i hi => memLoad32_congr fun j hj => by
        rw [add_ofNat_assoc, add_ofNat_assoc, fG]; exact h _ (by omega) (by omega)
    have gS : ∀ {c l d : Nat}, c + l ≤ d ∨ d + 1 ≤ c → c + l ≤ 0x280 → d < 0x280 →
        Sep (G + BitVec.ofNat 32 c) l (G + BitVec.ofNat 32 d) 1 := fun h h1 h2 => sG h h1 (by omega)
    have A1 : accV M' res 8 = accV t16.mem res 8 := accV_congr 8 fun i hi => memLoad32_congr fun j hj => by
      rw [← hM']
      apply memStore8_ne
      intro e
      have := sep_offsets res (c := 4 * i + j) (n := 1) (d := 0x20) (k := 1) (.inl (by omega)) (by omega) (by omega)
      exact this 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero, ← add_ofNat_assoc, e]; rfl)
    have A2 : accV t16.mem res 8 = accV t13.mem F 8 := accV_congr2 8 fun i hi => by
      have h : memLoad32 t16.mem (res + BitVec.ofNat 32 (4 * i)) =
          memLoad32 (copyBytes t13.mem res F 32) (res + BitVec.ofNat 32 (4 * i)) :=
        memLoad32_congr fun j hj => memt16 _ (by
          have := (rG48 (c := 0x170) (l := 16) (by decide)).symm.subR (c := 4 * i + j) (l := 1) (by omega)
          rwa [← add_ofNat_assoc] at this)
      rw [h, cb_load (by omega) (by decide)]
    have A3 : accV t13.mem F 8 = accV t10.mem (F + 0x28) 8 := accV_congr2 8 fun i hi => by
      have h : memLoad32 t13.mem (F + BitVec.ofNat 32 (4 * i)) =
          memLoad32 (copyBytes t10.mem F (F + 0x28) 32) (F + BitVec.ofNat 32 (4 * i)) :=
        memLoad32_congr fun j hj => memt13 _ (by
          rw [add_ofNat_assoc, fG]; exact gS (.inl (by omega)) (by decide) (by omega))
      rw [h, cb_load (by omega) (by decide)]
    have A4 := accV_ite (n := 8) (c := cv = 1) w10
    have A5 : accV n7.mem F 8 = accV M F 8 := by
      have := accF (M1 := n7.mem) (M2 := M) 0 8 (by decide) fun d h1 h2 => by
        rw [fr7 _ (by rw [eM4]; exact gS (.inl (by omega)) (by decide) (by omega)),
          fr6 _ (by rw [e38]; exact gS (.inr (by omega)) (by decide) (by omega)),
          fr5 _ (by rw [eM4]; exact gS (.inl (by omega)) (by decide) (by omega))
            (by rw [eE8]; exact gS (.inr (by omega)) (by decide) (by omega)),
          frM2 _ (by rw [eE8]; exact gS (.inr (by omega)) (by decide) (by omega))]
      rwa [add_ofNat_zero] at this
    have A6 : accV n7.mem (F + 0xA8) 8 = accV M5 (F + 0xA8) 8 :=
      accF 0xA8 8 (by decide) fun d h1 h2 => by
        rw [fr7 _ (by rw [eM4]; exact gS (.inl (by omega)) (by decide) (by omega)),
          fr6 _ (by rw [e38]; exact gS (.inl (by omega)) (by decide) (by omega))]
    have Xeq : accV t2.mem F 8 = accV M F 8 := by
      have := accF (M1 := t2.mem) (M2 := M) 0 8 (by decide) fun d h1 h2 =>
        frM2 _ (by rw [eE8]; exact gS (.inr (by omega)) (by decide) (by omega))
      rwa [add_ofNat_zero] at this
    have Meq : accV t2.mem mp 8 = accV M0 mp 8 :=
      accV_congr 8 fun i hi => memLoad32_congr fun j hj => frG2 _ (by
        have := env.mG.symm.subR (c := 4 * i + j) (l := 1) (by omega); rwa [← add_ofNat_assoc] at this)
    have s3e : reg n5 19 = memLoad32 M (F + 0x20) := by
      rw [k5 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), K8 19 (by decide), g1, f0s3, rsp]
    have cvE : cv = aluEval .and (aluEval .sltu (memLoad32 M (F + 0x20)) 1) (reg n5 a2) := by
      rw [← hcv, memLoad32_store32_same, s3e]
    rw [A1, A2, A3, A4, A5, A6, cvE]
    exact ph5_val'8 bm5 (accV_lt M0 mp 8) (accV_lt M5 (F + 0xA8) 8) v5 Xeq Meq
  · rw [u17.regs, spt16, rt15 _ (by decide), g14, f5k sp (by decide), sp13]
  · intro q hq
    rw [u17.regs, k16 q (mem_sub hq (by decide)), chainR q (mem_sub hq (by decide)), chain6 q (mem_sub hq (by decide))]


set_option exponentiation.threshold 128 in
/-- The arithmetic that joins the phases: phase 3's difference `R` and
borrow `sw`, phase 4's negation and shift into `lo + 2^256 hi`, and phase
5's reduction give `lrsm8`. -/
theorem lm8_final {σ A XA R sw s lo hi M MI mf : Nat} {hw : Word} (hσ : σ ≤ 1) (hsw : sw ≤ 1)
    (hA : A < 2 ^ 320) (hX : XA < 2 ^ 320) (hR : R < 2 ^ 320) (hlo : lo < 2 ^ 256)
    (hmf : lrsmMf A MI s = mf) (hXA : XA = M * mf)
    (h3 : R + XA = A + 2 ^ 320 * sw)
    (h4 : lo + 2 ^ 256 * hi = (if sw = 1 then (2 ^ 320 - R) % 2 ^ 320 else R) / 2 ^ s)
    (hhw : hw.toNat = hi % 2 ^ 32) :
    lrsm8 σ A MI s M = (if sw = 1 then 1 - σ else σ,
      if hw.toNat = 0 ∧ lo < M then lo else (lo + 2 ^ 256 - M) % 2 ^ 256) := by
  have hiff : A < M * lrsmMf A MI s ↔ sw = 1 := by
    rw [hmf, ← hXA]
    rcases (by omega : sw = 0 ∨ sw = 1) with h | h <;> subst h
    · exact ⟨fun h => absurd h (by omega), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => rfl, fun _ => by omega⟩
  have hY : (if A < M * lrsmMf A MI s then M * lrsmMf A MI s - A else A - M * lrsmMf A MI s) =
      (if sw = 1 then (2 ^ 320 - R) % 2 ^ 320 else R) := by
    rw [hmf, ← hXA]; rw [hmf, ← hXA] at hiff
    rcases (by omega : sw = 0 ∨ sw = 1) with h | h <;> subst h
    · rw [ite_eq_right (fun h => absurd (hiff.mp h) (by decide)), ite_eq_right (by decide)]; omega
    · rw [ite_eq_left (hiff.mpr rfl), ite_eq_left rfl]
      generalize (2 : Nat) ^ 320 = K at *
      rw [show K - R = XA - A by omega, Nat.mod_eq_of_lt (by omega)]
  unfold lrsm8
  simp only
  rw [hY, ← h4]
  have e1 : (lo + 2 ^ 256 * hi) % 2 ^ 256 = lo := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo]
  have e2 : (lo + 2 ^ 256 * hi) / 2 ^ 256 = hi := by
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos 256), Nat.div_eq_of_lt hlo, Nat.zero_add]
  rw [e1, e2, ← hhw]
  by_cases h : sw = 1
  · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (hiff.mp h')), ite_eq_right h]


set_option exponentiation.threshold 128 in
theorem acc_lo28 (M : Word → BitVec 8) (b : Word) (h : Nat) :
    (accV M b 8 + 2 ^ 256 * h) % 2 ^ 64 = accV M b 2 := by
  rw [show (8 : Nat) = 2 + 6 from rfl, accV_split, show 32 * 2 = 64 from rfl,
    show (256 : Nat) = 64 + 192 from rfl, Nat.pow_add, Nat.add_assoc, Nat.mul_assoc, ← Nat.mul_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (accV_lt M b 2)]

set_option exponentiation.threshold 128 in
theorem acc14_lt8 (M : Word → BitVec 8) (b c : Word) : accV M b 8 + 2 ^ 256 * accV M c 2 < 2 ^ 320 := by
  have h1 := accV_lt M b 8
  have h2 := accV_lt M c 2
  rw [show 32 * 8 = 256 from rfl] at h1
  rw [show 32 * 2 = 64 from rfl] at h2
  rw [show (320 : Nat) = 256 + 64 from rfl, Nat.pow_add]
  generalize (2 : Nat) ^ 256 = K at *
  generalize (2 : Nat) ^ 64 = L at *
  have : K * accV M c 2 + K ≤ K * L := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h2
  omega

theorem lm8Epi_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base F : Word} {len : Nat} (hF : f sp = F)
    (h : ∀ c : Nat, 0xD4 ≤ c → c + 4 ≤ 0x100 → c % 4 = 0 → (F + BitVec.ofNat 32 c).toNat % 4 = 0) :
    BlockOk base len lm8Epi (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, lm8Epi, restoreBlock, lm8Ps, List.map, upd, ↓reduceIte, and_true,
    true_and, ev_add]
  rw [hF]
  exact ⟨(h 0xFC (by decide) (by decide) (by decide)), (h 0xF8 (by decide) (by decide) (by decide)), (h 0xF4 (by decide) (by decide) (by decide)), (h 0xF0 (by decide) (by decide) (by decide)), (h 0xEC (by decide) (by decide) (by decide)), (h 0xE8 (by decide) (by decide) (by decide)), (h 0xE4 (by decide) (by decide) (by decide)), (h 0xE0 (by decide) (by decide) (by decide)), (h 0xDC (by decide) (by decide) (by decide)), (h 0xD8 (by decide) (by decide) (by decide)), (h 0xD4 (by decide) (by decide) (by decide))⟩


set_option exponentiation.threshold 128 in
theorem mul_lt_4488 (M : Word → BitVec 8) (b c : Word) : accV M b 8 * accV M c 2 < 2 ^ 320 := by
  rw [show (320 : Nat) = 256 + 64 from rfl, Nat.pow_add]
  exact Nat.mul_lt_mul'' (accV_lt M b 8) (accV_lt M c 2)

set_option exponentiation.threshold 128 in
theorem mul_lt_448'8 (M M' : Word → BitVec 8) (b c : Word) : accV M b 8 * accV M' c 2 < 2 ^ 320 := by
  rw [show (320 : Nat) = 256 + 64 from rfl, Nat.pow_add]
  exact Nat.mul_lt_mul'' (accV_lt M b 8) (accV_lt M' c 2)

set_option exponentiation.threshold 128 in
theorem lm8_final' {σ A A' XA R sw s lo hi M MI mf : Nat} {hw : Word} (hσ : σ ≤ 1) (hsw : sw ≤ 1)
    (hA : A < 2 ^ 320) (hX : XA < 2 ^ 320) (hR : R < 2 ^ 320) (hlo : lo < 2 ^ (32 * 8))
    (hmf : lrsmMf A MI s = mf) (hXA : XA = M * mf) (hAA : A' = A) (h3 : R + XA = A' + 2 ^ 320 * sw)
    (h4 : lo + 2 ^ 256 * hi = (if sw = 1 then (2 ^ 320 - R) % 2 ^ 320 else R) / 2 ^ s)
    (hhw : hw.toNat = hi % 2 ^ 32) :
    lrsm8 σ A MI s M = (if sw = 1 then 1 - σ else σ,
      if hw.toNat = 0 ∧ lo < M then lo else (lo + 2 ^ 256 - M) % 2 ^ 256) := by
  subst hAA; exact lm8_final hσ hsw hA hX hR hlo hmf hXA h3 h4 hhw

/-- The frame slot that holds callee-saved register `q`. -/
def lm8Slot (q : Fin 32) : Word := ((lm8Ps.find? fun p => p.1 == q).map Prod.snd).getD 0

theorem lm8Slot_mem : ∀ q : Fin 32, q.val ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25] → (q, lm8Slot q) ∈ lm8Ps := by
  decide

theorem lm8_keep_split : ∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
    q.val ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25] ∨ q.val ∈ [3, 4, 26, 27] := by decide

set_option exponentiation.threshold 128 in
set_option maxRecDepth 60000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `SignedInt<8>::lincomb_int_reduce_shift_mod::<2>`**: for
`a` and `b` with sign bytes 0 or 1, `c` and `d` as `Int<2>`, a shift from 1
to 63, the modulus at `mp`, and `mi` at `mip`, it stores at `res` the
8-limb magnitude and the sign byte that `lrsm8` gives for the linear
combination `σ, A`, `mi`, the shift, and the modulus. It returns, restores
`sp`, `gp`, `tp`, and `s0` through `s11`, and changes no memory outside its
0x280 bytes of stack and the result. -/
theorem lincombShiftMod8_correct (m : Machine) {P G res ap bp cp dp mp mip retAddr : Word} {s : Nat}
    (env : LMEnv8 m.mem P G res ap bp cp dp mp mip) (hpc : m.pc = P) (hsp : reg m sp = G + 0x280)
    (ha0 : reg m a0 = res) (ha1 : reg m a1 = ap) (ha2 : reg m a2 = bp) (ha3 : reg m a3 = cp)
    (ha4 : reg m a4 = dp) (ha5 : reg m a5 = BitVec.ofNat 32 s) (ha6 : reg m a6 = mp) (ha7 : reg m 17 = mip)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hs1 : 1 ≤ s) (hs2 : s ≤ 63)
    (hsa : (m.mem (ap + 0x20)).toNat ≤ 1) (hsb : (m.mem (bp + 0x20)).toNat ≤ 1) :
    ∃ m' σ A, Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = G + 0x280 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      σ ≤ 1 ∧
      sgnVal σ A = sgnVal (m.mem (ap + 0x20)).toNat (accV m.mem ap 8) * i64Val (accV m.mem cp 2) +
        sgnVal (m.mem (bp + 0x20)).toNat (accV m.mem bp 8) * i64Val (accV m.mem dp 2) ∧
      (m'.mem (res + 0x20)).toNat = (lrsm8 σ A (accV m.mem mip 2) s (accV m.mem mp 8)).1 ∧
      accV m'.mem res 8 = (lrsm8 σ A (accV m.mem mip 2) s (accV m.mem mp 8)).2 ∧
      ∀ x, Sep G 0x280 x 1 → Sep res 33 x 1 → m'.mem x = m.mem x := by
  obtain ⟨n1, M1, σ, c1, u1, at1, hσ, s6, val1⟩ := lm8_ph1 m env hpc hsp ha0 ha1 ha2 ha3 ha4 hsa hsb
  obtain ⟨F, hF⟩ : ∃ F, G + 0x180 = F := ⟨_, rfl⟩
  have hGt := env.hGt
  have tG : ∀ c, c < 0x280 → (G + BitVec.ofNat 32 c).toNat = G.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show c < 2 ^ 32 by omega),
      Nat.mod_eq_of_lt (show G.toNat + c < 2 ^ 32 by omega)]
  have fG : ∀ c, F + BitVec.ofNat 32 c = G + BitVec.ofNat 32 (0x180 + c) := fun c => by
    rw [← hF, show (0x180 : Word) = BitVec.ofNat 32 0x180 from rfl, add_ofNat_assoc]
  have eF : F = G + BitVec.ofNat 32 0x180 := hF.symm
  have hFn : F.toNat = G.toNat + 0x180 := by rw [eF, tG _ (by decide)]
  have hFa : F.toNat % 4 = 0 := by rw [hFn]; have := env.hG; omega
  have sub : ∀ {b : Word} {k : Nat} (c l : Nat), c + l ≤ 0x280 → Sep G 0x280 b k → Sep (G + BitVec.ofNat 32 c) l b k :=
    fun c l h hs => hs.sub h
  have sG : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x280 → d + k ≤ 0x280 →
      Sep (G + BitVec.ofNat 32 c) n (G + BitVec.ofNat 32 d) k := fun h h1 h2 =>
    sep_offsets G h (by omega) (by omega)
  have sF : ∀ {b : Word} {k : Nat} (c l : Nat), 0x180 + c + l ≤ 0x280 → Sep G 0x280 b k →
      Sep (F + BitVec.ofNat 32 c) l b k := fun c l h hs => by rw [fG]; exact sub _ l h hs
  have cOf : ∀ {M' : Word → BitVec 8}, (∀ x, Sep G 0x280 x 1 → M' x = m.mem x) →
      ∀ {b : Word} {code : List Nat}, CodeIn m.mem b code → Sep G 0x280 b code.length → CodeIn M' b code :=
    fun hM' _ _ hc hs i hi => by rw [hM' _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have e38 : F + 0x28 = G + BitVec.ofNat 32 0x1A8 := fG 0x28
  have e118 : F + 0xC8 = G + BitVec.ofNat 32 0x248 := fG 0xC8
  -- phase 2
  have hc1 := cOf at1.frame env.code env.sC
  obtain ⟨n2, M2, c2, u2, hc2, fr2, v2, r21b, sp2, k2⟩ := lm8_ph2 (sh := s) env.hP u1 hc1
    (cOf at1.frame env.lm env.sLm) (cOf at1.frame env.tr env.sTr) (cOf at1.frame env.max env.sX)
    (by rw [at1.sp, hF]) (by rw [at1.s3, ha5]) (by rw [at1.s4, hF]) (by rw [at1.s5, ha7]) hs1 hs2 hFa env.hmip
    (sF 0x28 8 (by decide) env.sC) (sF 0x58 8 (by decide) env.sC) (sF 0xC8 8 (by decide) env.sC)
    (sF 0x28 8 (by decide) env.sLm) (sF 0x28 8 (by decide) env.sTr) (sF 0x28 8 (by decide) env.sX)
    (by rw [e118, e38]; exact sG (.inr (by decide)) (by decide) (by decide))
    (sF 0xC8 8 (by decide) env.iG.symm) (sF 0xC8 8 (by decide) env.sLm) (sF 0xC8 8 (by decide) env.sTr)
    (sF 0xC8 8 (by decide) env.sX)
  have hM2 : ∀ x, Sep G 0x280 x 1 → M2 x = m.mem x := fun x hx => by
    rw [fr2 x (sF 0x28 8 (by decide) hx) (sF 0x58 8 (by decide) hx) (sF 0xC8 8 (by decide) hx), at1.frame x hx]
  -- phase 3
  obtain ⟨n3, M3, sw, c3, u3, fr3, hsw, r20c, v3, sp3, k3⟩ := lm8_ph3 env hM2 u2 (by rw [sp2, hF])
    (by rw [k2 23 (by decide), at1.s7, ha6]) (by rw [r21b, hF])
  have h304 : ∀ {x : Word}, Sep G 0x280 x 1 → Sep G 0x254 x 1 := fun hx => by
    have := hx.sub (c := 0) (l := 0x254) (by decide); rwa [add_ofNat_zero] at this
  have hM3 : ∀ x, Sep G 0x280 x 1 → M3 x = m.mem x := fun x hx => by rw [fr3 x (h304 hx), hM2 x hx]
  -- phase 4
  obtain ⟨n4, M4, c4, u4, fr4, v4, sp4, r21d, k4⟩ := lm8_ph4 env hM3 u3 sp3 r20c hsw
    (by rw [k3 19 (by decide), k2 19 (by decide), at1.s3, ha5]) hs1 hs2
  have hM4 : ∀ x, Sep G 0x280 x 1 → M4 x = m.mem x := fun x hx => by rw [fr4 x (h304 hx), hM3 x hx]
  -- phase 5
  obtain ⟨n5, M5, c5, u5, fr5, sgn5, val5, sp5, k5⟩ := lm8_ph5 env hM4 u4 sp4 r21d
    (by rw [k4 23 (by decide), k3 23 (by decide), k2 23 (by decide), at1.s7, ha6])
    (by rw [k4 22 (by decide), k3 22 (by decide), k2 22 (by decide), s6]) hσ
    (by rw [k4 20 (by decide), r20c]) hsw
    (by rw [k4 18 (by decide), k3 18 (by decide), k2 18 (by decide), at1.s2, ha0])
  have hM5 : ∀ x, Sep G 0x280 x 1 → Sep res 33 x 1 → M5 x = m.mem x := fun x hx hr => by
    rw [fr5 x (h304 hx) hr, hM4 x hx]
  have hc5 : CodeIn M5 P lincombShiftMod8Code := fun i hi => by
    rw [hM5 _ (env.sC.subR (c := i) (l := 1) (by omega)) (env.rC.subR (c := i) (l := 1) (by omega))]
    exact env.code i hi
  have sp5F : reg n5 sp = F := by rw [sp5, hF]
  have aF : ∀ c, c % 4 = 0 → 0x180 + c < 0x280 → (F + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h1 h2 => by
    rw [fG, tG _ h2]; have := env.hG; omega
  obtain ⟨n6, c6, u6⟩ := St.block lm8Epi u5 hc5 lm8Epi_end (lm8Epi_ok sp5F fun c h1 h2 h3 => aF c h3 (by omega))
  obtain ⟨er, em, ek⟩ := lm8Epi_run (M := M5) (f := reg n5) u5.zero
  rw [em] at u6
  have g6 : ∀ q, reg n6 q = (runBlock lm8Epi (M5, reg n5)).2 q := u6.regs
  obtain ⟨n7, d7, u7⟩ := u6.self.aluImm hc5 lsm8_at_2c8 (off' := 0x2CA) (by decide)
  -- the saved registers survive every phase
  have slot5 : ∀ c, 0xD4 ≤ c → c + 4 ≤ 0x100 → memLoad32 M5 (F + BitVec.ofNat 32 c) = memLoad32 M1 (F + BitVec.ofNat 32 c) :=
    fun c h1 h2 => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc, fG]
      have g304 : Sep G 0x254 (G + BitVec.ofNat 32 (0x180 + (c + j))) 1 := by
        have := sep_offsets G (c := 0) (n := 0x254) (d := 0x180 + (c + j)) (k := 1) (.inl (by omega)) (by omega) (by omega)
        rwa [add_ofNat_zero] at this
      rw [fr5 _ g304 (env.rG.subR (c := 0x180 + (c + j)) (l := 1) (by omega)), fr4 _ g304, fr3 _ g304,
        fr2 _ (by rw [e38]; exact sG (.inl (by omega)) (by decide) (by omega))
          (by rw [show F + 0x58 = G + BitVec.ofNat 32 0x1D8 from fG 0x58]; exact sG (.inl (by omega)) (by decide) (by omega))
          (by rw [e118]; exact sG (.inl (by omega)) (by decide) (by omega))]
  have slotv : ∀ r o, (r, o) ∈ lm8Ps → memLoad32 M5 (reg n5 sp + o) = reg m r := fun r o h => by
    obtain ⟨_, h2, h3⟩ := lm8Ps_range (r, o) h
    have := slot5 o.toNat h2 h3
    rw [ofNat_toNat_self] at this
    rw [sp5F, this, ← at1.slots r o h, hF]
  have rRa : reg n7 ra = retAddr := by
    rw [u7.oldReg u6.self.zero ra (by decide), g6, er ra 0xFC (by decide), slotv ra 0xFC (by decide), hra]
  obtain ⟨n8, d8, pc8, mem8, regs8⟩ := u7.self.jalr hc5 lsm8_at_2ca
  have g7 : ∀ q, q ≠ sp → reg n7 q = reg n6 q := fun q hq => u7.oldReg u6.self.zero q hq
  have mem7 : n8.mem = M5 := mem8
  have lo64 : (accV M1 (G + 0x180) 8 + 2 ^ 256 * accV M1 (G + 0x180 + 0x20) 2) % 2 ^ 64 =
      (memLoad32 M1 (F + 0x28)).toNat + 2 ^ 32 * (memLoad32 M1 (F + 0x2C)).toNat := by
    rw [acc_lo28, acc2, ← at1.lo2.1, ← at1.lo2.2, hF]
  have l0 : ∀ k, k ≤ 4 → memLoad32 M1 (mip + BitVec.ofNat 32 k) = memLoad32 m.mem (mip + BitVec.ofNat 32 k) :=
    fun k hk => memLoad32_congr fun j hj => at1.frame _ (by
      have := env.iG.symm.subR (c := k + j) (l := 1) (by omega); rwa [← add_ofNat_assoc] at this)
  have hMI : accV m.mem mip 2 = (memLoad32 M1 mip).toNat + 2 ^ 32 * (memLoad32 M1 (mip + 4)).toNat := by
    have a := l0 0 (by decide); rw [add_ofNat_zero] at a
    rw [acc2, a, show mip + 4 = mip + BitVec.ofNat 32 4 from rfl, l0 4 (by decide)]
  have hmf2 : accV M2 (F + 0xC8) 2 = (memLoad32 M2 (F + 0xC8)).toNat + 2 ^ 32 * (memLoad32 M2 (F + 0xCC)).toNat := by
    rw [acc2, show F + 0xC8 + 4 = F + 0xCC by rw [BitVec.add_assoc]; rfl]
  have mfE : accV M2 (G + 0x180 + 0xC8) 2 = accV M2 (F + 0xC8) 2 := by rw [hF]
  have hMF := mf_eq v2 lo64 hMI hmf2 mfE
  have b2 : ∀ d, 0x180 ≤ d → d < 0x1A8 → M2 (G + BitVec.ofNat 32 d) = M1 (G + BitVec.ofNat 32 d) := fun d h1 h2 =>
    fr2 _ (by rw [e38]; exact sG (.inr (by omega)) (by decide) (by omega))
      (by rw [show F + 0x58 = G + BitVec.ofNat 32 0x1D8 from fG 0x58]; exact sG (.inr (by omega)) (by decide) (by omega))
      (by rw [e118]; exact sG (.inr (by omega)) (by decide) (by omega))
  have hAA : accV M2 (G + 0x180) 8 + 2 ^ 256 * accV M2 (G + 0x180 + 0x20) 2 =
      accV M1 (G + 0x180) 8 + 2 ^ 256 * accV M1 (G + 0x180 + 0x20) 2 := by
    have q1 : accV M2 (G + 0x180) 8 = accV M1 (G + 0x180) 8 :=
      accV_congr 8 fun i hi => memLoad32_congr fun j hj => by
        rw [show (0x180 : Word) = BitVec.ofNat 32 0x180 from rfl, add_ofNat_assoc, add_ofNat_assoc]
        exact b2 _ (by omega) (by omega)
    have q2 : accV M2 (G + 0x180 + 0x20) 2 = accV M1 (G + 0x180 + 0x20) 2 :=
      accV_congr 2 fun i hi => memLoad32_congr fun j hj => by
        rw [show (0x180 : Word) = BitVec.ofNat 32 0x180 from rfl, show (0x20 : Word) = BitVec.ofNat 32 0x20 from rfl,
          add_ofNat_assoc, add_ofNat_assoc, add_ofNat_assoc]
        exact b2 _ (by omega) (by omega)
    rw [q1, q2]
  have hhw : (memLoad32 M4 (G + 0x180 + 0x20)).toNat = accV M4 (G + 0x180 + 0x20) 2 % 2 ^ 32 := (acc2_mod _ _).symm
  have LF := lm8_final' (σ := σ) hσ hsw (acc14_lt8 M1 _ _) (mul_lt_448'8 m.mem M2 mp _) (acc14_lt8 M3 _ _)
    (accV_lt M4 _ 8) hMF rfl hAA v3 v4 hhw
  refine ⟨n8, σ, accV M1 (G + 0x180) 8 + 2 ^ 256 * accV M1 (G + 0x180 + 0x20) 2,
    c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (.cons d7 (.single d8))))))),
    by rw [pc8, rRa, add_lit_zero]; exact hret, ?_, ?_, hσ, val1, ?_, ?_,
    fun x hx hr => by rw [mem7]; exact hM5 x hx hr⟩
  · rw [regs8, u7.newReg (by decide)]
    show reg n6 sp + 0x100 = _
    rw [g6, ek sp (by decide), sp5F, eF, BitVec.add_assoc]; rfl
  · intro q hq
    rw [regs8, g7 q (fun e => by rw [e] at hq; exact absurd hq (by decide)), g6]
    rcases lm8_keep_split q hq with h | h
    · rw [er q (lm8Slot q) (lm8Slot_mem q h), slotv q (lm8Slot q) (lm8Slot_mem q h)]
    · rw [ek q (nmem_disj h (by decide)), k5 q h, k4 q (mem_sub h (by decide)), k3 q (mem_sub h (by decide)),
        k2 q (nmem_disj h (by decide)), at1.keep q h]
  · rw [mem7, LF]; exact sgn5
  · rw [mem7, LF]; exact val5

end C3.RV32
