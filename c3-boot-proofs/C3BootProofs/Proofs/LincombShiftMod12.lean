import C3BootProofs.Proofs.ToUintResize
import C3BootProofs.Proofs.Norm12

/-!
# `SignedInt<12>::lincomb_int_reduce_shift_mod::<2>`

The step of Bernstein-Yang inversion that updates `d` and `e`: the linear
combination `a·c + b·d` through the proved `lincomb_int`, plus the multiple
`m·mf` of the modulus that clears its low `shift` bits (`mf` is the low 64
bits times `mi`, masked to `shift` bits), shifted right by `shift`, and
reduced below `m` with one conditional subtraction. The compiled function
inlines the 64-bit multiplication, the mask, and three subtraction loops,
and calls the proved `to_uint_resize`, `leading_mut`, `trailing`,
`widening_mul_fixed::<12, 2>`, `borrowing_sub`,
`conditional_negate_in_place_wide`, `shr_in_place_wide`, `Uint<12>::select`,
`memset`, and `memcpy`.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem lm12_at_0 : fetchRel lincombShiftMod12Code 0x0 = some (.aluImm .add sp sp 0xFFFFFEB0, 2) := by decide
theorem lm12_at_2 : fetchRel lincombShiftMod12Code 0x2 = some (.store .sw sp ra 0x14C, 4) := by decide
theorem lm12_at_6 : fetchRel lincombShiftMod12Code 0x6 = some (.store .sw sp (8 : Fin 32) 0x148, 4) := by decide
theorem lm12_at_a : fetchRel lincombShiftMod12Code 0xA = some (.aluImm .add (8 : Fin 32) sp 0x100, 2) := by decide
theorem lm12_at_c : fetchRel lincombShiftMod12Code 0xC = some (.store .sw (8 : Fin 32) (9 : Fin 32) 0x44, 2) := by decide
theorem lm12_at_e : fetchRel lincombShiftMod12Code 0xE = some (.store .sw (8 : Fin 32) (18 : Fin 32) 0x40, 4) := by decide
theorem lm12_at_12 : fetchRel lincombShiftMod12Code 0x12 = some (.store .sw (8 : Fin 32) (19 : Fin 32) 0x3C, 4) := by decide
theorem lm12_at_16 : fetchRel lincombShiftMod12Code 0x16 = some (.store .sw (8 : Fin 32) (20 : Fin 32) 0x38, 4) := by decide
theorem lm12_at_1a : fetchRel lincombShiftMod12Code 0x1A = some (.store .sw (8 : Fin 32) (21 : Fin 32) 0x34, 4) := by decide
theorem lm12_at_1e : fetchRel lincombShiftMod12Code 0x1E = some (.store .sw (8 : Fin 32) (22 : Fin 32) 0x30, 4) := by decide
theorem lm12_at_22 : fetchRel lincombShiftMod12Code 0x22 = some (.store .sw (8 : Fin 32) (23 : Fin 32) 0x2C, 4) := by decide
theorem lm12_at_26 : fetchRel lincombShiftMod12Code 0x26 = some (.store .sw (8 : Fin 32) (24 : Fin 32) 0x28, 4) := by decide
theorem lm12_at_2a : fetchRel lincombShiftMod12Code 0x2A = some (.store .sw (8 : Fin 32) (25 : Fin 32) 0x24, 4) := by decide
theorem lm12_at_2e : fetchRel lincombShiftMod12Code 0x2E = some (.alu .add (21 : Fin 32) x0 (17 : Fin 32), 2) := by decide
theorem lm12_at_30 : fetchRel lincombShiftMod12Code 0x30 = some (.alu .add (23 : Fin 32) x0 a6, 2) := by decide
theorem lm12_at_32 : fetchRel lincombShiftMod12Code 0x32 = some (.alu .add (19 : Fin 32) x0 a5, 2) := by decide
theorem lm12_at_34 : fetchRel lincombShiftMod12Code 0x34 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem lm12_at_36 : fetchRel lincombShiftMod12Code 0x36 = some (.aluImm .add a0 sp 0x38, 2) := by decide
theorem lm12_at_38 : fetchRel lincombShiftMod12Code 0x38 = some (.aluImm .add (20 : Fin 32) sp 0x38, 4) := by decide
theorem lm12_at_3c : fetchRel lincombShiftMod12Code 0x3C = some (.auipc ra 0x0, 4) := by decide
theorem lm12_at_40 : fetchRel lincombShiftMod12Code 0x40 = some (.jalr ra ra 0xFFFFF9E8, 4) := by decide
theorem lm12_at_44 : fetchRel lincombShiftMod12Code 0x44 = some (.alu .add a0 x0 sp, 2) := by decide
theorem lm12_at_46 : fetchRel lincombShiftMod12Code 0x46 = some (.aluImm .add a1 sp 0x38, 2) := by decide
theorem lm12_at_48 : fetchRel lincombShiftMod12Code 0x48 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem lm12_at_4c : fetchRel lincombShiftMod12Code 0x4C = some (.auipc ra 0x1000, 4) := by decide
theorem lm12_at_50 : fetchRel lincombShiftMod12Code 0x50 = some (.jalr ra ra 0x2E8, 4) := by decide
theorem lm12_at_54 : fetchRel lincombShiftMod12Code 0x54 = some (.load .lw a0 sp 0x68, 2) := by decide
theorem lm12_at_56 : fetchRel lincombShiftMod12Code 0x56 = some (.load .lw a1 sp 0x6C, 2) := by decide
theorem lm12_at_58 : fetchRel lincombShiftMod12Code 0x58 = some (.load .lbu (22 : Fin 32) sp 0x70, 4) := by decide
theorem lm12_at_5c : fetchRel lincombShiftMod12Code 0x5C = some (.store .sw sp a0 0x30, 2) := by decide
theorem lm12_at_5e : fetchRel lincombShiftMod12Code 0x5E = some (.store .sw sp a1 0x34, 2) := by decide
theorem lm12_at_60 : fetchRel lincombShiftMod12Code 0x60 = some (.aluImm .add a0 sp 0x38, 2) := by decide
theorem lm12_at_62 : fetchRel lincombShiftMod12Code 0x62 = some (.alu .add a1 x0 sp, 2) := by decide
theorem lm12_at_64 : fetchRel lincombShiftMod12Code 0x64 = some (.auipc ra 0xFFFFA000, 4) := by decide
theorem lm12_at_68 : fetchRel lincombShiftMod12Code 0x68 = some (.jalr ra ra 0xFFFFFD6A, 4) := by decide
theorem lm12_at_6c : fetchRel lincombShiftMod12Code 0x6C = some (.aluImm .add (6 : Fin 32) x0 0x0, 2) := by decide
theorem lm12_at_6e : fetchRel lincombShiftMod12Code 0x6E = some (.store .sw sp x0 0x118, 4) := by decide
theorem lm12_at_72 : fetchRel lincombShiftMod12Code 0x72 = some (.store .sw sp x0 0x11C, 4) := by decide
theorem lm12_at_76 : fetchRel lincombShiftMod12Code 0x76 = some (.aluImm .add (17 : Fin 32) sp 0x118, 4) := by decide
theorem lm12_at_7a : fetchRel lincombShiftMod12Code 0x7A = some (.aluImm .add a6 x0 0x2, 2) := by decide
theorem lm12_at_7c : fetchRel lincombShiftMod12Code 0x7C = some (.aluImm .add (5 : Fin 32) x0 0x2, 2) := by decide
theorem lm12_at_7e : fetchRel lincombShiftMod12Code 0x7E = some (.branch .beq a6 x0 0x48, 4) := by decide
theorem lm12_at_82 : fetchRel lincombShiftMod12Code 0x82 = some (.aluImm .add (9 : Fin 32) x0 0x0, 2) := by decide
theorem lm12_at_84 : fetchRel lincombShiftMod12Code 0x84 = some (.aluImm .sll a1 (6 : Fin 32) 0x2, 4) := by decide
theorem lm12_at_88 : fetchRel lincombShiftMod12Code 0x88 = some (.alu .add a1 a1 (20 : Fin 32), 2) := by decide
theorem lm12_at_8a : fetchRel lincombShiftMod12Code 0x8A = some (.load .lw a4 a1 0x0, 2) := by decide
theorem lm12_at_8c : fetchRel lincombShiftMod12Code 0x8C = some (.alu .add a5 x0 (5 : Fin 32), 2) := by decide
theorem lm12_at_8e : fetchRel lincombShiftMod12Code 0x8E = some (.alu .add a1 x0 (17 : Fin 32), 2) := by decide
theorem lm12_at_90 : fetchRel lincombShiftMod12Code 0x90 = some (.alu .add (8 : Fin 32) x0 (21 : Fin 32), 2) := by decide
theorem lm12_at_92 : fetchRel lincombShiftMod12Code 0x92 = some (.branch .beq (5 : Fin 32) x0 0x2A, 4) := by decide
theorem lm12_at_96 : fetchRel lincombShiftMod12Code 0x96 = some (.load .lw a2 (8 : Fin 32) 0x0, 2) := by decide
theorem lm12_at_98 : fetchRel lincombShiftMod12Code 0x98 = some (.alu .mul a3 a2 a4, 4) := by decide
theorem lm12_at_9c : fetchRel lincombShiftMod12Code 0x9C = some (.load .lw a0 a1 0x0, 2) := by decide
theorem lm12_at_9e : fetchRel lincombShiftMod12Code 0x9E = some (.alu .mulhu a2 a2 a4, 4) := by decide
theorem lm12_at_a2 : fetchRel lincombShiftMod12Code 0xA2 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, 2) := by decide
theorem lm12_at_a4 : fetchRel lincombShiftMod12Code 0xA4 = some (.alu .add (9 : Fin 32) (9 : Fin 32) a0, 2) := by decide
theorem lm12_at_a6 : fetchRel lincombShiftMod12Code 0xA6 = some (.alu .sltu a0 (9 : Fin 32) a0, 4) := by decide
theorem lm12_at_aa : fetchRel lincombShiftMod12Code 0xAA = some (.alu .add a3 a3 (9 : Fin 32), 2) := by decide
theorem lm12_at_ac : fetchRel lincombShiftMod12Code 0xAC = some (.alu .add a0 a0 a2, 2) := by decide
theorem lm12_at_ae : fetchRel lincombShiftMod12Code 0xAE = some (.alu .sltu (9 : Fin 32) a3 (9 : Fin 32), 4) := by decide
theorem lm12_at_b2 : fetchRel lincombShiftMod12Code 0xB2 = some (.store .sw a1 a3 0x0, 2) := by decide
theorem lm12_at_b4 : fetchRel lincombShiftMod12Code 0xB4 = some (.alu .add (9 : Fin 32) (9 : Fin 32) a0, 2) := by decide
theorem lm12_at_b6 : fetchRel lincombShiftMod12Code 0xB6 = some (.aluImm .add a1 a1 0x4, 2) := by decide
theorem lm12_at_b8 : fetchRel lincombShiftMod12Code 0xB8 = some (.aluImm .add a5 a5 0xFFFFFFFF, 2) := by decide
theorem lm12_at_ba : fetchRel lincombShiftMod12Code 0xBA = some (.branch .bne a5 x0 0xFFFFFFDC, 2) := by decide
theorem lm12_at_bc : fetchRel lincombShiftMod12Code 0xBC = some (.aluImm .add (6 : Fin 32) (6 : Fin 32) 0x1, 2) := by decide
theorem lm12_at_be : fetchRel lincombShiftMod12Code 0xBE = some (.aluImm .add (17 : Fin 32) (17 : Fin 32) 0x4, 2) := by decide
theorem lm12_at_c0 : fetchRel lincombShiftMod12Code 0xC0 = some (.aluImm .add (5 : Fin 32) (5 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem lm12_at_c2 : fetchRel lincombShiftMod12Code 0xC2 = some (.branch .bne (6 : Fin 32) a6 0xFFFFFFC0, 4) := by decide
theorem lm12_at_c6 : fetchRel lincombShiftMod12Code 0xC6 = some (.aluImm .add a0 x0 0x40, 4) := by decide
theorem lm12_at_ca : fetchRel lincombShiftMod12Code 0xCA = some (.alu .sub (24 : Fin 32) a0 (19 : Fin 32), 4) := by decide
theorem lm12_at_ce : fetchRel lincombShiftMod12Code 0xCE = some (.branch .bgeu (24 : Fin 32) a0 0x238, 4) := by decide
theorem lm12_at_d2 : fetchRel lincombShiftMod12Code 0xD2 = some (.aluImm .srl (21 : Fin 32) (24 : Fin 32) 0x5, 4) := by decide
theorem lm12_at_d6 : fetchRel lincombShiftMod12Code 0xD6 = some (.aluImm .add a0 x0 0x2, 2) := by decide
theorem lm12_at_d8 : fetchRel lincombShiftMod12Code 0xD8 = some (.store .sw sp x0 0x38, 2) := by decide
theorem lm12_at_da : fetchRel lincombShiftMod12Code 0xDA = some (.store .sw sp x0 0x3C, 2) := by decide
theorem lm12_at_dc : fetchRel lincombShiftMod12Code 0xDC = some (.alu .sub a2 a0 (21 : Fin 32), 4) := by decide
theorem lm12_at_e0 : fetchRel lincombShiftMod12Code 0xE0 = some (.aluImm .add a0 sp 0x38, 2) := by decide
theorem lm12_at_e2 : fetchRel lincombShiftMod12Code 0xE2 = some (.aluImm .add a1 x0 0x2, 2) := by decide
theorem lm12_at_e4 : fetchRel lincombShiftMod12Code 0xE4 = some (.auipc ra 0x0, 4) := by decide
theorem lm12_at_e8 : fetchRel lincombShiftMod12Code 0xE8 = some (.jalr ra ra 0xFFFFFCB2, 4) := by decide
theorem lm12_at_ec : fetchRel lincombShiftMod12Code 0xEC = some (.alu .add (20 : Fin 32) x0 a0, 2) := by decide
theorem lm12_at_ee : fetchRel lincombShiftMod12Code 0xEE = some (.alu .add (8 : Fin 32) x0 a1, 2) := by decide
theorem lm12_at_f0 : fetchRel lincombShiftMod12Code 0xF0 = some (.lui a0 0x3FCC5000, 4) := by decide
theorem lm12_at_f4 : fetchRel lincombShiftMod12Code 0xF4 = some (.aluImm .add a0 a0 0xFFFFF838, 4) := by decide
theorem lm12_at_f8 : fetchRel lincombShiftMod12Code 0xF8 = some (.aluImm .add a1 x0 0x2, 2) := by decide
theorem lm12_at_fa : fetchRel lincombShiftMod12Code 0xFA = some (.alu .add a2 x0 (21 : Fin 32), 2) := by decide
theorem lm12_at_fc : fetchRel lincombShiftMod12Code 0xFC = some (.auipc ra 0x0, 4) := by decide
theorem lm12_at_100 : fetchRel lincombShiftMod12Code 0x100 = some (.jalr ra ra 0xFFFFFCAA, 4) := by decide
theorem lm12_at_104 : fetchRel lincombShiftMod12Code 0x104 = some (.branch .bne (8 : Fin 32) a1 0x1FA, 4) := by decide
theorem lm12_at_108 : fetchRel lincombShiftMod12Code 0x108 = some (.aluImm .add (21 : Fin 32) sp 0xB0, 4) := by decide
theorem lm12_at_10c : fetchRel lincombShiftMod12Code 0x10C = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem lm12_at_10e : fetchRel lincombShiftMod12Code 0x10E = some (.alu .add a2 x0 (20 : Fin 32), 2) := by decide
theorem lm12_at_110 : fetchRel lincombShiftMod12Code 0x110 = some (.branch .beq (8 : Fin 32) x0 0xE, 2) := by decide
theorem lm12_at_112 : fetchRel lincombShiftMod12Code 0x112 = some (.load .lw a3 a0 0x0, 2) := by decide
theorem lm12_at_114 : fetchRel lincombShiftMod12Code 0x114 = some (.aluImm .add a0 a0 0x4, 2) := by decide
theorem lm12_at_116 : fetchRel lincombShiftMod12Code 0x116 = some (.store .sw a2 a3 0x0, 2) := by decide
theorem lm12_at_118 : fetchRel lincombShiftMod12Code 0x118 = some (.aluImm .add a2 a2 0x4, 2) := by decide
theorem lm12_at_11a : fetchRel lincombShiftMod12Code 0x11A = some (.aluImm .add a1 a1 0xFFFFFFFF, 2) := by decide
theorem lm12_at_11c : fetchRel lincombShiftMod12Code 0x11C = some (.branch .bne a1 x0 0xFFFFFFF6, 2) := by decide
theorem lm12_at_11e : fetchRel lincombShiftMod12Code 0x11E = some (.aluImm .and a0 (24 : Fin 32) 0x1F, 4) := by decide
theorem lm12_at_122 : fetchRel lincombShiftMod12Code 0x122 = some (.branch .beq a0 x0 0x28, 2) := by decide
theorem lm12_at_124 : fetchRel lincombShiftMod12Code 0x124 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem lm12_at_126 : fetchRel lincombShiftMod12Code 0x126 = some (.aluImm .sll a2 (8 : Fin 32) 0x2, 4) := by decide
theorem lm12_at_12a : fetchRel lincombShiftMod12Code 0x12A = some (.alu .add a3 a2 (20 : Fin 32), 4) := by decide
theorem lm12_at_12e : fetchRel lincombShiftMod12Code 0x12E = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem lm12_at_132 : fetchRel lincombShiftMod12Code 0x132 = some (.alu .sub a2 a2 a0, 2) := by decide
theorem lm12_at_134 : fetchRel lincombShiftMod12Code 0x134 = some (.aluImm .add a3 a3 0xFFFFFFFC, 2) := by decide
theorem lm12_at_136 : fetchRel lincombShiftMod12Code 0x136 = some (.branch .beq (8 : Fin 32) x0 0x14, 2) := by decide
theorem lm12_at_138 : fetchRel lincombShiftMod12Code 0x138 = some (.load .lw a4 a3 0x0, 2) := by decide
theorem lm12_at_13a : fetchRel lincombShiftMod12Code 0x13A = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem lm12_at_13c : fetchRel lincombShiftMod12Code 0x13C = some (.alu .srl a5 a4 a0, 4) := by decide
theorem lm12_at_140 : fetchRel lincombShiftMod12Code 0x140 = some (.alu .or a5 a5 a1, 2) := by decide
theorem lm12_at_142 : fetchRel lincombShiftMod12Code 0x142 = some (.alu .sll a1 a4 a2, 4) := by decide
theorem lm12_at_146 : fetchRel lincombShiftMod12Code 0x146 = some (.store .sw a3 a5 0x0, 2) := by decide
theorem lm12_at_148 : fetchRel lincombShiftMod12Code 0x148 = some (.jal x0 0xFFFFFFEC, 2) := by decide
theorem lm12_at_14a : fetchRel lincombShiftMod12Code 0x14A = some (.load .lw a2 sp 0x38, 2) := by decide
theorem lm12_at_14c : fetchRel lincombShiftMod12Code 0x14C = some (.load .lw a3 sp 0x3C, 2) := by decide
theorem lm12_at_14e : fetchRel lincombShiftMod12Code 0x14E = some (.store .sw sp x0 0x38, 2) := by decide
theorem lm12_at_150 : fetchRel lincombShiftMod12Code 0x150 = some (.store .sw sp x0 0x3C, 2) := by decide
theorem lm12_at_152 : fetchRel lincombShiftMod12Code 0x152 = some (.aluImm .add a0 sp 0x118, 2) := by decide
theorem lm12_at_154 : fetchRel lincombShiftMod12Code 0x154 = some (.aluImm .add a1 sp 0x78, 2) := by decide
theorem lm12_at_156 : fetchRel lincombShiftMod12Code 0x156 = some (.store .sw sp a2 0x78, 2) := by decide
theorem lm12_at_158 : fetchRel lincombShiftMod12Code 0x158 = some (.store .sw sp a3 0x7C, 2) := by decide
theorem lm12_at_15a : fetchRel lincombShiftMod12Code 0x15A = some (.aluImm .add a2 sp 0x38, 2) := by decide
theorem lm12_at_15c : fetchRel lincombShiftMod12Code 0x15C = some (.aluImm .add a3 x0 0x2, 2) := by decide
theorem lm12_at_15e : fetchRel lincombShiftMod12Code 0x15E = some (.branch .beq a3 x0 0x14, 2) := by decide
theorem lm12_at_160 : fetchRel lincombShiftMod12Code 0x160 = some (.load .lw a4 a0 0x0, 2) := by decide
theorem lm12_at_162 : fetchRel lincombShiftMod12Code 0x162 = some (.load .lw a5 a1 0x0, 2) := by decide
theorem lm12_at_164 : fetchRel lincombShiftMod12Code 0x164 = some (.aluImm .add a0 a0 0x4, 2) := by decide
theorem lm12_at_166 : fetchRel lincombShiftMod12Code 0x166 = some (.alu .and a4 a4 a5, 2) := by decide
theorem lm12_at_168 : fetchRel lincombShiftMod12Code 0x168 = some (.aluImm .add a1 a1 0x4, 2) := by decide
theorem lm12_at_16a : fetchRel lincombShiftMod12Code 0x16A = some (.store .sw a2 a4 0x0, 2) := by decide
theorem lm12_at_16c : fetchRel lincombShiftMod12Code 0x16C = some (.aluImm .add a2 a2 0x4, 2) := by decide
theorem lm12_at_16e : fetchRel lincombShiftMod12Code 0x16E = some (.aluImm .add a3 a3 0xFFFFFFFF, 2) := by decide
theorem lm12_at_170 : fetchRel lincombShiftMod12Code 0x170 = some (.branch .bne a3 x0 0xFFFFFFF0, 2) := by decide
theorem lm12_at_172 : fetchRel lincombShiftMod12Code 0x172 = some (.load .lw a0 sp 0x38, 2) := by decide
theorem lm12_at_174 : fetchRel lincombShiftMod12Code 0x174 = some (.load .lw a1 sp 0x3C, 2) := by decide
theorem lm12_at_176 : fetchRel lincombShiftMod12Code 0x176 = some (.store .sw sp a0 0x118, 4) := by decide
theorem lm12_at_17a : fetchRel lincombShiftMod12Code 0x17A = some (.store .sw sp a1 0x11C, 4) := by decide
theorem lm12_at_17e : fetchRel lincombShiftMod12Code 0x17E = some (.aluImm .add a0 sp 0x80, 2) := by decide
theorem lm12_at_180 : fetchRel lincombShiftMod12Code 0x180 = some (.aluImm .add a2 sp 0x118, 2) := by decide
theorem lm12_at_182 : fetchRel lincombShiftMod12Code 0x182 = some (.alu .add a1 x0 (23 : Fin 32), 2) := by decide
theorem lm12_at_184 : fetchRel lincombShiftMod12Code 0x184 = some (.aluImm .add (24 : Fin 32) sp 0x80, 4) := by decide
theorem lm12_at_188 : fetchRel lincombShiftMod12Code 0x188 = some (.auipc ra 0x0, 4) := by decide
theorem lm12_at_18c : fetchRel lincombShiftMod12Code 0x18C = some (.jalr ra ra 0xFFFFFC34, 4) := by decide
theorem lm12_at_190 : fetchRel lincombShiftMod12Code 0x190 = some (.aluImm .add a0 sp 0xB8, 2) := by decide
theorem lm12_at_192 : fetchRel lincombShiftMod12Code 0x192 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem lm12_at_196 : fetchRel lincombShiftMod12Code 0x196 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem lm12_at_198 : fetchRel lincombShiftMod12Code 0x198 = some (.aluImm .add (25 : Fin 32) sp 0xB8, 4) := by decide
theorem lm12_at_19c : fetchRel lincombShiftMod12Code 0x19C = some (.auipc ra 0x1000, 4) := by decide
theorem lm12_at_1a0 : fetchRel lincombShiftMod12Code 0x1A0 = some (.jalr ra ra 0x130, 4) := by decide
theorem lm12_at_1a4 : fetchRel lincombShiftMod12Code 0x1A4 = some (.aluImm .add (20 : Fin 32) x0 0x0, 2) := by decide
theorem lm12_at_1a6 : fetchRel lincombShiftMod12Code 0x1A6 = some (.alu .add (9 : Fin 32) x0 sp, 2) := by decide
theorem lm12_at_1a8 : fetchRel lincombShiftMod12Code 0x1A8 = some (.aluImm .add (8 : Fin 32) x0 0xC, 2) := by decide
theorem lm12_at_1aa : fetchRel lincombShiftMod12Code 0x1AA = some (.branch .beq (8 : Fin 32) x0 0x22, 2) := by decide
theorem lm12_at_1ac : fetchRel lincombShiftMod12Code 0x1AC = some (.load .lw a0 (9 : Fin 32) 0x0, 2) := by decide
theorem lm12_at_1ae : fetchRel lincombShiftMod12Code 0x1AE = some (.load .lw a1 (24 : Fin 32) 0x0, 4) := by decide
theorem lm12_at_1b2 : fetchRel lincombShiftMod12Code 0x1B2 = some (.alu .add a2 x0 (20 : Fin 32), 2) := by decide
theorem lm12_at_1b4 : fetchRel lincombShiftMod12Code 0x1B4 = some (.auipc ra 0xFFFEF000, 4) := by decide
theorem lm12_at_1b8 : fetchRel lincombShiftMod12Code 0x1B8 = some (.jalr ra ra 0xFFFFFC52, 4) := by decide
theorem lm12_at_1bc : fetchRel lincombShiftMod12Code 0x1BC = some (.alu .add (20 : Fin 32) x0 a1, 2) := by decide
theorem lm12_at_1be : fetchRel lincombShiftMod12Code 0x1BE = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x4, 2) := by decide
theorem lm12_at_1c0 : fetchRel lincombShiftMod12Code 0x1C0 = some (.store .sw (25 : Fin 32) a0 0x0, 4) := by decide
theorem lm12_at_1c4 : fetchRel lincombShiftMod12Code 0x1C4 = some (.aluImm .add (24 : Fin 32) (24 : Fin 32) 0x4, 2) := by decide
theorem lm12_at_1c6 : fetchRel lincombShiftMod12Code 0x1C6 = some (.aluImm .add (25 : Fin 32) (25 : Fin 32) 0x4, 2) := by decide
theorem lm12_at_1c8 : fetchRel lincombShiftMod12Code 0x1C8 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem lm12_at_1ca : fetchRel lincombShiftMod12Code 0x1CA = some (.branch .bne (8 : Fin 32) x0 0xFFFFFFE2, 2) := by decide
theorem lm12_at_1cc : fetchRel lincombShiftMod12Code 0x1CC = some (.alu .add a0 x0 sp, 2) := by decide
theorem lm12_at_1ce : fetchRel lincombShiftMod12Code 0x1CE = some (.aluImm .add a1 sp 0xB8, 2) := by decide
theorem lm12_at_1d0 : fetchRel lincombShiftMod12Code 0x1D0 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem lm12_at_1d4 : fetchRel lincombShiftMod12Code 0x1D4 = some (.auipc ra 0x1000, 4) := by decide
theorem lm12_at_1d8 : fetchRel lincombShiftMod12Code 0x1D8 = some (.jalr ra ra 0x160, 4) := by decide
theorem lm12_at_1dc : fetchRel lincombShiftMod12Code 0x1DC = some (.store .sw sp x0 0x38, 2) := by decide
theorem lm12_at_1de : fetchRel lincombShiftMod12Code 0x1DE = some (.store .sw sp x0 0x3C, 2) := by decide
theorem lm12_at_1e0 : fetchRel lincombShiftMod12Code 0x1E0 = some (.aluImm .add (24 : Fin 32) sp 0x30, 4) := by decide
theorem lm12_at_1e4 : fetchRel lincombShiftMod12Code 0x1E4 = some (.aluImm .add (9 : Fin 32) sp 0x38, 2) := by decide
theorem lm12_at_1e6 : fetchRel lincombShiftMod12Code 0x1E6 = some (.aluImm .add (8 : Fin 32) x0 0x2, 2) := by decide
theorem lm12_at_1e8 : fetchRel lincombShiftMod12Code 0x1E8 = some (.branch .beq (8 : Fin 32) x0 0x22, 2) := by decide
theorem lm12_at_1ea : fetchRel lincombShiftMod12Code 0x1EA = some (.load .lw a0 (24 : Fin 32) 0x0, 4) := by decide
theorem lm12_at_1ee : fetchRel lincombShiftMod12Code 0x1EE = some (.load .lw a1 (21 : Fin 32) 0x0, 4) := by decide
theorem lm12_at_1f2 : fetchRel lincombShiftMod12Code 0x1F2 = some (.alu .add a2 x0 (20 : Fin 32), 2) := by decide
theorem lm12_at_1f4 : fetchRel lincombShiftMod12Code 0x1F4 = some (.auipc ra 0xFFFEF000, 4) := by decide
theorem lm12_at_1f8 : fetchRel lincombShiftMod12Code 0x1F8 = some (.jalr ra ra 0xFFFFFC12, 4) := by decide
theorem lm12_at_1fc : fetchRel lincombShiftMod12Code 0x1FC = some (.alu .add (20 : Fin 32) x0 a1, 2) := by decide
theorem lm12_at_1fe : fetchRel lincombShiftMod12Code 0x1FE = some (.aluImm .add (24 : Fin 32) (24 : Fin 32) 0x4, 2) := by decide
theorem lm12_at_200 : fetchRel lincombShiftMod12Code 0x200 = some (.store .sw (9 : Fin 32) a0 0x0, 2) := by decide
theorem lm12_at_202 : fetchRel lincombShiftMod12Code 0x202 = some (.aluImm .add (21 : Fin 32) (21 : Fin 32) 0x4, 2) := by decide
theorem lm12_at_204 : fetchRel lincombShiftMod12Code 0x204 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x4, 2) := by decide
theorem lm12_at_206 : fetchRel lincombShiftMod12Code 0x206 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem lm12_at_208 : fetchRel lincombShiftMod12Code 0x208 = some (.branch .bne (8 : Fin 32) x0 0xFFFFFFE2, 2) := by decide
theorem lm12_at_20a : fetchRel lincombShiftMod12Code 0x20A = some (.load .lw a0 sp 0x38, 2) := by decide
theorem lm12_at_20c : fetchRel lincombShiftMod12Code 0x20C = some (.load .lw a1 sp 0x3C, 2) := by decide
theorem lm12_at_20e : fetchRel lincombShiftMod12Code 0x20E = some (.store .sw sp a0 0x30, 2) := by decide
theorem lm12_at_210 : fetchRel lincombShiftMod12Code 0x210 = some (.store .sw sp a1 0x34, 2) := by decide
theorem lm12_at_212 : fetchRel lincombShiftMod12Code 0x212 = some (.store .sw sp (20 : Fin 32) 0x38, 2) := by decide
theorem lm12_at_214 : fetchRel lincombShiftMod12Code 0x214 = some (.aluImm .add a0 sp 0x38, 2) := by decide
theorem lm12_at_216 : fetchRel lincombShiftMod12Code 0x216 = some (.load .lw a0 sp 0x38, 2) := by decide
theorem lm12_at_218 : fetchRel lincombShiftMod12Code 0x218 = some (.alu .sltu (20 : Fin 32) x0 a0, 4) := by decide
theorem lm12_at_21c : fetchRel lincombShiftMod12Code 0x21C = some (.alu .add a0 x0 sp, 2) := by decide
theorem lm12_at_21e : fetchRel lincombShiftMod12Code 0x21E = some (.aluImm .add a1 sp 0x30, 2) := by decide
theorem lm12_at_220 : fetchRel lincombShiftMod12Code 0x220 = some (.alu .add a2 x0 (20 : Fin 32), 2) := by decide
theorem lm12_at_222 : fetchRel lincombShiftMod12Code 0x222 = some (.alu .add (21 : Fin 32) x0 sp, 2) := by decide
theorem lm12_at_224 : fetchRel lincombShiftMod12Code 0x224 = some (.auipc ra 0x0, 4) := by decide
theorem lm12_at_228 : fetchRel lincombShiftMod12Code 0x228 = some (.jalr ra ra 0xFFFFFC82, 4) := by decide
theorem lm12_at_22c : fetchRel lincombShiftMod12Code 0x22C = some (.alu .add a0 x0 sp, 2) := by decide
theorem lm12_at_22e : fetchRel lincombShiftMod12Code 0x22E = some (.aluImm .add a1 sp 0x30, 2) := by decide
theorem lm12_at_230 : fetchRel lincombShiftMod12Code 0x230 = some (.alu .add a2 x0 (19 : Fin 32), 2) := by decide
theorem lm12_at_232 : fetchRel lincombShiftMod12Code 0x232 = some (.auipc ra 0x0, 4) := by decide
theorem lm12_at_236 : fetchRel lincombShiftMod12Code 0x236 = some (.jalr ra ra 0xFFFFF976, 4) := by decide
theorem lm12_at_23a : fetchRel lincombShiftMod12Code 0x23A = some (.load .lw (19 : Fin 32) sp 0x30, 2) := by decide
theorem lm12_at_23c : fetchRel lincombShiftMod12Code 0x23C = some (.aluImm .add a0 sp 0xE8, 2) := by decide
theorem lm12_at_23e : fetchRel lincombShiftMod12Code 0x23E = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem lm12_at_242 : fetchRel lincombShiftMod12Code 0x242 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem lm12_at_244 : fetchRel lincombShiftMod12Code 0x244 = some (.aluImm .add (8 : Fin 32) sp 0xE8, 2) := by decide
theorem lm12_at_246 : fetchRel lincombShiftMod12Code 0x246 = some (.auipc ra 0x1000, 4) := by decide
theorem lm12_at_24a : fetchRel lincombShiftMod12Code 0x24A = some (.jalr ra ra 0x86, 4) := by decide
theorem lm12_at_24e : fetchRel lincombShiftMod12Code 0x24E = some (.aluImm .add a2 x0 0x0, 2) := by decide
theorem lm12_at_250 : fetchRel lincombShiftMod12Code 0x250 = some (.aluImm .add (9 : Fin 32) x0 0xC, 2) := by decide
theorem lm12_at_252 : fetchRel lincombShiftMod12Code 0x252 = some (.branch .beq (9 : Fin 32) x0 0x20, 2) := by decide
theorem lm12_at_254 : fetchRel lincombShiftMod12Code 0x254 = some (.load .lw a0 (21 : Fin 32) 0x0, 4) := by decide
theorem lm12_at_258 : fetchRel lincombShiftMod12Code 0x258 = some (.load .lw a1 (23 : Fin 32) 0x0, 4) := by decide
theorem lm12_at_25c : fetchRel lincombShiftMod12Code 0x25C = some (.auipc ra 0xFFFEF000, 4) := by decide
theorem lm12_at_260 : fetchRel lincombShiftMod12Code 0x260 = some (.jalr ra ra 0xFFFFFBAA, 4) := by decide
theorem lm12_at_264 : fetchRel lincombShiftMod12Code 0x264 = some (.alu .add a2 x0 a1, 2) := by decide
theorem lm12_at_266 : fetchRel lincombShiftMod12Code 0x266 = some (.aluImm .add (21 : Fin 32) (21 : Fin 32) 0x4, 2) := by decide
theorem lm12_at_268 : fetchRel lincombShiftMod12Code 0x268 = some (.store .sw (8 : Fin 32) a0 0x0, 2) := by decide
theorem lm12_at_26a : fetchRel lincombShiftMod12Code 0x26A = some (.aluImm .add (23 : Fin 32) (23 : Fin 32) 0x4, 2) := by decide
theorem lm12_at_26c : fetchRel lincombShiftMod12Code 0x26C = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, 2) := by decide
theorem lm12_at_26e : fetchRel lincombShiftMod12Code 0x26E = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem lm12_at_270 : fetchRel lincombShiftMod12Code 0x270 = some (.branch .bne (9 : Fin 32) x0 0xFFFFFFE4, 2) := by decide
theorem lm12_at_272 : fetchRel lincombShiftMod12Code 0x272 = some (.store .sw sp (19 : Fin 32) 0x38, 2) := by decide
theorem lm12_at_274 : fetchRel lincombShiftMod12Code 0x274 = some (.aluImm .add a0 sp 0x38, 2) := by decide
theorem lm12_at_276 : fetchRel lincombShiftMod12Code 0x276 = some (.load .lw a0 sp 0x38, 2) := by decide
theorem lm12_at_278 : fetchRel lincombShiftMod12Code 0x278 = some (.aluImm .sltu (9 : Fin 32) a0 0x1, 4) := by decide
theorem lm12_at_27c : fetchRel lincombShiftMod12Code 0x27C = some (.alu .and (9 : Fin 32) (9 : Fin 32) a2, 2) := by decide
theorem lm12_at_27e : fetchRel lincombShiftMod12Code 0x27E = some (.store .sb sp (9 : Fin 32) 0x38, 4) := by decide
theorem lm12_at_282 : fetchRel lincombShiftMod12Code 0x282 = some (.aluImm .add a0 sp 0x38, 2) := by decide
theorem lm12_at_284 : fetchRel lincombShiftMod12Code 0x284 = some (.load .lbu a0 sp 0x38, 4) := by decide
theorem lm12_at_288 : fetchRel lincombShiftMod12Code 0x288 = some (.aluImm .add a0 a0 0xFFFFFFFF, 2) := by decide
theorem lm12_at_28a : fetchRel lincombShiftMod12Code 0x28A = some (.alu .xor (8 : Fin 32) (22 : Fin 32) (20 : Fin 32), 4) := by decide
theorem lm12_at_28e : fetchRel lincombShiftMod12Code 0x28E = some (.alu .and a2 a2 a0, 2) := by decide
theorem lm12_at_290 : fetchRel lincombShiftMod12Code 0x290 = some (.alu .add a0 x0 (19 : Fin 32), 2) := by decide
theorem lm12_at_292 : fetchRel lincombShiftMod12Code 0x292 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem lm12_at_294 : fetchRel lincombShiftMod12Code 0x294 = some (.auipc ra 0xFFFEF000, 4) := by decide
theorem lm12_at_298 : fetchRel lincombShiftMod12Code 0x298 = some (.jalr ra ra 0xFFFFFB72, 4) := by decide
theorem lm12_at_29c : fetchRel lincombShiftMod12Code 0x29C = some (.aluImm .add a0 sp 0x38, 2) := by decide
theorem lm12_at_29e : fetchRel lincombShiftMod12Code 0x29E = some (.aluImm .add a1 sp 0xE8, 2) := by decide
theorem lm12_at_2a0 : fetchRel lincombShiftMod12Code 0x2A0 = some (.alu .add a2 x0 sp, 2) := by decide
theorem lm12_at_2a2 : fetchRel lincombShiftMod12Code 0x2A2 = some (.alu .add a3 x0 (9 : Fin 32), 2) := by decide
theorem lm12_at_2a4 : fetchRel lincombShiftMod12Code 0x2A4 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem lm12_at_2a8 : fetchRel lincombShiftMod12Code 0x2A8 = some (.jalr ra ra 0x6AA, 4) := by decide
theorem lm12_at_2ac : fetchRel lincombShiftMod12Code 0x2AC = some (.alu .add a0 x0 sp, 2) := by decide
theorem lm12_at_2ae : fetchRel lincombShiftMod12Code 0x2AE = some (.aluImm .add a1 sp 0x38, 2) := by decide
theorem lm12_at_2b0 : fetchRel lincombShiftMod12Code 0x2B0 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem lm12_at_2b4 : fetchRel lincombShiftMod12Code 0x2B4 = some (.auipc ra 0x1000, 4) := by decide
theorem lm12_at_2b8 : fetchRel lincombShiftMod12Code 0x2B8 = some (.jalr ra ra 0x80, 4) := by decide
theorem lm12_at_2bc : fetchRel lincombShiftMod12Code 0x2BC = some (.alu .add a1 x0 sp, 2) := by decide
theorem lm12_at_2be : fetchRel lincombShiftMod12Code 0x2BE = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem lm12_at_2c2 : fetchRel lincombShiftMod12Code 0x2C2 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem lm12_at_2c4 : fetchRel lincombShiftMod12Code 0x2C4 = some (.auipc ra 0x1000, 4) := by decide
theorem lm12_at_2c8 : fetchRel lincombShiftMod12Code 0x2C8 = some (.jalr ra ra 0x70, 4) := by decide
theorem lm12_at_2cc : fetchRel lincombShiftMod12Code 0x2CC = some (.store .sb (18 : Fin 32) (8 : Fin 32) 0x30, 4) := by decide
theorem lm12_at_2d0 : fetchRel lincombShiftMod12Code 0x2D0 = some (.aluImm .add a0 sp 0x100, 2) := by decide
theorem lm12_at_2d2 : fetchRel lincombShiftMod12Code 0x2D2 = some (.load .lw ra a0 0x4C, 4) := by decide
theorem lm12_at_2d6 : fetchRel lincombShiftMod12Code 0x2D6 = some (.load .lw (8 : Fin 32) a0 0x48, 2) := by decide
theorem lm12_at_2d8 : fetchRel lincombShiftMod12Code 0x2D8 = some (.load .lw (9 : Fin 32) a0 0x44, 2) := by decide
theorem lm12_at_2da : fetchRel lincombShiftMod12Code 0x2DA = some (.load .lw (18 : Fin 32) a0 0x40, 4) := by decide
theorem lm12_at_2de : fetchRel lincombShiftMod12Code 0x2DE = some (.load .lw (19 : Fin 32) a0 0x3C, 4) := by decide
theorem lm12_at_2e2 : fetchRel lincombShiftMod12Code 0x2E2 = some (.load .lw (20 : Fin 32) a0 0x38, 4) := by decide
theorem lm12_at_2e6 : fetchRel lincombShiftMod12Code 0x2E6 = some (.load .lw (21 : Fin 32) a0 0x34, 4) := by decide
theorem lm12_at_2ea : fetchRel lincombShiftMod12Code 0x2EA = some (.load .lw (22 : Fin 32) a0 0x30, 4) := by decide
theorem lm12_at_2ee : fetchRel lincombShiftMod12Code 0x2EE = some (.load .lw (23 : Fin 32) a0 0x2C, 4) := by decide
theorem lm12_at_2f2 : fetchRel lincombShiftMod12Code 0x2F2 = some (.load .lw (24 : Fin 32) a0 0x28, 4) := by decide
theorem lm12_at_2f6 : fetchRel lincombShiftMod12Code 0x2F6 = some (.load .lw (25 : Fin 32) a0 0x24, 4) := by decide
theorem lm12_at_2fa : fetchRel lincombShiftMod12Code 0x2FA = some (.aluImm .add sp sp 0x150, 2) := by decide
theorem lm12_at_2fc : fetchRel lincombShiftMod12Code 0x2FC = some (.jalr x0 ra 0x0, 2) := by decide
theorem lm12_at_2fe : fetchRel lincombShiftMod12Code 0x2FE = some (.auipc ra 0xFFFFA000, 4) := by decide
theorem lm12_at_302 : fetchRel lincombShiftMod12Code 0x302 = some (.jalr ra ra 0xFFFFFA46, 4) := by decide
theorem lm12_at_306 : fetchRel lincombShiftMod12Code 0x306 = some (.aluImm .add a0 x0 0x1B, 2) := by decide
theorem lm12_at_308 : fetchRel lincombShiftMod12Code 0x308 = some (.auipc ra 0xFFFFA000, 4) := by decide
theorem lm12_at_30c : fetchRel lincombShiftMod12Code 0x30C = some (.jalr ra ra 0xFFFFFA96, 4) := by decide
end

/-- `mf`: the low 64 bits of the magnitude `A` times `mi`'s value `MI`,
modulo 2^64, masked to the low `s` bits. -/
def lrsmMf (A MI s : Nat) : Nat := A % 2 ^ 64 * MI % 2 ^ 64 % 2 ^ s

/-- What `lincomb_int_reduce_shift_mod` stores, from the linear combination's
sign `σ` and 448-bit magnitude `A`, `mi`'s value `MI`, the shift `s`, and the
modulus `M`: the sign byte, and the 12-limb magnitude. -/
def lrsm (σ A MI s M : Nat) : Nat × Nat :=
  let XA := M * lrsmMf A MI s
  let Y := if A < XA then XA - A else A - XA
  let Z := Y / 2 ^ s
  let lo := Z % 2 ^ 384
  (if A < XA then 1 - σ else σ,
    if Z / 2 ^ 384 % 2 ^ 32 = 0 ∧ lo < M then lo else (lo + 2 ^ 384 - M) % 2 ^ 384)

/-- `lincomb_int`'s address, from the function's. -/
abbrev lmLc (P : Word) : Word := P + 0xFFFFFA24

/-- `shr_in_place_wide`'s address, from the function's. -/
abbrev lmShr (P : Word) : Word := P + 0xFFFFFBA8

/-- Where the function runs: its code, its callees' code at their offsets,
the 0x330 bytes of stack at `G` that it and its callees use (its frame is
the top 0x150), the result `res`, the operands, the modulus at `mp`, and
`mi` at `mip`, each apart from what it must not touch. -/
structure LMEnv (M : Word → BitVec 8) (P G res ap bp cp dp mp mip : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P lincombShiftMod12Code
  lc : CodeIn M (lmLc P) lincomb12Code
  abs : CodeIn M (lmLc P + 0xFFFFA54E) absSign2Code
  wide : CodeIn M (lmLc P + 0x398) wideMul12x2Code
  neg : CodeIn M (lmLc P + 0x482) condNeg12Code
  mset : CodeIn M (lmLc P + 0x18A8) memsetCode
  stub : CodeIn M (lmLc P + 0x1910) memcpyStubCode
  body : CodeIn M (lmLc P + 0x1918) memcpyBodyCode
  bsub : CodeIn M (lcBsub (lmLc P)) borrowingSubCode
  sel2 : CodeIn M (lmLc P + 0x592) uintSelect2Code
  sel12 : CodeIn M (lmLc P + 0xFFFFFF2A) uintSelect12Code
  zero : CodeIn M (BitVec.ofNat 32 u2ZeroAddress) u2ZeroData
  one : CodeIn M (BitVec.ofNat 32 u2OneAddress) u2OneData
  shr : CodeIn M (lmShr P) shr12Code
  lm : CodeIn M (lmShr P + 0x1EE) leadMut12Code
  tr : CodeIn M (lmShr P + 0x1FE) trailing12Code
  tur : CodeIn M (P + 0xFFFF9DCE) toUintResize2Code
  max : CodeIn M (BitVec.ofNat 32 u2MaxAddress) u2MaxData
  hG : G.toNat % 4 = 0
  hGt : G.toNat + 0x330 ≤ 2 ^ 32
  hres : res.toNat % 4 = 0
  hap : ap.toNat % 4 = 0
  hbp : bp.toNat % 4 = 0
  hcp : cp.toNat % 4 = 0
  hdp : dp.toNat % 4 = 0
  hmp : mp.toNat % 4 = 0
  hmip : mip.toNat % 4 = 0
  hwr : res.toNat + 49 < 2 ^ 32
  hwa : ap.toNat + 49 < 2 ^ 32
  hwb : bp.toNat + 49 < 2 ^ 32
  sC : Sep G 0x330 P lincombShiftMod12Code.length
  sL : Sep G 0x330 (lmLc P) lincomb12Code.length
  sA : Sep G 0x330 (lmLc P + 0xFFFFA54E) absSign2Code.length
  sW : Sep G 0x330 (lmLc P + 0x398) wideMul12x2Code.length
  sN : Sep G 0x330 (lmLc P + 0x482) condNeg12Code.length
  sM : Sep G 0x330 (lmLc P + 0x18A8) memsetCode.length
  sU : Sep G 0x330 (lmLc P + 0x1910) memcpyStubCode.length
  sB : Sep G 0x330 (lmLc P + 0x1918) memcpyBodyCode.length
  sBs : Sep G 0x330 (lcBsub (lmLc P)) borrowingSubCode.length
  s2 : Sep G 0x330 (lmLc P + 0x592) uintSelect2Code.length
  s12 : Sep G 0x330 (lmLc P + 0xFFFFFF2A) uintSelect12Code.length
  sZ : Sep G 0x330 (BitVec.ofNat 32 u2ZeroAddress) 8
  sO : Sep G 0x330 (BitVec.ofNat 32 u2OneAddress) 8
  sS : Sep G 0x330 (lmShr P) shr12Code.length
  sLm : Sep G 0x330 (lmShr P + 0x1EE) leadMut12Code.length
  sTr : Sep G 0x330 (lmShr P + 0x1FE) trailing12Code.length
  sT : Sep G 0x330 (P + 0xFFFF9DCE) toUintResize2Code.length
  sX : Sep G 0x330 (BitVec.ofNat 32 u2MaxAddress) 8
  rG : Sep res 49 G 0x330
  aG : Sep ap 49 G 0x330
  bG : Sep bp 49 G 0x330
  cG : Sep cp 8 G 0x330
  dG : Sep dp 8 G 0x330
  mG : Sep mp 48 G 0x330
  iG : Sep mip 8 G 0x330
  rC : Sep res 49 P lincombShiftMod12Code.length
  rB : Sep res 49 (lmLc P + 0x1918) memcpyBodyCode.length

/-- The prologue, from 0 to the call at 0x3C: the frame, the saved registers
(through `s0 = sp + 0x100`), and the arguments kept in saved registers. -/
def lmPro : List BInstr :=
  [.aluImm .add sp sp 0xFFFFFEB0, .sw sp ra 0x14C, .sw sp (8 : Fin 32) 0x148, .aluImm .add (8 : Fin 32) sp 0x100,
   .sw (8 : Fin 32) (9 : Fin 32) 0x44, .sw (8 : Fin 32) (18 : Fin 32) 0x40, .sw (8 : Fin 32) (19 : Fin 32) 0x3C,
   .sw (8 : Fin 32) (20 : Fin 32) 0x38, .sw (8 : Fin 32) (21 : Fin 32) 0x34, .sw (8 : Fin 32) (22 : Fin 32) 0x30,
   .sw (8 : Fin 32) (23 : Fin 32) 0x2C, .sw (8 : Fin 32) (24 : Fin 32) 0x28, .sw (8 : Fin 32) (25 : Fin 32) 0x24,
   .alu .add (21 : Fin 32) x0 (17 : Fin 32), .alu .add (23 : Fin 32) x0 a6, .alu .add (19 : Fin 32) x0 a5,
   .alu .add (18 : Fin 32) x0 a0, .aluImm .add a0 sp 0x38, .aluImm .add (20 : Fin 32) sp 0x38]

/-- The epilogue, from 0x2D0 to the frame's release at 0x2FA: the saved
registers, through `a0 = sp + 0x100`. -/
def lmEpi : List BInstr :=
  [.aluImm .add a0 sp 0x100, .lw ra a0 0x4C, .lw (8 : Fin 32) a0 0x48, .lw (9 : Fin 32) a0 0x44,
   .lw (18 : Fin 32) a0 0x40, .lw (19 : Fin 32) a0 0x3C, .lw (20 : Fin 32) a0 0x38, .lw (21 : Fin 32) a0 0x34,
   .lw (22 : Fin 32) a0 0x30, .lw (23 : Fin 32) a0 0x2C, .lw (24 : Fin 32) a0 0x28, .lw (25 : Fin 32) a0 0x24]

section
set_option maxRecDepth 20000
theorem lmPro_end : blockEnd lincombShiftMod12Code 0 lmPro = some 0x3C := by decide
theorem lmEpi_end : blockEnd lincombShiftMod12Code 0x2D0 lmEpi = some 0x2FA := by decide
end

/-- The registers the function saves, at offsets from its `sp`. -/
abbrev lmPs : List (Fin 32 × Word) :=
  [(ra, 0x14C), ((8 : Fin 32), 0x148), ((9 : Fin 32), 0x144), ((18 : Fin 32), 0x140), ((19 : Fin 32), 0x13C),
   ((20 : Fin 32), 0x138), ((21 : Fin 32), 0x134), ((22 : Fin 32), 0x130), ((23 : Fin 32), 0x12C),
   ((24 : Fin 32), 0x128), ((25 : Fin 32), 0x124)]

theorem lmPs_range : ∀ p ∈ lmPs, p.2.toNat % 4 = 0 ∧ 0x124 ≤ p.2.toNat ∧ p.2.toNat + 4 ≤ 0x150 := by decide

set_option maxRecDepth 20000 in
theorem lmPro_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lmPro (M, f)).1 = saveMem M (f sp + 0xFFFFFEB0) f lmPs ∧
    (runBlock lmPro (M, f)).2 sp = f sp + 0xFFFFFEB0 ∧
    (runBlock lmPro (M, f)).2 (8 : Fin 32) = f sp + 0xFFFFFEB0 + 0x100 ∧
    (runBlock lmPro (M, f)).2 (21 : Fin 32) = f (17 : Fin 32) ∧
    (runBlock lmPro (M, f)).2 (23 : Fin 32) = f a6 ∧
    (runBlock lmPro (M, f)).2 (19 : Fin 32) = f a5 ∧
    (runBlock lmPro (M, f)).2 (18 : Fin 32) = f a0 ∧
    (runBlock lmPro (M, f)).2 a0 = f sp + 0xFFFFFEB0 + 0x38 ∧
    (runBlock lmPro (M, f)).2 (20 : Fin 32) = f sp + 0xFFFFFEB0 + 0x38 ∧
    ∀ q : Fin 32, q.val ∉ [2, 8, 10, 18, 19, 20, 21, 23] → (runBlock lmPro (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, lmPro]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · simp +decide only [upd, ↓reduceIte, saveMem, ev_add, BitVec.add_assoc]; rfl
  any_goals (simp +decide only [upd, ↓reduceIte, ev_add]; first | rfl | exact BitVec.zero_add _ | skip)
  have nq : ∀ w : Fin 32, w.val ∈ [2, 8, 10, 18, 19, 20, 21, 23] → q ≠ w := fun w hw e => hq (e ▸ hw)
  by_cases h0 : q.val = 0
  · have : q = 0 := Fin.ext h0
    subst this; simp [hz]
  · simp only [h0, nq sp (by decide), nq 8 (by decide), nq a0 (by decide), nq 18 (by decide),
      nq 19 (by decide), nq 20 (by decide), nq 21 (by decide), nq 23 (by decide), ite_false]

set_option maxRecDepth 20000 in
theorem lmEpi_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (∀ r o, (r, o) ∈ lmPs → (runBlock lmEpi (M, f)).2 r = memLoad32 M (f sp + o)) ∧
    (runBlock lmEpi (M, f)).1 = M ∧
    ∀ q : Fin 32, q.val ∉ [1, 8, 9, 10, 18, 19, 20, 21, 22, 23, 24, 25] → (runBlock lmEpi (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, lmEpi]
  refine ⟨fun r o h => ?_, trivial, fun q hq => ?_⟩
  · simp only [lmPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp +decide only [upd, ↓reduceIte, ev_add, BitVec.add_assoc]; rfl
  · have nq : ∀ w : Fin 32, w.val ∈ [1, 8, 9, 10, 18, 19, 20, 21, 22, 23, 24, 25] → q ≠ w :=
      fun w hw e => hq (e ▸ hw)
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [hz]
    · simp only [upd, h0, nq ra (by decide), nq 8 (by decide), nq 9 (by decide), nq a0 (by decide),
        nq 18 (by decide), nq 19 (by decide), nq 20 (by decide), nq 21 (by decide), nq 22 (by decide),
        nq 23 (by decide), nq 24 (by decide), nq 25 (by decide), ite_false]

/-! ## The 64-bit product `x · mi`, from 0x6C to 0xC6 -/

/-- From 0x6C to the branch at 0x7E: zero the product, and the loop
counters. -/
def lmM0 : List BInstr :=
  [.aluImm .add (6 : Fin 32) x0 0, .sw sp x0 0x118, .sw sp x0 0x11C, .aluImm .add (17 : Fin 32) sp 0x118,
   .aluImm .add a6 x0 2, .aluImm .add (5 : Fin 32) x0 2]

/-- From 0x82 to the branch at 0x92: start row `t1`. -/
def lmM1 : List BInstr :=
  [.aluImm .add (9 : Fin 32) x0 0, .aluImm .sll a1 (6 : Fin 32) 2, .alu .add a1 a1 (20 : Fin 32), .lw a4 a1 0,
   .alu .add a5 x0 (5 : Fin 32), .alu .add a1 x0 (17 : Fin 32), .alu .add (8 : Fin 32) x0 (21 : Fin 32)]

/-- From 0x96 to the branch at 0xBA: one multiply-accumulate step. -/
def lmM2 : List BInstr :=
  [.lw a2 (8 : Fin 32) 0, .alu .mul a3 a2 a4, .lw a0 a1 0, .alu .mulhu a2 a2 a4, .aluImm .add (8 : Fin 32) (8 : Fin 32) 4,
   .alu .add (9 : Fin 32) (9 : Fin 32) a0, .alu .sltu a0 (9 : Fin 32) a0, .alu .add a3 a3 (9 : Fin 32),
   .alu .add a0 a0 a2, .alu .sltu (9 : Fin 32) a3 (9 : Fin 32), .sw a1 a3 0, .alu .add (9 : Fin 32) (9 : Fin 32) a0,
   .aluImm .add a1 a1 4, .aluImm .add a5 a5 0xFFFFFFFF]

/-- From 0xBC to the branch at 0xC2: the next row. -/
def lmM3 : List BInstr :=
  [.aluImm .add (6 : Fin 32) (6 : Fin 32) 1, .aluImm .add (17 : Fin 32) (17 : Fin 32) 4,
   .aluImm .add (5 : Fin 32) (5 : Fin 32) 0xFFFFFFFF]

section
set_option maxRecDepth 20000
theorem lmM0_end : blockEnd lincombShiftMod12Code 0x6C lmM0 = some 0x7E := by decide
theorem lmM1_end : blockEnd lincombShiftMod12Code 0x82 lmM1 = some 0x92 := by decide
theorem lmM2_end : blockEnd lincombShiftMod12Code 0x96 lmM2 = some 0xBA := by decide
theorem lmM3_end : blockEnd lincombShiftMod12Code 0xBC lmM3 = some 0xC2 := by decide
end

/-- One multiply-accumulate step: with `p` the word at `s0`, `y` the word at
`a1`, and `c` the carry in `s1`, the word at `a1` gets the low word of
`p · a4 + y + c` and `s1` the high word. -/
def macLo (p x y c : Word) : Word := aluEval .mul p x + (c + y)

def macHi (p x y c : Word) : Word :=
  aluEval .sltu (aluEval .mul p x + (c + y)) (c + y) + (aluEval .sltu (c + y) y + aluEval .mulhu p x)

set_option maxRecDepth 20000 in
theorem lmM2_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lmM2 (M, f)).1 = memStore32 M (f a1 + 0)
      (macLo (memLoad32 M (f 8 + 0)) (f a4) (memLoad32 M (f a1 + 0)) (f 9)) ∧
    (runBlock lmM2 (M, f)).2 (9 : Fin 32) =
      macHi (memLoad32 M (f 8 + 0)) (f a4) (memLoad32 M (f a1 + 0)) (f 9) ∧
    (runBlock lmM2 (M, f)).2 (8 : Fin 32) = f 8 + 4 ∧ (runBlock lmM2 (M, f)).2 a1 = f a1 + 4 ∧
    (runBlock lmM2 (M, f)).2 a5 = f a5 + 0xFFFFFFFF ∧
    ∀ q : Fin 32, q.val ∉ [8, 9, 10, 11, 12, 13, 15] → (runBlock lmM2 (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, lmM2]
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

theorem sltu_tn (a b : Word) : (aluEval .sltu a b).toNat = if a.toNat < b.toNat then 1 else 0 := by
  simp only [aluEval, BitVec.ult]
  by_cases h : a.toNat < b.toNat
  · rw [ite_eq_left (decide_eq_true h), ite_eq_left h]; rfl
  · rw [ite_eq_right (by simpa using h), ite_eq_right h]; rfl

/-- One multiply-accumulate step is exact: the low and high words of
`p · x + y + c`. -/
theorem mac_val (p x y c : Word) :
    (macLo p x y c).toNat + 2 ^ 32 * (macHi p x y c).toNat = p.toNat * x.toNat + y.toNat + c.toNat := by
  have hp := p.isLt; have hx := x.isLt; have hy := y.isLt; have hc := c.isLt
  have hP : p.toNat * x.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have hm : (aluEval .mul p x).toNat = p.toNat * x.toNat % 2 ^ 32 := by
    simp only [aluEval, BitVec.toNat_mul]
  have hh : (aluEval .mulhu p x).toNat = p.toNat * x.toNat / 2 ^ 32 := by
    simp only [aluEval, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  generalize p.toNat * x.toNat = P at hP hm hh
  have hs1 := sltu_tn (c + y) y
  have hs2 := sltu_tn (aluEval .mul p x + (c + y)) (c + y)
  simp only [macLo, macHi, BitVec.toNat_add] at hs1 hs2 ⊢
  rw [hs1, hs2, hh]
  split <;> split <;> omega

set_option maxRecDepth 20000 in
theorem lmM0_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lmM0 (M, f)).1 = memStore32 (memStore32 M (f sp + 0x118) 0) (f sp + 0x11C) 0 ∧
    (runBlock lmM0 (M, f)).2 (6 : Fin 32) = 0 ∧ (runBlock lmM0 (M, f)).2 (17 : Fin 32) = f sp + 0x118 ∧
    (runBlock lmM0 (M, f)).2 a6 = 2 ∧ (runBlock lmM0 (M, f)).2 (5 : Fin 32) = 2 ∧
    ∀ q : Fin 32, q.val ∉ [5, 6, 16, 17] → (runBlock lmM0 (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, lmM0]
  refine ⟨?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · simp +decide only [upd, ↓reduceIte, hz]
  any_goals (simp +decide only [upd, ↓reduceIte, hz, ev_add]; first | rfl | skip)
  have nq : ∀ w : Fin 32, w.val ∈ [5, 6, 16, 17] → q ≠ w := fun w hw e => hq (e ▸ hw)
  by_cases h0 : q.val = 0
  · have : q = 0 := Fin.ext h0
    subst this; simp [hz]
  · simp only [upd, h0, nq 5 (by decide), nq 6 (by decide), nq a6 (by decide), nq 17 (by decide), ite_false]

theorem lmM0_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h0 : (f sp + 0x118).toNat % 4 = 0) (h4 : (f sp + 0x11C).toNat % 4 = 0)
    (s0 : Sep (f sp + 0x118) 4 base len) (s4 : Sep (f sp + 0x11C) 4 base len) :
    BlockOk base len lmM0 (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, lmM0, upd, ↓reduceIte, and_true, true_and]
  exact ⟨⟨h0, s0⟩, h4, s4⟩

set_option maxRecDepth 20000 in
theorem lmM1_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lmM1 (M, f)).1 = M ∧
    (runBlock lmM1 (M, f)).2 (9 : Fin 32) = 0 ∧
    (runBlock lmM1 (M, f)).2 a4 = memLoad32 M (aluEval .sll (f 6) 2 + f 20 + 0) ∧
    (runBlock lmM1 (M, f)).2 a5 = f 5 ∧ (runBlock lmM1 (M, f)).2 a1 = f 17 ∧
    (runBlock lmM1 (M, f)).2 (8 : Fin 32) = f 21 ∧
    ∀ q : Fin 32, q.val ∉ [8, 9, 11, 14, 15] → (runBlock lmM1 (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, lmM1]
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  any_goals (simp +decide only [upd, ↓reduceIte, hz, ev_add]; first | rfl | exact BitVec.zero_add _ | skip)
  have nq : ∀ w : Fin 32, w.val ∈ [8, 9, 11, 14, 15] → q ≠ w := fun w hw e => hq (e ▸ hw)
  by_cases h0 : q.val = 0
  · have : q = 0 := Fin.ext h0
    subst this; simp [hz]
  · simp only [upd, h0, nq 8 (by decide), nq 9 (by decide), nq a1 (by decide), nq a4 (by decide),
      nq a5 (by decide), ite_false]

theorem lmM1_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h : (aluEval .sll (f 6) 2 + f 20 + 0).toNat % 4 = 0) : BlockOk base len lmM1 (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, lmM1, upd, ↓reduceIte, and_true, true_and]
  exact h

theorem lmM2_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h8 : (f 8 + 0).toNat % 4 = 0) (h1 : (f a1 + 0).toNat % 4 = 0) (s1 : Sep (f a1 + 0) 4 base len) :
    BlockOk base len lmM2 (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, lmM2, upd, ↓reduceIte, and_true, true_and]
  exact ⟨h8, h1, h1, s1⟩

set_option maxRecDepth 20000 in
theorem lmM3_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lmM3 (M, f)).1 = M ∧
    (runBlock lmM3 (M, f)).2 (6 : Fin 32) = f 6 + 1 ∧ (runBlock lmM3 (M, f)).2 (17 : Fin 32) = f 17 + 4 ∧
    (runBlock lmM3 (M, f)).2 (5 : Fin 32) = f 5 + 0xFFFFFFFF ∧
    ∀ q : Fin 32, q.val ∉ [5, 6, 17] → (runBlock lmM3 (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, lmM3]
  refine ⟨trivial, ?_, ?_, ?_, fun q hq => ?_⟩
  any_goals (simp +decide only [upd, ↓reduceIte, ev_add]; first | rfl | skip)
  have nq : ∀ w : Fin 32, w.val ∈ [5, 6, 17] → q ≠ w := fun w hw e => hq (e ▸ hw)
  by_cases h0 : q.val = 0
  · have : q = 0 := Fin.ext h0
    subst this; simp [hz]
  · simp only [upd, h0, nq 5 (by decide), nq 6 (by decide), nq 17 (by decide), ite_false]

/-- The two words a 64-bit product leaves: `x · mi` modulo 2^64, schoolbook,
with the high-by-high product dropped. -/
theorem mul64_val (x0 x1 m0 m1 : Word) :
    (macLo m0 x0 0 0).toNat + 2 ^ 32 * (macLo m0 x1 (macLo m1 x0 0 (macHi m0 x0 0 0)) 0).toNat =
      (x0.toNat + 2 ^ 32 * x1.toNat) * (m0.toNat + 2 ^ 32 * m1.toNat) % 2 ^ 64 := by
  have v1 := mac_val m0 x0 0 0
  have v2 := mac_val m1 x0 0 (macHi m0 x0 0 0)
  have v3 := mac_val m0 x1 (macLo m1 x0 0 (macHi m0 x0 0 0)) 0
  have l3 := (macLo m0 x1 (macLo m1 x0 0 (macHi m0 x0 0 0)) 0).isLt
  have h2 := (macHi m1 x0 0 (macHi m0 x0 0 0)).isLt
  have h3 := (macHi m0 x1 (macLo m1 x0 0 (macHi m0 x0 0 0)) 0).isLt
  have e : (x0.toNat + 2 ^ 32 * x1.toNat) * (m0.toNat + 2 ^ 32 * m1.toNat) =
      m0.toNat * x0.toNat + 2 ^ 32 * (m1.toNat * x0.toNat) + 2 ^ 32 * (m0.toNat * x1.toNat) +
        2 ^ 32 * 2 ^ 32 * (m1.toNat * x1.toNat) := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; ac_rfl
  rw [e]
  have z : (0 : Word).toNat = 0 := rfl
  rw [z] at v1 v2 v3
  generalize m0.toNat * x0.toNat = P00 at v1 ⊢
  generalize m1.toNat * x0.toNat = P10 at v2 ⊢
  generalize m0.toNat * x1.toNat = P01 at v3 ⊢
  generalize m1.toNat * x1.toNat = P11
  omega

theorem nmem_of {q : Nat} {L1 L2 : List Nat} (hs : ∀ x ∈ L2, x ∈ L1) (h : q ∉ L1) : q ∉ L2 :=
  fun h2 => h (hs q h2)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **The 64-bit product**, from 0x6C to 0xC6: the two words at `F + 0x118`
get `x · mi` modulo 2^64, for `x` the two words at `F + 0x38` and `mi` the
two at `mip`. -/
theorem lm_mul {M : Word → BitVec 8} {P F mip : Word} {n : Machine} (s : St M P n 0x6C (reg n))
    (hc : CodeIn M P lincombShiftMod12Code) (rsp : reg n sp = F) (r20 : reg n 20 = F + 0x38)
    (r21 : reg n 21 = mip) (hF : F.toNat % 4 = 0) (hmip : mip.toNat % 4 = 0)
    (sC : Sep (F + 0x118) 8 P lincombShiftMod12Code.length) (sX : Sep (F + 0x118) 8 (F + 0x38) 8)
    (sI : Sep (F + 0x118) 8 mip 8) :
    ∃ n' M', Steps n n' ∧ St M' P n' 0xC6 (reg n') ∧ CodeIn M' P lincombShiftMod12Code ∧
      (∀ x, Sep (F + 0x118) 8 x 1 → M' x = M x) ∧
      (memLoad32 M' (F + 0x118)).toNat + 2 ^ 32 * (memLoad32 M' (F + 0x11C)).toNat =
        ((memLoad32 M (F + 0x38)).toNat + 2 ^ 32 * (memLoad32 M (F + 0x3C)).toNat) *
          ((memLoad32 M mip).toNat + 2 ^ 32 * (memLoad32 M (mip + 4)).toNat) % 2 ^ 64 ∧
      ∀ q : Fin 32, q.val ∉ [5, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17] → reg n' q = reg n q := by
  have hz := s.zero
  have s0 : Sep (F + 0x118) 4 P lincombShiftMod12Code.length := by
    have := sC.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
  have s4 : Sep (F + 0x11C) 4 P lincombShiftMod12Code.length := by
    have := sC.sub (c := 4) (l := 4) (by decide); rw [BitVec.add_assoc] at this; exact this
  have a0' : (F + 0x118).toNat % 4 = 0 := aligned_add hF (by decide)
  have a4' : (F + 0x11C).toNat % 4 = 0 := aligned_add hF (by decide)
  -- zero the product
  obtain ⟨n1, c1, u1⟩ := St.block lmM0 s hc lmM0_end
    (lmM0_ok (by rw [rsp]; exact a0') (by rw [rsp]; exact a4') (by rw [rsp]; exact s0) (by rw [rsp]; exact s4))
  obtain ⟨m0e, m0t1, m0a7, m0a6, m0t0, m0k⟩ := lmM0_run (M := M) (f := reg n) hz
  rw [m0e, rsp] at u1
  obtain ⟨Mz, hMz⟩ : ∃ Mz, memStore32 (memStore32 M (F + 0x118) 0) (F + 0x11C) 0 = Mz := ⟨_, rfl⟩
  rw [hMz] at u1
  have hcz : CodeIn Mz P lincombShiftMod12Code := by rw [← hMz]; exact (hc.store32 s0).store32 s4
  have frz : ∀ x, Sep (F + 0x118) 8 x 1 → Mz x = M x := fun x hx => by
    have h4 : Sep (F + 0x11C) 4 x 1 := by
      have := hx.sub (c := 4) (l := 4) (by decide); rw [BitVec.add_assoc] at this; exact this
    have h0 : Sep (F + 0x118) 4 x 1 := by
      have := hx.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    rw [← hMz, memStore32_get_sep h4, memStore32_get_sep h0]
  have ldz : ∀ {a : Word}, Sep (F + 0x118) 8 a 4 → memLoad32 Mz a = memLoad32 M a := fun h =>
    memLoad32_congr fun j hj => frz _ (h.subR (c := j) (l := 1) (by omega))
  have g1 : ∀ q, reg n1 q = (runBlock lmM0 (M, reg n)).2 q := u1.regs
  have k1 : ∀ q : Fin 32, q.val ∉ [5, 6, 16, 17] → reg n1 q = reg n q := fun q hq => by rw [g1, m0k q hq]
  obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hcz 0x82 lm12_at_7e (by decide) (by rw [g1, m0a6, u1.self.zero]; decide)
  have k2 : ∀ q, reg n2 q = reg n1 q := u2.regs
  -- row 0
  have sll0 : aluEval .sll (0 : Word) 2 = 0 := by decide
  have sll1 : aluEval .sll (1 : Word) 2 = 4 := by decide
  have e38 : (0 : Word) + (F + 0x38) + 0 = F + 0x38 := by rw [add_lit_zero]; exact BitVec.zero_add _
  have e3c : (4 : Word) + (F + 0x38) + 0 = F + 0x3C := by
    rw [add_lit_zero, BitVec.add_comm, BitVec.add_assoc]; rfl
  have r2t1 : reg n2 6 = 0 := by rw [k2, g1, m0t1]
  have r2s4 : reg n2 20 = F + 0x38 := by rw [k2, k1 20 (by decide), r20]
  have r2s5 : reg n2 21 = mip := by rw [k2, k1 21 (by decide), r21]
  have r2a7 : reg n2 17 = F + 0x118 := by rw [k2, g1, m0a7, rsp]
  have r2t0 : reg n2 5 = 2 := by rw [k2, g1, m0t0]
  have r2a6 : reg n2 16 = 2 := by rw [k2, g1, m0a6]
  obtain ⟨n3, c3, u3⟩ := St.block lmM1 u2.self hcz lmM1_end
    (lmM1_ok (by rw [r2t1, r2s4, sll0, e38]; exact aligned_add hF (by decide)))
  obtain ⟨m1e, m1s1, m1a4, m1a5, m1a1, m1s0, m1k⟩ := lmM1_run (M := Mz) (f := reg n2) u2.self.zero
  rw [m1e] at u3
  have g3 : ∀ q, reg n3 q = (runBlock lmM1 (Mz, reg n2)).2 q := u3.regs
  have x0e : reg n3 a4 = memLoad32 M (F + 0x38) := by
    rw [g3, m1a4, r2t1, r2s4, sll0, e38]
    exact ldz (by have := sX.subR (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this)
  obtain ⟨n4, d4, u4⟩ := u3.self.notTaken hcz 0x96 lm12_at_92 (by decide)
    (by rw [g3, m1k 5 (by decide), r2t0, u3.self.zero]; decide)
  have k4 : ∀ q, reg n4 q = reg n3 q := u4.regs
  have r4s0 : reg n4 8 = mip := by rw [k4, g3, m1s0, r2s5]
  have r4a1 : reg n4 a1 = F + 0x118 := by rw [k4, g3, m1a1, r2a7]
  have r4s1 : reg n4 9 = 0 := by rw [k4, g3, m1s1]
  have hm0 : memLoad32 Mz mip = memLoad32 M mip :=
    ldz (by have := sI.subR (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this)
  have hm1 : memLoad32 Mz (mip + 4) = memLoad32 M (mip + 4) := ldz (sI.subR (c := 4) (l := 4) (by decide))
  have z0 : memLoad32 Mz (F + 0x118) = 0 := by
    rw [← hMz, memLoad32_store32_sep (by
      have := sep_offsets F (c := 0x11C) (n := 4) (d := 0x118) (k := 4) (.inr (by decide)) (by decide) (by decide)
      exact this), memLoad32_store32_same]
  have z4 : memLoad32 Mz (F + 0x11C) = 0 := by rw [← hMz, memLoad32_store32_same]
  -- the first multiply-accumulate step
  obtain ⟨n5, c5, u5⟩ := St.block lmM2 u4.self hcz lmM2_end
    (lmM2_ok (by rw [r4s0, add_lit_zero]; exact hmip) (by rw [r4a1, add_lit_zero]; exact a0')
      (by rw [r4a1, add_lit_zero]; exact s0))
  obtain ⟨m2e, m2s1, m2s0, m2a1, m2a5, m2k⟩ := lmM2_run (M := Mz) (f := reg n4) u4.self.zero
  have r4a4 : reg n4 a4 = memLoad32 M (F + 0x38) := by rw [k4, x0e]
  rw [m2e, r4s0, r4a1, add_lit_zero, add_lit_zero, hm0, z0, r4a4, r4s1] at u5
  obtain ⟨x0, hx0⟩ : ∃ x0, memLoad32 M (F + 0x38) = x0 := ⟨_, rfl⟩
  obtain ⟨m0, hm0'⟩ : ∃ m0, memLoad32 M mip = m0 := ⟨_, rfl⟩
  obtain ⟨m1, hm1'⟩ : ∃ m1, memLoad32 M (mip + 4) = m1 := ⟨_, rfl⟩
  rw [hx0, hm0'] at u5
  have g5 : ∀ q, reg n5 q = (runBlock lmM2 (Mz, reg n4)).2 q := u5.regs
  have e11c : F + 0x118 + 4 = F + 0x11C := by rw [BitVec.add_assoc]; rfl
  have hcA : CodeIn (memStore32 Mz (F + 0x118) (macLo m0 x0 0 0)) P lincombShiftMod12Code := hcz.store32 s0
  obtain ⟨n6, d6, u6⟩ := u5.self.taken hcA 0x96 lm12_at_ba (by decide)
    (by rw [g5, m2a5, k4, g3, m1a5, r2t0, u5.self.zero]; decide)
  have k6 : ∀ q, reg n6 q = reg n5 q := u6.regs
  have r6s0 : reg n6 8 = mip + 4 := by rw [k6, g5, m2s0, r4s0]
  have r6a1 : reg n6 a1 = F + 0x11C := by rw [k6, g5, m2a1, r4a1, e11c]
  have r6s1 : reg n6 9 = macHi m0 x0 0 0 := by
    rw [k6, g5, m2s1, r4s0, r4a1, add_lit_zero, add_lit_zero, hm0, z0, r4a4, r4s1, hx0, hm0']
  have r6a4 : reg n6 a4 = x0 := by rw [k6, g5, m2k a4 (by decide), r4a4, hx0]
  have r6a5 : reg n6 a5 = 1 := by rw [k6, g5, m2a5, k4, g3, m1a5, r2t0]; rfl
  -- the second step of row 0
  obtain ⟨n7, c7, u7⟩ := St.block lmM2 u6.self hcA lmM2_end
    (lmM2_ok (by rw [r6s0, add_lit_zero]; exact aligned_add hmip (by decide)) (by rw [r6a1, add_lit_zero]; exact a4')
      (by rw [r6a1, add_lit_zero]; exact s4))
  obtain ⟨m2e', m2s1', m2s0', m2a1', m2a5', m2k'⟩ := lmM2_run (M := memStore32 Mz (F + 0x118) (macLo m0 x0 0 0))
    (f := reg n6) u6.self.zero
  have sIm : Sep (F + 0x118) 4 (mip + 4) 4 := by
    have := (sI.sub (c := 0) (l := 4) (by decide)).subR (c := 4) (l := 4) (by decide)
    rwa [add_ofNat_zero] at this
  have s11c : Sep (F + 0x118) 4 (F + 0x11C) 4 := by
    have := sep_offsets F (c := 0x118) (n := 4) (d := 0x11C) (k := 4) (.inl (by decide)) (by decide) (by decide)
    exact this
  have l1 : memLoad32 (memStore32 Mz (F + 0x118) (macLo m0 x0 0 0)) (mip + 4) = m1 := by
    rw [memLoad32_store32_sep sIm, hm1, hm1']
  have l2 : memLoad32 (memStore32 Mz (F + 0x118) (macLo m0 x0 0 0)) (F + 0x11C) = 0 := by
    rw [memLoad32_store32_sep s11c, z4]
  rw [m2e', r6s0, r6a1, add_lit_zero, add_lit_zero, l1, l2, r6a4, r6s1] at u7
  obtain ⟨MB, hMB⟩ : ∃ MB, memStore32 (memStore32 Mz (F + 0x118) (macLo m0 x0 0 0)) (F + 0x11C)
      (macLo m1 x0 0 (macHi m0 x0 0 0)) = MB := ⟨_, rfl⟩
  rw [hMB] at u7
  have hcB : CodeIn MB P lincombShiftMod12Code := by rw [← hMB]; exact hcA.store32 s4
  have g7 : ∀ q, reg n7 q = (runBlock lmM2 (memStore32 Mz (F + 0x118) (macLo m0 x0 0 0), reg n6)).2 q := u7.regs
  obtain ⟨n8, d8, u8⟩ := u7.self.notTaken hcB 0xBC lm12_at_ba (by decide)
    (by rw [g7, m2a5', r6a5, u7.self.zero]; decide)
  -- the next row
  obtain ⟨n9, c9, u9⟩ := St.block lmM3 u8.self hcB lmM3_end (by simp [BlockOk, BInstr.ok, lmM3])
  obtain ⟨m3e, m3t1, m3a7, m3t0, m3k⟩ := lmM3_run (M := MB) (f := reg n8) u8.self.zero
  rw [m3e] at u9
  have g9 : ∀ q, reg n9 q = (runBlock lmM3 (MB, reg n8)).2 q := u9.regs
  have k8 : ∀ q, reg n8 q = reg n7 q := u8.regs
  -- registers the inner loop leaves alone
  have kin : ∀ q : Fin 32, q.val ∉ [8, 9, 10, 11, 12, 13, 15] → reg n8 q = reg n4 q := fun q hq => by
    rw [k8, g7, m2k' q hq, k6, g5, m2k q hq]
  have r9t1 : reg n9 6 = 1 := by
    rw [g9, m3t1, kin 6 (by decide), k4, g3, m1k 6 (by decide), r2t1]; rfl
  have r9a6 : reg n9 16 = 2 := by
    rw [g9, m3k 16 (by decide), kin 16 (by decide), k4, g3, m1k 16 (by decide), r2a6]
  obtain ⟨n10, d10, u10⟩ := u9.self.taken hcB 0x82 lm12_at_c2 (by decide)
    (by rw [r9t1, r9a6]; decide)
  have k10 : ∀ q, reg n10 q = reg n9 q := u10.regs
  have r10t1 : reg n10 6 = 1 := by rw [k10, r9t1]
  have r10s4 : reg n10 20 = F + 0x38 := by
    rw [k10, g9, m3k 20 (by decide), kin 20 (by decide), k4, g3, m1k 20 (by decide), r2s4]
  have r10s5 : reg n10 21 = mip := by
    rw [k10, g9, m3k 21 (by decide), kin 21 (by decide), k4, g3, m1k 21 (by decide), r2s5]
  have r10a7 : reg n10 17 = F + 0x11C := by
    rw [k10, g9, m3a7, kin 17 (by decide), k4, g3, m1k 17 (by decide), r2a7, e11c]
  have r10t0 : reg n10 5 = 1 := by
    rw [k10, g9, m3t0, kin 5 (by decide), k4, g3, m1k 5 (by decide), r2t0]; rfl
  -- row 1
  obtain ⟨n11, c11, u11⟩ := St.block lmM1 u10.self hcB lmM1_end
    (lmM1_ok (by rw [r10t1, r10s4, sll1, e3c]; exact aligned_add hF (by decide)))
  obtain ⟨m1e', m1s1', m1a4', m1a5', m1a1', m1s0', m1k'⟩ := lmM1_run (M := MB) (f := reg n10) u10.self.zero
  rw [m1e'] at u11
  have g11 : ∀ q, reg n11 q = (runBlock lmM1 (MB, reg n10)).2 q := u11.regs
  obtain ⟨x1, hx1⟩ : ∃ x1, memLoad32 M (F + 0x3C) = x1 := ⟨_, rfl⟩
  have sX4 : Sep (F + 0x118) 8 (F + 0x3C) 4 := by
    have := sX.subR (c := 4) (l := 4) (by decide); rw [BitVec.add_assoc] at this; exact this
  have mbX : ∀ {a : Word}, Sep (F + 0x118) 8 a 4 → memLoad32 MB a = memLoad32 M a := fun {a} h => by
    have h4 : Sep (F + 0x11C) 4 a 4 := by
      have := h.sub (c := 4) (l := 4) (by decide); rw [BitVec.add_assoc] at this; exact this
    have h0 : Sep (F + 0x118) 4 a 4 := by
      have := h.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    rw [← hMB, memLoad32_store32_sep h4, memLoad32_store32_sep h0]
    exact ldz h
  have r11a4 : reg n11 a4 = x1 := by rw [g11, m1a4', r10t1, r10s4, sll1, e3c, mbX sX4, hx1]
  obtain ⟨n12, d12, u12⟩ := u11.self.notTaken hcB 0x96 lm12_at_92 (by decide)
    (by rw [g11, m1k' 5 (by decide), r10t0, u11.self.zero]; decide)
  have k12 : ∀ q, reg n12 q = reg n11 q := u12.regs
  have r12s0 : reg n12 8 = mip := by rw [k12, g11, m1s0', r10s5]
  have r12a1 : reg n12 a1 = F + 0x11C := by rw [k12, g11, m1a1', r10a7]
  have r12s1 : reg n12 9 = 0 := by rw [k12, g11, m1s1']
  have r12a4 : reg n12 a4 = x1 := by rw [k12, r11a4]
  have r12a5 : reg n12 a5 = 1 := by rw [k12, g11, m1a5', r10t0]
  obtain ⟨n13, c13, u13⟩ := St.block lmM2 u12.self hcB lmM2_end
    (lmM2_ok (by rw [r12s0, add_lit_zero]; exact hmip) (by rw [r12a1, add_lit_zero]; exact a4')
      (by rw [r12a1, add_lit_zero]; exact s4))
  obtain ⟨m2e'', m2s1'', m2s0'', m2a1'', m2a5'', m2k''⟩ := lmM2_run (M := MB) (f := reg n12) u12.self.zero
  have l3 : memLoad32 MB mip = m0 := by
    rw [mbX (by have := sI.subR (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this), hm0']
  have l4 : memLoad32 MB (F + 0x11C) = macLo m1 x0 0 (macHi m0 x0 0 0) := by
    rw [← hMB, memLoad32_store32_same]
  rw [m2e'', r12s0, r12a1, add_lit_zero, add_lit_zero, l3, l4, r12a4, r12s1] at u13
  have hcC := hcB.store32 (v := macLo m0 x1 (macLo m1 x0 0 (macHi m0 x0 0 0)) 0) s4
  have g13 : ∀ q, reg n13 q = (runBlock lmM2 (MB, reg n12)).2 q := u13.regs
  obtain ⟨n14, d14, u14⟩ := u13.self.notTaken hcC 0xBC lm12_at_ba (by decide)
    (by rw [g13, m2a5'', r12a5, u13.self.zero]; decide)
  obtain ⟨n15, c15, u15⟩ := St.block lmM3 u14.self hcC lmM3_end (by simp [BlockOk, BInstr.ok, lmM3])
  obtain ⟨m3e', m3t1', m3a7', m3t0', m3k'⟩ := lmM3_run (M := memStore32 MB (F + 0x11C)
    (macLo m0 x1 (macLo m1 x0 0 (macHi m0 x0 0 0)) 0)) (f := reg n14) u14.self.zero
  rw [m3e'] at u15
  have g15 : ∀ q, reg n15 q = _ := u15.regs
  have k14 : ∀ q, reg n14 q = reg n13 q := u14.regs
  have kin2 : ∀ q : Fin 32, q.val ∉ [8, 9, 10, 11, 12, 13, 14, 15] → reg n14 q = reg n10 q := fun q hq => by
    rw [k14, g13, m2k'' q (nmem_of (by decide) hq), k12, g11, m1k' q (nmem_of (by decide) hq)]
  have r15t1 : reg n15 6 = 2 := by rw [g15, m3t1', kin2 6 (by decide), r10t1]; rfl
  have r15a6 : reg n15 16 = 2 := by rw [g15, m3k' 16 (by decide), kin2 16 (by decide), k10, r9a6]
  obtain ⟨n16, d16, u16⟩ := u15.self.notTaken hcC 0xC6 lm12_at_c2 (by decide)
    (by rw [r15t1, r15a6]; decide)
  have m1x : memLoad32 M (mip + 4) = m1 := hm1'
  refine ⟨n16, memStore32 MB (F + 0x11C) (macLo m0 x1 (macLo m1 x0 0 (macHi m0 x0 0 0)) 0),
    c1.trans (.cons d2 (c3.trans (.cons d4 (c5.trans (.cons d6 (c7.trans (.cons d8 (c9.trans (.cons d10
      (c11.trans (.cons d12 (c13.trans (.cons d14 (c15.trans (.single d16))))))))))))))),
    u16.self, hcC, fun x hx => ?_, ?_, fun q hq => ?_⟩
  · have h4 : Sep (F + 0x11C) 4 x 1 := by
      have := hx.sub (c := 4) (l := 4) (by decide); rw [BitVec.add_assoc] at this; exact this
    have h0 : Sep (F + 0x118) 4 x 1 := by
      have := hx.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    rw [memStore32_get_sep h4, ← hMB, memStore32_get_sep h4, memStore32_get_sep h0, frz x hx]
  · rw [memLoad32_store32_same, memLoad32_store32_sep s11c.symm, ← hMB, memLoad32_store32_sep s11c.symm,
      memLoad32_store32_same, hx0, hx1, hm0', m1x]
    exact mul64_val x0 x1 m0 m1
  · rw [u16.regs, g15, m3k' q (nmem_of (by decide) hq), kin2 q (nmem_of (by decide) hq), k10, g9,
      m3k q (nmem_of (by decide) hq), kin q (nmem_of (by decide) hq), k4, g3, m1k q (nmem_of (by decide) hq),
      k2, k1 q (nmem_of (by decide) hq)]


/-! ## The mask `2^s - 1` and `mf`, from 0xC6 to 0x17E -/

/-- From 0xC6 to the panic check at 0xCE: `s8 = 64 - shift`. -/
def lmK0 : List BInstr := [.aluImm .add a0 x0 0x40, .alu .sub (24 : Fin 32) a0 (19 : Fin 32)]

/-- From 0xD2 to `leading_mut`'s call at 0xE4: the word shift, and a zeroed
mask buffer. -/
def lmK1 : List BInstr :=
  [.aluImm .srl (21 : Fin 32) (24 : Fin 32) 5, .aluImm .add a0 x0 2, .sw sp x0 0x38, .sw sp x0 0x3C,
   .alu .sub a2 a0 (21 : Fin 32), .aluImm .add a0 sp 0x38, .aluImm .add a1 x0 2]

/-- From 0xEC to `trailing`'s call at 0xFC: keep the buffer, and pass
`Uint<2>::MAX`. -/
def lmK2 : List BInstr :=
  [.alu .add (20 : Fin 32) x0 a0, .alu .add (8 : Fin 32) x0 a1, .lui a0 0x3FCC5000, .aluImm .add a0 a0 0xFFFFF838,
   .aluImm .add a1 x0 2, .alu .add a2 x0 (21 : Fin 32)]

/-- From 0x108 to the branch at 0x110: `xa`'s high limbs, and the copy's
count and destination. -/
def lmK3 : List BInstr :=
  [.aluImm .add (21 : Fin 32) sp 0xB0, .alu .add a1 x0 (8 : Fin 32), .alu .add a2 x0 (20 : Fin 32)]

/-- From 0x112 to the branch at 0x11C: copy one word. -/
def lmK4 : List BInstr :=
  [.lw a3 a0 0, .aluImm .add a0 a0 4, .sw a2 a3 0, .aluImm .add a2 a2 4, .aluImm .add a1 a1 0xFFFFFFFF]

/-- From 0x124 to the branch at 0x136: the bit shift's setup. -/
def lmK6 : List BInstr :=
  [.aluImm .add a1 x0 0, .aluImm .sll a2 (8 : Fin 32) 2, .alu .add a3 a2 (20 : Fin 32), .aluImm .add a2 x0 0x20,
   .alu .sub a2 a2 a0, .aluImm .add a3 a3 0xFFFFFFFC]

/-- From 0x138 to the jump at 0x148: shift one word right, bringing in the
bits from the word above. -/
def lmK7 : List BInstr :=
  [.lw a4 a3 0, .aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF, .alu .srl a5 a4 a0, .alu .or a5 a5 a1,
   .alu .sll a1 a4 a2, .sw a3 a5 0]

/-- From 0x14A to the branch at 0x15E: take the mask, store it at
`sp + 0x78`, and set up the AND. -/
def lmK8 : List BInstr :=
  [.lw a2 sp 0x38, .lw a3 sp 0x3C, .sw sp x0 0x38, .sw sp x0 0x3C, .aluImm .add a0 sp 0x118,
   .aluImm .add a1 sp 0x78, .sw sp a2 0x78, .sw sp a3 0x7C, .aluImm .add a2 sp 0x38, .aluImm .add a3 x0 2]

/-- From 0x160 to the branch at 0x170: AND one word. -/
def lmK9 : List BInstr :=
  [.lw a4 a0 0, .lw a5 a1 0, .aluImm .add a0 a0 4, .alu .and a4 a4 a5, .aluImm .add a1 a1 4, .sw a2 a4 0,
   .aluImm .add a2 a2 4, .aluImm .add a3 a3 0xFFFFFFFF]

/-- From 0x172 to 0x17E: copy the masked `mf` back to `sp + 0x118`. -/
def lmK10 : List BInstr := [.lw a0 sp 0x38, .lw a1 sp 0x3C, .sw sp a0 0x118, .sw sp a1 0x11C]

section
set_option maxRecDepth 20000
theorem lmK0_end : blockEnd lincombShiftMod12Code 0xC6 lmK0 = some 0xCE := by decide
theorem lmK1_end : blockEnd lincombShiftMod12Code 0xD2 lmK1 = some 0xE4 := by decide
theorem lmK2_end : blockEnd lincombShiftMod12Code 0xEC lmK2 = some 0xFC := by decide
theorem lmK3_end : blockEnd lincombShiftMod12Code 0x108 lmK3 = some 0x110 := by decide
theorem lmK4_end : blockEnd lincombShiftMod12Code 0x112 lmK4 = some 0x11C := by decide
theorem lmK6_end : blockEnd lincombShiftMod12Code 0x124 lmK6 = some 0x136 := by decide
theorem lmK7_end : blockEnd lincombShiftMod12Code 0x138 lmK7 = some 0x148 := by decide
theorem lmK8_end : blockEnd lincombShiftMod12Code 0x14A lmK8 = some 0x15E := by decide
theorem lmK9_end : blockEnd lincombShiftMod12Code 0x160 lmK9 = some 0x170 := by decide
theorem lmK10_end : blockEnd lincombShiftMod12Code 0x172 lmK10 = some 0x17E := by decide
theorem lmK6b_end : blockEnd lincombShiftMod12Code 0x134 [.aluImm .add a3 a3 0xFFFFFFFC] = some 0x136 := by decide
end


/-- A block leaves every register outside the list `L` as it was, when
every register it writes is in `L`. -/
theorem runBlock_keepL {is : List BInstr} {L : List Nat} (hd : ∀ r ∈ is.filterMap BInstr.dst, r.val ∈ L)
    {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) {q : Fin 32} (hq : q.val ∉ L) :
    (runBlock is (M, f)).2 q = f q :=
  runBlock_reg is M f q hz fun h => hq (hd q h)

set_option maxRecDepth 20000 in
theorem lmK0_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lmK0 (M, f)).1 = M ∧ (runBlock lmK0 (M, f)).2 a0 = 0x40 ∧
    (runBlock lmK0 (M, f)).2 (24 : Fin 32) = 0x40 - f 19 ∧
    ∀ q : Fin 32, q.val ∉ [10, 24] → (runBlock lmK0 (M, f)).2 q = f q := by
  refine ⟨?_, ?_, ?_, fun q hq => ?_⟩
  · simp only [runBlock, BInstr.run, lmK0]
  · simp only [runBlock, BInstr.run, lmK0]; simp +decide only [upd, ↓reduceIte, ev_add, hz]; try rfl
  · simp only [runBlock, BInstr.run, lmK0]; simp +decide only [upd, ↓reduceIte, ev_add, hz]; try rfl
  · exact runBlock_keepL (by decide) hz hq


macro "blk_val" : tactic => `(tactic| (simp +decide only [upd, ↓reduceIte, ev_add]; try rfl))

set_option maxRecDepth 20000 in
theorem lmK1_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lmK1 (M, f)).1 = memStore32 (memStore32 M (f sp + 0x38) 0) (f sp + 0x3C) 0 ∧
    (runBlock lmK1 (M, f)).2 (21 : Fin 32) = aluEval .srl (f 24) 5 ∧
    (runBlock lmK1 (M, f)).2 a2 = 2 - aluEval .srl (f 24) 5 ∧
    (runBlock lmK1 (M, f)).2 a0 = f sp + 0x38 ∧ (runBlock lmK1 (M, f)).2 a1 = 2 ∧
    ∀ q : Fin 32, q.val ∉ [10, 11, 12, 21] → (runBlock lmK1 (M, f)).2 q = f q := by
  refine ⟨?_, ?_, ?_, ?_, ?_, fun q hq => runBlock_keepL (by decide) hz hq⟩ <;>
    simp only [runBlock, BInstr.run, lmK1] <;> simp +decide only [upd, ↓reduceIte, ev_add, hz] <;> first | rfl | exact BitVec.zero_add _ | skip

set_option maxRecDepth 20000 in
theorem lmK2_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lmK2 (M, f)).1 = M ∧
    (runBlock lmK2 (M, f)).2 (20 : Fin 32) = f a0 ∧ (runBlock lmK2 (M, f)).2 (8 : Fin 32) = f a1 ∧
    (runBlock lmK2 (M, f)).2 a0 = BitVec.ofNat 32 u2MaxAddress ∧ (runBlock lmK2 (M, f)).2 a1 = 2 ∧
    (runBlock lmK2 (M, f)).2 a2 = f 21 ∧
    ∀ q : Fin 32, q.val ∉ [8, 10, 11, 12, 20] → (runBlock lmK2 (M, f)).2 q = f q := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun q hq => runBlock_keepL (by decide) hz hq⟩ <;>
    simp only [runBlock, BInstr.run, lmK2] <;> simp +decide only [upd, ↓reduceIte, ev_add, hz] <;> first | rfl | exact BitVec.zero_add _ | skip

set_option maxRecDepth 20000 in
theorem lmK3_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lmK3 (M, f)).1 = M ∧
    (runBlock lmK3 (M, f)).2 (21 : Fin 32) = f sp + 0xB0 ∧ (runBlock lmK3 (M, f)).2 a1 = f 8 ∧
    (runBlock lmK3 (M, f)).2 a2 = f 20 ∧
    ∀ q : Fin 32, q.val ∉ [11, 12, 21] → (runBlock lmK3 (M, f)).2 q = f q := by
  refine ⟨?_, ?_, ?_, ?_, fun q hq => runBlock_keepL (by decide) hz hq⟩ <;>
    simp only [runBlock, BInstr.run, lmK3] <;> simp +decide only [upd, ↓reduceIte, ev_add, hz] <;> first | rfl | exact BitVec.zero_add _ | skip

set_option maxRecDepth 20000 in
theorem lmK4_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lmK4 (M, f)).1 = memStore32 M (f a2 + 0) (memLoad32 M (f a0 + 0)) ∧
    (runBlock lmK4 (M, f)).2 a0 = f a0 + 4 ∧ (runBlock lmK4 (M, f)).2 a2 = f a2 + 4 ∧
    (runBlock lmK4 (M, f)).2 a1 = f a1 + 0xFFFFFFFF ∧
    ∀ q : Fin 32, q.val ∉ [10, 11, 12, 13] → (runBlock lmK4 (M, f)).2 q = f q := by
  refine ⟨?_, ?_, ?_, ?_, fun q hq => runBlock_keepL (by decide) hz hq⟩ <;>
    simp only [runBlock, BInstr.run, lmK4] <;> simp +decide only [upd, ↓reduceIte, ev_add, hz] <;> first | rfl | exact BitVec.zero_add _ | skip

theorem lmK4_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h0 : (f a0 + 0).toNat % 4 = 0) (h2 : (f a2 + 0).toNat % 4 = 0) (s2 : Sep (f a2 + 0) 4 base len) :
    BlockOk base len lmK4 (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, lmK4, upd, ↓reduceIte, and_true, true_and]
  exact ⟨h0, h2, s2⟩

set_option maxRecDepth 20000 in
theorem lmK6_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lmK6 (M, f)).1 = M ∧ (runBlock lmK6 (M, f)).2 a1 = 0 ∧
    (runBlock lmK6 (M, f)).2 a2 = 0x20 - f a0 ∧
    (runBlock lmK6 (M, f)).2 a3 = aluEval .sll (f 8) 2 + f 20 + 0xFFFFFFFC ∧
    ∀ q : Fin 32, q.val ∉ [11, 12, 13] → (runBlock lmK6 (M, f)).2 q = f q := by
  refine ⟨?_, ?_, ?_, ?_, fun q hq => runBlock_keepL (by decide) hz hq⟩ <;>
    simp only [runBlock, BInstr.run, lmK6] <;> simp +decide only [upd, ↓reduceIte, ev_add, hz] <;> first | rfl | exact BitVec.zero_add _ | skip

set_option maxRecDepth 20000 in
theorem lmK7_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lmK7 (M, f)).1 = memStore32 M (f a3 + 0)
      (aluEval .or (aluEval .srl (memLoad32 M (f a3 + 0)) (f a0)) (f a1)) ∧
    (runBlock lmK7 (M, f)).2 a1 = aluEval .sll (memLoad32 M (f a3 + 0)) (f a2) ∧
    (runBlock lmK7 (M, f)).2 (8 : Fin 32) = f 8 + 0xFFFFFFFF ∧
    ∀ q : Fin 32, q.val ∉ [8, 11, 14, 15] → (runBlock lmK7 (M, f)).2 q = f q := by
  refine ⟨?_, ?_, ?_, fun q hq => runBlock_keepL (by decide) hz hq⟩ <;>
    simp only [runBlock, BInstr.run, lmK7] <;> simp +decide only [upd, ↓reduceIte, ev_add, hz] <;> first | rfl | exact BitVec.zero_add _ | skip

theorem lmK7_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h3 : (f a3 + 0).toNat % 4 = 0) (s3 : Sep (f a3 + 0) 4 base len) :
    BlockOk base len lmK7 (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, lmK7, upd, ↓reduceIte, and_true, true_and]
  exact ⟨h3, h3, s3⟩

set_option maxRecDepth 20000 in
theorem lmK8_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lmK8 (M, f)).1 = memStore32 (memStore32 (memStore32 (memStore32 M (f sp + 0x38) 0) (f sp + 0x3C) 0)
      (f sp + 0x78) (memLoad32 M (f sp + 0x38))) (f sp + 0x7C) (memLoad32 M (f sp + 0x3C)) ∧
    (runBlock lmK8 (M, f)).2 a0 = f sp + 0x118 ∧ (runBlock lmK8 (M, f)).2 a1 = f sp + 0x78 ∧
    (runBlock lmK8 (M, f)).2 a2 = f sp + 0x38 ∧ (runBlock lmK8 (M, f)).2 a3 = 2 ∧
    ∀ q : Fin 32, q.val ∉ [10, 11, 12, 13] → (runBlock lmK8 (M, f)).2 q = f q := by
  refine ⟨?_, ?_, ?_, ?_, ?_, fun q hq => runBlock_keepL (by decide) hz hq⟩ <;>
    simp only [runBlock, BInstr.run, lmK8] <;> simp +decide only [upd, ↓reduceIte, ev_add, hz] <;> first | rfl | exact BitVec.zero_add _ | skip

set_option maxRecDepth 20000 in
theorem lmK9_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lmK9 (M, f)).1 = memStore32 M (f a2 + 0) (memLoad32 M (f a0 + 0) &&& memLoad32 M (f a1 + 0)) ∧
    (runBlock lmK9 (M, f)).2 a0 = f a0 + 4 ∧ (runBlock lmK9 (M, f)).2 a1 = f a1 + 4 ∧
    (runBlock lmK9 (M, f)).2 a2 = f a2 + 4 ∧ (runBlock lmK9 (M, f)).2 a3 = f a3 + 0xFFFFFFFF ∧
    ∀ q : Fin 32, q.val ∉ [10, 11, 12, 13, 14, 15] → (runBlock lmK9 (M, f)).2 q = f q := by
  refine ⟨?_, ?_, ?_, ?_, ?_, fun q hq => runBlock_keepL (by decide) hz hq⟩ <;>
    simp only [runBlock, BInstr.run, lmK9] <;> simp +decide only [upd, ↓reduceIte, ev_add, ev_and, hz] <;> first | rfl | exact BitVec.zero_add _ | skip

theorem lmK9_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h0 : (f a0 + 0).toNat % 4 = 0) (h1 : (f a1 + 0).toNat % 4 = 0) (h2 : (f a2 + 0).toNat % 4 = 0)
    (s2 : Sep (f a2 + 0) 4 base len) : BlockOk base len lmK9 (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, lmK9, upd, ↓reduceIte, and_true, true_and]
  exact ⟨h0, h1, h2, s2⟩

set_option maxRecDepth 20000 in
theorem lmK10_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lmK10 (M, f)).1 = memStore32 (memStore32 M (f sp + 0x118) (memLoad32 M (f sp + 0x38)))
      (f sp + 0x11C) (memLoad32 M (f sp + 0x3C)) ∧
    ∀ q : Fin 32, q.val ∉ [10, 11] → (runBlock lmK10 (M, f)).2 q = f q := by
  refine ⟨?_, fun q hq => runBlock_keepL (by decide) hz hq⟩
  simp only [runBlock, BInstr.run, lmK10]; simp +decide only [upd, ↓reduceIte, hz]


/-- A call to `UintRef::leading_mut` at `L`, from offset `off` of `code`: it
returns the buffer `a0` with length `a2`, at most the buffer's length `a1`. -/
theorem call_lead {M : Word → BitVec 8} {P L : Word} {code : List Nat} {n : Machine} {off : Nat}
    {imm o len want : Word} (hP : P.toNat % 2 = 0) (s : St M P n off (reg n)) (hc : CodeIn M P code)
    (hl : CodeIn M L leadMut12Code) (hL : L.toNat % 2 = 0)
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
theorem call_trail {M : Word → BitVec 8} {P T : Word} {code : List Nat} {n : Machine} {off : Nat}
    {imm o p len k : Word} (hP : P.toNat % 2 = 0) (s : St M P n off (reg n)) (hc : CodeIn M P code)
    (ht : CodeIn M T trailing12Code) (hT : T.toNat % 2 = 0)
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


theorem k_word {sh : Nat} (h1 : 1 ≤ sh) (h2 : sh ≤ 63) :
    (0x40 : Word) - BitVec.ofNat 32 sh = BitVec.ofNat 32 (64 - sh) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  show (2 ^ 32 - sh % 2 ^ 32 + 64) % 2 ^ 32 = (64 - sh) % 2 ^ 32
  omega

theorem srl5 {k : Nat} (h : k < 64) : aluEval .srl (BitVec.ofNat 32 k) 5 = BitVec.ofNat 32 (k / 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [aluEval, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  show k % 2 ^ 32 / 2 ^ 5 = k / 32 % 2 ^ 32
  omega

/-- **The mask's setup**, from 0xC6 to the copy loop at 0x112: `s8 = k = 64 -
shift`, the buffer at `F + 0x38` zeroed, and the copy's source (the words of
`Uint<2>::MAX` from `k / 32`), count, and destination. -/
theorem lm_maskPre {M : Word → BitVec 8} {P F : Word} {n : Machine} {sh : Nat} (hP : P.toNat % 2 = 0)
    (s : St M P n 0xC6 (reg n)) (hc : CodeIn M P lincombShiftMod12Code)
    (hl : CodeIn M (lmShr P + 0x1EE) leadMut12Code) (ht : CodeIn M (lmShr P + 0x1FE) trailing12Code)
    (rsp : reg n sp = F) (r19 : reg n 19 = BitVec.ofNat 32 sh) (hs1 : 1 ≤ sh) (hs2 : sh ≤ 63)
    (hF : F.toNat % 4 = 0) (sC : Sep (F + 0x38) 8 P lincombShiftMod12Code.length)
    (sLm : Sep (F + 0x38) 8 (lmShr P + 0x1EE) leadMut12Code.length)
    (sTr : Sep (F + 0x38) 8 (lmShr P + 0x1FE) trailing12Code.length) :
    ∃ n', Steps n n' ∧
      St (memStore32 (memStore32 M (F + 0x38) 0) (F + 0x3C) 0) P n' 0x112 (reg n') ∧
      reg n' 24 = BitVec.ofNat 32 (64 - sh) ∧ reg n' 21 = F + 0xB0 ∧ reg n' 20 = F + 0x38 ∧
      reg n' 8 = BitVec.ofNat 32 (2 - (64 - sh) / 32) ∧
      reg n' a0 = BitVec.ofNat 32 u2MaxAddress + BitVec.ofNat 32 (4 * ((64 - sh) / 32)) ∧
      reg n' a1 = BitVec.ofNat 32 (2 - (64 - sh) / 32) ∧ reg n' a2 = F + 0x38 ∧
      ∀ q : Fin 32, q.val ∉ [1, 8, 10, 11, 12, 13, 20, 21, 24] → reg n' q = reg n q := by
  have hz := s.zero
  have hk : 64 - sh < 64 := by omega
  have hk32 : (64 - sh) / 32 ≤ 1 := by omega
  -- `s8 = 64 - shift`, and the panic check
  obtain ⟨n1, c1, u1⟩ := St.block lmK0 s hc lmK0_end (by simp [BlockOk, BInstr.ok, lmK0])
  obtain ⟨k0e, k0a0, k0s8, k0k⟩ := lmK0_run (M := M) (f := reg n) hz
  rw [k0e] at u1
  have g1 : ∀ q, reg n1 q = (runBlock lmK0 (M, reg n)).2 q := u1.regs
  have r1s8 : reg n1 24 = BitVec.ofNat 32 (64 - sh) := by rw [g1, k0s8, r19, k_word hs1 hs2]
  obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc 0xD2 lm12_at_ce (by decide) (by
    rw [r1s8, g1, k0a0]
    show (!(BitVec.ofNat 32 (64 - sh)).ult 0x40) = false
    have : (BitVec.ofNat 32 (64 - sh)).ult 0x40 = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat]; exact decide_eq_true (by show _ < 64; omega)
    rw [this]; rfl)
  have k2 : ∀ q, reg n2 q = reg n1 q := u2.regs
  -- zero the buffer, and `leading_mut`
  have s38 : Sep (F + 0x38) 4 P lincombShiftMod12Code.length := by
    have := sC.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
  have s3c : Sep (F + 0x3C) 4 P lincombShiftMod12Code.length := by
    have := sC.sub (c := 4) (l := 4) (by decide); rw [BitVec.add_assoc] at this; exact this
  have r2sp : reg n2 sp = F := by rw [k2, g1, k0k sp (by decide), rsp]
  obtain ⟨n3, c3, u3⟩ := St.block lmK1 u2.self hc lmK1_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, lmK1, upd, ↓reduceIte, and_true, true_and]
    rw [r2sp]
    exact ⟨⟨aligned_add hF (by decide), s38⟩, aligned_add hF (by decide), s3c⟩)
  obtain ⟨k1e, k1s5, k1a2, k1a0, k1a1, k1k⟩ := lmK1_run (M := M) (f := reg n2) u2.self.zero
  rw [k1e, r2sp] at u3
  obtain ⟨Mz, hMz⟩ : ∃ Mz, memStore32 (memStore32 M (F + 0x38) 0) (F + 0x3C) 0 = Mz := ⟨_, rfl⟩
  rw [hMz] at u3
  have hcz : CodeIn Mz P lincombShiftMod12Code := by rw [← hMz]; exact (hc.store32 s38).store32 s3c
  have g3 : ∀ q, reg n3 q = (runBlock lmK1 (M, reg n2)).2 q := u3.regs
  have r3s5 : reg n3 21 = BitVec.ofNat 32 ((64 - sh) / 32) := by rw [g3, k1s5, k2, r1s8, srl5 hk]
  have w2 : (2 : Word) - BitVec.ofNat 32 ((64 - sh) / 32) = BitVec.ofNat 32 (2 - (64 - sh) / 32) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    show (2 ^ 32 - (64 - sh) / 32 % 2 ^ 32 + 2) % 2 ^ 32 = (2 - (64 - sh) / 32) % 2 ^ 32
    omega
  have r3a2 : reg n3 a2 = BitVec.ofNat 32 (2 - (64 - sh) / 32) := by rw [g3, k1a2, k2, r1s8, srl5 hk, w2]
  have eL : lmShr P + 0x1EE = P + 0xFFFFFD96 := by rw [BitVec.add_assoc]; rfl
  have eT : lmShr P + 0x1FE = P + 0xFFFFFDA6 := by rw [BitVec.add_assoc]; rfl
  have hlA : (lmShr P + 0x1EE).toNat % 2 = 0 := by rw [eL]; exact even_at P hP 0xFFFFFD96 (by decide)
  have htA : (lmShr P + 0x1FE).toNat % 2 = 0 := by rw [eT]; exact even_at P hP 0xFFFFFDA6 (by decide)
  have cz : ∀ {b : Word} {code : List Nat}, CodeIn M b code → Sep (F + 0x38) 8 b code.length → CodeIn Mz b code :=
    fun {b code} h hs => by
      rw [← hMz]
      exact (h.store32 (by have := hs.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this)).store32
        (by have := hs.sub (c := 4) (l := 4) (by decide); rw [BitVec.add_assoc] at this; exact this)
  obtain ⟨n4, c4, u4, a14, k4⟩ := call_lead hP u3.self hcz (cz hl sLm)
    hlA lm12_at_e4 lm12_at_e8 (by rw [eL, BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    (by rw [g3, k1a1]) r3a2 (by rw [BitVec.toNat_ofNat]; show _ ≤ 2; omega)
  have r4a0 : reg n4 a0 = F + 0x38 := by rw [k4 _ (by decide) (by decide), g3, k1a0, r2sp]
  have r4s5 : reg n4 21 = BitVec.ofNat 32 ((64 - sh) / 32) := by rw [k4 _ (by decide) (by decide), r3s5]
  obtain ⟨n5, c5, u5⟩ := St.block lmK2 u4 hcz lmK2_end (by simp [BlockOk, BInstr.ok, lmK2])
  obtain ⟨k2e, k2s4, k2s0, k2a0, k2a1, k2a2, k2k⟩ := lmK2_run (M := Mz) (f := reg n4) u4.zero
  rw [k2e] at u5
  have g5 : ∀ q, reg n5 q = (runBlock lmK2 (Mz, reg n4)).2 q := u5.regs
  obtain ⟨n6, c6, u6, a06, a16, k6⟩ := call_trail hP u5.self hcz (cz ht sTr) htA lm12_at_fc lm12_at_100
    (by rw [eT, BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide) (by rw [g5, k2a0]) (by rw [g5, k2a1])
    (by rw [g5, k2a2, r4s5]) (by rw [BitVec.toNat_ofNat]; show _ ≤ 2; omega)
  have w2' : (2 : Word) - BitVec.ofNat 32 ((64 - sh) / 32) = BitVec.ofNat 32 (2 - (64 - sh) / 32) := w2
  have r6s0 : reg n6 8 = BitVec.ofNat 32 (2 - (64 - sh) / 32) := by
    rw [k6 _ (by decide) (by decide) (by decide) (by decide), g5, k2s0, a14]
  obtain ⟨n7, d7, u7⟩ := u6.notTaken hcz 0x108 lm12_at_104 (by decide) (by
    rw [r6s0, a16, w2']; simp [branchTaken])
  have k7 : ∀ q, reg n7 q = reg n6 q := u7.regs
  have r7s4 : reg n7 20 = F + 0x38 := by
    rw [k7, k6 _ (by decide) (by decide) (by decide) (by decide), g5, k2s4, r4a0]
  obtain ⟨n8, c8, u8⟩ := St.block lmK3 u7.self hcz lmK3_end (by simp [BlockOk, BInstr.ok, lmK3])
  obtain ⟨k3e, k3s5, k3a1, k3a2, k3k⟩ := lmK3_run (M := Mz) (f := reg n7) u7.self.zero
  rw [k3e] at u8
  have g8 : ∀ q, reg n8 q = (runBlock lmK3 (Mz, reg n7)).2 q := u8.regs
  have r8s0 : reg n8 8 = BitVec.ofNat 32 (2 - (64 - sh) / 32) := by rw [g8, k3k 8 (by decide), k7, r6s0]
  obtain ⟨n9, d9, u9⟩ := u8.self.notTaken hcz 0x112 lm12_at_110 (by decide) (by
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


theorem tb_pow_sub_one : ∀ (n i : Nat), (2 ^ n - 1).testBit i = decide (i < n)
  | 0, i => by
    rw [show 2 ^ 0 - 1 = 0 from rfl, Nat.zero_testBit]; exact (decide_eq_false (Nat.not_lt_zero i)).symm
  | n + 1, 0 => by
    have e : 2 ^ (n + 1) - 1 = 2 * (2 ^ n - 1) + 1 := by
      have := Nat.one_le_two_pow (n := n); rw [Nat.pow_succ]; omega
    rw [e, Nat.testBit_zero, decide_eq_true (show (2 * (2 ^ n - 1) + 1) % 2 = 1 by omega),
      decide_eq_true (Nat.succ_pos n)]
  | n + 1, i + 1 => by
    have e : 2 ^ (n + 1) - 1 = 2 * (2 ^ n - 1) + 1 := by
      have := Nat.one_le_two_pow (n := n); rw [Nat.pow_succ]; omega
    have h : (2 * (2 ^ n - 1) + 1) / 2 = 2 ^ n - 1 := by omega
    rw [e, Nat.testBit_succ, h, tb_pow_sub_one n i]
    exact decide_eq_decide.mpr Nat.succ_lt_succ_iff.symm

/-- ANDing with `2^n - 1` keeps the low `n` bits. Core's
`Nat.and_two_pow_sub_one_eq_mod` depends on `Classical.choice`. -/
theorem and_pow_sub_one (x n : Nat) : x &&& (2 ^ n - 1) = x % 2 ^ n :=
  Nat.eq_of_testBit_eq fun i => by
    rw [Nat.testBit_and, tb_pow_sub_one, Nat.testBit_mod_two_pow, Bool.and_comm]

theorem and_mask_word {w m : Word} {j : Nat} (hm : m.toNat = 2 ^ j - 1) : (w &&& m).toNat = w.toNat % 2 ^ j := by
  rw [BitVec.toNat_and, hm, and_pow_sub_one]

/-- What the mask words `m0` and `m1` must do: AND a 64-bit value down to
its low `sh` bits. -/
def maskOK (sh : Nat) (m0 m1 : Word) : Prop :=
  ∀ w0 w1 : Word, (w0 &&& m0).toNat + 2 ^ 32 * (w1 &&& m1).toNat = (w0.toNat + 2 ^ 32 * w1.toNat) % 2 ^ sh

theorem maskOK_hi {sh : Nat} {m1 : Word} (h1 : 32 < sh) (hm : m1.toNat = 2 ^ (sh - 32) - 1) :
    maskOK sh 0xFFFFFFFF m1 := fun w0 w1 => by
  rw [ng_and_ones, and_mask_word hm]
  have e : 2 ^ sh = 2 ^ 32 * 2 ^ (sh - 32) := by rw [← Nat.pow_add]; congr 1; omega
  obtain ⟨P, hP⟩ : ∃ P, 2 ^ (sh - 32) = P := ⟨_, rfl⟩
  have hP1 : 1 ≤ P := hP ▸ Nat.one_le_two_pow
  rw [e, hP]
  have hw0 := w0.isLt
  have hd := Nat.div_add_mod w1.toNat P
  have hr := Nat.mod_lt w1.toNat (show 0 < P by omega)
  generalize w1.toNat / P = q at hd
  generalize w1.toNat % P = r at hd hr ⊢
  rw [← hd, Nat.mul_add, ← Nat.mul_assoc, Nat.add_comm (2 ^ 32 * P * q), ← Nat.add_assoc,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
  have : 2 ^ 32 * r ≤ 2 ^ 32 * (P - 1) := Nat.mul_le_mul_left _ (by omega)
  have : 2 ^ 32 * (P - 1) + 2 ^ 32 = 2 ^ 32 * P := by
    rw [← Nat.mul_succ]; congr 1; omega
  omega

theorem maskOK_32 : maskOK 32 0xFFFFFFFF 0 := fun w0 w1 => by
  rw [ng_and_ones, show w1 &&& (0 : Word) = 0 from BitVec.and_zero]
  have := w0.isLt
  show w0.toNat + 2 ^ 32 * 0 = _
  omega

theorem maskOK_lo {sh : Nat} {m0 : Word} (h1 : sh ≤ 32) (hm : m0.toNat = 2 ^ sh - 1) :
    maskOK sh m0 0 := fun w0 w1 => by
  rw [and_mask_word hm, show w1 &&& (0 : Word) = 0 from BitVec.and_zero]
  have e : 2 ^ 32 = 2 ^ sh * 2 ^ (32 - sh) := by rw [← Nat.pow_add]; congr 1; omega
  show w0.toNat % 2 ^ sh + 2 ^ 32 * 0 = _
  rw [Nat.mul_zero, Nat.add_zero, e, Nat.mul_assoc, Nat.add_mul_mod_self_left]

set_option maxRecDepth 100000 in
theorem maskA_words : ∀ k : Fin 32, 1 ≤ k.val →
    aluEval .and (BitVec.ofNat 32 k.val) 0x1F ≠ 0 ∧
    (aluEval .or (aluEval .srl 0xFFFFFFFF (aluEval .and (BitVec.ofNat 32 k.val) 0x1F)) 0).toNat =
        2 ^ (32 - k.val) - 1 ∧
      aluEval .or (aluEval .srl 0xFFFFFFFF (aluEval .and (BitVec.ofNat 32 k.val) 0x1F))
        (aluEval .sll 0xFFFFFFFF (0x20 - aluEval .and (BitVec.ofNat 32 k.val) 0x1F)) = 0xFFFFFFFF := by
  decide

set_option maxRecDepth 100000 in
theorem maskC_words : ∀ k : Fin 64, 33 ≤ k.val →
    aluEval .and (BitVec.ofNat 32 k.val) 0x1F ≠ 0 ∧
    (aluEval .or (aluEval .srl 0xFFFFFFFF (aluEval .and (BitVec.ofNat 32 k.val) 0x1F)) 0).toNat =
        2 ^ (64 - k.val) - 1 := by
  decide


theorem max_word {M : Word → BitVec 8} (h : CodeIn M (BitVec.ofNat 32 u2MaxAddress) u2MaxData) (i : Nat)
    (hi : i < 2) : memLoad32 M (BitVec.ofNat 32 u2MaxAddress + BitVec.ofNat 32 (4 * i)) = 0xFFFFFFFF := by
  rw [u2_data_word h (by decide) i (by simp [u2MaxData]; omega)]
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- The copy for `shift = 32`: one word of `Uint<2>::MAX` to the buffer, and
no bit shift. -/
theorem lm_maskB {M : Word → BitVec 8} {P F : Word} {n : Machine} (s : St M P n 0x112 (reg n))
    (hc : CodeIn M P lincombShiftMod12Code) (hmax : CodeIn M (BitVec.ofNat 32 u2MaxAddress) u2MaxData)
    (r24 : reg n 24 = BitVec.ofNat 32 32) (ra0 : reg n a0 = BitVec.ofNat 32 u2MaxAddress + BitVec.ofNat 32 (4 * 1))
    (ra1 : reg n a1 = BitVec.ofNat 32 1) (ra2 : reg n a2 = F + 0x38) (hF : F.toNat % 4 = 0)
    (sC : Sep (F + 0x38) 8 P lincombShiftMod12Code.length)
    (sMX : Sep (F + 0x38) 8 (BitVec.ofNat 32 u2MaxAddress) 8) (hb1 : memLoad32 M (F + 0x3C) = 0) :
    ∃ n' M', Steps n n' ∧ St M' P n' 0x14A (reg n') ∧ CodeIn M' P lincombShiftMod12Code ∧
      (∀ x, Sep (F + 0x38) 8 x 1 → M' x = M x) ∧ maskOK 32 (memLoad32 M' (F + 0x38)) (memLoad32 M' (F + 0x3C)) ∧
      ∀ q : Fin 32, q.val ∉ [8, 10, 11, 12, 13, 14, 15] → reg n' q = reg n q := by
  have hz := s.zero
  have s38 : Sep (F + 0x38) 4 P lincombShiftMod12Code.length := by
    have := sC.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
  have mx1 : memLoad32 M (BitVec.ofNat 32 u2MaxAddress + BitVec.ofNat 32 (4 * 1)) = 0xFFFFFFFF := max_word hmax 1 (by decide)
  obtain ⟨n1, c1, u1⟩ := St.block lmK4 s hc lmK4_end
    (lmK4_ok (by rw [ra0, add_lit_zero]; exact aligned_add (by decide) (by decide))
      (by rw [ra2, add_lit_zero]; exact aligned_add hF (by decide)) (by rw [ra2, add_lit_zero]; exact s38))
  obtain ⟨k4e, k4a0, k4a2, k4a1, k4k⟩ := lmK4_run (M := M) (f := reg n) hz
  rw [k4e, ra0, ra2, add_lit_zero, add_lit_zero, mx1] at u1
  have hc1 : CodeIn (memStore32 M (F + 0x38) 0xFFFFFFFF) P lincombShiftMod12Code := hc.store32 s38
  have g1 : ∀ q, reg n1 q = (runBlock lmK4 (M, reg n)).2 q := u1.regs
  obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc1 0x11E lm12_at_11c (by decide)
    (by rw [g1, k4a1, ra1, u1.self.zero]; decide)
  obtain ⟨n3, d3, u3⟩ := u2.self.aluImm hc1 lm12_at_11e (off' := 0x122) (by decide)
  have r3a0 : upd (reg n2) a0 (aluEval .and (reg n2 24) 0x1F) a0 = 0 := by
    rw [upd_same (by decide), u2.regs, g1, k4k 24 (by decide), r24]; decide
  obtain ⟨n4, d4, u4⟩ := u3.taken hc1 0x14A lm12_at_122 (by decide) (by rw [r3a0, upd_zero]; decide)
  refine ⟨n4, _, c1.trans (.cons d2 (.cons d3 (.single d4))), u4.self, hc1, fun x hx => ?_, ?_, fun q hq => ?_⟩
  · exact memStore32_get_sep (by have := hx.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this)
  · rw [memLoad32_store32_same, memLoad32_store32_sep (by
      have := sep_offsets F (c := 0x38) (n := 4) (d := 0x3C) (k := 4) (.inl (by decide)) (by decide) (by decide)
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
theorem lm_maskC {M : Word → BitVec 8} {P F : Word} {n : Machine} {sh : Nat} (hP : P.toNat % 2 = 0)
    (s : St M P n 0x112 (reg n)) (hc : CodeIn M P lincombShiftMod12Code)
    (hmax : CodeIn M (BitVec.ofNat 32 u2MaxAddress) u2MaxData) (hs1 : 1 ≤ sh) (hs2 : sh ≤ 31)
    (r24 : reg n 24 = BitVec.ofNat 32 (64 - sh)) (ra0 : reg n a0 = BitVec.ofNat 32 u2MaxAddress + BitVec.ofNat 32 (4 * 1))
    (ra1 : reg n a1 = BitVec.ofNat 32 1) (ra2 : reg n a2 = F + 0x38) (r8 : reg n 8 = BitVec.ofNat 32 1)
    (r20 : reg n 20 = F + 0x38) (hF : F.toNat % 4 = 0)
    (sC : Sep (F + 0x38) 8 P lincombShiftMod12Code.length)
    (sMX : Sep (F + 0x38) 8 (BitVec.ofNat 32 u2MaxAddress) 8) (hb1 : memLoad32 M (F + 0x3C) = 0) :
    ∃ n' M', Steps n n' ∧ St M' P n' 0x14A (reg n') ∧ CodeIn M' P lincombShiftMod12Code ∧
      (∀ x, Sep (F + 0x38) 8 x 1 → M' x = M x) ∧ maskOK sh (memLoad32 M' (F + 0x38)) (memLoad32 M' (F + 0x3C)) ∧
      ∀ q : Fin 32, q.val ∉ [8, 10, 11, 12, 13, 14, 15] → reg n' q = reg n q := by
  have hz := s.zero
  obtain ⟨wnz, wval⟩ := maskC_words ⟨64 - sh, by omega⟩ (by show 33 ≤ 64 - sh; omega)
  simp only at wnz wval
  have s38 : Sep (F + 0x38) 4 P lincombShiftMod12Code.length := by
    have := sC.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
  have a38 : (F + 0x38).toNat % 4 = 0 := aligned_add hF (by decide)
  have mx1 : memLoad32 M (BitVec.ofNat 32 u2MaxAddress + BitVec.ofNat 32 (4 * 1)) = 0xFFFFFFFF := max_word hmax 1 (by decide)
  -- the copy
  obtain ⟨n1, c1, u1⟩ := St.block lmK4 s hc lmK4_end
    (lmK4_ok (by rw [ra0, add_lit_zero]; exact aligned_add (by decide) (by decide))
      (by rw [ra2, add_lit_zero]; exact a38) (by rw [ra2, add_lit_zero]; exact s38))
  obtain ⟨k4e, k4a0, k4a2, k4a1, k4k⟩ := lmK4_run (M := M) (f := reg n) hz
  rw [k4e, ra0, ra2, add_lit_zero, add_lit_zero, mx1] at u1
  have hc1 : CodeIn (memStore32 M (F + 0x38) 0xFFFFFFFF) P lincombShiftMod12Code := hc.store32 s38
  have g1 : ∀ q, reg n1 q = (runBlock lmK4 (M, reg n)).2 q := u1.regs
  obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc1 0x11E lm12_at_11c (by decide)
    (by rw [g1, k4a1, ra1, u1.self.zero]; decide)
  obtain ⟨n3, d3, u3⟩ := u2.self.aluImm hc1 lm12_at_11e (off' := 0x122) (by decide)
  have e24 : reg n2 24 = BitVec.ofNat 32 (64 - sh) := by rw [u2.regs, g1, k4k 24 (by decide), r24]
  obtain ⟨n4, d4, u4⟩ := u3.notTaken hc1 0x124 lm12_at_122 (by decide) (by
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
  obtain ⟨n5, c5, u5⟩ := St.block lmK6 u4.self hc1 lmK6_end (by simp [BlockOk, BInstr.ok, lmK6])
  obtain ⟨k6e, k6a1, k6a2, k6a3, k6k⟩ := lmK6_run (M := memStore32 M (F + 0x38) 0xFFFFFFFF) (f := reg n4) u4.self.zero
  rw [k6e] at u5
  have g5 : ∀ q, reg n5 q = (runBlock lmK6 (memStore32 M (F + 0x38) 0xFFFFFFFF, reg n4)).2 q := u5.regs
  have r5a3 : reg n5 a3 = F + 0x38 := by
    rw [g5, k6a3, k4r 8 (by decide), k4r 20 (by decide), r8, r20]
    show aluEval .sll (BitVec.ofNat 32 1) 2 + (F + 0x38) + 0xFFFFFFFC = F + 0x38
    rw [show aluEval .sll (BitVec.ofNat 32 1) 2 = 4 by decide, BitVec.add_comm (4 : Word), BitVec.add_assoc,
      BitVec.add_assoc]
    rfl
  have r5s0 : reg n5 8 = BitVec.ofNat 32 1 := by rw [g5, k6k 8 (by decide), k4r 8 (by decide), r8]
  obtain ⟨n6, d6, u6⟩ := u5.self.notTaken hc1 0x138 lm12_at_136 (by decide)
    (by rw [r5s0, u5.self.zero]; decide)
  -- one pass of the shift
  obtain ⟨n7, c7, u7⟩ := St.block lmK7 u6.self hc1 lmK7_end
    (lmK7_ok (by rw [u6.regs, r5a3, add_lit_zero]; exact a38) (by rw [u6.regs, r5a3, add_lit_zero]; exact s38))
  obtain ⟨k7e, k7a1, k7s0, k7k⟩ := lmK7_run (M := memStore32 M (F + 0x38) 0xFFFFFFFF) (f := reg n6) u6.self.zero
  have e6a3 : reg n6 a3 = F + 0x38 := by rw [u6.regs, r5a3]
  have e6a0 : reg n6 a0 = aluEval .and (BitVec.ofNat 32 (64 - sh)) 0x1F := by
    rw [u6.regs, g5, k6k a0 (by decide), r4a0]
  have e6a1 : reg n6 a1 = 0 := by rw [u6.regs, g5, k6a1]
  rw [k7e, e6a3, add_lit_zero, memLoad32_store32_same, e6a0, e6a1] at u7
  obtain ⟨Mw, hMw⟩ : ∃ Mw, memStore32 (memStore32 M (F + 0x38) 0xFFFFFFFF) (F + 0x38)
      (aluEval .or (aluEval .srl 0xFFFFFFFF (aluEval .and (BitVec.ofNat 32 (64 - sh)) 0x1F)) 0) = Mw := ⟨_, rfl⟩
  rw [hMw] at u7
  have hc7 : CodeIn Mw P lincombShiftMod12Code := by rw [← hMw]; exact hc1.store32 s38
  have g7 : ∀ q, reg n7 q = (runBlock lmK7 (memStore32 M (F + 0x38) 0xFFFFFFFF, reg n6)).2 q := u7.regs
  obtain ⟨n8, d8, u8⟩ := u7.self.jump hc7 lm12_at_148 (off' := 0x134) (by decide) (by
    rw [u7.pc, show P + BitVec.ofNat 32 0x148 + 0xFFFFFFEC = P + BitVec.ofNat 32 0x134 by rw [BitVec.add_assoc]; rfl]
    exact even_bit0 (even_at P hP 0x134 (by decide)))
  obtain ⟨n9, d9, u9⟩ := u8.self.aluImm hc7 lm12_at_134 (off' := 0x136) (by decide)
  have r9s0 : upd (reg n8) a3 (aluEval .add (reg n8 a3) 0xFFFFFFFC) 8 = 0 := by
    rw [upd_ne (by decide) (by decide), u8.regs, g7, k7s0, u6.regs, r5s0]; rfl
  obtain ⟨n10, d10, u10⟩ := u9.taken hc7 0x14A lm12_at_136 (by decide) (by rw [r9s0, upd_zero]; decide)
  refine ⟨n10, Mw, c1.trans (.cons d2 (.cons d3 (.cons d4 (c5.trans (.cons d6 (c7.trans (.cons d8 (.cons d9
    (.single d10))))))))), u10.self, hc7, fun x hx => ?_, ?_, fun q hq => ?_⟩
  · have h0 : Sep (F + 0x38) 4 x 1 := by
      have := hx.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    rw [← hMw, memStore32_get_sep h0, memStore32_get_sep h0]
  · have s3c : Sep (F + 0x38) 4 (F + 0x3C) 4 := by
      have := sep_offsets F (c := 0x38) (n := 4) (d := 0x3C) (k := 4) (.inl (by decide)) (by decide) (by decide)
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
theorem lm_maskA {M : Word → BitVec 8} {P F : Word} {n : Machine} {sh : Nat} (hP : P.toNat % 2 = 0)
    (s : St M P n 0x112 (reg n)) (hc : CodeIn M P lincombShiftMod12Code)
    (hmax : CodeIn M (BitVec.ofNat 32 u2MaxAddress) u2MaxData) (hs1 : 33 ≤ sh) (hs2 : sh ≤ 63)
    (r24 : reg n 24 = BitVec.ofNat 32 (64 - sh)) (ra0 : reg n a0 = BitVec.ofNat 32 u2MaxAddress + BitVec.ofNat 32 (4 * 0))
    (ra1 : reg n a1 = BitVec.ofNat 32 2) (ra2 : reg n a2 = F + 0x38) (r8 : reg n 8 = BitVec.ofNat 32 2)
    (r20 : reg n 20 = F + 0x38) (hF : F.toNat % 4 = 0)
    (sC : Sep (F + 0x38) 8 P lincombShiftMod12Code.length)
    (sMX : Sep (F + 0x38) 8 (BitVec.ofNat 32 u2MaxAddress) 8) :
    ∃ n' M', Steps n n' ∧ St M' P n' 0x14A (reg n') ∧ CodeIn M' P lincombShiftMod12Code ∧
      (∀ x, Sep (F + 0x38) 8 x 1 → M' x = M x) ∧ maskOK sh (memLoad32 M' (F + 0x38)) (memLoad32 M' (F + 0x3C)) ∧
      ∀ q : Fin 32, q.val ∉ [8, 10, 11, 12, 13, 14, 15] → reg n' q = reg n q := by
  have hz := s.zero
  obtain ⟨wnz, wtop, wlow⟩ := maskA_words ⟨64 - sh, by omega⟩ (by show 1 ≤ 64 - sh; omega)
  simp only at wnz wtop wlow
  have s38 : Sep (F + 0x38) 4 P lincombShiftMod12Code.length := by
    have := sC.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
  have s3c : Sep (F + 0x3C) 4 P lincombShiftMod12Code.length := by
    have := sC.sub (c := 4) (l := 4) (by decide); rw [BitVec.add_assoc] at this; exact this
  have a38 : (F + 0x38).toNat % 4 = 0 := aligned_add hF (by decide)
  have a3c : (F + 0x3C).toNat % 4 = 0 := aligned_add hF (by decide)
  have e3c : F + 0x38 + 4 = F + 0x3C := by rw [BitVec.add_assoc]; rfl
  have s83 : Sep (F + 0x38) 4 (F + 0x3C) 4 := by
    have := sep_offsets F (c := 0x38) (n := 4) (d := 0x3C) (k := 4) (.inl (by decide)) (by decide) (by decide)
    exact this
  have mx0 : memLoad32 M (BitVec.ofNat 32 u2MaxAddress + BitVec.ofNat 32 (4 * 0)) = 0xFFFFFFFF :=
    max_word hmax 0 (by decide)
  have mx1 : memLoad32 M (BitVec.ofNat 32 u2MaxAddress + BitVec.ofNat 32 (4 * 1)) = 0xFFFFFFFF :=
    max_word hmax 1 (by decide)
  have eMX : BitVec.ofNat 32 u2MaxAddress + BitVec.ofNat 32 (4 * 0) + 4 = BitVec.ofNat 32 u2MaxAddress + BitVec.ofNat 32 (4 * 1) := by
    rw [BitVec.add_assoc]; rfl
  -- the first copy
  obtain ⟨n1, c1, u1⟩ := St.block lmK4 s hc lmK4_end
    (lmK4_ok (by rw [ra0, add_lit_zero]; exact aligned_add (by decide) (by decide))
      (by rw [ra2, add_lit_zero]; exact a38) (by rw [ra2, add_lit_zero]; exact s38))
  obtain ⟨k4e, k4a0, k4a2, k4a1, k4k⟩ := lmK4_run (M := M) (f := reg n) hz
  rw [k4e, ra0, ra2, add_lit_zero, add_lit_zero, mx0] at u1
  have hc1 : CodeIn (memStore32 M (F + 0x38) 0xFFFFFFFF) P lincombShiftMod12Code := hc.store32 s38
  have g1 : ∀ q, reg n1 q = (runBlock lmK4 (M, reg n)).2 q := u1.regs
  obtain ⟨n2, d2, u2⟩ := u1.self.taken hc1 0x112 lm12_at_11c (by decide)
    (by rw [g1, k4a1, ra1, u1.self.zero]; decide)
  -- the second copy
  have r2a0 : reg n2 a0 = BitVec.ofNat 32 u2MaxAddress + BitVec.ofNat 32 (4 * 1) := by rw [u2.regs, g1, k4a0, ra0, eMX]
  have r2a2 : reg n2 a2 = F + 0x3C := by rw [u2.regs, g1, k4a2, ra2, e3c]
  have r2a1 : reg n2 a1 = BitVec.ofNat 32 1 := by rw [u2.regs, g1, k4a1, ra1]; rfl
  have mx1' : memLoad32 (memStore32 M (F + 0x38) 0xFFFFFFFF) (BitVec.ofNat 32 u2MaxAddress + BitVec.ofNat 32 (4 * 1)) =
      0xFFFFFFFF := by
    rw [memLoad32_store32_sep (by
      have := (sMX.sub (c := 0) (l := 4) (by decide)).subR (c := 4) (l := 4) (by decide)
      rwa [add_ofNat_zero] at this), mx1]
  obtain ⟨n3, c3, u3⟩ := St.block lmK4 u2.self hc1 lmK4_end
    (lmK4_ok (by rw [r2a0, add_lit_zero]; exact aligned_add (by decide) (by decide))
      (by rw [r2a2, add_lit_zero]; exact a3c) (by rw [r2a2, add_lit_zero]; exact s3c))
  obtain ⟨k4e', k4a0', k4a2', k4a1', k4k'⟩ := lmK4_run (M := memStore32 M (F + 0x38) 0xFFFFFFFF) (f := reg n2)
    u2.self.zero
  rw [k4e', r2a0, r2a2, add_lit_zero, add_lit_zero, mx1'] at u3
  obtain ⟨Mc, hMc⟩ : ∃ Mc, memStore32 (memStore32 M (F + 0x38) 0xFFFFFFFF) (F + 0x3C) 0xFFFFFFFF = Mc := ⟨_, rfl⟩
  rw [hMc] at u3
  have hc3 : CodeIn Mc P lincombShiftMod12Code := by rw [← hMc]; exact hc1.store32 s3c
  have g3 : ∀ q, reg n3 q = (runBlock lmK4 (memStore32 M (F + 0x38) 0xFFFFFFFF, reg n2)).2 q := u3.regs
  obtain ⟨n4, d4, u4⟩ := u3.self.notTaken hc3 0x11E lm12_at_11c (by decide)
    (by rw [g3, k4a1', r2a1, u3.self.zero]; decide)
  have k4r : ∀ q : Fin 32, q.val ∉ [10, 11, 12, 13] → reg n4 q = reg n q := fun q hq => by
    rw [u4.regs, g3, k4k' q hq, u2.regs, g1, k4k q hq]
  obtain ⟨n5, d5, u5⟩ := u4.self.aluImm hc3 lm12_at_11e (off' := 0x122) (by decide)
  have e24 : reg n4 24 = BitVec.ofNat 32 (64 - sh) := by rw [k4r 24 (by decide), r24]
  obtain ⟨n6, d6, u6⟩ := u5.notTaken hc3 0x124 lm12_at_122 (by decide) (by
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
  obtain ⟨n7, c7, u7⟩ := St.block lmK6 u6.self hc3 lmK6_end (by simp [BlockOk, BInstr.ok, lmK6])
  obtain ⟨k6e, k6a1, k6a2, k6a3, k6k⟩ := lmK6_run (M := Mc) (f := reg n6) u6.self.zero
  rw [k6e] at u7
  have g7 : ∀ q, reg n7 q = (runBlock lmK6 (Mc, reg n6)).2 q := u7.regs
  have r7a3 : reg n7 a3 = F + 0x3C := by
    rw [g7, k6a3, k6r 8 (by decide), k6r 20 (by decide), r8, r20]
    show aluEval .sll (BitVec.ofNat 32 2) 2 + (F + 0x38) + 0xFFFFFFFC = F + 0x3C
    rw [show aluEval .sll (BitVec.ofNat 32 2) 2 = 8 by decide, BitVec.add_comm (8 : Word), BitVec.add_assoc,
      BitVec.add_assoc]
    rfl
  have r7s0 : reg n7 8 = BitVec.ofNat 32 2 := by rw [g7, k6k 8 (by decide), k6r 8 (by decide), r8]
  have r7a0 : reg n7 a0 = aluEval .and (BitVec.ofNat 32 (64 - sh)) 0x1F := by rw [g7, k6k a0 (by decide), r6a0]
  have r7a2 : reg n7 a2 = 0x20 - aluEval .and (BitVec.ofNat 32 (64 - sh)) 0x1F := by rw [g7, k6a2, r6a0]
  have r7a1 : reg n7 a1 = 0 := by rw [g7, k6a1]
  obtain ⟨n8, d8, u8⟩ := u7.self.notTaken hc3 0x138 lm12_at_136 (by decide)
    (by rw [r7s0, u7.self.zero]; decide)
  -- the top word
  have e8 : ∀ q, reg n8 q = reg n7 q := u8.regs
  obtain ⟨n9, c9, u9⟩ := St.block lmK7 u8.self hc3 lmK7_end
    (lmK7_ok (by rw [e8, r7a3, add_lit_zero]; exact a3c) (by rw [e8, r7a3, add_lit_zero]; exact s3c))
  obtain ⟨k7e, k7a1, k7s0, k7k⟩ := lmK7_run (M := Mc) (f := reg n8) u8.self.zero
  have ldc : memLoad32 Mc (F + 0x3C) = 0xFFFFFFFF := by rw [← hMc, memLoad32_store32_same]
  rw [k7e, e8, r7a3, add_lit_zero, ldc, e8, r7a0, e8, r7a1] at u9
  obtain ⟨top, htop⟩ : ∃ top, aluEval .or (aluEval .srl 0xFFFFFFFF (aluEval .and (BitVec.ofNat 32 (64 - sh)) 0x1F)) 0 = top :=
    ⟨_, rfl⟩
  rw [htop] at u9 wtop
  have hc9 : CodeIn (memStore32 Mc (F + 0x3C) top) P lincombShiftMod12Code := hc3.store32 s3c
  have g9 : ∀ q, reg n9 q = (runBlock lmK7 (Mc, reg n8)).2 q := u9.regs
  obtain ⟨n10, d10, u10⟩ := u9.self.jump hc9 lm12_at_148 (off' := 0x134) (by decide) (by
    rw [u9.pc, show P + BitVec.ofNat 32 0x148 + 0xFFFFFFEC = P + BitVec.ofNat 32 0x134 by rw [BitVec.add_assoc]; rfl]
    exact even_bit0 (even_at P hP 0x134 (by decide)))
  obtain ⟨n11, d11, u11⟩ := u10.self.aluImm hc9 lm12_at_134 (off' := 0x136) (by decide)
  have r11s0 : upd (reg n10) a3 (aluEval .add (reg n10 a3) 0xFFFFFFFC) 8 = BitVec.ofNat 32 1 := by
    rw [upd_ne (by decide) (by decide), u10.regs, g9, k7s0, e8, r7s0]; rfl
  obtain ⟨n12, d12, u12⟩ := u11.notTaken hc9 0x138 lm12_at_136 (by decide) (by rw [r11s0, upd_zero]; decide)
  -- the low word
  have r12 : ∀ q, reg n12 q = upd (reg n10) a3 (aluEval .add (reg n10 a3) 0xFFFFFFFC) q := u12.regs
  have r12a3 : reg n12 a3 = F + 0x38 := by
    rw [r12, upd_same (by decide), u10.regs, g9, k7k a3 (by decide), e8, r7a3]
    show F + 0x3C + 0xFFFFFFFC = F + 0x38
    rw [BitVec.add_assoc]; rfl
  have r12a0 : reg n12 a0 = aluEval .and (BitVec.ofNat 32 (64 - sh)) 0x1F := by
    rw [r12, upd_ne (by decide) (by decide), u10.regs, g9, k7k a0 (by decide), e8, r7a0]
  have r12a1 : reg n12 a1 = aluEval .sll 0xFFFFFFFF (0x20 - aluEval .and (BitVec.ofNat 32 (64 - sh)) 0x1F) := by
    rw [r12, upd_ne (by decide) (by decide), u10.regs, g9, k7a1, e8, r7a3, add_lit_zero, ldc, e8, r7a2]
  have r12s0 : reg n12 8 = BitVec.ofNat 32 1 := by rw [r12, r11s0]
  obtain ⟨n13, c13, u13⟩ := St.block lmK7 u12.self hc9 lmK7_end
    (lmK7_ok (by rw [r12a3, add_lit_zero]; exact a38) (by rw [r12a3, add_lit_zero]; exact s38))
  obtain ⟨k7e', k7a1', k7s0', k7k'⟩ := lmK7_run (M := memStore32 Mc (F + 0x3C) top) (f := reg n12) u12.self.zero
  have ldl : memLoad32 (memStore32 Mc (F + 0x3C) top) (F + 0x38) = 0xFFFFFFFF := by
    rw [memLoad32_store32_sep s83.symm, ← hMc, memLoad32_store32_sep s83.symm, memLoad32_store32_same]
  rw [k7e', r12a3, add_lit_zero, ldl, r12a0, r12a1, wlow] at u13
  have hc13 : CodeIn (memStore32 (memStore32 Mc (F + 0x3C) top) (F + 0x38) 0xFFFFFFFF) P lincombShiftMod12Code :=
    hc9.store32 s38
  have g13 : ∀ q, reg n13 q = (runBlock lmK7 (memStore32 Mc (F + 0x3C) top, reg n12)).2 q := u13.regs
  obtain ⟨n14, d14, u14⟩ := u13.self.jump hc13 lm12_at_148 (off' := 0x134) (by decide) (by
    rw [u13.pc, show P + BitVec.ofNat 32 0x148 + 0xFFFFFFEC = P + BitVec.ofNat 32 0x134 by rw [BitVec.add_assoc]; rfl]
    exact even_bit0 (even_at P hP 0x134 (by decide)))
  obtain ⟨n15, d15, u15⟩ := u14.self.aluImm hc13 lm12_at_134 (off' := 0x136) (by decide)
  have r15s0 : upd (reg n14) a3 (aluEval .add (reg n14 a3) 0xFFFFFFFC) 8 = 0 := by
    rw [upd_ne (by decide) (by decide), u14.regs, g13, k7s0', r12s0]; rfl
  obtain ⟨n16, d16, u16⟩ := u15.taken hc13 0x14A lm12_at_136 (by decide) (by rw [r15s0, upd_zero]; decide)
  refine ⟨n16, _, c1.trans (.cons d2 (c3.trans (.cons d4 (.cons d5 (.cons d6 (c7.trans (.cons d8 (c9.trans
    (.cons d10 (.cons d11 (.cons d12 (c13.trans (.cons d14 (.cons d15 (.single d16))))))))))))))),
    u16.self, hc13, fun x hx => ?_, ?_, fun q hq => ?_⟩
  · have h0 : Sep (F + 0x38) 4 x 1 := by
      have := hx.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    have h4 : Sep (F + 0x3C) 4 x 1 := by
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
/-- **Masking `mf`**, from 0x14A to 0x17E: with the mask words in the buffer
at `F + 0x38`, AND them into the two words of `mf` at `F + 0x118`. -/
theorem lm_maskEnd {M : Word → BitVec 8} {P F : Word} {n : Machine} {sh : Nat} (s : St M P n 0x14A (reg n))
    (hc : CodeIn M P lincombShiftMod12Code) (rsp : reg n sp = F) (hF : F.toNat % 4 = 0)
    (hm : maskOK sh (memLoad32 M (F + 0x38)) (memLoad32 M (F + 0x3C)))
    (sC1 : Sep (F + 0x38) 8 P lincombShiftMod12Code.length) (sC2 : Sep (F + 0x78) 8 P lincombShiftMod12Code.length)
    (sC3 : Sep (F + 0x118) 8 P lincombShiftMod12Code.length) :
    ∃ n' M', Steps n n' ∧ St M' P n' 0x17E (reg n') ∧ CodeIn M' P lincombShiftMod12Code ∧
      (∀ x, Sep (F + 0x38) 8 x 1 → Sep (F + 0x78) 8 x 1 → Sep (F + 0x118) 8 x 1 → M' x = M x) ∧
      (memLoad32 M' (F + 0x118)).toNat + 2 ^ 32 * (memLoad32 M' (F + 0x11C)).toNat =
        ((memLoad32 M (F + 0x118)).toNat + 2 ^ 32 * (memLoad32 M (F + 0x11C)).toNat) % 2 ^ sh ∧
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
  obtain ⟨c38, c3c⟩ := sc (c := 0x38) sC1
  obtain ⟨c78, c7c⟩ := sc (c := 0x78) sC2
  obtain ⟨c118, c11c⟩ := sc (c := 0x118) sC3
  obtain ⟨m0, hm0⟩ : ∃ m0, memLoad32 M (F + 0x38) = m0 := ⟨_, rfl⟩
  obtain ⟨m1, hm1⟩ : ∃ m1, memLoad32 M (F + 0x3C) = m1 := ⟨_, rfl⟩
  obtain ⟨w0, hw0⟩ : ∃ w0, memLoad32 M (F + 0x118) = w0 := ⟨_, rfl⟩
  obtain ⟨w1, hw1⟩ : ∃ w1, memLoad32 M (F + 0x11C) = w1 := ⟨_, rfl⟩
  rw [hm0, hm1] at hm
  -- save the mask
  obtain ⟨n1, c1, u1⟩ := St.block lmK8 s hc lmK8_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, lmK8, upd, ↓reduceIte, and_true, true_and]
    rw [rsp]
    exact ⟨al 0x38 rfl, al 0x3C rfl, ⟨al 0x38 rfl, c38⟩, ⟨al 0x3C rfl, c3c⟩, ⟨al 0x78 rfl, c78⟩, al 0x7C rfl, c7c⟩)
  obtain ⟨k8e, k8a0, k8a1, k8a2, k8a3, k8k⟩ := lmK8_run (M := M) (f := reg n) hz
  rw [k8e, rsp, hm0, hm1] at u1
  obtain ⟨M8, hM8⟩ : ∃ M8, memStore32 (memStore32 (memStore32 (memStore32 M (F + 0x38) 0) (F + 0x3C) 0)
      (F + 0x78) m0) (F + 0x7C) m1 = M8 := ⟨_, rfl⟩
  rw [hM8] at u1
  have hc8 : CodeIn M8 P lincombShiftMod12Code := by
    rw [← hM8]; exact (((hc.store32 c38).store32 c3c).store32 c78).store32 c7c
  have g1 : ∀ q, reg n1 q = (runBlock lmK8 (M, reg n)).2 q := u1.regs
  obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc8 0x160 lm12_at_15e (by decide)
    (by rw [g1, k8a3, u1.self.zero]; decide)
  have r2a0 : reg n2 a0 = F + 0x118 := by rw [u2.regs, g1, k8a0, rsp]
  have r2a1 : reg n2 a1 = F + 0x78 := by rw [u2.regs, g1, k8a1, rsp]
  have r2a2 : reg n2 a2 = F + 0x38 := by rw [u2.regs, g1, k8a2, rsp]
  have r2a3 : reg n2 a3 = 2 := by rw [u2.regs, g1, k8a3]
  have l8 : memLoad32 M8 (F + 0x118) = w0 ∧ memLoad32 M8 (F + 0x11C) = w1 ∧ memLoad32 M8 (F + 0x78) = m0 ∧
      memLoad32 M8 (F + 0x7C) = m1 := by
    rw [← hM8, ← hw0, ← hw1]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp (disch := decide) only [ls_lit, ls_same]
  -- AND the low words
  obtain ⟨n3, c3, u3⟩ := St.block lmK9 u2.self hc8 lmK9_end
    (lmK9_ok (by rw [r2a0, add_lit_zero]; exact al 0x118 rfl) (by rw [r2a1, add_lit_zero]; exact al 0x78 rfl)
      (by rw [r2a2, add_lit_zero]; exact al 0x38 rfl) (by rw [r2a2, add_lit_zero]; exact c38))
  obtain ⟨k9e, k9a0, k9a1, k9a2, k9a3, k9k⟩ := lmK9_run (M := M8) (f := reg n2) u2.self.zero
  rw [k9e, r2a0, r2a1, r2a2, add_lit_zero, add_lit_zero, add_lit_zero, l8.1, l8.2.2.1] at u3
  have hc3 := hc8.store32 (v := w0 &&& m0) c38
  have g3 : ∀ q, reg n3 q = (runBlock lmK9 (M8, reg n2)).2 q := u3.regs
  obtain ⟨n4, d4, u4⟩ := u3.self.taken hc3 0x160 lm12_at_170 (by decide)
    (by rw [g3, k9a3, r2a3, u3.self.zero]; decide)
  have e4 : ∀ c : Nat, F + BitVec.ofNat 32 c + 4 = F + BitVec.ofNat 32 (c + 4) := fun c => by
    rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]
  have r4a0 : reg n4 a0 = F + 0x11C := by rw [u4.regs, g3, k9a0, r2a0]; exact e4 0x118
  have r4a1 : reg n4 a1 = F + 0x7C := by rw [u4.regs, g3, k9a1, r2a1]; exact e4 0x78
  have r4a2 : reg n4 a2 = F + 0x3C := by rw [u4.regs, g3, k9a2, r2a2]; exact e4 0x38
  have r4a3 : reg n4 a3 = 1 := by rw [u4.regs, g3, k9a3, r2a3]; rfl
  -- AND the high words
  obtain ⟨n5, c5, u5⟩ := St.block lmK9 u4.self hc3 lmK9_end
    (lmK9_ok (by rw [r4a0, add_lit_zero]; exact al 0x11C rfl) (by rw [r4a1, add_lit_zero]; exact al 0x7C rfl)
      (by rw [r4a2, add_lit_zero]; exact al 0x3C rfl) (by rw [r4a2, add_lit_zero]; exact c3c))
  obtain ⟨k9e', k9a0', k9a1', k9a2', k9a3', k9k'⟩ := lmK9_run (M := memStore32 M8 (F + 0x38) (w0 &&& m0)) (f := reg n4)
    u4.self.zero
  have l9 : memLoad32 (memStore32 M8 (F + 0x38) (w0 &&& m0)) (F + 0x11C) = w1 ∧
      memLoad32 (memStore32 M8 (F + 0x38) (w0 &&& m0)) (F + 0x7C) = m1 := by
    refine ⟨?_, ?_⟩
    · simp (disch := decide) only [ls_lit]; exact l8.2.1
    · simp (disch := decide) only [ls_lit]; exact l8.2.2.2
  rw [k9e', r4a0, r4a1, r4a2, add_lit_zero, add_lit_zero, add_lit_zero, l9.1, l9.2] at u5
  have hc5 := hc3.store32 (v := w1 &&& m1) c3c
  have g5 : ∀ q, reg n5 q = (runBlock lmK9 (memStore32 M8 (F + 0x38) (w0 &&& m0), reg n4)).2 q := u5.regs
  obtain ⟨n6, d6, u6⟩ := u5.self.notTaken hc5 0x172 lm12_at_170 (by decide)
    (by rw [g5, k9a3', r4a3, u5.self.zero]; decide)
  -- copy back
  have r6sp : reg n6 sp = F := by
    rw [u6.regs, g5, k9k' sp (by decide), u4.regs, g3, k9k sp (by decide), u2.regs, g1, k8k sp (by decide), rsp]
  obtain ⟨n7, c7, u7⟩ := St.block lmK10 u6.self hc5 lmK10_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, lmK10, upd, ↓reduceIte, and_true, true_and]
    rw [r6sp]
    exact ⟨al 0x38 rfl, al 0x3C rfl, ⟨al 0x118 rfl, c118⟩, al 0x11C rfl, c11c⟩)
  obtain ⟨k10e, k10k⟩ := lmK10_run (M := memStore32 (memStore32 M8 (F + 0x38) (w0 &&& m0)) (F + 0x3C) (w1 &&& m1))
    (f := reg n6) u6.self.zero
  rw [k10e, r6sp] at u7
  have lA : memLoad32 (memStore32 (memStore32 M8 (F + 0x38) (w0 &&& m0)) (F + 0x3C) (w1 &&& m1)) (F + 0x38) = w0 &&& m0 ∧
      memLoad32 (memStore32 (memStore32 M8 (F + 0x38) (w0 &&& m0)) (F + 0x3C) (w1 &&& m1)) (F + 0x3C) = w1 &&& m1 := by
    refine ⟨?_, ?_⟩ <;> simp (disch := decide) only [ls_lit, ls_same]
  rw [lA.1, lA.2] at u7
  obtain ⟨MF, hMF⟩ : ∃ MF, memStore32 (memStore32 (memStore32 (memStore32 M8 (F + 0x38) (w0 &&& m0)) (F + 0x3C)
      (w1 &&& m1)) (F + 0x118) (w0 &&& m0)) (F + 0x11C) (w1 &&& m1) = MF := ⟨_, rfl⟩
  rw [hMF] at u7
  have hc7 : CodeIn MF P lincombShiftMod12Code := by
    rw [← hMF]; exact (hc5.store32 (v := w0 &&& m0) c118).store32 (v := w1 &&& m1) c11c
  have lF : memLoad32 MF (F + 0x118) = w0 &&& m0 ∧ memLoad32 MF (F + 0x11C) = w1 &&& m1 := by
    rw [← hMF]; refine ⟨?_, ?_⟩ <;> simp (disch := decide) only [ls_lit, ls_same]
  refine ⟨n7, MF, c1.trans (.cons d2 (c3.trans (.cons d4 (c5.trans (.cons d6 c7))))), u7.self, hc7,
    fun x h1 h2 h3 => ?_, ?_, fun q hq => ?_⟩
  · obtain ⟨x38, x3c⟩ := sc (c := 0x38) h1
    obtain ⟨x78, x7c⟩ := sc (c := 0x78) h2
    obtain ⟨x118, x11c⟩ := sc (c := 0x118) h3
    rw [← hMF, memStore32_get_sep (a := F + 0x11C) x11c, memStore32_get_sep (a := F + 0x118) x118,
      memStore32_get_sep (a := F + 0x3C) x3c, memStore32_get_sep (a := F + 0x38) x38, ← hM8,
      memStore32_get_sep (a := F + 0x7C) x7c, memStore32_get_sep (a := F + 0x78) x78,
      memStore32_get_sep (a := F + 0x3C) x3c, memStore32_get_sep (a := F + 0x38) x38]
  · rw [lF.1, lF.2, hw0, hw1]; exact hm w0 w1
  · rw [u7.regs, k10k q (nmem_of (by decide) hq), u6.regs, g5, k9k' q hq, u4.regs, g3, k9k q hq, u2.regs, g1,
      k8k q (nmem_of (by decide) hq)]

end C3.RV32
