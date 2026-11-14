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

end C3.RV32
