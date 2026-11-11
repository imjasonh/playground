import C3BootProofs.Proofs.FieldWideArith
import C3BootProofs.Proofs.FieldSub
import C3BootProofs.Proofs.MemcpyAny
import C3BootProofs.Proofs.MemsetAny

/-!
# P-384's Montgomery multiplication, as compiled

`crypto_bigint`'s `mul_montgomery_form::<12>` multiplies two 12-limb numbers
in Montgomery form with `montgomery_multiply_inner`: an outer loop over the
first operand's limbs, each pass adding that limb times the second operand
and one multiple of the modulus that clears the low limb, and shifting the
accumulator down a limb. A final `try_sub_with_carry` subtracts the modulus
once if needed, with `borrowing_sub` and `Uint<12>::select`.

`square_montgomery_form::<12>` compiles the same loop with other registers,
so the loop body is stated once, over its registers (`mmBody`).
-/

namespace C3.RV32

open C3.Image

section

set_option maxRecDepth 20000

theorem mm_at_0 : fetchRel mulMont12Code 0x0 = some (.aluImm .add sp sp 0xFFFFFF60, 2) := by decide
theorem mm_at_2 : fetchRel mulMont12Code 0x2 = some (.auipc (5 : Fin 32) 0xD000, 4) := by decide
theorem mm_at_6 : fetchRel mulMont12Code 0x6 = some (.jalr (5 : Fin 32) (5 : Fin 32) 0xFFFFFB98, 4) := by decide
theorem mm_at_a : fetchRel mulMont12Code 0xA = some (.alu .add (19 : Fin 32) x0 a4, 2) := by decide
theorem mm_at_c : fetchRel mulMont12Code 0xC = some (.alu .add (23 : Fin 32) x0 a3, 2) := by decide
theorem mm_at_e : fetchRel mulMont12Code 0xE = some (.alu .add (21 : Fin 32) x0 a2, 2) := by decide
theorem mm_at_10 : fetchRel mulMont12Code 0x10 = some (.alu .add (20 : Fin 32) x0 a1, 2) := by decide
theorem mm_at_12 : fetchRel mulMont12Code 0x12 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem mm_at_14 : fetchRel mulMont12Code 0x14 = some (.aluImm .add a0 sp 0xC, 2) := by decide
theorem mm_at_16 : fetchRel mulMont12Code 0x16 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem mm_at_1a : fetchRel mulMont12Code 0x1A = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem mm_at_1c : fetchRel mulMont12Code 0x1C = some (.auipc ra 0xD000, 4) := by decide
theorem mm_at_20 : fetchRel mulMont12Code 0x20 = some (.jalr ra ra 0x2D8, 4) := by decide
theorem mm_at_24 : fetchRel mulMont12Code 0x24 = some (.auipc (5 : Fin 32) 0xD000, 4) := by decide
theorem mm_at_28 : fetchRel mulMont12Code 0x28 = some (.jalr (5 : Fin 32) (5 : Fin 32) 0x1C, 4) := by decide
theorem mm_at_2c : fetchRel mulMont12Code 0x2C = some (.aluImm .add (5 : Fin 32) x0 0xC, 2) := by decide
theorem mm_at_2e : fetchRel mulMont12Code 0x2E = some (.branch .beq (5 : Fin 32) x0 0xB4, 4) := by decide
theorem mm_at_32 : fetchRel mulMont12Code 0x32 = some (.aluImm .sll a0 (29 : Fin 32) 0x2, 4) := by decide
theorem mm_at_36 : fetchRel mulMont12Code 0x36 = some (.alu .add a0 a0 (20 : Fin 32), 2) := by decide
theorem mm_at_38 : fetchRel mulMont12Code 0x38 = some (.load .lw (30 : Fin 32) a0 0x0, 4) := by decide
theorem mm_at_3c : fetchRel mulMont12Code 0x3C = some (.alu .mul a0 (6 : Fin 32) (30 : Fin 32), 4) := by decide
theorem mm_at_40 : fetchRel mulMont12Code 0x40 = some (.load .lw a1 sp 0xC, 2) := by decide
theorem mm_at_42 : fetchRel mulMont12Code 0x42 = some (.alu .add a1 a1 a0, 2) := by decide
theorem mm_at_44 : fetchRel mulMont12Code 0x44 = some (.alu .mul (31 : Fin 32) (19 : Fin 32) a1, 4) := by decide
theorem mm_at_48 : fetchRel mulMont12Code 0x48 = some (.alu .mulhu a2 (6 : Fin 32) (30 : Fin 32), 4) := by decide
theorem mm_at_4c : fetchRel mulMont12Code 0x4C = some (.alu .mul a3 (31 : Fin 32) (7 : Fin 32), 4) := by decide
theorem mm_at_50 : fetchRel mulMont12Code 0x50 = some (.alu .mulhu (9 : Fin 32) (31 : Fin 32) (7 : Fin 32), 4) := by decide
theorem mm_at_54 : fetchRel mulMont12Code 0x54 = some (.alu .sltu a0 a1 a0, 4) := by decide
theorem mm_at_58 : fetchRel mulMont12Code 0x58 = some (.alu .add a0 a0 a2, 2) := by decide
theorem mm_at_5a : fetchRel mulMont12Code 0x5A = some (.alu .add a1 a1 a3, 2) := by decide
theorem mm_at_5c : fetchRel mulMont12Code 0x5C = some (.alu .add a0 a0 (9 : Fin 32), 2) := by decide
theorem mm_at_5e : fetchRel mulMont12Code 0x5E = some (.alu .sltu a2 a1 a3, 4) := by decide
theorem mm_at_62 : fetchRel mulMont12Code 0x62 = some (.aluImm .add (25 : Fin 32) x0 0xB, 2) := by decide
theorem mm_at_64 : fetchRel mulMont12Code 0x64 = some (.alu .add a2 a2 a0, 2) := by decide
theorem mm_at_66 : fetchRel mulMont12Code 0x66 = some (.alu .sltu a3 a0 (9 : Fin 32), 4) := by decide
theorem mm_at_6a : fetchRel mulMont12Code 0x6A = some (.alu .sltu a0 a2 a0, 4) := by decide
theorem mm_at_6e : fetchRel mulMont12Code 0x6E = some (.alu .add (26 : Fin 32) x0 (17 : Fin 32), 2) := by decide
theorem mm_at_70 : fetchRel mulMont12Code 0x70 = some (.alu .add (24 : Fin 32) a3 a0, 4) := by decide
theorem mm_at_74 : fetchRel mulMont12Code 0x74 = some (.alu .add a3 x0 a6, 2) := by decide
theorem mm_at_76 : fetchRel mulMont12Code 0x76 = some (.alu .add (9 : Fin 32) x0 (21 : Fin 32), 2) := by decide
theorem mm_at_78 : fetchRel mulMont12Code 0x78 = some (.branch .beq (25 : Fin 32) x0 0x52, 4) := by decide
theorem mm_at_7c : fetchRel mulMont12Code 0x7C = some (.load .lw a4 (26 : Fin 32) 0x0, 4) := by decide
theorem mm_at_80 : fetchRel mulMont12Code 0x80 = some (.load .lw a5 (9 : Fin 32) 0x0, 2) := by decide
theorem mm_at_82 : fetchRel mulMont12Code 0x82 = some (.alu .mulhu a0 a4 (31 : Fin 32), 4) := by decide
theorem mm_at_86 : fetchRel mulMont12Code 0x86 = some (.alu .mul (8 : Fin 32) a5 (30 : Fin 32), 4) := by decide
theorem mm_at_8a : fetchRel mulMont12Code 0x8A = some (.alu .mul a4 a4 (31 : Fin 32), 4) := by decide
theorem mm_at_8e : fetchRel mulMont12Code 0x8E = some (.load .lw a1 a3 0x0, 2) := by decide
theorem mm_at_90 : fetchRel mulMont12Code 0x90 = some (.alu .mulhu a5 a5 (30 : Fin 32), 4) := by decide
theorem mm_at_94 : fetchRel mulMont12Code 0x94 = some (.alu .add a0 a0 (24 : Fin 32), 2) := by decide
theorem mm_at_96 : fetchRel mulMont12Code 0x96 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x4, 2) := by decide
theorem mm_at_98 : fetchRel mulMont12Code 0x98 = some (.alu .add a1 a1 (8 : Fin 32), 2) := by decide
theorem mm_at_9a : fetchRel mulMont12Code 0x9A = some (.alu .add a2 a2 a4, 2) := by decide
theorem mm_at_9c : fetchRel mulMont12Code 0x9C = some (.alu .sltu (8 : Fin 32) a1 (8 : Fin 32), 4) := by decide
theorem mm_at_a0 : fetchRel mulMont12Code 0xA0 = some (.alu .sltu a4 a2 a4, 4) := by decide
theorem mm_at_a4 : fetchRel mulMont12Code 0xA4 = some (.alu .add a1 a1 a2, 2) := by decide
theorem mm_at_a6 : fetchRel mulMont12Code 0xA6 = some (.alu .add a5 a5 (8 : Fin 32), 2) := by decide
theorem mm_at_a8 : fetchRel mulMont12Code 0xA8 = some (.alu .add a0 a0 a4, 2) := by decide
theorem mm_at_aa : fetchRel mulMont12Code 0xAA = some (.alu .sltu a2 a1 a2, 4) := by decide
theorem mm_at_ae : fetchRel mulMont12Code 0xAE = some (.alu .add a5 a5 a0, 2) := by decide
theorem mm_at_b0 : fetchRel mulMont12Code 0xB0 = some (.store .sw a3 a1 0xFFFFFFFC, 4) := by decide
theorem mm_at_b4 : fetchRel mulMont12Code 0xB4 = some (.alu .add a2 a2 a5, 2) := by decide
theorem mm_at_b6 : fetchRel mulMont12Code 0xB6 = some (.alu .sltu (24 : Fin 32) a5 a0, 4) := by decide
theorem mm_at_ba : fetchRel mulMont12Code 0xBA = some (.alu .sltu a0 a2 a5, 4) := by decide
theorem mm_at_be : fetchRel mulMont12Code 0xBE = some (.aluImm .add a3 a3 0x4, 2) := by decide
theorem mm_at_c0 : fetchRel mulMont12Code 0xC0 = some (.alu .add (24 : Fin 32) (24 : Fin 32) a0, 2) := by decide
theorem mm_at_c2 : fetchRel mulMont12Code 0xC2 = some (.aluImm .add (26 : Fin 32) (26 : Fin 32) 0x4, 2) := by decide
theorem mm_at_c4 : fetchRel mulMont12Code 0xC4 = some (.aluImm .add (25 : Fin 32) (25 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem mm_at_c6 : fetchRel mulMont12Code 0xC6 = some (.branch .bne (25 : Fin 32) x0 0xFFFFFFB6, 4) := by decide
theorem mm_at_ca : fetchRel mulMont12Code 0xCA = some (.alu .add (22 : Fin 32) (22 : Fin 32) a2, 2) := by decide
theorem mm_at_cc : fetchRel mulMont12Code 0xCC = some (.alu .add a0 (24 : Fin 32) (28 : Fin 32), 4) := by decide
theorem mm_at_d0 : fetchRel mulMont12Code 0xD0 = some (.alu .sltu a1 (22 : Fin 32) a2, 4) := by decide
theorem mm_at_d4 : fetchRel mulMont12Code 0xD4 = some (.store .sw sp (22 : Fin 32) 0x38, 2) := by decide
theorem mm_at_d6 : fetchRel mulMont12Code 0xD6 = some (.alu .add (22 : Fin 32) a0 a1, 4) := by decide
theorem mm_at_da : fetchRel mulMont12Code 0xDA = some (.aluImm .add (29 : Fin 32) (29 : Fin 32) 0x1, 2) := by decide
theorem mm_at_dc : fetchRel mulMont12Code 0xDC = some (.aluImm .add (28 : Fin 32) x0 0x0, 2) := by decide
theorem mm_at_de : fetchRel mulMont12Code 0xDE = some (.branch .bne (29 : Fin 32) (5 : Fin 32) 0xFFFFFF54, 4) := by decide
theorem mm_at_e2 : fetchRel mulMont12Code 0xE2 = some (.aluImm .add a0 sp 0x3C, 2) := by decide
theorem mm_at_e4 : fetchRel mulMont12Code 0xE4 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem mm_at_e8 : fetchRel mulMont12Code 0xE8 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem mm_at_ea : fetchRel mulMont12Code 0xEA = some (.aluImm .add (19 : Fin 32) sp 0x3C, 4) := by decide
theorem mm_at_ee : fetchRel mulMont12Code 0xEE = some (.auipc ra 0xD000, 4) := by decide
theorem mm_at_f2 : fetchRel mulMont12Code 0xF2 = some (.jalr ra ra 0x206, 4) := by decide
theorem mm_at_f6 : fetchRel mulMont12Code 0xF6 = some (.aluImm .add a2 x0 0x0, 2) := by decide
theorem mm_at_f8 : fetchRel mulMont12Code 0xF8 = some (.aluImm .add (9 : Fin 32) sp 0xC, 2) := by decide
theorem mm_at_fa : fetchRel mulMont12Code 0xFA = some (.aluImm .add (8 : Fin 32) x0 0xC, 2) := by decide
theorem mm_at_fc : fetchRel mulMont12Code 0xFC = some (.branch .beq (8 : Fin 32) x0 0x20, 2) := by decide
theorem mm_at_fe : fetchRel mulMont12Code 0xFE = some (.load .lw a0 (9 : Fin 32) 0x0, 2) := by decide
theorem mm_at_100 : fetchRel mulMont12Code 0x100 = some (.load .lw a1 (23 : Fin 32) 0x0, 4) := by decide
theorem mm_at_104 : fetchRel mulMont12Code 0x104 = some (.auipc ra 0xFFFF0000, 4) := by decide
theorem mm_at_108 : fetchRel mulMont12Code 0x108 = some (.jalr ra ra 0xFFFFFE86, 4) := by decide
theorem mm_at_10c : fetchRel mulMont12Code 0x10C = some (.alu .add a2 x0 a1, 2) := by decide
theorem mm_at_10e : fetchRel mulMont12Code 0x10E = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x4, 2) := by decide
theorem mm_at_110 : fetchRel mulMont12Code 0x110 = some (.store .sw (19 : Fin 32) a0 0x0, 4) := by decide
theorem mm_at_114 : fetchRel mulMont12Code 0x114 = some (.aluImm .add (23 : Fin 32) (23 : Fin 32) 0x4, 2) := by decide
theorem mm_at_116 : fetchRel mulMont12Code 0x116 = some (.aluImm .add (19 : Fin 32) (19 : Fin 32) 0x4, 2) := by decide
theorem mm_at_118 : fetchRel mulMont12Code 0x118 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem mm_at_11a : fetchRel mulMont12Code 0x11A = some (.branch .bne (8 : Fin 32) x0 0xFFFFFFE4, 2) := by decide
theorem mm_at_11c : fetchRel mulMont12Code 0x11C = some (.store .sw sp (22 : Fin 32) 0x6C, 2) := by decide
theorem mm_at_11e : fetchRel mulMont12Code 0x11E = some (.aluImm .add a0 sp 0x6C, 2) := by decide
theorem mm_at_120 : fetchRel mulMont12Code 0x120 = some (.load .lw a0 sp 0x6C, 2) := by decide
theorem mm_at_122 : fetchRel mulMont12Code 0x122 = some (.aluImm .sltu (9 : Fin 32) a0 0x1, 4) := by decide
theorem mm_at_126 : fetchRel mulMont12Code 0x126 = some (.alu .and (9 : Fin 32) (9 : Fin 32) a2, 2) := by decide
theorem mm_at_128 : fetchRel mulMont12Code 0x128 = some (.store .sb sp (9 : Fin 32) 0x6C, 4) := by decide
theorem mm_at_12c : fetchRel mulMont12Code 0x12C = some (.aluImm .add a0 sp 0x6C, 2) := by decide
theorem mm_at_12e : fetchRel mulMont12Code 0x12E = some (.load .lbu a0 sp 0x6C, 4) := by decide
theorem mm_at_132 : fetchRel mulMont12Code 0x132 = some (.aluImm .add a0 a0 0xFFFFFFFF, 2) := by decide
theorem mm_at_134 : fetchRel mulMont12Code 0x134 = some (.alu .and a2 a2 a0, 2) := by decide
theorem mm_at_136 : fetchRel mulMont12Code 0x136 = some (.alu .add a0 x0 (22 : Fin 32), 2) := by decide
theorem mm_at_138 : fetchRel mulMont12Code 0x138 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem mm_at_13a : fetchRel mulMont12Code 0x13A = some (.auipc ra 0xFFFF0000, 4) := by decide
theorem mm_at_13e : fetchRel mulMont12Code 0x13E = some (.jalr ra ra 0xFFFFFE50, 4) := by decide
theorem mm_at_142 : fetchRel mulMont12Code 0x142 = some (.aluImm .add a1 sp 0x3C, 2) := by decide
theorem mm_at_144 : fetchRel mulMont12Code 0x144 = some (.aluImm .add a2 sp 0xC, 2) := by decide
theorem mm_at_146 : fetchRel mulMont12Code 0x146 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem mm_at_148 : fetchRel mulMont12Code 0x148 = some (.alu .add a3 x0 (9 : Fin 32), 2) := by decide
theorem mm_at_14a : fetchRel mulMont12Code 0x14A = some (.auipc ra 0x0, 4) := by decide
theorem mm_at_14e : fetchRel mulMont12Code 0x14E = some (.jalr ra ra 0x14, 4) := by decide
theorem mm_at_152 : fetchRel mulMont12Code 0x152 = some (.auipc (5 : Fin 32) 0xD000, 4) := by decide
theorem mm_at_156 : fetchRel mulMont12Code 0x156 = some (.jalr (5 : Fin 32) (5 : Fin 32) 0xFFFFFA96, 4) := by decide
theorem mm_at_15a : fetchRel mulMont12Code 0x15A = some (.aluImm .add sp sp 0xA0, 2) := by decide
theorem mm_at_15c : fetchRel mulMont12Code 0x15C = some (.jalr x0 ra 0x0, 2) := by decide
theorem us_at_0 : fetchRel uintSelect12Code 0x0 = some (.aluImm .add sp sp 0xFFFFFFB0, 2) := by decide
theorem us_at_2 : fetchRel uintSelect12Code 0x2 = some (.store .sw sp ra 0x4C, 2) := by decide
theorem us_at_4 : fetchRel uintSelect12Code 0x4 = some (.store .sw sp (8 : Fin 32) 0x48, 2) := by decide
theorem us_at_6 : fetchRel uintSelect12Code 0x6 = some (.store .sw sp (9 : Fin 32) 0x44, 2) := by decide
theorem us_at_8 : fetchRel uintSelect12Code 0x8 = some (.store .sw sp (18 : Fin 32) 0x40, 2) := by decide
theorem us_at_a : fetchRel uintSelect12Code 0xA = some (.store .sw sp (19 : Fin 32) 0x3C, 2) := by decide
theorem us_at_c : fetchRel uintSelect12Code 0xC = some (.store .sw sp (20 : Fin 32) 0x38, 2) := by decide
theorem us_at_e : fetchRel uintSelect12Code 0xE = some (.alu .add (19 : Fin 32) x0 a3, 2) := by decide
theorem us_at_10 : fetchRel uintSelect12Code 0x10 = some (.alu .add (20 : Fin 32) x0 a2, 2) := by decide
theorem us_at_12 : fetchRel uintSelect12Code 0x12 = some (.alu .add (9 : Fin 32) x0 a1, 2) := by decide
theorem us_at_14 : fetchRel uintSelect12Code 0x14 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem us_at_16 : fetchRel uintSelect12Code 0x16 = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem us_at_18 : fetchRel uintSelect12Code 0x18 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem us_at_1c : fetchRel uintSelect12Code 0x1C = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem us_at_1e : fetchRel uintSelect12Code 0x1E = some (.aluImm .add (8 : Fin 32) sp 0x4, 2) := by decide
theorem us_at_20 : fetchRel uintSelect12Code 0x20 = some (.auipc ra 0xD000, 4) := by decide
theorem us_at_24 : fetchRel uintSelect12Code 0x24 = some (.jalr ra ra 0x176, 4) := by decide
theorem us_at_28 : fetchRel uintSelect12Code 0x28 = some (.aluImm .add a0 x0 0xC, 2) := by decide
theorem us_at_2a : fetchRel uintSelect12Code 0x2A = some (.aluImm .add a1 sp 0x37, 4) := by decide
theorem us_at_2e : fetchRel uintSelect12Code 0x2E = some (.branch .beq a0 x0 0x1A, 2) := by decide
theorem us_at_30 : fetchRel uintSelect12Code 0x30 = some (.load .lw a2 (9 : Fin 32) 0x0, 2) := by decide
theorem us_at_32 : fetchRel uintSelect12Code 0x32 = some (.store .sb sp (19 : Fin 32) 0x37, 4) := by decide
theorem us_at_36 : fetchRel uintSelect12Code 0x36 = some (.load .lw a3 (20 : Fin 32) 0x0, 4) := by decide
theorem us_at_3a : fetchRel uintSelect12Code 0x3A = some (.load .lbu a4 sp 0x37, 4) := by decide
theorem us_at_3e : fetchRel uintSelect12Code 0x3E = some (.auipc (5 : Fin 32) 0xD000, 4) := by decide
theorem us_at_42 : fetchRel uintSelect12Code 0x42 = some (.jalr (5 : Fin 32) (5 : Fin 32) 0xFFFFFFB0, 4) := by decide
theorem us_at_46 : fetchRel uintSelect12Code 0x46 = some (.branch .bne a0 x0 0xFFFFFFEA, 2) := by decide
theorem us_at_48 : fetchRel uintSelect12Code 0x48 = some (.aluImm .add a1 sp 0x4, 2) := by decide
theorem us_at_4a : fetchRel uintSelect12Code 0x4A = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem us_at_4e : fetchRel uintSelect12Code 0x4E = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem us_at_50 : fetchRel uintSelect12Code 0x50 = some (.auipc ra 0xD000, 4) := by decide
theorem us_at_54 : fetchRel uintSelect12Code 0x54 = some (.jalr ra ra 0x1AE, 4) := by decide
theorem us_at_58 : fetchRel uintSelect12Code 0x58 = some (.load .lw ra sp 0x4C, 2) := by decide
theorem us_at_5a : fetchRel uintSelect12Code 0x5A = some (.load .lw (8 : Fin 32) sp 0x48, 2) := by decide
theorem us_at_5c : fetchRel uintSelect12Code 0x5C = some (.load .lw (9 : Fin 32) sp 0x44, 2) := by decide
theorem us_at_5e : fetchRel uintSelect12Code 0x5E = some (.load .lw (18 : Fin 32) sp 0x40, 2) := by decide
theorem us_at_60 : fetchRel uintSelect12Code 0x60 = some (.load .lw (19 : Fin 32) sp 0x3C, 2) := by decide
theorem us_at_62 : fetchRel uintSelect12Code 0x62 = some (.load .lw (20 : Fin 32) sp 0x38, 2) := by decide
theorem us_at_64 : fetchRel uintSelect12Code 0x64 = some (.aluImm .add sp sp 0x50, 2) := by decide
theorem us_at_66 : fetchRel uintSelect12Code 0x66 = some (.jalr x0 ra 0x0, 2) := by decide

end

/-- One column of the compiled Montgomery loop, as the instructions compute
it: the word stored, then the two-word carry out. -/
def mmCols (N Y O U X CL CH : Word) : Word × Word × Word :=
  let th0 := aluEval .mulhu N U
  let tl0 := aluEval .mul Y X
  let tn1 := aluEval .mul N U
  let ty1 := aluEval .mulhu Y X
  let th1 := aluEval .add th0 CH
  let ta1 := aluEval .add O tl0
  let cl1 := aluEval .add CL tn1
  let tl1 := aluEval .sltu ta1 tl0
  let tn2 := aluEval .sltu cl1 tn1
  let ta2 := aluEval .add ta1 cl1
  let ty2 := aluEval .add ty1 tl1
  let th2 := aluEval .add th1 tn2
  let cl2 := aluEval .sltu ta2 cl1
  let ty3 := aluEval .add ty2 th2
  let cl3 := aluEval .add cl2 ty3
  let ch1 := aluEval .sltu ty3 th2
  let th3 := aluEval .sltu cl3 ty3
  (ta2, cl3, aluEval .add ch1 th3)

theorem add_toNat (x y : Word) : (aluEval .add x y).toNat = (x.toNat + y.toNat) % 2 ^ 32 := by
  show (x + y).toNat = _; rw [BitVec.toNat_add]

theorem carry_le1 {s a c : Word} (h : s.toNat + 2 ^ 32 * c.toNat = a.toNat + a.toNat) : c.toNat ≤ 1 := by
  have := s.isLt; have := a.isLt; omega

set_option maxHeartbeats 2000000 in
theorem mm_step (N Y O U X CL CH : Word) (hc : CL.toNat + 2 ^ 32 * CH.toNat ≤ 2 * 2 ^ 32 - 2) :
    (mmCols N Y O U X CL CH).1.toNat + 2 ^ 32 * ((mmCols N Y O U X CL CH).2.1.toNat +
        2 ^ 32 * (mmCols N Y O U X CL CH).2.2.toNat) =
      X.toNat * Y.toNat + O.toNat + U.toNat * N.toNat + CL.toNat + 2 ^ 32 * CH.toNat ∧
    (mmCols N Y O U X CL CH).2.1.toNat + 2 ^ 32 * (mmCols N Y O U X CL CH).2.2.toNat ≤ 2 * 2 ^ 32 - 2 := by
  unfold mmCols
  simp only
  have e0 := mul_mulhu N U
  have e1 := mul_mulhu Y X
  have e2 := add_carry O (aluEval .mul Y X)
  have e3 := add_carry CL (aluEval .mul N U)
  have a1 := add_toNat (aluEval .mulhu N U) CH
  generalize aluEval .mulhu N U = th0 at e0 a1 ⊢
  generalize aluEval .mul Y X = tl0 at e1 e2 ⊢
  generalize aluEval .mul N U = tn1 at e0 e3 ⊢
  generalize aluEval .mulhu Y X = ty1 at e1 ⊢
  generalize aluEval .add th0 CH = th1 at a1 ⊢
  generalize aluEval .add O tl0 = ta1 at e2 ⊢
  generalize aluEval .add CL tn1 = cl1 at e3 ⊢
  generalize aluEval .sltu ta1 tl0 = tl1 at e2 ⊢
  generalize aluEval .sltu cl1 tn1 = tn2 at e3 ⊢
  have e4 := add_carry ta1 cl1
  have a2 := add_toNat ty1 tl1
  have a3 := add_toNat th1 tn2
  generalize aluEval .add ta1 cl1 = ta2 at e4 ⊢
  generalize aluEval .add ty1 tl1 = ty2 at a2 ⊢
  generalize aluEval .add th1 tn2 = th2 at a3 ⊢
  generalize aluEval .sltu ta2 cl1 = cl2 at e4 ⊢
  have e5 := add_carry ty2 th2
  generalize aluEval .add ty2 th2 = ty3 at e5 ⊢
  have e6 := add_carry cl2 ty3
  generalize aluEval .add cl2 ty3 = cl3 at e6 ⊢
  generalize aluEval .sltu ty3 th2 = ch1 at e5 ⊢
  generalize aluEval .sltu cl3 ty3 = th3 at e6 ⊢
  have a4 := add_toNat ch1 th3
  generalize aluEval .add ch1 th3 = ch2 at a4 ⊢
  have hN := N.isLt; have hY := Y.isLt; have hU := U.isLt; have hX := X.isLt
  have P1 : N.toNat * U.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have P2 : Y.toNat * X.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
  rw [Nat.mul_comm X.toNat Y.toNat, Nat.mul_comm U.toNat N.toNat]
  generalize N.toNat * U.toNat = p1 at e0 P1 ⊢
  generalize Y.toNat * X.toNat = p2 at e1 P2 ⊢
  have := th0.isLt; have := tl0.isLt; have := tn1.isLt; have := ty1.isLt; have := th1.isLt; have := ta1.isLt
  have := cl1.isLt; have := tl1.isLt; have := tn2.isLt; have := ta2.isLt; have := ty2.isLt; have := th2.isLt
  have := cl2.isLt; have := ty3.isLt; have := cl3.isLt; have := ch1.isLt; have := th3.isLt; have := ch2.isLt
  have := O.isLt; have := CL.isLt; have := CH.isLt
  have hth0 : th0.toNat ≤ 2 ^ 32 - 2 := by omega
  have hty1 : ty1.toNat ≤ 2 ^ 32 - 2 := by omega
  have hCH : CH.toNat ≤ 1 := by omega
  have h1 : th1.toNat = th0.toNat + CH.toNat := by rw [a1]; exact Nat.mod_eq_of_lt (by omega)
  have htl1 : tl1.toNat ≤ 1 := by omega
  have htn2 : tn2.toNat ≤ 1 := by omega
  have hcl2 : cl2.toNat ≤ 1 := by omega
  have h2 : ty2.toNat = ty1.toNat + tl1.toNat := by rw [a2]; exact Nat.mod_eq_of_lt (by omega)
  have hsum : tn2.toNat + th0.toNat + CH.toNat ≤ 2 ^ 32 - 1 := by omega
  have h3 : th2.toNat = th1.toNat + tn2.toNat := by rw [a3]; exact Nat.mod_eq_of_lt (by omega)
  have hch1 : ch1.toNat ≤ 1 := by omega
  have hth3 : th3.toNat ≤ 1 := by omega
  have h4 : ch2.toNat = ch1.toNat + th3.toNat := by rw [a4]; exact Nat.mod_eq_of_lt (by omega)
  rw [h4]
  constructor
  · omega
  · omega

/-- The first column of a pass of the compiled Montgomery loop: the factor
`u`, then the two-word carry out. The column's own word is zero. -/
def mmHead (Y0 X O0 K N0 : Word) : Word × Word × Word :=
  let a0 := aluEval .mul Y0 X
  let a1 := aluEval .add O0 a0
  let u := aluEval .mul K a1
  let a2 := aluEval .mulhu Y0 X
  let a3 := aluEval .mul u N0
  let s1 := aluEval .mulhu u N0
  let c1 := aluEval .sltu a1 a0
  let h1 := aluEval .add c1 a2
  let lo := aluEval .add a1 a3
  let h2 := aluEval .add h1 s1
  let c2 := aluEval .sltu lo a3
  let cl := aluEval .add c2 h2
  let o1 := aluEval .sltu h2 s1
  let o2 := aluEval .sltu cl h2
  (u, cl, aluEval .add o1 o2)

theorem mont_low {s k n : Nat} (h : (k * n + 1) % 2 ^ 32 = 0) : (s + k * s % 2 ^ 32 * n % 2 ^ 32) % 2 ^ 32 = 0 := by
  rw [Nat.add_mod, Nat.mod_mod, Nat.mul_mod (k * s % 2 ^ 32) n, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod,
    show s + k * s * n = s * (k * n + 1) by rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm s, Nat.mul_assoc,
      Nat.mul_comm s n, ← Nat.mul_assoc, Nat.add_comm], Nat.mul_mod, h, Nat.mul_zero, Nat.zero_mod]

set_option maxHeartbeats 2000000 in
theorem mm_head (Y0 X O0 K N0 : Word) (hk : (K.toNat * N0.toNat + 1) % 2 ^ 32 = 0) :
    X.toNat * Y0.toNat + O0.toNat + (mmHead Y0 X O0 K N0).1.toNat * N0.toNat =
      2 ^ 32 * ((mmHead Y0 X O0 K N0).2.1.toNat + 2 ^ 32 * (mmHead Y0 X O0 K N0).2.2.toNat) ∧
    (mmHead Y0 X O0 K N0).2.1.toNat + 2 ^ 32 * (mmHead Y0 X O0 K N0).2.2.toNat ≤ 2 * 2 ^ 32 - 2 := by
  unfold mmHead
  simp only
  have e1 := mul_mulhu Y0 X
  have e2 := add_carry O0 (aluEval .mul Y0 X)
  have hu : (aluEval .mul K (aluEval .add O0 (aluEval .mul Y0 X))).toNat =
      K.toNat * (aluEval .add O0 (aluEval .mul Y0 X)).toNat % 2 ^ 32 := by
    show (K * _).toNat = _; rw [BitVec.toNat_mul]
  have e3 := mul_mulhu (aluEval .mul K (aluEval .add O0 (aluEval .mul Y0 X))) N0
  have hlun : (aluEval .mul (aluEval .mul K (aluEval .add O0 (aluEval .mul Y0 X))) N0).toNat =
      (aluEval .mul K (aluEval .add O0 (aluEval .mul Y0 X))).toNat * N0.toNat % 2 ^ 32 := by
    show (_ * N0).toNat = _; rw [BitVec.toNat_mul]
  generalize aluEval .mul Y0 X = a0 at e1 e2 hu hlun e3 ⊢
  generalize aluEval .add O0 a0 = a1 at e2 hu hlun e3 ⊢
  generalize aluEval .mul K a1 = u at hu hlun e3 ⊢
  generalize aluEval .mulhu Y0 X = a2 at e1 ⊢
  generalize aluEval .mul u N0 = a3 at e3 hlun ⊢
  generalize aluEval .mulhu u N0 = s1 at e3 ⊢
  generalize aluEval .sltu a1 a0 = c1 at e2 ⊢
  have b1 := add_toNat c1 a2
  generalize aluEval .add c1 a2 = h1 at b1 ⊢
  have e4 := add_carry a1 a3
  generalize aluEval .add a1 a3 = lo at e4 ⊢
  have e5 := add_carry h1 s1
  generalize aluEval .add h1 s1 = h2 at e5 ⊢
  generalize aluEval .sltu lo a3 = c2 at e4 ⊢
  have e6 := add_carry c2 h2
  generalize aluEval .add c2 h2 = cl at e6 ⊢
  generalize aluEval .sltu h2 s1 = o1 at e5 ⊢
  generalize aluEval .sltu cl h2 = o2 at e6 ⊢
  have b2 := add_toNat o1 o2
  generalize aluEval .add o1 o2 = ch at b2 ⊢
  have hlo : lo.toNat = 0 := by
    have h0 := mont_low (s := a1.toNat) hk
    rw [← hu, ← hlun] at h0
    have := lo.isLt; have := a1.isLt; have := a3.isLt
    have : lo.toNat = (a1.toNat + a3.toNat) % 2 ^ 32 := by omega
    omega
  have hY := Y0.isLt; have hX := X.isLt; have hN := N0.isLt; have hU := u.isLt
  have P1 : Y0.toNat * X.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have P2 : u.toNat * N0.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
  rw [Nat.mul_comm X.toNat Y0.toNat]
  generalize Y0.toNat * X.toNat = p1 at e1 P1 ⊢
  generalize u.toNat * N0.toNat = p2 at e3 P2 hlun ⊢
  have := a0.isLt; have := a1.isLt; have := a2.isLt; have := a3.isLt; have := s1.isLt; have := c1.isLt
  have := h1.isLt; have := h2.isLt; have := c2.isLt; have := cl.isLt; have := o1.isLt; have := o2.isLt
  have := ch.isLt; have := O0.isLt
  have ha2 : a2.toNat ≤ 2 ^ 32 - 2 := by omega
  have hc1 : c1.toNat ≤ 1 := by omega
  have hh1 : h1.toNat = c1.toNat + a2.toNat := by rw [b1]; exact Nat.mod_eq_of_lt (by omega)
  have ho1 : o1.toNat ≤ 1 := by omega
  have ho2 : o2.toNat ≤ 1 := by omega
  have hch : ch.toNat = o1.toNat + o2.toNat := by rw [b2]; exact Nat.mod_eq_of_lt (by omega)
  rw [hch]
  constructor
  · omega
  · omega


/-- One pass of the inner loop, over its registers: the modulus pointer
`pn`, the second operand's pointer `py`, the accumulator pointer `po`, the
factor `u`, the first operand's limb `xi`, the carry `cl` and `ch`, the
count `cnt`, and five scratch registers. -/
def mmBody (pn py po u xi cl ch cnt tn ty th tl ta : Fin 32) : List BInstr :=
  [.lw tn pn 0, .lw ty py 0, .alu .mulhu th tn u, .alu .mul tl ty xi, .alu .mul tn tn u, .lw ta po 0,
   .alu .mulhu ty ty xi, .alu .add th th ch, .aluImm .add py py 4, .alu .add ta ta tl, .alu .add cl cl tn,
   .alu .sltu tl ta tl, .alu .sltu tn cl tn, .alu .add ta ta cl, .alu .add ty ty tl, .alu .add th th tn,
   .alu .sltu cl ta cl, .alu .add ty ty th, .sw po ta 0xFFFFFFFC, .alu .add cl cl ty, .alu .sltu ch ty th,
   .alu .sltu th cl ty, .aluImm .add po po 4, .alu .add ch ch th, .aluImm .add pn pn 4,
   .aluImm .add cnt cnt 0xFFFFFFFF]

/-- The loop body in `mul_montgomery_form::<12>`. -/
abbrev mmBodyM : List BInstr :=
  mmBody (26 : Fin 32) (9 : Fin 32) a3 (31 : Fin 32) (30 : Fin 32) a2 (24 : Fin 32) (25 : Fin 32) a4 a5 a0
    (8 : Fin 32) a1

section
set_option maxRecDepth 20000
theorem mmBodyM_end : blockEnd mulMont12Code 0x7C mmBodyM = some 0xC6 := by decide
end

set_option maxRecDepth 20000 in
theorem mmBodyM_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock mmBodyM (M, f)).1 = memStore32 M (f a3 + 0xFFFFFFFC)
        (mmCols (memLoad32 M (f (26 : Fin 32) + 0)) (memLoad32 M (f (9 : Fin 32) + 0)) (memLoad32 M (f a3 + 0))
          (f (31 : Fin 32)) (f (30 : Fin 32)) (f a2) (f (24 : Fin 32))).1 ∧
    (runBlock mmBodyM (M, f)).2 a2 = (mmCols (memLoad32 M (f (26 : Fin 32) + 0)) (memLoad32 M (f (9 : Fin 32) + 0))
        (memLoad32 M (f a3 + 0)) (f (31 : Fin 32)) (f (30 : Fin 32)) (f a2) (f (24 : Fin 32))).2.1 ∧
    (runBlock mmBodyM (M, f)).2 (24 : Fin 32) = (mmCols (memLoad32 M (f (26 : Fin 32) + 0))
        (memLoad32 M (f (9 : Fin 32) + 0)) (memLoad32 M (f a3 + 0)) (f (31 : Fin 32)) (f (30 : Fin 32)) (f a2)
        (f (24 : Fin 32))).2.2 ∧
    (runBlock mmBodyM (M, f)).2 (26 : Fin 32) = f (26 : Fin 32) + 4 ∧
    (runBlock mmBodyM (M, f)).2 (9 : Fin 32) = f (9 : Fin 32) + 4 ∧
    (runBlock mmBodyM (M, f)).2 a3 = f a3 + 4 ∧
    (runBlock mmBodyM (M, f)).2 (25 : Fin 32) = f (25 : Fin 32) + 0xFFFFFFFF ∧
    ∀ q, q ≠ (26 : Fin 32) → q ≠ (9 : Fin 32) → q ≠ a3 → q ≠ a2 → q ≠ (24 : Fin 32) → q ≠ (25 : Fin 32) →
      q ≠ a4 → q ≠ a5 → q ≠ a0 → q ≠ (8 : Fin 32) → q ≠ a1 → (runBlock mmBodyM (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, mmBody]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q q26 q9 q13 q12 q24 q25 q14 q15 q10 q8 q11 => ?_⟩
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · by_cases hq : q.val = 0
    · have : q = 0 := Fin.ext hq
      subst this; simp [upd, hz]
    · simp [upd, hq, q26, q9, q13, q12, q24, q25, q14, q15, q10, q8, q11]

theorem mmBodyM_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (hn : (f (26 : Fin 32) + 0).toNat % 4 = 0) (hy : (f (9 : Fin 32) + 0).toNat % 4 = 0)
    (ho : (f a3 + 0).toNat % 4 = 0) (hs : (f a3 + 0xFFFFFFFC).toNat % 4 = 0)
    (hsep : Sep (f a3 + 0xFFFFFFFC) 4 base len) : BlockOk base len mmBodyM (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, mmBody, upd, ↓reduceIte, true_and, and_true]
  exact ⟨hn, hy, ho, hs, hsep⟩

end C3.RV32
