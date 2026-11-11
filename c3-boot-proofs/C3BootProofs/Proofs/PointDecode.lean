import C3BootProofs.Proofs.Block

/-!
# The P-256 field addition, subtraction, doubling, and point addition, decoded

`scripts/decode-lemmas.py` wrote these from `llvm-objdump` output; `decide`
checks each against the extracted bytes.
-/

namespace C3.RV32

open C3.ImageV0

set_option maxRecDepth 20000

theorem fa_at_0 : fetchRel fieldAddCode 0x0 = some (.aluImm .add sp sp 0xFFFFFF80, 2) := by decide
theorem fa_at_2 : fetchRel fieldAddCode 0x2 = some (.store .sw sp ra 0x7C, 2) := by decide
theorem fa_at_4 : fetchRel fieldAddCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x78, 2) := by decide
theorem fa_at_6 : fetchRel fieldAddCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x74, 2) := by decide
theorem fa_at_8 : fetchRel fieldAddCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x70, 2) := by decide
theorem fa_at_a : fetchRel fieldAddCode 0xA = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem fa_at_c : fetchRel fieldAddCode 0xC = some (.load .lw a6 a1 0x0, 4) := by decide
theorem fa_at_10 : fetchRel fieldAddCode 0x10 = some (.load .lw a3 a2 0x0, 2) := by decide
theorem fa_at_12 : fetchRel fieldAddCode 0x12 = some (.load .lw a4 a2 0x4, 2) := by decide
theorem fa_at_14 : fetchRel fieldAddCode 0x14 = some (.load .lw (5 : Fin 32) a1 0x4, 4) := by decide
theorem fa_at_18 : fetchRel fieldAddCode 0x18 = some (.load .lw (6 : Fin 32) a1 0x8, 4) := by decide
theorem fa_at_1c : fetchRel fieldAddCode 0x1C = some (.load .lw (17 : Fin 32) a1 0xC, 4) := by decide
theorem fa_at_20 : fetchRel fieldAddCode 0x20 = some (.load .lw a5 a2 0x8, 2) := by decide
theorem fa_at_22 : fetchRel fieldAddCode 0x22 = some (.load .lw a0 a2 0xC, 2) := by decide
theorem fa_at_24 : fetchRel fieldAddCode 0x24 = some (.alu .add a6 a6 a3, 2) := by decide
theorem fa_at_26 : fetchRel fieldAddCode 0x26 = some (.alu .add (5 : Fin 32) (5 : Fin 32) a4, 2) := by decide
theorem fa_at_28 : fetchRel fieldAddCode 0x28 = some (.alu .sltu a3 a6 a3, 4) := by decide
theorem fa_at_2c : fetchRel fieldAddCode 0x2C = some (.alu .add (7 : Fin 32) (5 : Fin 32) a3, 4) := by decide
theorem fa_at_30 : fetchRel fieldAddCode 0x30 = some (.alu .sltu a4 (5 : Fin 32) a4, 4) := by decide
theorem fa_at_34 : fetchRel fieldAddCode 0x34 = some (.alu .sltu a3 (7 : Fin 32) (5 : Fin 32), 4) := by decide
theorem fa_at_38 : fetchRel fieldAddCode 0x38 = some (.alu .add (6 : Fin 32) (6 : Fin 32) a5, 2) := by decide
theorem fa_at_3a : fetchRel fieldAddCode 0x3A = some (.alu .add a3 a3 a4, 2) := by decide
theorem fa_at_3c : fetchRel fieldAddCode 0x3C = some (.load .lw (5 : Fin 32) a1 0x10, 4) := by decide
theorem fa_at_40 : fetchRel fieldAddCode 0x40 = some (.alu .add (28 : Fin 32) (6 : Fin 32) a3, 4) := by decide
theorem fa_at_44 : fetchRel fieldAddCode 0x44 = some (.alu .sltu a5 (6 : Fin 32) a5, 4) := by decide
theorem fa_at_48 : fetchRel fieldAddCode 0x48 = some (.alu .sltu a4 (28 : Fin 32) (6 : Fin 32), 4) := by decide
theorem fa_at_4c : fetchRel fieldAddCode 0x4C = some (.alu .add (17 : Fin 32) (17 : Fin 32) a0, 2) := by decide
theorem fa_at_4e : fetchRel fieldAddCode 0x4E = some (.alu .add a4 a4 a5, 2) := by decide
theorem fa_at_50 : fetchRel fieldAddCode 0x50 = some (.load .lw a5 a2 0x10, 2) := by decide
theorem fa_at_52 : fetchRel fieldAddCode 0x52 = some (.alu .add (6 : Fin 32) (17 : Fin 32) a4, 4) := by decide
theorem fa_at_56 : fetchRel fieldAddCode 0x56 = some (.alu .sltu a0 (17 : Fin 32) a0, 4) := by decide
theorem fa_at_5a : fetchRel fieldAddCode 0x5A = some (.alu .sltu a3 (6 : Fin 32) (17 : Fin 32), 4) := by decide
theorem fa_at_5e : fetchRel fieldAddCode 0x5E = some (.alu .add (17 : Fin 32) a0 a3, 4) := by decide
theorem fa_at_62 : fetchRel fieldAddCode 0x62 = some (.load .lw (29 : Fin 32) a1 0x14, 4) := by decide
theorem fa_at_66 : fetchRel fieldAddCode 0x66 = some (.load .lw (30 : Fin 32) a1 0x18, 4) := by decide
theorem fa_at_6a : fetchRel fieldAddCode 0x6A = some (.load .lw a1 a1 0x1C, 2) := by decide
theorem fa_at_6c : fetchRel fieldAddCode 0x6C = some (.load .lw a0 a2 0x14, 2) := by decide
theorem fa_at_6e : fetchRel fieldAddCode 0x6E = some (.load .lw a3 a2 0x18, 2) := by decide
theorem fa_at_70 : fetchRel fieldAddCode 0x70 = some (.load .lw a2 a2 0x1C, 2) := by decide
theorem fa_at_72 : fetchRel fieldAddCode 0x72 = some (.alu .add (5 : Fin 32) (5 : Fin 32) a5, 2) := by decide
theorem fa_at_74 : fetchRel fieldAddCode 0x74 = some (.alu .add (17 : Fin 32) (17 : Fin 32) (5 : Fin 32), 2) := by decide
theorem fa_at_76 : fetchRel fieldAddCode 0x76 = some (.alu .sltu a5 (5 : Fin 32) a5, 4) := by decide
theorem fa_at_7a : fetchRel fieldAddCode 0x7A = some (.alu .sltu a4 (17 : Fin 32) (5 : Fin 32), 4) := by decide
theorem fa_at_7e : fetchRel fieldAddCode 0x7E = some (.alu .add a4 a4 a5, 2) := by decide
theorem fa_at_80 : fetchRel fieldAddCode 0x80 = some (.alu .add (29 : Fin 32) (29 : Fin 32) a0, 2) := by decide
theorem fa_at_82 : fetchRel fieldAddCode 0x82 = some (.alu .add a4 a4 (29 : Fin 32), 2) := by decide
theorem fa_at_84 : fetchRel fieldAddCode 0x84 = some (.alu .sltu a0 (29 : Fin 32) a0, 4) := by decide
theorem fa_at_88 : fetchRel fieldAddCode 0x88 = some (.alu .sltu a5 a4 (29 : Fin 32), 4) := by decide
theorem fa_at_8c : fetchRel fieldAddCode 0x8C = some (.alu .add a0 a0 a5, 2) := by decide
theorem fa_at_8e : fetchRel fieldAddCode 0x8E = some (.alu .add (30 : Fin 32) (30 : Fin 32) a3, 2) := by decide
theorem fa_at_90 : fetchRel fieldAddCode 0x90 = some (.alu .add a0 a0 (30 : Fin 32), 2) := by decide
theorem fa_at_92 : fetchRel fieldAddCode 0x92 = some (.alu .sltu a3 (30 : Fin 32) a3, 4) := by decide
theorem fa_at_96 : fetchRel fieldAddCode 0x96 = some (.alu .sltu a5 a0 (30 : Fin 32), 4) := by decide
theorem fa_at_9a : fetchRel fieldAddCode 0x9A = some (.alu .add a3 a3 a5, 2) := by decide
theorem fa_at_9c : fetchRel fieldAddCode 0x9C = some (.alu .add a1 a1 a2, 2) := by decide
theorem fa_at_9e : fetchRel fieldAddCode 0x9E = some (.alu .add a3 a3 a1, 2) := by decide
theorem fa_at_a0 : fetchRel fieldAddCode 0xA0 = some (.alu .sltu a2 a1 a2, 4) := by decide
theorem fa_at_a4 : fetchRel fieldAddCode 0xA4 = some (.alu .sltu a1 a3 a1, 4) := by decide
theorem fa_at_a8 : fetchRel fieldAddCode 0xA8 = some (.alu .add a1 a1 a2, 2) := by decide
theorem fa_at_aa : fetchRel fieldAddCode 0xAA = some (.store .sw sp a6 0x28, 2) := by decide
theorem fa_at_ac : fetchRel fieldAddCode 0xAC = some (.store .sw sp (7 : Fin 32) 0x2C, 2) := by decide
theorem fa_at_ae : fetchRel fieldAddCode 0xAE = some (.store .sw sp (28 : Fin 32) 0x30, 2) := by decide
theorem fa_at_b0 : fetchRel fieldAddCode 0xB0 = some (.store .sw sp (6 : Fin 32) 0x34, 2) := by decide
theorem fa_at_b2 : fetchRel fieldAddCode 0xB2 = some (.store .sw sp (17 : Fin 32) 0x38, 2) := by decide
theorem fa_at_b4 : fetchRel fieldAddCode 0xB4 = some (.store .sw sp a4 0x3C, 2) := by decide
theorem fa_at_b6 : fetchRel fieldAddCode 0xB6 = some (.store .sw sp a0 0x40, 2) := by decide
theorem fa_at_b8 : fetchRel fieldAddCode 0xB8 = some (.store .sw sp a3 0x44, 2) := by decide
theorem fa_at_ba : fetchRel fieldAddCode 0xBA = some (.store .sw sp a1 0x48, 2) := by decide
theorem fa_at_bc : fetchRel fieldAddCode 0xBC = some (.aluImm .add a0 x0 0xFFFFFFFF, 2) := by decide
theorem fa_at_be : fetchRel fieldAddCode 0xBE = some (.store .sw sp a0 0x4C, 2) := by decide
theorem fa_at_c0 : fetchRel fieldAddCode 0xC0 = some (.store .sw sp a0 0x50, 2) := by decide
theorem fa_at_c2 : fetchRel fieldAddCode 0xC2 = some (.store .sw sp a0 0x54, 2) := by decide
theorem fa_at_c4 : fetchRel fieldAddCode 0xC4 = some (.store .sw sp x0 0x58, 2) := by decide
theorem fa_at_c6 : fetchRel fieldAddCode 0xC6 = some (.aluImm .add a1 x0 0x1, 2) := by decide
theorem fa_at_c8 : fetchRel fieldAddCode 0xC8 = some (.store .sw sp x0 0x5C, 2) := by decide
theorem fa_at_ca : fetchRel fieldAddCode 0xCA = some (.store .sw sp x0 0x60, 2) := by decide
theorem fa_at_cc : fetchRel fieldAddCode 0xCC = some (.store .sw sp a1 0x64, 2) := by decide
theorem fa_at_ce : fetchRel fieldAddCode 0xCE = some (.store .sw sp a0 0x68, 2) := by decide
theorem fa_at_d0 : fetchRel fieldAddCode 0xD0 = some (.store .sw sp x0 0x6C, 2) := by decide
theorem fa_at_d2 : fetchRel fieldAddCode 0xD2 = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem fa_at_d4 : fetchRel fieldAddCode 0xD4 = some (.aluImm .add a1 sp 0x28, 2) := by decide
theorem fa_at_d6 : fetchRel fieldAddCode 0xD6 = some (.aluImm .add a2 sp 0x4C, 2) := by decide
theorem fa_at_d8 : fetchRel fieldAddCode 0xD8 = some (.auipc ra 0x0, 4) := by decide
theorem fa_at_dc : fetchRel fieldAddCode 0xDC = some (.jalr ra ra 0xFFFFFBD2, 4) := by decide
theorem fa_at_e0 : fetchRel fieldAddCode 0xE0 = some (.load .lw a0 sp 0x4, 2) := by decide
theorem fa_at_e2 : fetchRel fieldAddCode 0xE2 = some (.load .lw a1 sp 0x8, 2) := by decide
theorem fa_at_e4 : fetchRel fieldAddCode 0xE4 = some (.load .lw a2 sp 0xC, 2) := by decide
theorem fa_at_e6 : fetchRel fieldAddCode 0xE6 = some (.load .lw a3 sp 0x10, 2) := by decide
theorem fa_at_e8 : fetchRel fieldAddCode 0xE8 = some (.load .lw a4 sp 0x14, 2) := by decide
theorem fa_at_ea : fetchRel fieldAddCode 0xEA = some (.load .lw a5 sp 0x18, 2) := by decide
theorem fa_at_ec : fetchRel fieldAddCode 0xEC = some (.load .lw (8 : Fin 32) sp 0x1C, 2) := by decide
theorem fa_at_ee : fetchRel fieldAddCode 0xEE = some (.load .lw (9 : Fin 32) sp 0x20, 2) := by decide
theorem fa_at_f0 : fetchRel fieldAddCode 0xF0 = some (.store .sw (18 : Fin 32) a0 0x0, 4) := by decide
theorem fa_at_f4 : fetchRel fieldAddCode 0xF4 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem fa_at_f6 : fetchRel fieldAddCode 0xF6 = some (.store .sw a0 a1 0x4, 2) := by decide
theorem fa_at_f8 : fetchRel fieldAddCode 0xF8 = some (.store .sw a0 a2 0x8, 2) := by decide
theorem fa_at_fa : fetchRel fieldAddCode 0xFA = some (.store .sw a0 a3 0xC, 2) := by decide
theorem fa_at_fc : fetchRel fieldAddCode 0xFC = some (.store .sw a0 a4 0x10, 2) := by decide
theorem fa_at_fe : fetchRel fieldAddCode 0xFE = some (.store .sw a0 a5 0x14, 2) := by decide
theorem fa_at_100 : fetchRel fieldAddCode 0x100 = some (.store .sw a0 (8 : Fin 32) 0x18, 2) := by decide
theorem fa_at_102 : fetchRel fieldAddCode 0x102 = some (.store .sw a0 (9 : Fin 32) 0x1C, 2) := by decide
theorem fa_at_104 : fetchRel fieldAddCode 0x104 = some (.load .lw ra sp 0x7C, 2) := by decide
theorem fa_at_106 : fetchRel fieldAddCode 0x106 = some (.load .lw (8 : Fin 32) sp 0x78, 2) := by decide
theorem fa_at_108 : fetchRel fieldAddCode 0x108 = some (.load .lw (9 : Fin 32) sp 0x74, 2) := by decide
theorem fa_at_10a : fetchRel fieldAddCode 0x10A = some (.load .lw (18 : Fin 32) sp 0x70, 2) := by decide
theorem fa_at_10c : fetchRel fieldAddCode 0x10C = some (.aluImm .add sp sp 0x80, 2) := by decide
theorem fa_at_10e : fetchRel fieldAddCode 0x10E = some (.jalr x0 ra 0x0, 2) := by decide
theorem fs_at_0 : fetchRel fieldSubCode 0x0 = some (.aluImm .add sp sp 0xFFFFFF80, 2) := by decide
theorem fs_at_2 : fetchRel fieldSubCode 0x2 = some (.store .sw sp ra 0x7C, 2) := by decide
theorem fs_at_4 : fetchRel fieldSubCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x78, 2) := by decide
theorem fs_at_6 : fetchRel fieldSubCode 0x6 = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem fs_at_8 : fetchRel fieldSubCode 0x8 = some (.load .lw a0 a1 0x0, 2) := by decide
theorem fs_at_a : fetchRel fieldSubCode 0xA = some (.load .lw a3 a1 0x4, 2) := by decide
theorem fs_at_c : fetchRel fieldSubCode 0xC = some (.load .lw a4 a1 0x8, 2) := by decide
theorem fs_at_e : fetchRel fieldSubCode 0xE = some (.load .lw a5 a1 0xC, 2) := by decide
theorem fs_at_10 : fetchRel fieldSubCode 0x10 = some (.load .lw a6 a1 0x10, 4) := by decide
theorem fs_at_14 : fetchRel fieldSubCode 0x14 = some (.load .lw (17 : Fin 32) a1 0x14, 4) := by decide
theorem fs_at_18 : fetchRel fieldSubCode 0x18 = some (.load .lw (5 : Fin 32) a1 0x18, 4) := by decide
theorem fs_at_1c : fetchRel fieldSubCode 0x1C = some (.load .lw a1 a1 0x1C, 2) := by decide
theorem fs_at_1e : fetchRel fieldSubCode 0x1E = some (.store .sw sp a0 0x30, 2) := by decide
theorem fs_at_20 : fetchRel fieldSubCode 0x20 = some (.store .sw sp a3 0x34, 2) := by decide
theorem fs_at_22 : fetchRel fieldSubCode 0x22 = some (.store .sw sp a4 0x38, 2) := by decide
theorem fs_at_24 : fetchRel fieldSubCode 0x24 = some (.store .sw sp a5 0x3C, 2) := by decide
theorem fs_at_26 : fetchRel fieldSubCode 0x26 = some (.store .sw sp a6 0x40, 2) := by decide
theorem fs_at_28 : fetchRel fieldSubCode 0x28 = some (.store .sw sp (17 : Fin 32) 0x44, 2) := by decide
theorem fs_at_2a : fetchRel fieldSubCode 0x2A = some (.store .sw sp (5 : Fin 32) 0x48, 2) := by decide
theorem fs_at_2c : fetchRel fieldSubCode 0x2C = some (.store .sw sp a1 0x4C, 2) := by decide
theorem fs_at_2e : fetchRel fieldSubCode 0x2E = some (.store .sw sp x0 0x50, 2) := by decide
theorem fs_at_30 : fetchRel fieldSubCode 0x30 = some (.load .lw a0 a2 0x0, 2) := by decide
theorem fs_at_32 : fetchRel fieldSubCode 0x32 = some (.load .lw a1 a2 0x4, 2) := by decide
theorem fs_at_34 : fetchRel fieldSubCode 0x34 = some (.load .lw a3 a2 0x8, 2) := by decide
theorem fs_at_36 : fetchRel fieldSubCode 0x36 = some (.load .lw a4 a2 0xC, 2) := by decide
theorem fs_at_38 : fetchRel fieldSubCode 0x38 = some (.load .lw a5 a2 0x10, 2) := by decide
theorem fs_at_3a : fetchRel fieldSubCode 0x3A = some (.load .lw a6 a2 0x14, 4) := by decide
theorem fs_at_3e : fetchRel fieldSubCode 0x3E = some (.load .lw (17 : Fin 32) a2 0x18, 4) := by decide
theorem fs_at_42 : fetchRel fieldSubCode 0x42 = some (.load .lw a2 a2 0x1C, 2) := by decide
theorem fs_at_44 : fetchRel fieldSubCode 0x44 = some (.store .sw sp a0 0x54, 2) := by decide
theorem fs_at_46 : fetchRel fieldSubCode 0x46 = some (.store .sw sp a1 0x58, 2) := by decide
theorem fs_at_48 : fetchRel fieldSubCode 0x48 = some (.store .sw sp a3 0x5C, 2) := by decide
theorem fs_at_4a : fetchRel fieldSubCode 0x4A = some (.store .sw sp a4 0x60, 2) := by decide
theorem fs_at_4c : fetchRel fieldSubCode 0x4C = some (.store .sw sp a5 0x64, 2) := by decide
theorem fs_at_4e : fetchRel fieldSubCode 0x4E = some (.store .sw sp a6 0x68, 2) := by decide
theorem fs_at_50 : fetchRel fieldSubCode 0x50 = some (.store .sw sp (17 : Fin 32) 0x6C, 2) := by decide
theorem fs_at_52 : fetchRel fieldSubCode 0x52 = some (.store .sw sp a2 0x70, 2) := by decide
theorem fs_at_54 : fetchRel fieldSubCode 0x54 = some (.store .sw sp x0 0x74, 2) := by decide
theorem fs_at_56 : fetchRel fieldSubCode 0x56 = some (.aluImm .add a0 sp 0xC, 2) := by decide
theorem fs_at_58 : fetchRel fieldSubCode 0x58 = some (.aluImm .add a1 sp 0x30, 2) := by decide
theorem fs_at_5a : fetchRel fieldSubCode 0x5A = some (.aluImm .add a2 sp 0x54, 2) := by decide
theorem fs_at_5c : fetchRel fieldSubCode 0x5C = some (.auipc ra 0x0, 4) := by decide
theorem fs_at_60 : fetchRel fieldSubCode 0x60 = some (.jalr ra ra 0xFFFFFB2C, 4) := by decide
theorem fs_at_64 : fetchRel fieldSubCode 0x64 = some (.load .lw a0 sp 0xC, 2) := by decide
theorem fs_at_66 : fetchRel fieldSubCode 0x66 = some (.load .lw a1 sp 0x10, 2) := by decide
theorem fs_at_68 : fetchRel fieldSubCode 0x68 = some (.load .lw a2 sp 0x14, 2) := by decide
theorem fs_at_6a : fetchRel fieldSubCode 0x6A = some (.load .lw a3 sp 0x18, 2) := by decide
theorem fs_at_6c : fetchRel fieldSubCode 0x6C = some (.load .lw a4 sp 0x1C, 2) := by decide
theorem fs_at_6e : fetchRel fieldSubCode 0x6E = some (.load .lw a5 sp 0x20, 2) := by decide
theorem fs_at_70 : fetchRel fieldSubCode 0x70 = some (.load .lw a6 sp 0x24, 2) := by decide
theorem fs_at_72 : fetchRel fieldSubCode 0x72 = some (.load .lw (17 : Fin 32) sp 0x28, 2) := by decide
theorem fs_at_74 : fetchRel fieldSubCode 0x74 = some (.store .sw (8 : Fin 32) a0 0x0, 2) := by decide
theorem fs_at_76 : fetchRel fieldSubCode 0x76 = some (.store .sw (8 : Fin 32) a1 0x4, 2) := by decide
theorem fs_at_78 : fetchRel fieldSubCode 0x78 = some (.store .sw (8 : Fin 32) a2 0x8, 2) := by decide
theorem fs_at_7a : fetchRel fieldSubCode 0x7A = some (.store .sw (8 : Fin 32) a3 0xC, 2) := by decide
theorem fs_at_7c : fetchRel fieldSubCode 0x7C = some (.store .sw (8 : Fin 32) a4 0x10, 2) := by decide
theorem fs_at_7e : fetchRel fieldSubCode 0x7E = some (.store .sw (8 : Fin 32) a5 0x14, 2) := by decide
theorem fs_at_80 : fetchRel fieldSubCode 0x80 = some (.store .sw (8 : Fin 32) a6 0x18, 4) := by decide
theorem fs_at_84 : fetchRel fieldSubCode 0x84 = some (.store .sw (8 : Fin 32) (17 : Fin 32) 0x1C, 4) := by decide
theorem fs_at_88 : fetchRel fieldSubCode 0x88 = some (.load .lw ra sp 0x7C, 2) := by decide
theorem fs_at_8a : fetchRel fieldSubCode 0x8A = some (.load .lw (8 : Fin 32) sp 0x78, 2) := by decide
theorem fs_at_8c : fetchRel fieldSubCode 0x8C = some (.aluImm .add sp sp 0x80, 2) := by decide
theorem fs_at_8e : fetchRel fieldSubCode 0x8E = some (.jalr x0 ra 0x0, 2) := by decide
theorem fd_at_0 : fetchRel fieldDoubleCode 0x0 = some (.alu .add a2 x0 a1, 2) := by decide
theorem fd_at_2 : fetchRel fieldDoubleCode 0x2 = some (.auipc (6 : Fin 32) 0x0, 4) := by decide
theorem fd_at_6 : fetchRel fieldDoubleCode 0x6 = some (.jalr x0 (6 : Fin 32) 0xFFFFFCF8, 4) := by decide
theorem pa_at_0 : fetchRel pointAddCode 0x0 = some (.aluImm .add sp sp 0xFFFFFDC0, 4) := by decide
theorem pa_at_4 : fetchRel pointAddCode 0x4 = some (.aluImm .add a2 sp 0x200, 2) := by decide
theorem pa_at_6 : fetchRel pointAddCode 0x6 = some (.store .sw a2 ra 0x3C, 4) := by decide
theorem pa_at_a : fetchRel pointAddCode 0xA = some (.store .sw a2 (8 : Fin 32) 0x38, 2) := by decide
theorem pa_at_c : fetchRel pointAddCode 0xC = some (.store .sw a2 (9 : Fin 32) 0x34, 2) := by decide
theorem pa_at_e : fetchRel pointAddCode 0xE = some (.store .sw a2 (18 : Fin 32) 0x30, 4) := by decide
theorem pa_at_12 : fetchRel pointAddCode 0x12 = some (.store .sw a2 (19 : Fin 32) 0x2C, 4) := by decide
theorem pa_at_16 : fetchRel pointAddCode 0x16 = some (.store .sw a2 (20 : Fin 32) 0x28, 4) := by decide
theorem pa_at_1a : fetchRel pointAddCode 0x1A = some (.store .sw a2 (21 : Fin 32) 0x24, 4) := by decide
theorem pa_at_1e : fetchRel pointAddCode 0x1E = some (.alu .add (9 : Fin 32) x0 a1, 2) := by decide
theorem pa_at_20 : fetchRel pointAddCode 0x20 = some (.alu .add (20 : Fin 32) x0 a0, 2) := by decide
theorem pa_at_22 : fetchRel pointAddCode 0x22 = some (.aluImm .add a0 sp 0x64, 2) := by decide
theorem pa_at_24 : fetchRel pointAddCode 0x24 = some (.alu .add a1 x0 (20 : Fin 32), 2) := by decide
theorem pa_at_26 : fetchRel pointAddCode 0x26 = some (.alu .add a2 x0 (9 : Fin 32), 2) := by decide
theorem pa_at_28 : fetchRel pointAddCode 0x28 = some (.auipc ra 0xF000, 4) := by decide
theorem pa_at_2c : fetchRel pointAddCode 0x2C = some (.jalr ra ra 0xFFFFF810, 4) := by decide
theorem pa_at_30 : fetchRel pointAddCode 0x30 = some (.aluImm .add (19 : Fin 32) (20 : Fin 32) 0x20, 4) := by decide
theorem pa_at_34 : fetchRel pointAddCode 0x34 = some (.aluImm .add (21 : Fin 32) (9 : Fin 32) 0x20, 4) := by decide
theorem pa_at_38 : fetchRel pointAddCode 0x38 = some (.aluImm .add a0 sp 0x104, 2) := by decide
theorem pa_at_3a : fetchRel pointAddCode 0x3A = some (.alu .add a1 x0 (19 : Fin 32), 2) := by decide
theorem pa_at_3c : fetchRel pointAddCode 0x3C = some (.alu .add a2 x0 (21 : Fin 32), 2) := by decide
theorem pa_at_3e : fetchRel pointAddCode 0x3E = some (.auipc ra 0xE000, 4) := by decide
theorem pa_at_42 : fetchRel pointAddCode 0x42 = some (.jalr ra ra 0x7FA, 4) := by decide
theorem pa_at_46 : fetchRel pointAddCode 0x46 = some (.aluImm .add (18 : Fin 32) (20 : Fin 32) 0x40, 4) := by decide
theorem pa_at_4a : fetchRel pointAddCode 0x4A = some (.aluImm .add (8 : Fin 32) (9 : Fin 32) 0x40, 4) := by decide
theorem pa_at_4e : fetchRel pointAddCode 0x4E = some (.aluImm .add a0 sp 0x24, 2) := by decide
theorem pa_at_50 : fetchRel pointAddCode 0x50 = some (.alu .add a1 x0 (18 : Fin 32), 2) := by decide
theorem pa_at_52 : fetchRel pointAddCode 0x52 = some (.alu .add a2 x0 (8 : Fin 32), 2) := by decide
theorem pa_at_54 : fetchRel pointAddCode 0x54 = some (.auipc ra 0xE000, 4) := by decide
theorem pa_at_58 : fetchRel pointAddCode 0x58 = some (.jalr ra ra 0x7E4, 4) := by decide
theorem pa_at_5c : fetchRel pointAddCode 0x5C = some (.aluImm .add a0 sp 0xA4, 2) := by decide
theorem pa_at_5e : fetchRel pointAddCode 0x5E = some (.alu .add a1 x0 (20 : Fin 32), 2) := by decide
theorem pa_at_60 : fetchRel pointAddCode 0x60 = some (.alu .add a2 x0 (19 : Fin 32), 2) := by decide
theorem pa_at_62 : fetchRel pointAddCode 0x62 = some (.auipc ra 0xF000, 4) := by decide
theorem pa_at_66 : fetchRel pointAddCode 0x66 = some (.jalr ra ra 0xFFFFFF28, 4) := by decide
theorem pa_at_6a : fetchRel pointAddCode 0x6A = some (.aluImm .add a0 sp 0xC4, 2) := by decide
theorem pa_at_6c : fetchRel pointAddCode 0x6C = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem pa_at_6e : fetchRel pointAddCode 0x6E = some (.alu .add a2 x0 (21 : Fin 32), 2) := by decide
theorem pa_at_70 : fetchRel pointAddCode 0x70 = some (.auipc ra 0xF000, 4) := by decide
theorem pa_at_74 : fetchRel pointAddCode 0x74 = some (.jalr ra ra 0xFFFFFF1A, 4) := by decide
theorem pa_at_78 : fetchRel pointAddCode 0x78 = some (.aluImm .add a0 sp 0x84, 2) := by decide
theorem pa_at_7a : fetchRel pointAddCode 0x7A = some (.aluImm .add a1 sp 0xA4, 2) := by decide
theorem pa_at_7c : fetchRel pointAddCode 0x7C = some (.aluImm .add a2 sp 0xC4, 2) := by decide
theorem pa_at_7e : fetchRel pointAddCode 0x7E = some (.auipc ra 0xE000, 4) := by decide
theorem pa_at_82 : fetchRel pointAddCode 0x82 = some (.jalr ra ra 0x7BA, 4) := by decide
theorem pa_at_86 : fetchRel pointAddCode 0x86 = some (.aluImm .add a0 sp 0xC4, 2) := by decide
theorem pa_at_88 : fetchRel pointAddCode 0x88 = some (.aluImm .add a1 sp 0x64, 2) := by decide
theorem pa_at_8a : fetchRel pointAddCode 0x8A = some (.aluImm .add a2 sp 0x104, 2) := by decide
theorem pa_at_8c : fetchRel pointAddCode 0x8C = some (.auipc ra 0xF000, 4) := by decide
theorem pa_at_90 : fetchRel pointAddCode 0x90 = some (.jalr ra ra 0xFFFFFEFE, 4) := by decide
theorem pa_at_94 : fetchRel pointAddCode 0x94 = some (.aluImm .add a0 sp 0x184, 2) := by decide
theorem pa_at_96 : fetchRel pointAddCode 0x96 = some (.aluImm .add a1 sp 0x84, 2) := by decide
theorem pa_at_98 : fetchRel pointAddCode 0x98 = some (.aluImm .add a2 sp 0xC4, 2) := by decide
theorem pa_at_9a : fetchRel pointAddCode 0x9A = some (.auipc ra 0xF000, 4) := by decide
theorem pa_at_9e : fetchRel pointAddCode 0x9E = some (.jalr ra ra 0x12, 4) := by decide
theorem pa_at_a2 : fetchRel pointAddCode 0xA2 = some (.aluImm .add a0 sp 0xA4, 2) := by decide
theorem pa_at_a4 : fetchRel pointAddCode 0xA4 = some (.alu .add a1 x0 (19 : Fin 32), 2) := by decide
theorem pa_at_a6 : fetchRel pointAddCode 0xA6 = some (.alu .add a2 x0 (18 : Fin 32), 2) := by decide
theorem pa_at_a8 : fetchRel pointAddCode 0xA8 = some (.auipc ra 0xF000, 4) := by decide
theorem pa_at_ac : fetchRel pointAddCode 0xAC = some (.jalr ra ra 0xFFFFFEE2, 4) := by decide
theorem pa_at_b0 : fetchRel pointAddCode 0xB0 = some (.aluImm .add a0 sp 0xC4, 2) := by decide
theorem pa_at_b2 : fetchRel pointAddCode 0xB2 = some (.alu .add a1 x0 (21 : Fin 32), 2) := by decide
theorem pa_at_b4 : fetchRel pointAddCode 0xB4 = some (.alu .add a2 x0 (8 : Fin 32), 2) := by decide
theorem pa_at_b6 : fetchRel pointAddCode 0xB6 = some (.auipc ra 0xF000, 4) := by decide
theorem pa_at_ba : fetchRel pointAddCode 0xBA = some (.jalr ra ra 0xFFFFFED4, 4) := by decide
theorem pa_at_be : fetchRel pointAddCode 0xBE = some (.aluImm .add a0 sp 0x84, 2) := by decide
theorem pa_at_c0 : fetchRel pointAddCode 0xC0 = some (.aluImm .add a1 sp 0xA4, 2) := by decide
theorem pa_at_c2 : fetchRel pointAddCode 0xC2 = some (.aluImm .add a2 sp 0xC4, 2) := by decide
theorem pa_at_c4 : fetchRel pointAddCode 0xC4 = some (.auipc ra 0xE000, 4) := by decide
theorem pa_at_c8 : fetchRel pointAddCode 0xC8 = some (.jalr ra ra 0x774, 4) := by decide
theorem pa_at_cc : fetchRel pointAddCode 0xCC = some (.aluImm .add a0 sp 0xC4, 2) := by decide
theorem pa_at_ce : fetchRel pointAddCode 0xCE = some (.aluImm .add a1 sp 0x104, 2) := by decide
theorem pa_at_d0 : fetchRel pointAddCode 0xD0 = some (.aluImm .add a2 sp 0x24, 2) := by decide
theorem pa_at_d2 : fetchRel pointAddCode 0xD2 = some (.auipc ra 0xF000, 4) := by decide
theorem pa_at_d6 : fetchRel pointAddCode 0xD6 = some (.jalr ra ra 0xFFFFFEB8, 4) := by decide
theorem pa_at_da : fetchRel pointAddCode 0xDA = some (.aluImm .add a0 sp 0x1A4, 2) := by decide
theorem pa_at_dc : fetchRel pointAddCode 0xDC = some (.aluImm .add a1 sp 0x84, 2) := by decide
theorem pa_at_de : fetchRel pointAddCode 0xDE = some (.aluImm .add a2 sp 0xC4, 2) := by decide
theorem pa_at_e0 : fetchRel pointAddCode 0xE0 = some (.auipc ra 0xF000, 4) := by decide
theorem pa_at_e4 : fetchRel pointAddCode 0xE4 = some (.jalr ra ra 0xFFFFFFCC, 4) := by decide
theorem pa_at_e8 : fetchRel pointAddCode 0xE8 = some (.aluImm .add a0 sp 0xA4, 2) := by decide
theorem pa_at_ea : fetchRel pointAddCode 0xEA = some (.alu .add a1 x0 (20 : Fin 32), 2) := by decide
theorem pa_at_ec : fetchRel pointAddCode 0xEC = some (.alu .add a2 x0 (18 : Fin 32), 2) := by decide
theorem pa_at_ee : fetchRel pointAddCode 0xEE = some (.auipc ra 0xF000, 4) := by decide
theorem pa_at_f2 : fetchRel pointAddCode 0xF2 = some (.jalr ra ra 0xFFFFFE9C, 4) := by decide
theorem pa_at_f6 : fetchRel pointAddCode 0xF6 = some (.aluImm .add a0 sp 0xC4, 2) := by decide
theorem pa_at_f8 : fetchRel pointAddCode 0xF8 = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem pa_at_fa : fetchRel pointAddCode 0xFA = some (.alu .add a2 x0 (8 : Fin 32), 2) := by decide
theorem pa_at_fc : fetchRel pointAddCode 0xFC = some (.auipc ra 0xF000, 4) := by decide
theorem pa_at_100 : fetchRel pointAddCode 0x100 = some (.jalr ra ra 0xFFFFFE8E, 4) := by decide
theorem pa_at_104 : fetchRel pointAddCode 0x104 = some (.aluImm .add a0 sp 0x84, 2) := by decide
theorem pa_at_106 : fetchRel pointAddCode 0x106 = some (.aluImm .add a1 sp 0xA4, 2) := by decide
theorem pa_at_108 : fetchRel pointAddCode 0x108 = some (.aluImm .add a2 sp 0xC4, 2) := by decide
theorem pa_at_10a : fetchRel pointAddCode 0x10A = some (.auipc ra 0xE000, 4) := by decide
theorem pa_at_10e : fetchRel pointAddCode 0x10E = some (.jalr ra ra 0x72E, 4) := by decide
theorem pa_at_112 : fetchRel pointAddCode 0x112 = some (.aluImm .add a0 sp 0xC4, 2) := by decide
theorem pa_at_114 : fetchRel pointAddCode 0x114 = some (.aluImm .add a1 sp 0x64, 2) := by decide
theorem pa_at_116 : fetchRel pointAddCode 0x116 = some (.aluImm .add a2 sp 0x24, 2) := by decide
theorem pa_at_118 : fetchRel pointAddCode 0x118 = some (.auipc ra 0xF000, 4) := by decide
theorem pa_at_11c : fetchRel pointAddCode 0x11C = some (.jalr ra ra 0xFFFFFE72, 4) := by decide
theorem pa_at_120 : fetchRel pointAddCode 0x120 = some (.aluImm .add a0 sp 0xE4, 2) := by decide
theorem pa_at_122 : fetchRel pointAddCode 0x122 = some (.aluImm .add a1 sp 0x84, 2) := by decide
theorem pa_at_124 : fetchRel pointAddCode 0x124 = some (.aluImm .add a2 sp 0xC4, 2) := by decide
theorem pa_at_126 : fetchRel pointAddCode 0x126 = some (.auipc ra 0xF000, 4) := by decide
theorem pa_at_12a : fetchRel pointAddCode 0x12A = some (.jalr ra ra 0xFFFFFF86, 4) := by decide
theorem pa_at_12e : fetchRel pointAddCode 0x12E = some (.lui (8 : Fin 32) 0x3FCC4000, 4) := by decide
theorem pa_at_132 : fetchRel pointAddCode 0x132 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x368, 4) := by decide
theorem pa_at_136 : fetchRel pointAddCode 0x136 = some (.aluImm .add a0 sp 0xC4, 2) := by decide
theorem pa_at_138 : fetchRel pointAddCode 0x138 = some (.aluImm .add a2 sp 0x24, 2) := by decide
theorem pa_at_13a : fetchRel pointAddCode 0x13A = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem pa_at_13c : fetchRel pointAddCode 0x13C = some (.auipc ra 0xE000, 4) := by decide
theorem pa_at_140 : fetchRel pointAddCode 0x140 = some (.jalr ra ra 0x6FC, 4) := by decide
theorem pa_at_144 : fetchRel pointAddCode 0x144 = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem pa_at_146 : fetchRel pointAddCode 0x146 = some (.aluImm .add a1 sp 0xE4, 2) := by decide
theorem pa_at_148 : fetchRel pointAddCode 0x148 = some (.aluImm .add a2 sp 0xC4, 2) := by decide
theorem pa_at_14a : fetchRel pointAddCode 0x14A = some (.auipc ra 0xF000, 4) := by decide
theorem pa_at_14e : fetchRel pointAddCode 0x14E = some (.jalr ra ra 0xFFFFFF62, 4) := by decide
theorem pa_at_152 : fetchRel pointAddCode 0x152 = some (.aluImm .add a0 sp 0xC4, 2) := by decide
theorem pa_at_154 : fetchRel pointAddCode 0x154 = some (.aluImm .add a1 sp 0x4, 2) := by decide
theorem pa_at_156 : fetchRel pointAddCode 0x156 = some (.auipc ra 0xF000, 4) := by decide
theorem pa_at_15a : fetchRel pointAddCode 0x15A = some (.jalr ra ra 0x13A, 4) := by decide
theorem pa_at_15e : fetchRel pointAddCode 0x15E = some (.aluImm .add a0 sp 0x124, 2) := by decide
theorem pa_at_160 : fetchRel pointAddCode 0x160 = some (.aluImm .add a1 sp 0xC4, 2) := by decide
theorem pa_at_162 : fetchRel pointAddCode 0x162 = some (.aluImm .add a2 sp 0x4, 2) := by decide
theorem pa_at_164 : fetchRel pointAddCode 0x164 = some (.auipc ra 0xF000, 4) := by decide
theorem pa_at_168 : fetchRel pointAddCode 0x168 = some (.jalr ra ra 0xFFFFFE26, 4) := by decide
theorem pa_at_16c : fetchRel pointAddCode 0x16C = some (.aluImm .add a0 sp 0x1E4, 2) := by decide
theorem pa_at_16e : fetchRel pointAddCode 0x16E = some (.aluImm .add a1 sp 0x104, 2) := by decide
theorem pa_at_170 : fetchRel pointAddCode 0x170 = some (.aluImm .add a2 sp 0x124, 2) := by decide
theorem pa_at_172 : fetchRel pointAddCode 0x172 = some (.auipc ra 0xF000, 4) := by decide
theorem pa_at_176 : fetchRel pointAddCode 0x176 = some (.jalr ra ra 0xFFFFFF3A, 4) := by decide
theorem pa_at_17a : fetchRel pointAddCode 0x17A = some (.aluImm .add a0 sp 0x164, 2) := by decide
theorem pa_at_17c : fetchRel pointAddCode 0x17C = some (.aluImm .add a1 sp 0x104, 2) := by decide
theorem pa_at_17e : fetchRel pointAddCode 0x17E = some (.aluImm .add a2 sp 0x124, 2) := by decide
theorem pa_at_180 : fetchRel pointAddCode 0x180 = some (.auipc ra 0xF000, 4) := by decide
theorem pa_at_184 : fetchRel pointAddCode 0x184 = some (.jalr ra ra 0xFFFFFE0A, 4) := by decide
theorem pa_at_188 : fetchRel pointAddCode 0x188 = some (.aluImm .add a0 sp 0xC4, 2) := by decide
theorem pa_at_18a : fetchRel pointAddCode 0x18A = some (.aluImm .add a1 sp 0x24, 2) := by decide
theorem pa_at_18c : fetchRel pointAddCode 0x18C = some (.auipc ra 0xF000, 4) := by decide
theorem pa_at_190 : fetchRel pointAddCode 0x190 = some (.jalr ra ra 0x104, 4) := by decide
theorem pa_at_194 : fetchRel pointAddCode 0x194 = some (.aluImm .add a0 sp 0x144, 2) := by decide
theorem pa_at_196 : fetchRel pointAddCode 0x196 = some (.aluImm .add a1 sp 0xC4, 2) := by decide
theorem pa_at_198 : fetchRel pointAddCode 0x198 = some (.aluImm .add a2 sp 0x24, 2) := by decide
theorem pa_at_19a : fetchRel pointAddCode 0x19A = some (.auipc ra 0xF000, 4) := by decide
theorem pa_at_19e : fetchRel pointAddCode 0x19E = some (.jalr ra ra 0xFFFFFDF0, 4) := by decide
theorem pa_at_1a2 : fetchRel pointAddCode 0x1A2 = some (.aluImm .add a0 sp 0xA4, 2) := by decide
theorem pa_at_1a4 : fetchRel pointAddCode 0x1A4 = some (.aluImm .add a2 sp 0xE4, 2) := by decide
theorem pa_at_1a6 : fetchRel pointAddCode 0x1A6 = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem pa_at_1a8 : fetchRel pointAddCode 0x1A8 = some (.auipc ra 0xE000, 4) := by decide
theorem pa_at_1ac : fetchRel pointAddCode 0x1AC = some (.jalr ra ra 0x690, 4) := by decide
theorem pa_at_1b0 : fetchRel pointAddCode 0x1B0 = some (.aluImm .add a0 sp 0xC4, 2) := by decide
theorem pa_at_1b2 : fetchRel pointAddCode 0x1B2 = some (.aluImm .add a1 sp 0x144, 2) := by decide
theorem pa_at_1b4 : fetchRel pointAddCode 0x1B4 = some (.aluImm .add a2 sp 0x64, 2) := by decide
theorem pa_at_1b6 : fetchRel pointAddCode 0x1B6 = some (.auipc ra 0xF000, 4) := by decide
theorem pa_at_1ba : fetchRel pointAddCode 0x1BA = some (.jalr ra ra 0xFFFFFDD4, 4) := by decide
theorem pa_at_1be : fetchRel pointAddCode 0x1BE = some (.aluImm .add a0 sp 0x44, 2) := by decide
theorem pa_at_1c0 : fetchRel pointAddCode 0x1C0 = some (.aluImm .add a1 sp 0xA4, 2) := by decide
theorem pa_at_1c2 : fetchRel pointAddCode 0x1C2 = some (.aluImm .add a2 sp 0xC4, 2) := by decide
theorem pa_at_1c4 : fetchRel pointAddCode 0x1C4 = some (.auipc ra 0xF000, 4) := by decide
theorem pa_at_1c8 : fetchRel pointAddCode 0x1C8 = some (.jalr ra ra 0xFFFFFEE8, 4) := by decide
theorem pa_at_1cc : fetchRel pointAddCode 0x1CC = some (.aluImm .add a0 sp 0xC4, 2) := by decide
theorem pa_at_1ce : fetchRel pointAddCode 0x1CE = some (.aluImm .add a1 sp 0x44, 2) := by decide
theorem pa_at_1d0 : fetchRel pointAddCode 0x1D0 = some (.auipc ra 0xF000, 4) := by decide
theorem pa_at_1d4 : fetchRel pointAddCode 0x1D4 = some (.jalr ra ra 0xC0, 4) := by decide
theorem pa_at_1d8 : fetchRel pointAddCode 0x1D8 = some (.aluImm .add a0 sp 0x1C4, 2) := by decide
theorem pa_at_1da : fetchRel pointAddCode 0x1DA = some (.aluImm .add a1 sp 0xC4, 2) := by decide
theorem pa_at_1dc : fetchRel pointAddCode 0x1DC = some (.aluImm .add a2 sp 0x44, 2) := by decide
theorem pa_at_1de : fetchRel pointAddCode 0x1DE = some (.auipc ra 0xF000, 4) := by decide
theorem pa_at_1e2 : fetchRel pointAddCode 0x1E2 = some (.jalr ra ra 0xFFFFFDAC, 4) := by decide
theorem pa_at_1e6 : fetchRel pointAddCode 0x1E6 = some (.aluImm .add a0 sp 0xC4, 2) := by decide
theorem pa_at_1e8 : fetchRel pointAddCode 0x1E8 = some (.aluImm .add a1 sp 0x64, 2) := by decide
theorem pa_at_1ea : fetchRel pointAddCode 0x1EA = some (.auipc ra 0xF000, 4) := by decide
theorem pa_at_1ee : fetchRel pointAddCode 0x1EE = some (.jalr ra ra 0xA6, 4) := by decide
theorem pa_at_1f2 : fetchRel pointAddCode 0x1F2 = some (.aluImm .add a0 sp 0xA4, 2) := by decide
theorem pa_at_1f4 : fetchRel pointAddCode 0x1F4 = some (.aluImm .add a1 sp 0xC4, 2) := by decide
theorem pa_at_1f6 : fetchRel pointAddCode 0x1F6 = some (.aluImm .add a2 sp 0x64, 2) := by decide
theorem pa_at_1f8 : fetchRel pointAddCode 0x1F8 = some (.auipc ra 0xF000, 4) := by decide
theorem pa_at_1fc : fetchRel pointAddCode 0x1FC = some (.jalr ra ra 0xFFFFFD92, 4) := by decide
theorem pa_at_200 : fetchRel pointAddCode 0x200 = some (.aluImm .add a0 sp 0x204, 2) := by decide
theorem pa_at_202 : fetchRel pointAddCode 0x202 = some (.aluImm .add a1 sp 0xA4, 2) := by decide
theorem pa_at_204 : fetchRel pointAddCode 0x204 = some (.aluImm .add a2 sp 0x144, 2) := by decide
theorem pa_at_206 : fetchRel pointAddCode 0x206 = some (.auipc ra 0xF000, 4) := by decide
theorem pa_at_20a : fetchRel pointAddCode 0x20A = some (.jalr ra ra 0xFFFFFEA6, 4) := by decide
theorem pa_at_20e : fetchRel pointAddCode 0x20E = some (.aluImm .add a0 sp 0xA4, 2) := by decide
theorem pa_at_210 : fetchRel pointAddCode 0x210 = some (.aluImm .add a1 sp 0x164, 2) := by decide
theorem pa_at_212 : fetchRel pointAddCode 0x212 = some (.aluImm .add a2 sp 0x184, 2) := by decide
theorem pa_at_214 : fetchRel pointAddCode 0x214 = some (.auipc ra 0xE000, 4) := by decide
theorem pa_at_218 : fetchRel pointAddCode 0x218 = some (.jalr ra ra 0x624, 4) := by decide
theorem pa_at_21c : fetchRel pointAddCode 0x21C = some (.aluImm .add a0 sp 0xC4, 2) := by decide
theorem pa_at_21e : fetchRel pointAddCode 0x21E = some (.aluImm .add a1 sp 0x1A4, 2) := by decide
theorem pa_at_220 : fetchRel pointAddCode 0x220 = some (.aluImm .add a2 sp 0x1C4, 2) := by decide
theorem pa_at_222 : fetchRel pointAddCode 0x222 = some (.auipc ra 0xE000, 4) := by decide
theorem pa_at_226 : fetchRel pointAddCode 0x226 = some (.jalr ra ra 0x616, 4) := by decide
theorem pa_at_22a : fetchRel pointAddCode 0x22A = some (.aluImm .add a0 sp 0x84, 2) := by decide
theorem pa_at_22c : fetchRel pointAddCode 0x22C = some (.aluImm .add a1 sp 0xA4, 2) := by decide
theorem pa_at_22e : fetchRel pointAddCode 0x22E = some (.aluImm .add a2 sp 0xC4, 2) := by decide
theorem pa_at_230 : fetchRel pointAddCode 0x230 = some (.auipc ra 0xF000, 4) := by decide
theorem pa_at_234 : fetchRel pointAddCode 0x234 = some (.jalr ra ra 0xFFFFFE7C, 4) := by decide
theorem pa_at_238 : fetchRel pointAddCode 0x238 = some (.aluImm .add a1 sp 0x84, 2) := by decide
theorem pa_at_23a : fetchRel pointAddCode 0x23A = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem pa_at_23e : fetchRel pointAddCode 0x23E = some (.alu .add a0 x0 (20 : Fin 32), 2) := by decide
theorem pa_at_240 : fetchRel pointAddCode 0x240 = some (.auipc ra 0x1D000, 4) := by decide
theorem pa_at_244 : fetchRel pointAddCode 0x244 = some (.jalr ra ra 0xFFFFFF28, 4) := by decide
theorem pa_at_248 : fetchRel pointAddCode 0x248 = some (.aluImm .add a0 sp 0xA4, 2) := by decide
theorem pa_at_24a : fetchRel pointAddCode 0x24A = some (.aluImm .add a1 sp 0x164, 2) := by decide
theorem pa_at_24c : fetchRel pointAddCode 0x24C = some (.aluImm .add a2 sp 0x1E4, 2) := by decide
theorem pa_at_24e : fetchRel pointAddCode 0x24E = some (.auipc ra 0xE000, 4) := by decide
theorem pa_at_252 : fetchRel pointAddCode 0x252 = some (.jalr ra ra 0x5EA, 4) := by decide
theorem pa_at_256 : fetchRel pointAddCode 0x256 = some (.aluImm .add a0 sp 0xC4, 2) := by decide
theorem pa_at_258 : fetchRel pointAddCode 0x258 = some (.aluImm .add a1 sp 0x204, 2) := by decide
theorem pa_at_25a : fetchRel pointAddCode 0x25A = some (.aluImm .add a2 sp 0x1C4, 2) := by decide
theorem pa_at_25c : fetchRel pointAddCode 0x25C = some (.auipc ra 0xE000, 4) := by decide
theorem pa_at_260 : fetchRel pointAddCode 0x260 = some (.jalr ra ra 0x5DC, 4) := by decide
theorem pa_at_264 : fetchRel pointAddCode 0x264 = some (.aluImm .add a0 sp 0x84, 2) := by decide
theorem pa_at_266 : fetchRel pointAddCode 0x266 = some (.aluImm .add a1 sp 0xA4, 2) := by decide
theorem pa_at_268 : fetchRel pointAddCode 0x268 = some (.aluImm .add a2 sp 0xC4, 2) := by decide
theorem pa_at_26a : fetchRel pointAddCode 0x26A = some (.auipc ra 0xF000, 4) := by decide
theorem pa_at_26e : fetchRel pointAddCode 0x26E = some (.jalr ra ra 0xFFFFFD20, 4) := by decide
theorem pa_at_272 : fetchRel pointAddCode 0x272 = some (.aluImm .add a1 sp 0x84, 2) := by decide
theorem pa_at_274 : fetchRel pointAddCode 0x274 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem pa_at_278 : fetchRel pointAddCode 0x278 = some (.alu .add a0 x0 (19 : Fin 32), 2) := by decide
theorem pa_at_27a : fetchRel pointAddCode 0x27A = some (.auipc ra 0x1D000, 4) := by decide
theorem pa_at_27e : fetchRel pointAddCode 0x27E = some (.jalr ra ra 0xFFFFFEEE, 4) := by decide
theorem pa_at_282 : fetchRel pointAddCode 0x282 = some (.aluImm .add a0 sp 0xA4, 2) := by decide
theorem pa_at_284 : fetchRel pointAddCode 0x284 = some (.aluImm .add a1 sp 0x1E4, 2) := by decide
theorem pa_at_286 : fetchRel pointAddCode 0x286 = some (.aluImm .add a2 sp 0x1A4, 2) := by decide
theorem pa_at_288 : fetchRel pointAddCode 0x288 = some (.auipc ra 0xE000, 4) := by decide
theorem pa_at_28c : fetchRel pointAddCode 0x28C = some (.jalr ra ra 0x5B0, 4) := by decide
theorem pa_at_290 : fetchRel pointAddCode 0x290 = some (.aluImm .add a0 sp 0xC4, 2) := by decide
theorem pa_at_292 : fetchRel pointAddCode 0x292 = some (.aluImm .add a1 sp 0x184, 2) := by decide
theorem pa_at_294 : fetchRel pointAddCode 0x294 = some (.aluImm .add a2 sp 0x204, 2) := by decide
theorem pa_at_296 : fetchRel pointAddCode 0x296 = some (.auipc ra 0xE000, 4) := by decide
theorem pa_at_29a : fetchRel pointAddCode 0x29A = some (.jalr ra ra 0x5A2, 4) := by decide
theorem pa_at_29e : fetchRel pointAddCode 0x29E = some (.aluImm .add a0 sp 0x84, 2) := by decide
theorem pa_at_2a0 : fetchRel pointAddCode 0x2A0 = some (.aluImm .add a1 sp 0xA4, 2) := by decide
theorem pa_at_2a2 : fetchRel pointAddCode 0x2A2 = some (.aluImm .add a2 sp 0xC4, 2) := by decide
theorem pa_at_2a4 : fetchRel pointAddCode 0x2A4 = some (.auipc ra 0xF000, 4) := by decide
theorem pa_at_2a8 : fetchRel pointAddCode 0x2A8 = some (.jalr ra ra 0xFFFFFCE6, 4) := by decide
theorem pa_at_2ac : fetchRel pointAddCode 0x2AC = some (.aluImm .add a1 sp 0x84, 2) := by decide
theorem pa_at_2ae : fetchRel pointAddCode 0x2AE = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem pa_at_2b2 : fetchRel pointAddCode 0x2B2 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem pa_at_2b4 : fetchRel pointAddCode 0x2B4 = some (.auipc ra 0x1D000, 4) := by decide
theorem pa_at_2b8 : fetchRel pointAddCode 0x2B8 = some (.jalr ra ra 0xFFFFFEB4, 4) := by decide
theorem pa_at_2bc : fetchRel pointAddCode 0x2BC = some (.aluImm .add a0 sp 0x200, 2) := by decide
theorem pa_at_2be : fetchRel pointAddCode 0x2BE = some (.load .lw ra a0 0x3C, 4) := by decide
theorem pa_at_2c2 : fetchRel pointAddCode 0x2C2 = some (.load .lw (8 : Fin 32) a0 0x38, 2) := by decide
theorem pa_at_2c4 : fetchRel pointAddCode 0x2C4 = some (.load .lw (9 : Fin 32) a0 0x34, 2) := by decide
theorem pa_at_2c6 : fetchRel pointAddCode 0x2C6 = some (.load .lw (18 : Fin 32) a0 0x30, 4) := by decide
theorem pa_at_2ca : fetchRel pointAddCode 0x2CA = some (.load .lw (19 : Fin 32) a0 0x2C, 4) := by decide
theorem pa_at_2ce : fetchRel pointAddCode 0x2CE = some (.load .lw (20 : Fin 32) a0 0x28, 4) := by decide
theorem pa_at_2d2 : fetchRel pointAddCode 0x2D2 = some (.load .lw (21 : Fin 32) a0 0x24, 4) := by decide
theorem pa_at_2d6 : fetchRel pointAddCode 0x2D6 = some (.aluImm .add sp sp 0x240, 4) := by decide
theorem pa_at_2da : fetchRel pointAddCode 0x2DA = some (.jalr x0 ra 0x0, 2) := by decide

end C3.RV32
