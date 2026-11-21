import C3BootProofs.Proofs.FeToBytesSpec

/-! # `FieldElement2625::to_bytes`'s instructions, decoded -/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem tb_at_0 : fetchRel feToBytesCode 0x0 = some (.aluImm .add sp sp 0xFFFFFF70, 2) := by decide
theorem tb_at_2 : fetchRel feToBytesCode 0x2 = some (.store .sw sp ra 0x8C, 2) := by decide
theorem tb_at_4 : fetchRel feToBytesCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x88, 2) := by decide
theorem tb_at_6 : fetchRel feToBytesCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x84, 2) := by decide
theorem tb_at_8 : fetchRel feToBytesCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x80, 2) := by decide
theorem tb_at_a : fetchRel feToBytesCode 0xA = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem tb_at_c : fetchRel feToBytesCode 0xC = some (.load .lw a0 a1 0x0, 2) := by decide
theorem tb_at_e : fetchRel feToBytesCode 0xE = some (.load .lw a2 a1 0x4, 2) := by decide
theorem tb_at_10 : fetchRel feToBytesCode 0x10 = some (.load .lw a3 a1 0x8, 2) := by decide
theorem tb_at_12 : fetchRel feToBytesCode 0x12 = some (.load .lw a4 a1 0xC, 2) := by decide
theorem tb_at_14 : fetchRel feToBytesCode 0x14 = some (.load .lw a5 a1 0x10, 2) := by decide
theorem tb_at_16 : fetchRel feToBytesCode 0x16 = some (.load .lw a6 a1 0x14, 4) := by decide
theorem tb_at_1a : fetchRel feToBytesCode 0x1A = some (.load .lw (17 : Fin 32) a1 0x18, 4) := by decide
theorem tb_at_1e : fetchRel feToBytesCode 0x1E = some (.load .lw (5 : Fin 32) a1 0x1C, 4) := by decide
theorem tb_at_22 : fetchRel feToBytesCode 0x22 = some (.load .lw (6 : Fin 32) a1 0x20, 4) := by decide
theorem tb_at_26 : fetchRel feToBytesCode 0x26 = some (.load .lw a1 a1 0x24, 2) := by decide
theorem tb_at_28 : fetchRel feToBytesCode 0x28 = some (.store .sw sp a0 0x30, 2) := by decide
theorem tb_at_2a : fetchRel feToBytesCode 0x2A = some (.store .sw sp x0 0x34, 2) := by decide
theorem tb_at_2c : fetchRel feToBytesCode 0x2C = some (.store .sw sp a2 0x38, 2) := by decide
theorem tb_at_2e : fetchRel feToBytesCode 0x2E = some (.store .sw sp x0 0x3C, 2) := by decide
theorem tb_at_30 : fetchRel feToBytesCode 0x30 = some (.store .sw sp a3 0x40, 2) := by decide
theorem tb_at_32 : fetchRel feToBytesCode 0x32 = some (.store .sw sp x0 0x44, 2) := by decide
theorem tb_at_34 : fetchRel feToBytesCode 0x34 = some (.store .sw sp a4 0x48, 2) := by decide
theorem tb_at_36 : fetchRel feToBytesCode 0x36 = some (.store .sw sp x0 0x4C, 2) := by decide
theorem tb_at_38 : fetchRel feToBytesCode 0x38 = some (.store .sw sp a5 0x50, 2) := by decide
theorem tb_at_3a : fetchRel feToBytesCode 0x3A = some (.store .sw sp x0 0x54, 2) := by decide
theorem tb_at_3c : fetchRel feToBytesCode 0x3C = some (.store .sw sp a6 0x58, 2) := by decide
theorem tb_at_3e : fetchRel feToBytesCode 0x3E = some (.store .sw sp x0 0x5C, 2) := by decide
theorem tb_at_40 : fetchRel feToBytesCode 0x40 = some (.store .sw sp (17 : Fin 32) 0x60, 2) := by decide
theorem tb_at_42 : fetchRel feToBytesCode 0x42 = some (.store .sw sp x0 0x64, 2) := by decide
theorem tb_at_44 : fetchRel feToBytesCode 0x44 = some (.store .sw sp (5 : Fin 32) 0x68, 2) := by decide
theorem tb_at_46 : fetchRel feToBytesCode 0x46 = some (.store .sw sp x0 0x6C, 2) := by decide
theorem tb_at_48 : fetchRel feToBytesCode 0x48 = some (.store .sw sp (6 : Fin 32) 0x70, 2) := by decide
theorem tb_at_4a : fetchRel feToBytesCode 0x4A = some (.store .sw sp x0 0x74, 2) := by decide
theorem tb_at_4c : fetchRel feToBytesCode 0x4C = some (.store .sw sp a1 0x78, 2) := by decide
theorem tb_at_4e : fetchRel feToBytesCode 0x4E = some (.store .sw sp x0 0x7C, 2) := by decide
theorem tb_at_50 : fetchRel feToBytesCode 0x50 = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem tb_at_52 : fetchRel feToBytesCode 0x52 = some (.aluImm .add a1 sp 0x30, 2) := by decide
theorem tb_at_54 : fetchRel feToBytesCode 0x54 = some (.auipc ra 0x0, 4) := by decide
theorem tb_at_58 : fetchRel feToBytesCode 0x58 = some (.jalr ra ra 0x1BC, 4) := by decide
theorem tb_at_5c : fetchRel feToBytesCode 0x5C = some (.load .lw a3 sp 0x8, 2) := by decide
theorem tb_at_5e : fetchRel feToBytesCode 0x5E = some (.load .lw a2 sp 0xC, 2) := by decide
theorem tb_at_60 : fetchRel feToBytesCode 0x60 = some (.load .lw (30 : Fin 32) sp 0x10, 2) := by decide
theorem tb_at_62 : fetchRel feToBytesCode 0x62 = some (.load .lw (29 : Fin 32) sp 0x14, 2) := by decide
theorem tb_at_64 : fetchRel feToBytesCode 0x64 = some (.aluImm .add a4 a3 0x13, 4) := by decide
theorem tb_at_68 : fetchRel feToBytesCode 0x68 = some (.aluImm .srl a4 a4 0x1A, 2) := by decide
theorem tb_at_6a : fetchRel feToBytesCode 0x6A = some (.alu .add a4 a4 a2, 2) := by decide
theorem tb_at_6c : fetchRel feToBytesCode 0x6C = some (.aluImm .srl a4 a4 0x19, 2) := by decide
theorem tb_at_6e : fetchRel feToBytesCode 0x6E = some (.load .lw (28 : Fin 32) sp 0x18, 2) := by decide
theorem tb_at_70 : fetchRel feToBytesCode 0x70 = some (.alu .add a4 a4 (30 : Fin 32), 2) := by decide
theorem tb_at_72 : fetchRel feToBytesCode 0x72 = some (.aluImm .srl a4 a4 0x1A, 2) := by decide
theorem tb_at_74 : fetchRel feToBytesCode 0x74 = some (.load .lw (7 : Fin 32) sp 0x1C, 2) := by decide
theorem tb_at_76 : fetchRel feToBytesCode 0x76 = some (.alu .add a4 a4 (29 : Fin 32), 2) := by decide
theorem tb_at_78 : fetchRel feToBytesCode 0x78 = some (.aluImm .srl a4 a4 0x19, 2) := by decide
theorem tb_at_7a : fetchRel feToBytesCode 0x7A = some (.load .lw (6 : Fin 32) sp 0x20, 2) := by decide
theorem tb_at_7c : fetchRel feToBytesCode 0x7C = some (.load .lw (5 : Fin 32) sp 0x24, 2) := by decide
theorem tb_at_7e : fetchRel feToBytesCode 0x7E = some (.alu .add a4 a4 (28 : Fin 32), 2) := by decide
theorem tb_at_80 : fetchRel feToBytesCode 0x80 = some (.aluImm .srl a4 a4 0x1A, 2) := by decide
theorem tb_at_82 : fetchRel feToBytesCode 0x82 = some (.alu .add a4 a4 (7 : Fin 32), 2) := by decide
theorem tb_at_84 : fetchRel feToBytesCode 0x84 = some (.aluImm .srl a4 a4 0x19, 2) := by decide
theorem tb_at_86 : fetchRel feToBytesCode 0x86 = some (.load .lw (17 : Fin 32) sp 0x28, 2) := by decide
theorem tb_at_88 : fetchRel feToBytesCode 0x88 = some (.alu .add a4 a4 (6 : Fin 32), 2) := by decide
theorem tb_at_8a : fetchRel feToBytesCode 0x8A = some (.aluImm .srl a4 a4 0x1A, 2) := by decide
theorem tb_at_8c : fetchRel feToBytesCode 0x8C = some (.load .lw a6 sp 0x2C, 2) := by decide
theorem tb_at_8e : fetchRel feToBytesCode 0x8E = some (.alu .add a4 a4 (5 : Fin 32), 2) := by decide
theorem tb_at_90 : fetchRel feToBytesCode 0x90 = some (.aluImm .srl a4 a4 0x19, 2) := by decide
theorem tb_at_92 : fetchRel feToBytesCode 0x92 = some (.alu .add a4 a4 (17 : Fin 32), 2) := by decide
theorem tb_at_94 : fetchRel feToBytesCode 0x94 = some (.aluImm .srl a4 a4 0x1A, 2) := by decide
theorem tb_at_96 : fetchRel feToBytesCode 0x96 = some (.alu .add a4 a4 a6, 2) := by decide
theorem tb_at_98 : fetchRel feToBytesCode 0x98 = some (.aluImm .add a5 x0 0x13, 2) := by decide
theorem tb_at_9a : fetchRel feToBytesCode 0x9A = some (.aluImm .srl a4 a4 0x19, 2) := by decide
theorem tb_at_9c : fetchRel feToBytesCode 0x9C = some (.alu .mul a4 a4 a5, 4) := by decide
theorem tb_at_a0 : fetchRel feToBytesCode 0xA0 = some (.alu .add a3 a3 a4, 2) := by decide
theorem tb_at_a2 : fetchRel feToBytesCode 0xA2 = some (.aluImm .srl a4 a3 0x1A, 4) := by decide
theorem tb_at_a6 : fetchRel feToBytesCode 0xA6 = some (.aluImm .srl (31 : Fin 32) a3 0x8, 4) := by decide
theorem tb_at_aa : fetchRel feToBytesCode 0xAA = some (.aluImm .srl a0 a3 0x10, 4) := by decide
theorem tb_at_ae : fetchRel feToBytesCode 0xAE = some (.aluImm .sll a1 a3 0x6, 4) := by decide
theorem tb_at_b2 : fetchRel feToBytesCode 0xB2 = some (.alu .add a2 a2 a4, 2) := by decide
theorem tb_at_b4 : fetchRel feToBytesCode 0xB4 = some (.aluImm .srl a1 a1 0x1E, 2) := by decide
theorem tb_at_b6 : fetchRel feToBytesCode 0xB6 = some (.aluImm .srl a4 a2 0x19, 4) := by decide
theorem tb_at_ba : fetchRel feToBytesCode 0xBA = some (.aluImm .sll a5 a2 0x2, 4) := by decide
theorem tb_at_be : fetchRel feToBytesCode 0xBE = some (.aluImm .srl (18 : Fin 32) a2 0x6, 4) := by decide
theorem tb_at_c2 : fetchRel feToBytesCode 0xC2 = some (.alu .add a4 a4 (30 : Fin 32), 2) := by decide
theorem tb_at_c4 : fetchRel feToBytesCode 0xC4 = some (.aluImm .srl (9 : Fin 32) a2 0xE, 4) := by decide
theorem tb_at_c8 : fetchRel feToBytesCode 0xC8 = some (.aluImm .sll a2 a2 0x7, 2) := by decide
theorem tb_at_ca : fetchRel feToBytesCode 0xCA = some (.alu .or a1 a1 a5, 2) := by decide
theorem tb_at_cc : fetchRel feToBytesCode 0xCC = some (.aluImm .srl a2 a2 0x1D, 2) := by decide
theorem tb_at_ce : fetchRel feToBytesCode 0xCE = some (.aluImm .srl a5 a4 0x1A, 4) := by decide
theorem tb_at_d2 : fetchRel feToBytesCode 0xD2 = some (.store .sb (8 : Fin 32) a3 0x0, 4) := by decide
theorem tb_at_d6 : fetchRel feToBytesCode 0xD6 = some (.store .sb (8 : Fin 32) (31 : Fin 32) 0x1, 4) := by decide
theorem tb_at_da : fetchRel feToBytesCode 0xDA = some (.store .sb (8 : Fin 32) a0 0x2, 4) := by decide
theorem tb_at_de : fetchRel feToBytesCode 0xDE = some (.store .sb (8 : Fin 32) a1 0x3, 4) := by decide
theorem tb_at_e2 : fetchRel feToBytesCode 0xE2 = some (.aluImm .sll a0 a4 0x3, 4) := by decide
theorem tb_at_e6 : fetchRel feToBytesCode 0xE6 = some (.aluImm .srl a1 a4 0x5, 4) := by decide
theorem tb_at_ea : fetchRel feToBytesCode 0xEA = some (.alu .add a5 a5 (29 : Fin 32), 2) := by decide
theorem tb_at_ec : fetchRel feToBytesCode 0xEC = some (.aluImm .srl a3 a4 0xD, 4) := by decide
theorem tb_at_f0 : fetchRel feToBytesCode 0xF0 = some (.aluImm .sll a4 a4 0x6, 2) := by decide
theorem tb_at_f2 : fetchRel feToBytesCode 0xF2 = some (.alu .or a0 a0 a2, 2) := by decide
theorem tb_at_f4 : fetchRel feToBytesCode 0xF4 = some (.aluImm .srl a4 a4 0x1B, 2) := by decide
theorem tb_at_f6 : fetchRel feToBytesCode 0xF6 = some (.aluImm .srl a2 a5 0x19, 4) := by decide
theorem tb_at_fa : fetchRel feToBytesCode 0xFA = some (.store .sb (8 : Fin 32) (18 : Fin 32) 0x4, 4) := by decide
theorem tb_at_fe : fetchRel feToBytesCode 0xFE = some (.store .sb (8 : Fin 32) (9 : Fin 32) 0x5, 4) := by decide
theorem tb_at_102 : fetchRel feToBytesCode 0x102 = some (.store .sb (8 : Fin 32) a0 0x6, 4) := by decide
theorem tb_at_106 : fetchRel feToBytesCode 0x106 = some (.store .sb (8 : Fin 32) a1 0x7, 4) := by decide
theorem tb_at_10a : fetchRel feToBytesCode 0x10A = some (.aluImm .sll a0 a5 0x5, 4) := by decide
theorem tb_at_10e : fetchRel feToBytesCode 0x10E = some (.aluImm .srl a1 a5 0x3, 4) := by decide
theorem tb_at_112 : fetchRel feToBytesCode 0x112 = some (.alu .add a2 a2 (28 : Fin 32), 2) := by decide
theorem tb_at_114 : fetchRel feToBytesCode 0x114 = some (.aluImm .srl (9 : Fin 32) a5 0xB, 4) := by decide
theorem tb_at_118 : fetchRel feToBytesCode 0x118 = some (.aluImm .sll a5 a5 0x7, 2) := by decide
theorem tb_at_11a : fetchRel feToBytesCode 0x11A = some (.alu .or a0 a0 a4, 2) := by decide
theorem tb_at_11c : fetchRel feToBytesCode 0x11C = some (.aluImm .srl a5 a5 0x1A, 2) := by decide
theorem tb_at_11e : fetchRel feToBytesCode 0x11E = some (.aluImm .srl a4 a2 0x1A, 4) := by decide
theorem tb_at_122 : fetchRel feToBytesCode 0x122 = some (.store .sb (8 : Fin 32) a3 0x8, 4) := by decide
theorem tb_at_126 : fetchRel feToBytesCode 0x126 = some (.store .sb (8 : Fin 32) a0 0x9, 4) := by decide
theorem tb_at_12a : fetchRel feToBytesCode 0x12A = some (.store .sb (8 : Fin 32) a1 0xA, 4) := by decide
theorem tb_at_12e : fetchRel feToBytesCode 0x12E = some (.store .sb (8 : Fin 32) (9 : Fin 32) 0xB, 4) := by decide
theorem tb_at_132 : fetchRel feToBytesCode 0x132 = some (.aluImm .sll a0 a2 0x6, 4) := by decide
theorem tb_at_136 : fetchRel feToBytesCode 0x136 = some (.aluImm .srl a1 a2 0x2, 4) := by decide
theorem tb_at_13a : fetchRel feToBytesCode 0x13A = some (.aluImm .srl a3 a2 0xA, 4) := by decide
theorem tb_at_13e : fetchRel feToBytesCode 0x13E = some (.alu .add a4 a4 (7 : Fin 32), 2) := by decide
theorem tb_at_140 : fetchRel feToBytesCode 0x140 = some (.aluImm .srl a2 a2 0x12, 2) := by decide
theorem tb_at_142 : fetchRel feToBytesCode 0x142 = some (.aluImm .srl (9 : Fin 32) a4 0x19, 4) := by decide
theorem tb_at_146 : fetchRel feToBytesCode 0x146 = some (.alu .or a0 a0 a5, 2) := by decide
theorem tb_at_148 : fetchRel feToBytesCode 0x148 = some (.alu .add (6 : Fin 32) (6 : Fin 32) (9 : Fin 32), 2) := by decide
theorem tb_at_14a : fetchRel feToBytesCode 0x14A = some (.aluImm .srl a5 (6 : Fin 32) 0x1A, 4) := by decide
theorem tb_at_14e : fetchRel feToBytesCode 0x14E = some (.store .sb (8 : Fin 32) a0 0xC, 4) := by decide
theorem tb_at_152 : fetchRel feToBytesCode 0x152 = some (.store .sb (8 : Fin 32) a1 0xD, 4) := by decide
theorem tb_at_156 : fetchRel feToBytesCode 0x156 = some (.store .sb (8 : Fin 32) a3 0xE, 4) := by decide
theorem tb_at_15a : fetchRel feToBytesCode 0x15A = some (.store .sb (8 : Fin 32) a2 0xF, 4) := by decide
theorem tb_at_15e : fetchRel feToBytesCode 0x15E = some (.alu .add a5 a5 (5 : Fin 32), 2) := by decide
theorem tb_at_160 : fetchRel feToBytesCode 0x160 = some (.aluImm .srl (5 : Fin 32) a4 0x8, 4) := by decide
theorem tb_at_164 : fetchRel feToBytesCode 0x164 = some (.aluImm .srl a1 a5 0x19, 4) := by decide
theorem tb_at_168 : fetchRel feToBytesCode 0x168 = some (.aluImm .sll a2 a4 0x7, 4) := by decide
theorem tb_at_16c : fetchRel feToBytesCode 0x16C = some (.alu .add a1 a1 (17 : Fin 32), 2) := by decide
theorem tb_at_16e : fetchRel feToBytesCode 0x16E = some (.aluImm .srl a2 a2 0x1F, 2) := by decide
theorem tb_at_170 : fetchRel feToBytesCode 0x170 = some (.aluImm .srl a3 a1 0x1A, 4) := by decide
theorem tb_at_174 : fetchRel feToBytesCode 0x174 = some (.aluImm .sll (9 : Fin 32) (6 : Fin 32) 0x1, 4) := by decide
theorem tb_at_178 : fetchRel feToBytesCode 0x178 = some (.alu .add a3 a3 a6, 2) := by decide
theorem tb_at_17a : fetchRel feToBytesCode 0x17A = some (.aluImm .srl a0 a4 0x10, 4) := by decide
theorem tb_at_17e : fetchRel feToBytesCode 0x17E = some (.alu .or a2 a2 (9 : Fin 32), 2) := by decide
theorem tb_at_180 : fetchRel feToBytesCode 0x180 = some (.store .sb (8 : Fin 32) a4 0x10, 4) := by decide
theorem tb_at_184 : fetchRel feToBytesCode 0x184 = some (.store .sb (8 : Fin 32) (5 : Fin 32) 0x11, 4) := by decide
theorem tb_at_188 : fetchRel feToBytesCode 0x188 = some (.store .sb (8 : Fin 32) a0 0x12, 4) := by decide
theorem tb_at_18c : fetchRel feToBytesCode 0x18C = some (.store .sb (8 : Fin 32) a2 0x13, 4) := by decide
theorem tb_at_190 : fetchRel feToBytesCode 0x190 = some (.aluImm .srl a0 (6 : Fin 32) 0x7, 4) := by decide
theorem tb_at_194 : fetchRel feToBytesCode 0x194 = some (.aluImm .sll a2 (6 : Fin 32) 0x6, 4) := by decide
theorem tb_at_198 : fetchRel feToBytesCode 0x198 = some (.aluImm .srl a2 a2 0x1D, 2) := by decide
theorem tb_at_19a : fetchRel feToBytesCode 0x19A = some (.aluImm .sll a4 a5 0x3, 4) := by decide
theorem tb_at_19e : fetchRel feToBytesCode 0x19E = some (.aluImm .srl (9 : Fin 32) (6 : Fin 32) 0xF, 4) := by decide
theorem tb_at_1a2 : fetchRel feToBytesCode 0x1A2 = some (.alu .or a2 a2 a4, 2) := by decide
theorem tb_at_1a4 : fetchRel feToBytesCode 0x1A4 = some (.aluImm .srl a4 a5 0x5, 4) := by decide
theorem tb_at_1a8 : fetchRel feToBytesCode 0x1A8 = some (.store .sb (8 : Fin 32) a0 0x14, 4) := by decide
theorem tb_at_1ac : fetchRel feToBytesCode 0x1AC = some (.store .sb (8 : Fin 32) (9 : Fin 32) 0x15, 4) := by decide
theorem tb_at_1b0 : fetchRel feToBytesCode 0x1B0 = some (.store .sb (8 : Fin 32) a2 0x16, 4) := by decide
theorem tb_at_1b4 : fetchRel feToBytesCode 0x1B4 = some (.store .sb (8 : Fin 32) a4 0x17, 4) := by decide
theorem tb_at_1b8 : fetchRel feToBytesCode 0x1B8 = some (.aluImm .sll a0 a5 0x7, 4) := by decide
theorem tb_at_1bc : fetchRel feToBytesCode 0x1BC = some (.aluImm .srl a0 a0 0x1C, 2) := by decide
theorem tb_at_1be : fetchRel feToBytesCode 0x1BE = some (.aluImm .sll a2 a1 0x4, 4) := by decide
theorem tb_at_1c2 : fetchRel feToBytesCode 0x1C2 = some (.aluImm .srl a5 a5 0xD, 2) := by decide
theorem tb_at_1c4 : fetchRel feToBytesCode 0x1C4 = some (.alu .or a0 a0 a2, 2) := by decide
theorem tb_at_1c6 : fetchRel feToBytesCode 0x1C6 = some (.aluImm .srl a2 a1 0x4, 4) := by decide
theorem tb_at_1ca : fetchRel feToBytesCode 0x1CA = some (.aluImm .sll a4 a1 0x6, 4) := by decide
theorem tb_at_1ce : fetchRel feToBytesCode 0x1CE = some (.aluImm .srl a1 a1 0xC, 2) := by decide
theorem tb_at_1d0 : fetchRel feToBytesCode 0x1D0 = some (.aluImm .srl a4 a4 0x1A, 2) := by decide
theorem tb_at_1d2 : fetchRel feToBytesCode 0x1D2 = some (.aluImm .sll (9 : Fin 32) a3 0x6, 4) := by decide
theorem tb_at_1d6 : fetchRel feToBytesCode 0x1D6 = some (.store .sb (8 : Fin 32) a5 0x18, 4) := by decide
theorem tb_at_1da : fetchRel feToBytesCode 0x1DA = some (.store .sb (8 : Fin 32) a0 0x19, 4) := by decide
theorem tb_at_1de : fetchRel feToBytesCode 0x1DE = some (.store .sb (8 : Fin 32) a2 0x1A, 4) := by decide
theorem tb_at_1e2 : fetchRel feToBytesCode 0x1E2 = some (.store .sb (8 : Fin 32) a1 0x1B, 4) := by decide
theorem tb_at_1e6 : fetchRel feToBytesCode 0x1E6 = some (.alu .or a4 a4 (9 : Fin 32), 2) := by decide
theorem tb_at_1e8 : fetchRel feToBytesCode 0x1E8 = some (.aluImm .srl a0 a3 0x2, 4) := by decide
theorem tb_at_1ec : fetchRel feToBytesCode 0x1EC = some (.aluImm .sll a1 a3 0x7, 4) := by decide
theorem tb_at_1f0 : fetchRel feToBytesCode 0x1F0 = some (.aluImm .srl a3 a3 0xA, 2) := by decide
theorem tb_at_1f2 : fetchRel feToBytesCode 0x1F2 = some (.aluImm .srl a1 a1 0x19, 2) := by decide
theorem tb_at_1f4 : fetchRel feToBytesCode 0x1F4 = some (.store .sb (8 : Fin 32) a4 0x1C, 4) := by decide
theorem tb_at_1f8 : fetchRel feToBytesCode 0x1F8 = some (.store .sb (8 : Fin 32) a0 0x1D, 4) := by decide
theorem tb_at_1fc : fetchRel feToBytesCode 0x1FC = some (.store .sb (8 : Fin 32) a3 0x1E, 4) := by decide
theorem tb_at_200 : fetchRel feToBytesCode 0x200 = some (.store .sb (8 : Fin 32) a1 0x1F, 4) := by decide
theorem tb_at_204 : fetchRel feToBytesCode 0x204 = some (.load .lw ra sp 0x8C, 2) := by decide
theorem tb_at_206 : fetchRel feToBytesCode 0x206 = some (.load .lw (8 : Fin 32) sp 0x88, 2) := by decide
theorem tb_at_208 : fetchRel feToBytesCode 0x208 = some (.load .lw (9 : Fin 32) sp 0x84, 2) := by decide
theorem tb_at_20a : fetchRel feToBytesCode 0x20A = some (.load .lw (18 : Fin 32) sp 0x80, 2) := by decide
theorem tb_at_20c : fetchRel feToBytesCode 0x20C = some (.aluImm .add sp sp 0x90, 2) := by decide
theorem tb_at_20e : fetchRel feToBytesCode 0x20E = some (.jalr x0 ra 0x0, 2) := by decide
end

section Step

variable {M : Word → BitVec 8} {base : Word} {m : Machine} {off : Nat} {f : Fin 32 → Word}
  {code : List Nat}

theorem St.sbG (s : St M base m off f) (hc : CodeIn M base code) {rs1 rs2 : Fin 32} {o len : Word}
    {off' : Nat} (hf : fetchRel code off = some (.store .sb rs1 rs2 o, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') {a v : Word} (ha : f rs1 + o = a) (hv : f rs2 = v) :
    ∃ m1, step m = some m1 ∧ St (memStore8 M a (v.extractLsb' 0 8)) base m1 off' f := by
  subst ha hv; exact s.sb hc hf hn

end Step

/-- Two of the 32 bytes at `out` are at different addresses. -/
theorem tb_off_ne {out : Word} {i j : Nat} (hi : i < 32) (hj : j < 32) (h : i ≠ j) :
    out + BitVec.ofNat 32 i ≠ out + BitVec.ofNat 32 j := fun e => h (by bv_omega)

theorem tb_byte (v : Word) : (v.extractLsb' 0 8).toNat = v.toNat % 2 ^ 8 := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]

end C3.RV32
