import C3BootProofs.Proofs.ImageParseCur

/-! # `image::parse`'s instructions on the current image, decoded from its bytes -/

namespace C3.RV32.Cur

open C3.Image

set_option maxRecDepth 20000

theorem ipc_at_0 : fetchRel imageParseCode 0x0 = some (.aluImm .add sp sp 0xFFFFFEA0, 2) := by decide
theorem ipc_at_2 : fetchRel imageParseCode 0x2 = some (.aluImm .add a4 sp 0x100, 2) := by decide
theorem ipc_at_4 : fetchRel imageParseCode 0x4 = some (.store .sw a4 ra 0x5C, 4) := by decide
theorem ipc_at_8 : fetchRel imageParseCode 0x8 = some (.store .sw a4 (8 : Fin 32) 0x58, 2) := by decide
theorem ipc_at_a : fetchRel imageParseCode 0xA = some (.store .sw a4 (9 : Fin 32) 0x54, 2) := by decide
theorem ipc_at_c : fetchRel imageParseCode 0xC = some (.store .sw a4 (18 : Fin 32) 0x50, 4) := by decide
theorem ipc_at_10 : fetchRel imageParseCode 0x10 = some (.store .sw a4 (19 : Fin 32) 0x4C, 4) := by decide
theorem ipc_at_14 : fetchRel imageParseCode 0x14 = some (.store .sw a4 (20 : Fin 32) 0x48, 4) := by decide
theorem ipc_at_18 : fetchRel imageParseCode 0x18 = some (.store .sw a4 (21 : Fin 32) 0x44, 4) := by decide
theorem ipc_at_1c : fetchRel imageParseCode 0x1C = some (.store .sw a4 (22 : Fin 32) 0x40, 4) := by decide
theorem ipc_at_20 : fetchRel imageParseCode 0x20 = some (.store .sw a4 (23 : Fin 32) 0x3C, 4) := by decide
theorem ipc_at_24 : fetchRel imageParseCode 0x24 = some (.store .sw a4 (24 : Fin 32) 0x38, 4) := by decide
theorem ipc_at_28 : fetchRel imageParseCode 0x28 = some (.store .sw a4 (25 : Fin 32) 0x34, 4) := by decide
theorem ipc_at_2c : fetchRel imageParseCode 0x2C = some (.store .sw a4 (26 : Fin 32) 0x30, 4) := by decide
theorem ipc_at_30 : fetchRel imageParseCode 0x30 = some (.store .sw a4 (27 : Fin 32) 0x2C, 4) := by decide
theorem ipc_at_34 : fetchRel imageParseCode 0x34 = some (.alu .add (9 : Fin 32) x0 a3, 2) := by decide
theorem ipc_at_36 : fetchRel imageParseCode 0x36 = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem ipc_at_38 : fetchRel imageParseCode 0x38 = some (.store .sw sp a1 0x18, 2) := by decide
theorem ipc_at_3a : fetchRel imageParseCode 0x3A = some (.store .sw sp a2 0x1C, 2) := by decide
theorem ipc_at_3c : fetchRel imageParseCode 0x3C = some (.store .sw sp x0 0x20, 2) := by decide
theorem ipc_at_3e : fetchRel imageParseCode 0x3E = some (.lui a1 0x4D493000, 4) := by decide
theorem ipc_at_42 : fetchRel imageParseCode 0x42 = some (.aluImm .add a1 a1 0x343, 4) := by decide
theorem ipc_at_46 : fetchRel imageParseCode 0x46 = some (.aluImm .add a0 sp 0x18, 2) := by decide
theorem ipc_at_48 : fetchRel imageParseCode 0x48 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem ipc_at_4c : fetchRel imageParseCode 0x4C = some (.jalr ra ra 0x540, 4) := by decide
theorem ipc_at_50 : fetchRel imageParseCode 0x50 = some (.aluImm .and a1 a0 0xFF, 4) := by decide
theorem ipc_at_54 : fetchRel imageParseCode 0x54 = some (.aluImm .add a1 a1 0xFFFFFF01, 4) := by decide
theorem ipc_at_58 : fetchRel imageParseCode 0x58 = some (.branch .bne a1 x0 0x5E, 2) := by decide
theorem ipc_at_5a : fetchRel imageParseCode 0x5A = some (.aluImm .add a0 sp 0x18, 2) := by decide
theorem ipc_at_5c : fetchRel imageParseCode 0x5C = some (.auipc ra 0x0, 4) := by decide
theorem ipc_at_60 : fetchRel imageParseCode 0x60 = some (.jalr ra ra 0x3D8, 4) := by decide
theorem ipc_at_64 : fetchRel imageParseCode 0x64 = some (.aluImm .and a1 a0 0xFF, 4) := by decide
theorem ipc_at_68 : fetchRel imageParseCode 0x68 = some (.aluImm .add a1 a1 0xFFFFFF01, 4) := by decide
theorem ipc_at_6c : fetchRel imageParseCode 0x6C = some (.branch .bne a1 x0 0x4A, 2) := by decide
theorem ipc_at_6e : fetchRel imageParseCode 0x6E = some (.aluImm .add a0 sp 0x18, 2) := by decide
theorem ipc_at_70 : fetchRel imageParseCode 0x70 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem ipc_at_74 : fetchRel imageParseCode 0x74 = some (.jalr ra ra 0x418, 4) := by decide
theorem ipc_at_78 : fetchRel imageParseCode 0x78 = some (.aluImm .and a1 a0 0x1, 4) := by decide
theorem ipc_at_7c : fetchRel imageParseCode 0x7C = some (.branch .beq a1 x0 0x6, 2) := by decide
theorem ipc_at_7e : fetchRel imageParseCode 0x7E = some (.aluImm .srl a0 a0 0x8, 2) := by decide
theorem ipc_at_80 : fetchRel imageParseCode 0x80 = some (.jal x0 0x36, 2) := by decide
theorem ipc_at_82 : fetchRel imageParseCode 0x82 = some (.aluImm .srl a0 a0 0x10, 2) := by decide
theorem ipc_at_84 : fetchRel imageParseCode 0x84 = some (.aluImm .add a1 x0 0x5, 2) := by decide
theorem ipc_at_86 : fetchRel imageParseCode 0x86 = some (.branch .bne a0 a1 0x20, 4) := by decide
theorem ipc_at_8a : fetchRel imageParseCode 0x8A = some (.aluImm .add a0 sp 0x18, 2) := by decide
theorem ipc_at_8c : fetchRel imageParseCode 0x8C = some (.auipc ra 0x0, 4) := by decide
theorem ipc_at_90 : fetchRel imageParseCode 0x90 = some (.jalr ra ra 0x3D2, 4) := by decide
theorem ipc_at_94 : fetchRel imageParseCode 0x94 = some (.aluImm .and a0 a0 0x1, 2) := by decide
theorem ipc_at_96 : fetchRel imageParseCode 0x96 = some (.alu .add (18 : Fin 32) x0 a1, 2) := by decide
theorem ipc_at_98 : fetchRel imageParseCode 0x98 = some (.branch .beq a0 x0 0x12, 2) := by decide
theorem ipc_at_9a : fetchRel imageParseCode 0x9A = some (.aluImm .add a0 x0 0xFFFFFFFF, 2) := by decide
theorem ipc_at_9c : fetchRel imageParseCode 0x9C = some (.store .sb (8 : Fin 32) (18 : Fin 32) 0x0, 4) := by decide
theorem ipc_at_a0 : fetchRel imageParseCode 0xA0 = some (.store .sb (8 : Fin 32) a0 0xC, 4) := by decide
theorem ipc_at_a4 : fetchRel imageParseCode 0xA4 = some (.jal x0 0x1C, 2) := by decide
theorem ipc_at_a6 : fetchRel imageParseCode 0xA6 = some (.aluImm .add a0 x0 0x8, 2) := by decide
theorem ipc_at_a8 : fetchRel imageParseCode 0xA8 = some (.jal x0 0xE, 2) := by decide
theorem ipc_at_aa : fetchRel imageParseCode 0xAA = some (.aluImm .and a0 (18 : Fin 32) 0xFF, 4) := by decide
theorem ipc_at_ae : fetchRel imageParseCode 0xAE = some (.aluImm .add a1 x0 0x10, 2) := by decide
theorem ipc_at_b0 : fetchRel imageParseCode 0xB0 = some (.branch .bgeu a1 a0 0x46, 4) := by decide
theorem ipc_at_b4 : fetchRel imageParseCode 0xB4 = some (.aluImm .add a0 x0 0x5, 2) := by decide
theorem ipc_at_b6 : fetchRel imageParseCode 0xB6 = some (.aluImm .add a1 x0 0xFFFFFFFF, 2) := by decide
theorem ipc_at_b8 : fetchRel imageParseCode 0xB8 = some (.store .sb (8 : Fin 32) a0 0x0, 4) := by decide
theorem ipc_at_bc : fetchRel imageParseCode 0xBC = some (.store .sb (8 : Fin 32) a1 0xC, 4) := by decide
theorem ipc_at_c0 : fetchRel imageParseCode 0xC0 = some (.aluImm .add a0 sp 0x100, 2) := by decide
theorem ipc_at_c2 : fetchRel imageParseCode 0xC2 = some (.load .lw ra a0 0x5C, 4) := by decide
theorem ipc_at_c6 : fetchRel imageParseCode 0xC6 = some (.load .lw (8 : Fin 32) a0 0x58, 2) := by decide
theorem ipc_at_c8 : fetchRel imageParseCode 0xC8 = some (.load .lw (9 : Fin 32) a0 0x54, 2) := by decide
theorem ipc_at_ca : fetchRel imageParseCode 0xCA = some (.load .lw (18 : Fin 32) a0 0x50, 4) := by decide
theorem ipc_at_ce : fetchRel imageParseCode 0xCE = some (.load .lw (19 : Fin 32) a0 0x4C, 4) := by decide
theorem ipc_at_d2 : fetchRel imageParseCode 0xD2 = some (.load .lw (20 : Fin 32) a0 0x48, 4) := by decide
theorem ipc_at_d6 : fetchRel imageParseCode 0xD6 = some (.load .lw (21 : Fin 32) a0 0x44, 4) := by decide
theorem ipc_at_da : fetchRel imageParseCode 0xDA = some (.load .lw (22 : Fin 32) a0 0x40, 4) := by decide
theorem ipc_at_de : fetchRel imageParseCode 0xDE = some (.load .lw (23 : Fin 32) a0 0x3C, 4) := by decide
theorem ipc_at_e2 : fetchRel imageParseCode 0xE2 = some (.load .lw (24 : Fin 32) a0 0x38, 4) := by decide
theorem ipc_at_e6 : fetchRel imageParseCode 0xE6 = some (.load .lw (25 : Fin 32) a0 0x34, 4) := by decide
theorem ipc_at_ea : fetchRel imageParseCode 0xEA = some (.load .lw (26 : Fin 32) a0 0x30, 4) := by decide
theorem ipc_at_ee : fetchRel imageParseCode 0xEE = some (.load .lw (27 : Fin 32) a0 0x2C, 4) := by decide
theorem ipc_at_f2 : fetchRel imageParseCode 0xF2 = some (.aluImm .add sp sp 0x160, 2) := by decide
theorem ipc_at_f4 : fetchRel imageParseCode 0xF4 = some (.jalr x0 ra 0x0, 2) := by decide
theorem ipc_at_f6 : fetchRel imageParseCode 0xF6 = some (.aluImm .add a0 sp 0x18, 2) := by decide
theorem ipc_at_f8 : fetchRel imageParseCode 0xF8 = some (.auipc ra 0x0, 4) := by decide
theorem ipc_at_fc : fetchRel imageParseCode 0xFC = some (.jalr ra ra 0x366, 4) := by decide
theorem ipc_at_100 : fetchRel imageParseCode 0x100 = some (.aluImm .and a0 a0 0x1, 2) := by decide
theorem ipc_at_102 : fetchRel imageParseCode 0x102 = some (.alu .add (19 : Fin 32) x0 a1, 2) := by decide
theorem ipc_at_104 : fetchRel imageParseCode 0x104 = some (.branch .beq a0 x0 0xA, 2) := by decide
theorem ipc_at_106 : fetchRel imageParseCode 0x106 = some (.aluImm .add a0 x0 0xFFFFFFFF, 2) := by decide
theorem ipc_at_108 : fetchRel imageParseCode 0x108 = some (.store .sb (8 : Fin 32) (19 : Fin 32) 0x0, 4) := by decide
theorem ipc_at_10c : fetchRel imageParseCode 0x10C = some (.jal x0 0xFFFFFF94, 2) := by decide
theorem ipc_at_10e : fetchRel imageParseCode 0x10E = some (.aluImm .add a0 (19 : Fin 32) 0xFFFFFFEF, 4) := by decide
theorem ipc_at_112 : fetchRel imageParseCode 0x112 = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem ipc_at_116 : fetchRel imageParseCode 0x116 = some (.aluImm .add a1 x0 0xEF, 4) := by decide
theorem ipc_at_11a : fetchRel imageParseCode 0x11A = some (.branch .bgeu a1 a0 0xFFFFFF9A, 4) := by decide
theorem ipc_at_11e : fetchRel imageParseCode 0x11E = some (.aluImm .add a0 sp 0x18, 2) := by decide
theorem ipc_at_120 : fetchRel imageParseCode 0x120 = some (.aluImm .add a1 x0 0x2, 2) := by decide
theorem ipc_at_122 : fetchRel imageParseCode 0x122 = some (.auipc ra 0x0, 4) := by decide
theorem ipc_at_126 : fetchRel imageParseCode 0x126 = some (.jalr ra ra 0x376, 4) := by decide
theorem ipc_at_12a : fetchRel imageParseCode 0x12A = some (.aluImm .and a1 a0 0xFF, 4) := by decide
theorem ipc_at_12e : fetchRel imageParseCode 0x12E = some (.aluImm .add a1 a1 0xFFFFFF01, 4) := by decide
theorem ipc_at_132 : fetchRel imageParseCode 0x132 = some (.branch .bne a1 x0 0xFFFFFF84, 2) := by decide
theorem ipc_at_134 : fetchRel imageParseCode 0x134 = some (.aluImm .add a0 sp 0x24, 2) := by decide
theorem ipc_at_136 : fetchRel imageParseCode 0x136 = some (.aluImm .add a1 sp 0x18, 2) := by decide
theorem ipc_at_138 : fetchRel imageParseCode 0x138 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem ipc_at_13c : fetchRel imageParseCode 0x13C = some (.jalr ra ra 0x3BA, 4) := by decide
theorem ipc_at_140 : fetchRel imageParseCode 0x140 = some (.load .lbu a0 sp 0x24, 4) := by decide
theorem ipc_at_144 : fetchRel imageParseCode 0x144 = some (.branch .bne a0 x0 0x16, 2) := by decide
theorem ipc_at_146 : fetchRel imageParseCode 0x146 = some (.load .lw (20 : Fin 32) sp 0x28, 2) := by decide
theorem ipc_at_148 : fetchRel imageParseCode 0x148 = some (.aluImm .add a0 sp 0x24, 2) := by decide
theorem ipc_at_14a : fetchRel imageParseCode 0x14A = some (.aluImm .add a1 sp 0x18, 2) := by decide
theorem ipc_at_14c : fetchRel imageParseCode 0x14C = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem ipc_at_150 : fetchRel imageParseCode 0x150 = some (.jalr ra ra 0x3A6, 4) := by decide
theorem ipc_at_154 : fetchRel imageParseCode 0x154 = some (.load .lbu a0 sp 0x24, 4) := by decide
theorem ipc_at_158 : fetchRel imageParseCode 0x158 = some (.branch .beq a0 x0 0x8, 2) := by decide
theorem ipc_at_15a : fetchRel imageParseCode 0x15A = some (.load .lbu a0 sp 0x25, 4) := by decide
theorem ipc_at_15e : fetchRel imageParseCode 0x15E = some (.jal x0 0xFFFFFF58, 2) := by decide
theorem ipc_at_160 : fetchRel imageParseCode 0x160 = some (.load .lw a0 sp 0x28, 2) := by decide
theorem ipc_at_162 : fetchRel imageParseCode 0x162 = some (.branch .bne a0 (9 : Fin 32) 0x196, 4) := by decide
theorem ipc_at_166 : fetchRel imageParseCode 0x166 = some (.store .sw sp (20 : Fin 32) 0x8, 2) := by decide
theorem ipc_at_168 : fetchRel imageParseCode 0x168 = some (.aluImm .and a0 (19 : Fin 32) 0xFF, 4) := by decide
theorem ipc_at_16c : fetchRel imageParseCode 0x16C = some (.store .sw sp a0 0xC, 2) := by decide
theorem ipc_at_16e : fetchRel imageParseCode 0x16E = some (.aluImm .add a0 sp 0x24, 2) := by decide
theorem ipc_at_170 : fetchRel imageParseCode 0x170 = some (.aluImm .add a1 x0 0x10, 2) := by decide
theorem ipc_at_172 : fetchRel imageParseCode 0x172 = some (.branch .beq a1 x0 0x12, 2) := by decide
theorem ipc_at_174 : fetchRel imageParseCode 0x174 = some (.aluImm .add a2 x0 0x0, 2) := by decide
theorem ipc_at_176 : fetchRel imageParseCode 0x176 = some (.store .sw a0 a2 0x0, 2) := by decide
theorem ipc_at_178 : fetchRel imageParseCode 0x178 = some (.store .sw a0 a2 0x4, 2) := by decide
theorem ipc_at_17a : fetchRel imageParseCode 0x17A = some (.store .sw a0 a2 0x8, 2) := by decide
theorem ipc_at_17c : fetchRel imageParseCode 0x17C = some (.store .sw a0 a2 0xC, 2) := by decide
theorem ipc_at_17e : fetchRel imageParseCode 0x17E = some (.aluImm .add a0 a0 0x10, 2) := by decide
theorem ipc_at_180 : fetchRel imageParseCode 0x180 = some (.aluImm .add a1 a1 0xFFFFFFFF, 2) := by decide
theorem ipc_at_182 : fetchRel imageParseCode 0x182 = some (.branch .bne a1 x0 0xFFFFFFF2, 2) := by decide
theorem ipc_at_184 : fetchRel imageParseCode 0x184 = some (.store .sw sp x0 0x10, 2) := by decide
theorem ipc_at_186 : fetchRel imageParseCode 0x186 = some (.lui a0 0x10000, 2) := by decide
theorem ipc_at_188 : fetchRel imageParseCode 0x188 = some (.load .lw (27 : Fin 32) sp 0xC, 2) := by decide
theorem ipc_at_18a : fetchRel imageParseCode 0x18A = some (.aluImm .sll (27 : Fin 32) (27 : Fin 32) 0x4, 2) := by decide
theorem ipc_at_18c : fetchRel imageParseCode 0x18C = some (.aluImm .add a0 a0 0xFFFFFFFF, 2) := by decide
theorem ipc_at_18e : fetchRel imageParseCode 0x18E = some (.store .sw sp a0 0x14, 2) := by decide
theorem ipc_at_190 : fetchRel imageParseCode 0x190 = some (.aluImm .add (21 : Fin 32) (27 : Fin 32) 0x14, 4) := by decide
theorem ipc_at_194 : fetchRel imageParseCode 0x194 = some (.aluImm .add (24 : Fin 32) x0 0x100, 4) := by decide
theorem ipc_at_198 : fetchRel imageParseCode 0x198 = some (.aluImm .add (25 : Fin 32) sp 0x2C, 4) := by decide
theorem ipc_at_19c : fetchRel imageParseCode 0x19C = some (.alu .add a0 (27 : Fin 32) (24 : Fin 32), 4) := by decide
theorem ipc_at_1a0 : fetchRel imageParseCode 0x1A0 = some (.aluImm .add a0 a0 0xFFFFFF00, 4) := by decide
theorem ipc_at_1a4 : fetchRel imageParseCode 0x1A4 = some (.branch .beq a0 x0 0x158, 4) := by decide
theorem ipc_at_1a8 : fetchRel imageParseCode 0x1A8 = some (.branch .beq (24 : Fin 32) x0 0x154, 4) := by decide
theorem ipc_at_1ac : fetchRel imageParseCode 0x1AC = some (.aluImm .add a0 sp 0x18, 2) := by decide
theorem ipc_at_1ae : fetchRel imageParseCode 0x1AE = some (.auipc ra 0x0, 4) := by decide
theorem ipc_at_1b2 : fetchRel imageParseCode 0x1B2 = some (.jalr ra ra 0x2B0, 4) := by decide
theorem ipc_at_1b6 : fetchRel imageParseCode 0x1B6 = some (.aluImm .and a0 a0 0x1, 2) := by decide
theorem ipc_at_1b8 : fetchRel imageParseCode 0x1B8 = some (.branch .bne a0 x0 0x6E, 2) := by decide
theorem ipc_at_1ba : fetchRel imageParseCode 0x1BA = some (.aluImm .add a1 a1 0xFFFFFFFF, 2) := by decide
theorem ipc_at_1bc : fetchRel imageParseCode 0x1BC = some (.aluImm .and (22 : Fin 32) a1 0xFF, 4) := by decide
theorem ipc_at_1c0 : fetchRel imageParseCode 0x1C0 = some (.aluImm .add a0 x0 0x3, 2) := by decide
theorem ipc_at_1c2 : fetchRel imageParseCode 0x1C2 = some (.branch .bgeu a0 (22 : Fin 32) 0x8, 4) := by decide
theorem ipc_at_1c6 : fetchRel imageParseCode 0x1C6 = some (.aluImm .add a1 x0 0x9, 2) := by decide
theorem ipc_at_1c8 : fetchRel imageParseCode 0x1C8 = some (.jal x0 0x5E, 2) := by decide
theorem ipc_at_1ca : fetchRel imageParseCode 0x1CA = some (.aluImm .add a0 sp 0x18, 2) := by decide
theorem ipc_at_1cc : fetchRel imageParseCode 0x1CC = some (.aluImm .add a1 x0 0x3, 2) := by decide
theorem ipc_at_1ce : fetchRel imageParseCode 0x1CE = some (.auipc ra 0x0, 4) := by decide
theorem ipc_at_1d2 : fetchRel imageParseCode 0x1D2 = some (.jalr ra ra 0x2CA, 4) := by decide
theorem ipc_at_1d6 : fetchRel imageParseCode 0x1D6 = some (.alu .add a1 x0 a0, 2) := by decide
theorem ipc_at_1d8 : fetchRel imageParseCode 0x1D8 = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem ipc_at_1dc : fetchRel imageParseCode 0x1DC = some (.aluImm .add a0 a0 0xFFFFFF01, 4) := by decide
theorem ipc_at_1e0 : fetchRel imageParseCode 0x1E0 = some (.branch .bne a0 x0 0x46, 2) := by decide
theorem ipc_at_1e2 : fetchRel imageParseCode 0x1E2 = some (.aluImm .add a0 sp 0x124, 2) := by decide
theorem ipc_at_1e4 : fetchRel imageParseCode 0x1E4 = some (.aluImm .add a1 sp 0x18, 2) := by decide
theorem ipc_at_1e6 : fetchRel imageParseCode 0x1E6 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem ipc_at_1ea : fetchRel imageParseCode 0x1EA = some (.jalr ra ra 0x30C, 4) := by decide
theorem ipc_at_1ee : fetchRel imageParseCode 0x1EE = some (.load .lbu a0 sp 0x124, 4) := by decide
theorem ipc_at_1f2 : fetchRel imageParseCode 0x1F2 = some (.branch .bne a0 x0 0x30, 2) := by decide
theorem ipc_at_1f4 : fetchRel imageParseCode 0x1F4 = some (.load .lw (23 : Fin 32) sp 0x128, 4) := by decide
theorem ipc_at_1f8 : fetchRel imageParseCode 0x1F8 = some (.aluImm .add a0 sp 0x124, 2) := by decide
theorem ipc_at_1fa : fetchRel imageParseCode 0x1FA = some (.aluImm .add a1 sp 0x18, 2) := by decide
theorem ipc_at_1fc : fetchRel imageParseCode 0x1FC = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem ipc_at_200 : fetchRel imageParseCode 0x200 = some (.jalr ra ra 0x2F6, 4) := by decide
theorem ipc_at_204 : fetchRel imageParseCode 0x204 = some (.load .lbu a0 sp 0x124, 4) := by decide
theorem ipc_at_208 : fetchRel imageParseCode 0x208 = some (.branch .bne a0 x0 0x1A, 2) := by decide
theorem ipc_at_20a : fetchRel imageParseCode 0x20A = some (.load .lw a0 sp 0x128, 4) := by decide
theorem ipc_at_20e : fetchRel imageParseCode 0x20E = some (.store .sw sp a0 0x4, 2) := by decide
theorem ipc_at_210 : fetchRel imageParseCode 0x210 = some (.aluImm .add a0 sp 0x124, 2) := by decide
theorem ipc_at_212 : fetchRel imageParseCode 0x212 = some (.aluImm .add a1 sp 0x18, 2) := by decide
theorem ipc_at_214 : fetchRel imageParseCode 0x214 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem ipc_at_218 : fetchRel imageParseCode 0x218 = some (.jalr ra ra 0x2DE, 4) := by decide
theorem ipc_at_21c : fetchRel imageParseCode 0x21C = some (.load .lbu a0 sp 0x124, 4) := by decide
theorem ipc_at_220 : fetchRel imageParseCode 0x220 = some (.branch .beq a0 x0 0xBE, 2) := by decide
theorem ipc_at_222 : fetchRel imageParseCode 0x222 = some (.load .lbu a1 sp 0x125, 4) := by decide
theorem ipc_at_226 : fetchRel imageParseCode 0x226 = some (.aluImm .and (23 : Fin 32) a1 0xFF, 4) := by decide
theorem ipc_at_22a : fetchRel imageParseCode 0x22A = some (.aluImm .or (26 : Fin 32) (26 : Fin 32) 0xFF, 4) := by decide
theorem ipc_at_22e : fetchRel imageParseCode 0x22E = some (.aluImm .and a2 (26 : Fin 32) 0xFF, 4) := by decide
theorem ipc_at_232 : fetchRel imageParseCode 0x232 = some (.aluImm .add a0 a2 0xFFFFFF01, 4) := by decide
theorem ipc_at_236 : fetchRel imageParseCode 0x236 = some (.branch .beq a0 x0 0xDA, 2) := by decide
theorem ipc_at_238 : fetchRel imageParseCode 0x238 = some (.aluImm .add a6 x0 0x9, 2) := by decide
theorem ipc_at_23a : fetchRel imageParseCode 0x23A = some (.branch .beq (19 : Fin 32) x0 0x1F2, 4) := by decide
theorem ipc_at_23e : fetchRel imageParseCode 0x23E = some (.alu .add a1 (20 : Fin 32) (19 : Fin 32), 4) := by decide
theorem ipc_at_242 : fetchRel imageParseCode 0x242 = some (.branch .bltu a1 (20 : Fin 32) 0xD2, 4) := by decide
theorem ipc_at_246 : fetchRel imageParseCode 0x246 = some (.branch .bltu (9 : Fin 32) a1 0x1E6, 4) := by decide
theorem ipc_at_24a : fetchRel imageParseCode 0x24A = some (.aluImm .sll a4 (26 : Fin 32) 0x18, 4) := by decide
theorem ipc_at_24e : fetchRel imageParseCode 0x24E = some (.aluImm .srl a4 a4 0x16, 2) := by decide
theorem ipc_at_250 : fetchRel imageParseCode 0x250 = some (.lui a3 0x3FCC5000, 4) := by decide
theorem ipc_at_254 : fetchRel imageParseCode 0x254 = some (.aluImm .add a3 a3 0xFFFFF980, 4) := by decide
theorem ipc_at_258 : fetchRel imageParseCode 0x258 = some (.alu .add a3 a3 a4, 2) := by decide
theorem ipc_at_25a : fetchRel imageParseCode 0x25A = some (.load .lw a0 a3 0x0, 2) := by decide
theorem ipc_at_25c : fetchRel imageParseCode 0x25C = some (.load .lw a3 sp 0x10, 2) := by decide
theorem ipc_at_25e : fetchRel imageParseCode 0x25E = some (.aluImm .sll a3 a3 0x8, 2) := by decide
theorem ipc_at_260 : fetchRel imageParseCode 0x260 = some (.aluImm .and a5 (23 : Fin 32) 0xFF, 4) := by decide
theorem ipc_at_264 : fetchRel imageParseCode 0x264 = some (.alu .or a3 a3 a5, 2) := by decide
theorem ipc_at_266 : fetchRel imageParseCode 0x266 = some (.alu .add a5 a3 (19 : Fin 32), 4) := by decide
theorem ipc_at_26a : fetchRel imageParseCode 0x26A = some (.branch .bltu a0 a5 0x1C2, 4) := by decide
theorem ipc_at_26e : fetchRel imageParseCode 0x26E = some (.branch .bltu a5 a3 0x1BE, 4) := by decide
theorem ipc_at_272 : fetchRel imageParseCode 0x272 = some (.lui a0 0x3FCC5000, 4) := by decide
theorem ipc_at_276 : fetchRel imageParseCode 0x276 = some (.aluImm .add a0 a0 0xFFFFF990, 4) := by decide
theorem ipc_at_27a : fetchRel imageParseCode 0x27A = some (.alu .add a4 a4 a0, 2) := by decide
theorem ipc_at_27c : fetchRel imageParseCode 0x27C = some (.load .lw a0 a4 0x0, 2) := by decide
theorem ipc_at_27e : fetchRel imageParseCode 0x27E = some (.branch .bltu a3 a0 0x1AE, 4) := by decide
theorem ipc_at_282 : fetchRel imageParseCode 0x282 = some (.alu .or a4 a3 (20 : Fin 32), 4) := by decide
theorem ipc_at_286 : fetchRel imageParseCode 0x286 = some (.load .lw a0 sp 0x14, 2) := by decide
theorem ipc_at_288 : fetchRel imageParseCode 0x288 = some (.alu .and a0 a0 a4, 2) := by decide
theorem ipc_at_28a : fetchRel imageParseCode 0x28A = some (.branch .beq a0 x0 0xA, 2) := by decide
theorem ipc_at_28c : fetchRel imageParseCode 0x28C = some (.aluImm .add a0 x0 0x2, 2) := by decide
theorem ipc_at_28e : fetchRel imageParseCode 0x28E = some (.branch .bltu a2 a0 0x19E, 4) := by decide
theorem ipc_at_292 : fetchRel imageParseCode 0x292 = some (.jal x0 0x12, 2) := by decide
theorem ipc_at_294 : fetchRel imageParseCode 0x294 = some (.aluImm .add a0 x0 0x1, 2) := by decide
theorem ipc_at_296 : fetchRel imageParseCode 0x296 = some (.branch .bltu a0 a2 0xE, 4) := by decide
theorem ipc_at_29a : fetchRel imageParseCode 0x29A = some (.load .lw a0 sp 0x14, 2) := by decide
theorem ipc_at_29c : fetchRel imageParseCode 0x29C = some (.alu .and a0 (19 : Fin 32) a0, 4) := by decide
theorem ipc_at_2a0 : fetchRel imageParseCode 0x2A0 = some (.branch .bne a0 x0 0x18C, 4) := by decide
theorem ipc_at_2a4 : fetchRel imageParseCode 0x2A4 = some (.aluImm .and a4 a4 0x3, 2) := by decide
theorem ipc_at_2a6 : fetchRel imageParseCode 0x2A6 = some (.branch .beq a4 x0 0xA, 2) := by decide
theorem ipc_at_2a8 : fetchRel imageParseCode 0x2A8 = some (.aluImm .add a0 x0 0x1, 2) := by decide
theorem ipc_at_2aa : fetchRel imageParseCode 0x2AA = some (.branch .bltu a0 a2 0x182, 4) := by decide
theorem ipc_at_2ae : fetchRel imageParseCode 0x2AE = some (.jal x0 0x14, 2) := by decide
theorem ipc_at_2b0 : fetchRel imageParseCode 0x2B0 = some (.aluImm .and a0 (19 : Fin 32) 0x3, 4) := by decide
theorem ipc_at_2b4 : fetchRel imageParseCode 0x2B4 = some (.aluImm .sltu a0 a0 0x1, 4) := by decide
theorem ipc_at_2b8 : fetchRel imageParseCode 0x2B8 = some (.aluImm .sltu a2 a2 0x2, 4) := by decide
theorem ipc_at_2bc : fetchRel imageParseCode 0x2BC = some (.alu .or a0 a0 a2, 2) := by decide
theorem ipc_at_2be : fetchRel imageParseCode 0x2BE = some (.branch .beq a0 x0 0x16E, 4) := by decide
theorem ipc_at_2c2 : fetchRel imageParseCode 0x2C2 = some (.branch .bltu (20 : Fin 32) (21 : Fin 32) 0x16A, 4) := by decide
theorem ipc_at_2c6 : fetchRel imageParseCode 0x2C6 = some (.store .sw (25 : Fin 32) a3 0xFFFFFFF8, 4) := by decide
theorem ipc_at_2ca : fetchRel imageParseCode 0x2CA = some (.store .sw (25 : Fin 32) (20 : Fin 32) 0xFFFFFFFC, 4) := by decide
theorem ipc_at_2ce : fetchRel imageParseCode 0x2CE = some (.store .sw (25 : Fin 32) (19 : Fin 32) 0x0, 4) := by decide
theorem ipc_at_2d2 : fetchRel imageParseCode 0x2D2 = some (.store .sw (25 : Fin 32) (26 : Fin 32) 0x4, 4) := by decide
theorem ipc_at_2d6 : fetchRel imageParseCode 0x2D6 = some (.aluImm .add (24 : Fin 32) (24 : Fin 32) 0xFFFFFFF0, 2) := by decide
theorem ipc_at_2d8 : fetchRel imageParseCode 0x2D8 = some (.aluImm .add (25 : Fin 32) (25 : Fin 32) 0x10, 2) := by decide
theorem ipc_at_2da : fetchRel imageParseCode 0x2DA = some (.alu .add (21 : Fin 32) x0 a1, 2) := by decide
theorem ipc_at_2dc : fetchRel imageParseCode 0x2DC = some (.jal x0 0xFFFFFEC0, 2) := by decide
theorem ipc_at_2de : fetchRel imageParseCode 0x2DE = some (.load .lw (19 : Fin 32) sp 0x128, 4) := by decide
theorem ipc_at_2e2 : fetchRel imageParseCode 0x2E2 = some (.load .lw a0 sp 0x0, 2) := by decide
theorem ipc_at_2e4 : fetchRel imageParseCode 0x2E4 = some (.aluImm .and a0 a0 0xFFFFFF00, 4) := by decide
theorem ipc_at_2e8 : fetchRel imageParseCode 0x2E8 = some (.alu .or (26 : Fin 32) a0 (22 : Fin 32), 4) := by decide
theorem ipc_at_2ec : fetchRel imageParseCode 0x2EC = some (.aluImm .srl a0 (23 : Fin 32) 0x8, 4) := by decide
theorem ipc_at_2f0 : fetchRel imageParseCode 0x2F0 = some (.store .sw sp a0 0x10, 2) := by decide
theorem ipc_at_2f2 : fetchRel imageParseCode 0x2F2 = some (.store .sw sp (26 : Fin 32) 0x0, 2) := by decide
theorem ipc_at_2f4 : fetchRel imageParseCode 0x2F4 = some (.load .lw (20 : Fin 32) sp 0x4, 2) := by decide
theorem ipc_at_2f6 : fetchRel imageParseCode 0x2F6 = some (.jal x0 0xFFFFFF38, 2) := by decide
theorem ipc_at_2f8 : fetchRel imageParseCode 0x2F8 = some (.aluImm .add a0 x0 0x7, 2) := by decide
theorem ipc_at_2fa : fetchRel imageParseCode 0x2FA = some (.jal x0 0xFFFFFDBC, 2) := by decide
theorem ipc_at_2fc : fetchRel imageParseCode 0x2FC = some (.branch .bne (21 : Fin 32) (9 : Fin 32) 0x10, 4) := by decide
theorem ipc_at_300 : fetchRel imageParseCode 0x300 = some (.aluImm .add a0 x0 0x10, 2) := by decide
theorem ipc_at_302 : fetchRel imageParseCode 0x302 = some (.load .lw a1 sp 0xC, 2) := by decide
theorem ipc_at_304 : fetchRel imageParseCode 0x304 = some (.branch .bgeu a0 a1 0x14, 4) := by decide
theorem ipc_at_308 : fetchRel imageParseCode 0x308 = some (.aluImm .add a6 x0 0x5, 2) := by decide
theorem ipc_at_30a : fetchRel imageParseCode 0x30A = some (.jal x0 0x122, 2) := by decide
theorem ipc_at_30c : fetchRel imageParseCode 0x30C = some (.aluImm .add a6 x0 0x9, 2) := by decide
theorem ipc_at_30e : fetchRel imageParseCode 0x30E = some (.jal x0 0x11E, 2) := by decide
theorem ipc_at_310 : fetchRel imageParseCode 0x310 = some (.alu .add a6 x0 (23 : Fin 32), 2) := by decide
theorem ipc_at_312 : fetchRel imageParseCode 0x312 = some (.jal x0 0x11A, 2) := by decide
theorem ipc_at_314 : fetchRel imageParseCode 0x314 = some (.aluImm .add a6 x0 0x6, 2) := by decide
theorem ipc_at_316 : fetchRel imageParseCode 0x316 = some (.jal x0 0x116, 2) := by decide
theorem ipc_at_318 : fetchRel imageParseCode 0x318 = some (.aluImm .add (20 : Fin 32) x0 0x0, 2) := by decide
theorem ipc_at_31a : fetchRel imageParseCode 0x31A = some (.load .lw a0 sp 0xC, 2) := by decide
theorem ipc_at_31c : fetchRel imageParseCode 0x31C = some (.aluImm .sltu a0 a0 0x11, 4) := by decide
theorem ipc_at_320 : fetchRel imageParseCode 0x320 = some (.aluImm .add (21 : Fin 32) sp 0x24, 4) := by decide
theorem ipc_at_324 : fetchRel imageParseCode 0x324 = some (.alu .sub a0 x0 a0, 4) := by decide
theorem ipc_at_328 : fetchRel imageParseCode 0x328 = some (.alu .and a0 a0 (21 : Fin 32), 4) := by decide
theorem ipc_at_32c : fetchRel imageParseCode 0x32C = some (.store .sw sp a0 0x14, 2) := by decide
theorem ipc_at_32e : fetchRel imageParseCode 0x32E = some (.alu .add (27 : Fin 32) (27 : Fin 32) (21 : Fin 32), 2) := by decide
theorem ipc_at_330 : fetchRel imageParseCode 0x330 = some (.aluImm .add (22 : Fin 32) x0 0x2, 2) := by decide
theorem ipc_at_332 : fetchRel imageParseCode 0x332 = some (.branch .beq (21 : Fin 32) (27 : Fin 32) 0xA2, 4) := by decide
theorem ipc_at_336 : fetchRel imageParseCode 0x336 = some (.load .lw a1 (21 : Fin 32) 0x0, 4) := by decide
theorem ipc_at_33a : fetchRel imageParseCode 0x33A = some (.load .lbu a2 (21 : Fin 32) 0xC, 4) := by decide
theorem ipc_at_33e : fetchRel imageParseCode 0x33E = some (.aluImm .add a0 sp 0x124, 2) := by decide
theorem ipc_at_340 : fetchRel imageParseCode 0x340 = some (.auipc ra 0x0, 4) := by decide
theorem ipc_at_344 : fetchRel imageParseCode 0x344 = some (.jalr ra ra 0x190, 4) := by decide
theorem ipc_at_348 : fetchRel imageParseCode 0x348 = some (.load .lbu (23 : Fin 32) sp 0x124, 4) := by decide
theorem ipc_at_34c : fetchRel imageParseCode 0x34C = some (.branch .beq (23 : Fin 32) (22 : Fin 32) 0xDC, 4) := by decide
theorem ipc_at_350 : fetchRel imageParseCode 0x350 = some (.load .lw (25 : Fin 32) sp 0x128, 4) := by decide
theorem ipc_at_354 : fetchRel imageParseCode 0x354 = some (.aluImm .add (24 : Fin 32) (21 : Fin 32) 0x10, 4) := by decide
theorem ipc_at_358 : fetchRel imageParseCode 0x358 = some (.aluImm .add (20 : Fin 32) (20 : Fin 32) 0x1, 2) := by decide
theorem ipc_at_35a : fetchRel imageParseCode 0x35A = some (.load .lw (19 : Fin 32) sp 0x14, 2) := by decide
theorem ipc_at_35c : fetchRel imageParseCode 0x35C = some (.alu .add a1 x0 (20 : Fin 32), 2) := by decide
theorem ipc_at_35e : fetchRel imageParseCode 0x35E = some (.branch .bne a1 x0 0x60, 2) := by decide
theorem ipc_at_360 : fetchRel imageParseCode 0x360 = some (.alu .add (26 : Fin 32) x0 (19 : Fin 32), 2) := by decide
theorem ipc_at_362 : fetchRel imageParseCode 0x362 = some (.branch .beq (19 : Fin 32) (27 : Fin 32) 0x6C, 4) := by decide
theorem ipc_at_366 : fetchRel imageParseCode 0x366 = some (.aluImm .add (19 : Fin 32) (26 : Fin 32) 0x10, 4) := by decide
theorem ipc_at_36a : fetchRel imageParseCode 0x36A = some (.branch .beq (26 : Fin 32) x0 0x64, 4) := by decide
theorem ipc_at_36e : fetchRel imageParseCode 0x36E = some (.load .lw a1 (26 : Fin 32) 0x0, 4) := by decide
theorem ipc_at_372 : fetchRel imageParseCode 0x372 = some (.load .lbu a2 (26 : Fin 32) 0xC, 4) := by decide
theorem ipc_at_376 : fetchRel imageParseCode 0x376 = some (.aluImm .add a0 sp 0x124, 2) := by decide
theorem ipc_at_378 : fetchRel imageParseCode 0x378 = some (.auipc ra 0x0, 4) := by decide
theorem ipc_at_37c : fetchRel imageParseCode 0x37C = some (.jalr ra ra 0x158, 4) := by decide
theorem ipc_at_380 : fetchRel imageParseCode 0x380 = some (.load .lbu a0 sp 0x124, 4) := by decide
theorem ipc_at_384 : fetchRel imageParseCode 0x384 = some (.branch .beq a0 (22 : Fin 32) 0xA4, 4) := by decide
theorem ipc_at_388 : fetchRel imageParseCode 0x388 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem ipc_at_38a : fetchRel imageParseCode 0x38A = some (.branch .bne (23 : Fin 32) a0 0xFFFFFFD4, 4) := by decide
theorem ipc_at_38e : fetchRel imageParseCode 0x38E = some (.load .lw a2 (21 : Fin 32) 0x8, 4) := by decide
theorem ipc_at_392 : fetchRel imageParseCode 0x392 = some (.alu .add a1 a2 (25 : Fin 32), 4) := by decide
theorem ipc_at_396 : fetchRel imageParseCode 0x396 = some (.aluImm .add a6 x0 0xA, 2) := by decide
theorem ipc_at_398 : fetchRel imageParseCode 0x398 = some (.branch .bltu a1 a2 0x94, 4) := by decide
theorem ipc_at_39c : fetchRel imageParseCode 0x39C = some (.load .lw a2 sp 0x128, 4) := by decide
theorem ipc_at_3a0 : fetchRel imageParseCode 0x3A0 = some (.load .lw a4 (26 : Fin 32) 0x8, 4) := by decide
theorem ipc_at_3a4 : fetchRel imageParseCode 0x3A4 = some (.alu .add a3 a4 a2, 4) := by decide
theorem ipc_at_3a8 : fetchRel imageParseCode 0x3A8 = some (.alu .sltu a4 a3 a4, 4) := by decide
theorem ipc_at_3ac : fetchRel imageParseCode 0x3AC = some (.branch .bne a4 x0 0x80, 2) := by decide
theorem ipc_at_3ae : fetchRel imageParseCode 0x3AE = some (.alu .sltu a3 (25 : Fin 32) a3, 4) := by decide
theorem ipc_at_3b2 : fetchRel imageParseCode 0x3B2 = some (.alu .sltu a1 a2 a1, 4) := by decide
theorem ipc_at_3b6 : fetchRel imageParseCode 0x3B6 = some (.alu .and a3 a3 a1, 2) := by decide
theorem ipc_at_3b8 : fetchRel imageParseCode 0x3B8 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem ipc_at_3ba : fetchRel imageParseCode 0x3BA = some (.branch .bne a3 x0 0x72, 2) := by decide
theorem ipc_at_3bc : fetchRel imageParseCode 0x3BC = some (.jal x0 0xFFFFFFA2, 2) := by decide
theorem ipc_at_3be : fetchRel imageParseCode 0x3BE = some (.alu .sub a0 (27 : Fin 32) (19 : Fin 32), 4) := by decide
theorem ipc_at_3c2 : fetchRel imageParseCode 0x3C2 = some (.aluImm .srl a0 a0 0x4, 2) := by decide
theorem ipc_at_3c4 : fetchRel imageParseCode 0x3C4 = some (.aluImm .sll (26 : Fin 32) a1 0x4, 4) := by decide
theorem ipc_at_3c8 : fetchRel imageParseCode 0x3C8 = some (.alu .add (26 : Fin 32) (26 : Fin 32) (19 : Fin 32), 2) := by decide
theorem ipc_at_3ca : fetchRel imageParseCode 0x3CA = some (.branch .bltu a1 a0 0xFFFFFF9C, 4) := by decide
theorem ipc_at_3ce : fetchRel imageParseCode 0x3CE = some (.alu .add (21 : Fin 32) x0 (24 : Fin 32), 2) := by decide
theorem ipc_at_3d0 : fetchRel imageParseCode 0x3D0 = some (.branch .bne (24 : Fin 32) (27 : Fin 32) 0xFFFFFF66, 4) := by decide
theorem ipc_at_3d4 : fetchRel imageParseCode 0x3D4 = some (.load .lw a1 sp 0x8, 2) := by decide
theorem ipc_at_3d6 : fetchRel imageParseCode 0x3D6 = some (.aluImm .and a1 a1 0x1, 2) := by decide
theorem ipc_at_3d8 : fetchRel imageParseCode 0x3D8 = some (.aluImm .add a6 x0 0xB, 2) := by decide
theorem ipc_at_3da : fetchRel imageParseCode 0x3DA = some (.branch .bne a1 x0 0x52, 2) := by decide
theorem ipc_at_3dc : fetchRel imageParseCode 0x3DC = some (.load .lw a1 sp 0x14, 2) := by decide
theorem ipc_at_3de : fetchRel imageParseCode 0x3DE = some (.branch .beq a1 (27 : Fin 32) 0x4E, 4) := by decide
theorem ipc_at_3e2 : fetchRel imageParseCode 0x3E2 = some (.load .lbu a2 a1 0xC, 4) := by decide
theorem ipc_at_3e6 : fetchRel imageParseCode 0x3E6 = some (.aluImm .and a2 a2 0x1, 2) := by decide
theorem ipc_at_3e8 : fetchRel imageParseCode 0x3E8 = some (.aluImm .add a0 a1 0x10, 4) := by decide
theorem ipc_at_3ec : fetchRel imageParseCode 0x3EC = some (.store .sw sp a0 0x14, 2) := by decide
theorem ipc_at_3ee : fetchRel imageParseCode 0x3EE = some (.branch .bne a2 x0 0xFFFFFFEE, 2) := by decide
theorem ipc_at_3f0 : fetchRel imageParseCode 0x3F0 = some (.load .lw a2 a1 0x0, 2) := by decide
theorem ipc_at_3f2 : fetchRel imageParseCode 0x3F2 = some (.load .lw a0 sp 0x8, 2) := by decide
theorem ipc_at_3f4 : fetchRel imageParseCode 0x3F4 = some (.branch .bltu a0 a2 0xFFFFFFE8, 4) := by decide
theorem ipc_at_3f8 : fetchRel imageParseCode 0x3F8 = some (.load .lw a1 a1 0x8, 2) := by decide
theorem ipc_at_3fa : fetchRel imageParseCode 0x3FA = some (.load .lw a0 sp 0x8, 2) := by decide
theorem ipc_at_3fc : fetchRel imageParseCode 0x3FC = some (.alu .sub a2 a0 a2, 4) := by decide
theorem ipc_at_400 : fetchRel imageParseCode 0x400 = some (.branch .bgeu a2 a1 0xFFFFFFDC, 4) := by decide
theorem ipc_at_404 : fetchRel imageParseCode 0x404 = some (.aluImm .add a1 sp 0x24, 2) := by decide
theorem ipc_at_406 : fetchRel imageParseCode 0x406 = some (.aluImm .add a2 x0 0x100, 4) := by decide
theorem ipc_at_40a : fetchRel imageParseCode 0x40A = some (.alu .add a0 x0 (8 : Fin 32), 2) := by decide
theorem ipc_at_40c : fetchRel imageParseCode 0x40C = some (.auipc ra 0x9000, 4) := by decide
theorem ipc_at_410 : fetchRel imageParseCode 0x410 = some (.jalr ra ra 0x76A, 4) := by decide
theorem ipc_at_414 : fetchRel imageParseCode 0x414 = some (.load .lw a0 sp 0x8, 2) := by decide
theorem ipc_at_416 : fetchRel imageParseCode 0x416 = some (.aluImm .add a1 (8 : Fin 32) 0x100, 4) := by decide
theorem ipc_at_41a : fetchRel imageParseCode 0x41A = some (.store .sw a1 a0 0x0, 2) := by decide
theorem ipc_at_41c : fetchRel imageParseCode 0x41C = some (.store .sw a1 (9 : Fin 32) 0x4, 2) := by decide
theorem ipc_at_41e : fetchRel imageParseCode 0x41E = some (.load .lw a0 sp 0xC, 2) := by decide
theorem ipc_at_420 : fetchRel imageParseCode 0x420 = some (.store .sw a1 a0 0x8, 2) := by decide
theorem ipc_at_422 : fetchRel imageParseCode 0x422 = some (.store .sb (8 : Fin 32) (18 : Fin 32) 0x10C, 4) := by decide
theorem ipc_at_426 : fetchRel imageParseCode 0x426 = some (.jal x0 0xFFFFFC9A, 2) := by decide
theorem ipc_at_428 : fetchRel imageParseCode 0x428 = some (.load .lbu a6 sp 0x125, 4) := by decide
theorem ipc_at_42c : fetchRel imageParseCode 0x42C = some (.aluImm .add a1 x0 0xFFFFFFFF, 2) := by decide
theorem ipc_at_42e : fetchRel imageParseCode 0x42E = some (.store .sb (8 : Fin 32) a6 0x0, 4) := by decide
theorem ipc_at_432 : fetchRel imageParseCode 0x432 = some (.jal x0 0xFFFFFC8A, 2) := by decide

end C3.RV32.Cur
