import C3BootProofs.Proofs.DecCall

/-!
# Steps of `CompressedEdwardsY::decompress`

The `fetchRel` lemmas for each instruction of `decompress`, and lemmas that
run one instruction from the invariant `DecSt`.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem dec_at_0 : fetchRel edDecompressCode 0x0 = some (.aluImm .add sp sp 0xFFFFFD60, 4) := by decide
theorem dec_at_4 : fetchRel edDecompressCode 0x4 = some (.aluImm .add a2 sp 0x280, 2) := by decide
theorem dec_at_6 : fetchRel edDecompressCode 0x6 = some (.store .sw a2 ra 0x1C, 4) := by decide
theorem dec_at_a : fetchRel edDecompressCode 0xA = some (.store .sw a2 (8 : Fin 32) 0x18, 2) := by decide
theorem dec_at_c : fetchRel edDecompressCode 0xC = some (.store .sw a2 (9 : Fin 32) 0x14, 2) := by decide
theorem dec_at_e : fetchRel edDecompressCode 0xE = some (.store .sw a2 (18 : Fin 32) 0x10, 4) := by decide
theorem dec_at_12 : fetchRel edDecompressCode 0x12 = some (.store .sw a2 (19 : Fin 32) 0xC, 4) := by decide
theorem dec_at_16 : fetchRel edDecompressCode 0x16 = some (.store .sw a2 (20 : Fin 32) 0x8, 4) := by decide
theorem dec_at_1a : fetchRel edDecompressCode 0x1A = some (.store .sw a2 (21 : Fin 32) 0x4, 4) := by decide
theorem dec_at_1e : fetchRel edDecompressCode 0x1E = some (.alu .add (20 : Fin 32) x0 a1, 2) := by decide
theorem dec_at_20 : fetchRel edDecompressCode 0x20 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem dec_at_22 : fetchRel edDecompressCode 0x22 = some (.alu .add a0 x0 a1, 2) := by decide
theorem dec_at_24 : fetchRel edDecompressCode 0x24 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem dec_at_26 : fetchRel edDecompressCode 0x26 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem dec_at_2a : fetchRel edDecompressCode 0x2A = some (.jalr ra ra 0xFFFFFC18, 4) := by decide
theorem dec_at_2e : fetchRel edDecompressCode 0x2E = some (.store .sw sp x0 0x54, 2) := by decide
theorem dec_at_30 : fetchRel edDecompressCode 0x30 = some (.store .sw sp a0 0x50, 2) := by decide
theorem dec_at_32 : fetchRel edDecompressCode 0x32 = some (.aluImm .add a1 x0 0x4, 2) := by decide
theorem dec_at_34 : fetchRel edDecompressCode 0x34 = some (.alu .add a0 x0 (20 : Fin 32), 2) := by decide
theorem dec_at_36 : fetchRel edDecompressCode 0x36 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem dec_at_3a : fetchRel edDecompressCode 0x3A = some (.jalr ra ra 0xFFFFFC2A, 4) := by decide
theorem dec_at_3e : fetchRel edDecompressCode 0x3E = some (.store .sw sp x0 0x5C, 2) := by decide
theorem dec_at_40 : fetchRel edDecompressCode 0x40 = some (.aluImm .sll a0 a0 0x6, 2) := by decide
theorem dec_at_42 : fetchRel edDecompressCode 0x42 = some (.store .sw sp a0 0x58, 2) := by decide
theorem dec_at_44 : fetchRel edDecompressCode 0x44 = some (.aluImm .add a1 x0 0x7, 2) := by decide
theorem dec_at_46 : fetchRel edDecompressCode 0x46 = some (.alu .add a0 x0 (20 : Fin 32), 2) := by decide
theorem dec_at_48 : fetchRel edDecompressCode 0x48 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem dec_at_4c : fetchRel edDecompressCode 0x4C = some (.jalr ra ra 0xFFFFFC18, 4) := by decide
theorem dec_at_50 : fetchRel edDecompressCode 0x50 = some (.store .sw sp x0 0x64, 2) := by decide
theorem dec_at_52 : fetchRel edDecompressCode 0x52 = some (.aluImm .sll a0 a0 0x5, 2) := by decide
theorem dec_at_54 : fetchRel edDecompressCode 0x54 = some (.store .sw sp a0 0x60, 2) := by decide
theorem dec_at_56 : fetchRel edDecompressCode 0x56 = some (.aluImm .add a1 x0 0xA, 2) := by decide
theorem dec_at_58 : fetchRel edDecompressCode 0x58 = some (.alu .add a0 x0 (20 : Fin 32), 2) := by decide
theorem dec_at_5a : fetchRel edDecompressCode 0x5A = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem dec_at_5e : fetchRel edDecompressCode 0x5E = some (.jalr ra ra 0xFFFFFC06, 4) := by decide
theorem dec_at_62 : fetchRel edDecompressCode 0x62 = some (.store .sw sp x0 0x6C, 2) := by decide
theorem dec_at_64 : fetchRel edDecompressCode 0x64 = some (.aluImm .sll a0 a0 0x3, 2) := by decide
theorem dec_at_66 : fetchRel edDecompressCode 0x66 = some (.store .sw sp a0 0x68, 2) := by decide
theorem dec_at_68 : fetchRel edDecompressCode 0x68 = some (.aluImm .add a1 x0 0xD, 2) := by decide
theorem dec_at_6a : fetchRel edDecompressCode 0x6A = some (.alu .add a0 x0 (20 : Fin 32), 2) := by decide
theorem dec_at_6c : fetchRel edDecompressCode 0x6C = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem dec_at_70 : fetchRel edDecompressCode 0x70 = some (.jalr ra ra 0xFFFFFBF4, 4) := by decide
theorem dec_at_74 : fetchRel edDecompressCode 0x74 = some (.store .sw sp x0 0x74, 2) := by decide
theorem dec_at_76 : fetchRel edDecompressCode 0x76 = some (.aluImm .sll a0 a0 0x2, 2) := by decide
theorem dec_at_78 : fetchRel edDecompressCode 0x78 = some (.store .sw sp a0 0x70, 2) := by decide
theorem dec_at_7a : fetchRel edDecompressCode 0x7A = some (.aluImm .add a1 x0 0x10, 2) := by decide
theorem dec_at_7c : fetchRel edDecompressCode 0x7C = some (.alu .add a0 x0 (20 : Fin 32), 2) := by decide
theorem dec_at_7e : fetchRel edDecompressCode 0x7E = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem dec_at_82 : fetchRel edDecompressCode 0x82 = some (.jalr ra ra 0xFFFFFBC0, 4) := by decide
theorem dec_at_86 : fetchRel edDecompressCode 0x86 = some (.store .sw sp x0 0x7C, 2) := by decide
theorem dec_at_88 : fetchRel edDecompressCode 0x88 = some (.store .sw sp a0 0x78, 2) := by decide
theorem dec_at_8a : fetchRel edDecompressCode 0x8A = some (.aluImm .add a1 x0 0x14, 2) := by decide
theorem dec_at_8c : fetchRel edDecompressCode 0x8C = some (.alu .add a0 x0 (20 : Fin 32), 2) := by decide
theorem dec_at_8e : fetchRel edDecompressCode 0x8E = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem dec_at_92 : fetchRel edDecompressCode 0x92 = some (.jalr ra ra 0xFFFFFBD2, 4) := by decide
theorem dec_at_96 : fetchRel edDecompressCode 0x96 = some (.store .sw sp x0 0x84, 2) := by decide
theorem dec_at_98 : fetchRel edDecompressCode 0x98 = some (.aluImm .sll a0 a0 0x7, 2) := by decide
theorem dec_at_9a : fetchRel edDecompressCode 0x9A = some (.store .sw sp a0 0x80, 2) := by decide
theorem dec_at_9c : fetchRel edDecompressCode 0x9C = some (.aluImm .add a1 x0 0x17, 2) := by decide
theorem dec_at_9e : fetchRel edDecompressCode 0x9E = some (.alu .add a0 x0 (20 : Fin 32), 2) := by decide
theorem dec_at_a0 : fetchRel edDecompressCode 0xA0 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem dec_at_a4 : fetchRel edDecompressCode 0xA4 = some (.jalr ra ra 0xFFFFFBC0, 4) := by decide
theorem dec_at_a8 : fetchRel edDecompressCode 0xA8 = some (.store .sw sp x0 0x8C, 2) := by decide
theorem dec_at_aa : fetchRel edDecompressCode 0xAA = some (.aluImm .sll a0 a0 0x5, 2) := by decide
theorem dec_at_ac : fetchRel edDecompressCode 0xAC = some (.store .sw sp a0 0x88, 2) := by decide
theorem dec_at_ae : fetchRel edDecompressCode 0xAE = some (.aluImm .add a1 x0 0x1A, 2) := by decide
theorem dec_at_b0 : fetchRel edDecompressCode 0xB0 = some (.alu .add a0 x0 (20 : Fin 32), 2) := by decide
theorem dec_at_b2 : fetchRel edDecompressCode 0xB2 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem dec_at_b6 : fetchRel edDecompressCode 0xB6 = some (.jalr ra ra 0xFFFFFBAE, 4) := by decide
theorem dec_at_ba : fetchRel edDecompressCode 0xBA = some (.store .sw sp x0 0x94, 2) := by decide
theorem dec_at_bc : fetchRel edDecompressCode 0xBC = some (.aluImm .sll a0 a0 0x4, 2) := by decide
theorem dec_at_be : fetchRel edDecompressCode 0xBE = some (.store .sw sp a0 0x90, 2) := by decide
theorem dec_at_c0 : fetchRel edDecompressCode 0xC0 = some (.aluImm .add a1 x0 0x1D, 2) := by decide
theorem dec_at_c2 : fetchRel edDecompressCode 0xC2 = some (.alu .add a0 x0 (20 : Fin 32), 2) := by decide
theorem dec_at_c4 : fetchRel edDecompressCode 0xC4 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem dec_at_c8 : fetchRel edDecompressCode 0xC8 = some (.jalr ra ra 0xFFFFFB9C, 4) := by decide
theorem dec_at_cc : fetchRel edDecompressCode 0xCC = some (.store .sw sp x0 0x9C, 2) := by decide
theorem dec_at_ce : fetchRel edDecompressCode 0xCE = some (.aluImm .sll a0 a0 0x9, 2) := by decide
theorem dec_at_d0 : fetchRel edDecompressCode 0xD0 = some (.aluImm .srl a0 a0 0x7, 2) := by decide
theorem dec_at_d2 : fetchRel edDecompressCode 0xD2 = some (.store .sw sp a0 0x98, 2) := by decide
theorem dec_at_d4 : fetchRel edDecompressCode 0xD4 = some (.aluImm .add a0 sp 0xF4, 2) := by decide
theorem dec_at_d6 : fetchRel edDecompressCode 0xD6 = some (.aluImm .add a1 sp 0x50, 2) := by decide
theorem dec_at_d8 : fetchRel edDecompressCode 0xD8 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem dec_at_dc : fetchRel edDecompressCode 0xDC = some (.jalr ra ra 0x19A, 4) := by decide
theorem dec_at_e0 : fetchRel edDecompressCode 0xE0 = some (.aluImm .add a0 sp 0x11C, 2) := by decide
theorem dec_at_e2 : fetchRel edDecompressCode 0xE2 = some (.aluImm .add a1 sp 0xF4, 2) := by decide
theorem dec_at_e4 : fetchRel edDecompressCode 0xE4 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem dec_at_e8 : fetchRel edDecompressCode 0xE8 = some (.jalr ra ra 0x502, 4) := by decide
theorem dec_at_ec : fetchRel edDecompressCode 0xEC = some (.lui (8 : Fin 32) 0x3FCC5000, 4) := by decide
theorem dec_at_f0 : fetchRel edDecompressCode 0xF0 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFF948, 4) := by decide
theorem dec_at_f4 : fetchRel edDecompressCode 0xF4 = some (.aluImm .add a0 sp 0x144, 2) := by decide
theorem dec_at_f6 : fetchRel edDecompressCode 0xF6 = some (.aluImm .add a1 sp 0x11C, 2) := by decide
theorem dec_at_f8 : fetchRel edDecompressCode 0xF8 = some (.alu .add a2 x0 (8 : Fin 32), 2) := by decide
theorem dec_at_fa : fetchRel edDecompressCode 0xFA = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem dec_at_fe : fetchRel edDecompressCode 0xFE = some (.jalr ra ra 0xFFFFFA4A, 4) := by decide
theorem dec_at_102 : fetchRel edDecompressCode 0x102 = some (.lui a2 0x3FCC5000, 4) := by decide
theorem dec_at_106 : fetchRel edDecompressCode 0x106 = some (.aluImm .add a2 a2 0xFFFFF970, 4) := by decide
theorem dec_at_10a : fetchRel edDecompressCode 0x10A = some (.aluImm .add a0 sp 0x50, 2) := by decide
theorem dec_at_10c : fetchRel edDecompressCode 0x10C = some (.aluImm .add a1 sp 0x11C, 2) := by decide
theorem dec_at_10e : fetchRel edDecompressCode 0x10E = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem dec_at_112 : fetchRel edDecompressCode 0x112 = some (.jalr ra ra 0x674, 4) := by decide
theorem dec_at_116 : fetchRel edDecompressCode 0x116 = some (.aluImm .add a0 sp 0x16C, 2) := by decide
theorem dec_at_118 : fetchRel edDecompressCode 0x118 = some (.aluImm .add a1 sp 0x50, 2) := by decide
theorem dec_at_11a : fetchRel edDecompressCode 0x11A = some (.alu .add a2 x0 (8 : Fin 32), 2) := by decide
theorem dec_at_11c : fetchRel edDecompressCode 0x11C = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem dec_at_120 : fetchRel edDecompressCode 0x120 = some (.jalr ra ra 0xFFFFF9DA, 4) := by decide
theorem dec_at_124 : fetchRel edDecompressCode 0x124 = some (.aluImm .add a0 sp 0x50, 2) := by decide
theorem dec_at_126 : fetchRel edDecompressCode 0x126 = some (.aluImm .add a1 sp 0x16C, 2) := by decide
theorem dec_at_128 : fetchRel edDecompressCode 0x128 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem dec_at_12c : fetchRel edDecompressCode 0x12C = some (.jalr ra ra 0x4BE, 4) := by decide
theorem dec_at_130 : fetchRel edDecompressCode 0x130 = some (.aluImm .add a0 sp 0x194, 2) := by decide
theorem dec_at_132 : fetchRel edDecompressCode 0x132 = some (.aluImm .add a1 sp 0x50, 2) := by decide
theorem dec_at_134 : fetchRel edDecompressCode 0x134 = some (.aluImm .add a2 sp 0x16C, 2) := by decide
theorem dec_at_136 : fetchRel edDecompressCode 0x136 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem dec_at_13a : fetchRel edDecompressCode 0x13A = some (.jalr ra ra 0x64C, 4) := by decide
theorem dec_at_13e : fetchRel edDecompressCode 0x13E = some (.aluImm .add a0 sp 0x50, 2) := by decide
theorem dec_at_140 : fetchRel edDecompressCode 0x140 = some (.aluImm .add a1 sp 0x194, 2) := by decide
theorem dec_at_142 : fetchRel edDecompressCode 0x142 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem dec_at_146 : fetchRel edDecompressCode 0x146 = some (.jalr ra ra 0x4A4, 4) := by decide
theorem dec_at_14a : fetchRel edDecompressCode 0x14A = some (.aluImm .add a0 sp 0x1BC, 2) := by decide
theorem dec_at_14c : fetchRel edDecompressCode 0x14C = some (.aluImm .add a1 sp 0x50, 2) := by decide
theorem dec_at_14e : fetchRel edDecompressCode 0x14E = some (.aluImm .add a2 sp 0x16C, 2) := by decide
theorem dec_at_150 : fetchRel edDecompressCode 0x150 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem dec_at_154 : fetchRel edDecompressCode 0x154 = some (.jalr ra ra 0x632, 4) := by decide
theorem dec_at_158 : fetchRel edDecompressCode 0x158 = some (.aluImm .add a0 sp 0x1E4, 2) := by decide
theorem dec_at_15a : fetchRel edDecompressCode 0x15A = some (.aluImm .add a1 sp 0x144, 2) := by decide
theorem dec_at_15c : fetchRel edDecompressCode 0x15C = some (.aluImm .add a2 sp 0x194, 2) := by decide
theorem dec_at_15e : fetchRel edDecompressCode 0x15E = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem dec_at_162 : fetchRel edDecompressCode 0x162 = some (.jalr ra ra 0x624, 4) := by decide
theorem dec_at_166 : fetchRel edDecompressCode 0x166 = some (.aluImm .add a0 sp 0x234, 2) := by decide
theorem dec_at_168 : fetchRel edDecompressCode 0x168 = some (.aluImm .add a1 sp 0x144, 2) := by decide
theorem dec_at_16a : fetchRel edDecompressCode 0x16A = some (.aluImm .add a2 sp 0x1BC, 2) := by decide
theorem dec_at_16c : fetchRel edDecompressCode 0x16C = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem dec_at_170 : fetchRel edDecompressCode 0x170 = some (.jalr ra ra 0x616, 4) := by decide
theorem dec_at_174 : fetchRel edDecompressCode 0x174 = some (.aluImm .add a0 sp 0x50, 2) := by decide
theorem dec_at_176 : fetchRel edDecompressCode 0x176 = some (.aluImm .add a1 sp 0x234, 2) := by decide
theorem dec_at_178 : fetchRel edDecompressCode 0x178 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem dec_at_17c : fetchRel edDecompressCode 0x17C = some (.jalr ra ra 0x2C6, 4) := by decide
theorem dec_at_180 : fetchRel edDecompressCode 0x180 = some (.aluImm .add a0 sp 0x25C, 2) := by decide
theorem dec_at_182 : fetchRel edDecompressCode 0x182 = some (.aluImm .add a1 sp 0x50, 2) := by decide
theorem dec_at_184 : fetchRel edDecompressCode 0x184 = some (.aluImm .add a2 x0 0x2, 2) := by decide
theorem dec_at_186 : fetchRel edDecompressCode 0x186 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem dec_at_18a : fetchRel edDecompressCode 0x18A = some (.jalr ra ra 0x40E, 4) := by decide
theorem dec_at_18e : fetchRel edDecompressCode 0x18E = some (.aluImm .add a0 sp 0x20C, 2) := by decide
theorem dec_at_190 : fetchRel edDecompressCode 0x190 = some (.aluImm .add a1 sp 0x234, 2) := by decide
theorem dec_at_192 : fetchRel edDecompressCode 0x192 = some (.aluImm .add a2 sp 0x25C, 2) := by decide
theorem dec_at_194 : fetchRel edDecompressCode 0x194 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem dec_at_198 : fetchRel edDecompressCode 0x198 = some (.jalr ra ra 0x5EE, 4) := by decide
theorem dec_at_19c : fetchRel edDecompressCode 0x19C = some (.aluImm .add a0 sp 0x25C, 2) := by decide
theorem dec_at_19e : fetchRel edDecompressCode 0x19E = some (.aluImm .add a1 sp 0x1E4, 2) := by decide
theorem dec_at_1a0 : fetchRel edDecompressCode 0x1A0 = some (.aluImm .add a2 sp 0x20C, 2) := by decide
theorem dec_at_1a2 : fetchRel edDecompressCode 0x1A2 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem dec_at_1a6 : fetchRel edDecompressCode 0x1A6 = some (.jalr ra ra 0x5E0, 4) := by decide
theorem dec_at_1aa : fetchRel edDecompressCode 0x1AA = some (.aluImm .add a0 sp 0x50, 2) := by decide
theorem dec_at_1ac : fetchRel edDecompressCode 0x1AC = some (.aluImm .add a1 sp 0x25C, 2) := by decide
theorem dec_at_1ae : fetchRel edDecompressCode 0x1AE = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem dec_at_1b2 : fetchRel edDecompressCode 0x1B2 = some (.jalr ra ra 0x438, 4) := by decide
theorem dec_at_1b6 : fetchRel edDecompressCode 0x1B6 = some (.aluImm .add a0 sp 0x20C, 2) := by decide
theorem dec_at_1b8 : fetchRel edDecompressCode 0x1B8 = some (.aluImm .add a1 sp 0x16C, 2) := by decide
theorem dec_at_1ba : fetchRel edDecompressCode 0x1BA = some (.aluImm .add a2 sp 0x50, 2) := by decide
theorem dec_at_1bc : fetchRel edDecompressCode 0x1BC = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem dec_at_1c0 : fetchRel edDecompressCode 0x1C0 = some (.jalr ra ra 0x5C6, 4) := by decide
theorem dec_at_1c4 : fetchRel edDecompressCode 0x1C4 = some (.aluImm .add a0 sp 0x20C, 2) := by decide
theorem dec_at_1c6 : fetchRel edDecompressCode 0x1C6 = some (.aluImm .add a1 sp 0x144, 2) := by decide
theorem dec_at_1c8 : fetchRel edDecompressCode 0x1C8 = some (.auipc ra 0x0, 4) := by decide
theorem dec_at_1cc : fetchRel edDecompressCode 0x1CC = some (.jalr ra ra 0xFFFFFE04, 4) := by decide
theorem dec_at_1d0 : fetchRel edDecompressCode 0x1D0 = some (.alu .add (19 : Fin 32) x0 a0, 2) := by decide
theorem dec_at_1d2 : fetchRel edDecompressCode 0x1D2 = some (.aluImm .add a0 sp 0x50, 2) := by decide
theorem dec_at_1d4 : fetchRel edDecompressCode 0x1D4 = some (.aluImm .add a1 sp 0x144, 2) := by decide
theorem dec_at_1d6 : fetchRel edDecompressCode 0x1D6 = some (.auipc ra 0x0, 4) := by decide
theorem dec_at_1da : fetchRel edDecompressCode 0x1DA = some (.jalr ra ra 0xFFFFFD2C, 4) := by decide
theorem dec_at_1de : fetchRel edDecompressCode 0x1DE = some (.aluImm .add a0 sp 0x20C, 2) := by decide
theorem dec_at_1e0 : fetchRel edDecompressCode 0x1E0 = some (.aluImm .add a1 sp 0x50, 2) := by decide
theorem dec_at_1e2 : fetchRel edDecompressCode 0x1E2 = some (.auipc ra 0x0, 4) := by decide
theorem dec_at_1e6 : fetchRel edDecompressCode 0x1E6 = some (.jalr ra ra 0xFFFFFDEA, 4) := by decide
theorem dec_at_1ea : fetchRel edDecompressCode 0x1EA = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem dec_at_1ec : fetchRel edDecompressCode 0x1EC = some (.aluImm .add a0 sp 0x50, 2) := by decide
theorem dec_at_1ee : fetchRel edDecompressCode 0x1EE = some (.aluImm .add a1 sp 0x144, 2) := by decide
theorem dec_at_1f0 : fetchRel edDecompressCode 0x1F0 = some (.auipc ra 0x0, 4) := by decide
theorem dec_at_1f4 : fetchRel edDecompressCode 0x1F4 = some (.jalr ra ra 0xFFFFFD12, 4) := by decide
theorem dec_at_1f8 : fetchRel edDecompressCode 0x1F8 = some (.lui (21 : Fin 32) 0x3FCC5000, 4) := by decide
theorem dec_at_1fc : fetchRel edDecompressCode 0x1FC = some (.aluImm .add (21 : Fin 32) (21 : Fin 32) 0xFFFFF998, 4) := by decide
theorem dec_at_200 : fetchRel edDecompressCode 0x200 = some (.aluImm .add a0 sp 0x234, 2) := by decide
theorem dec_at_202 : fetchRel edDecompressCode 0x202 = some (.aluImm .add a1 sp 0x50, 2) := by decide
theorem dec_at_204 : fetchRel edDecompressCode 0x204 = some (.alu .add a2 x0 (21 : Fin 32), 2) := by decide
theorem dec_at_206 : fetchRel edDecompressCode 0x206 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem dec_at_20a : fetchRel edDecompressCode 0x20A = some (.jalr ra ra 0x57C, 4) := by decide
theorem dec_at_20e : fetchRel edDecompressCode 0x20E = some (.aluImm .add a0 sp 0x20C, 2) := by decide
theorem dec_at_210 : fetchRel edDecompressCode 0x210 = some (.aluImm .add a1 sp 0x234, 2) := by decide
theorem dec_at_212 : fetchRel edDecompressCode 0x212 = some (.auipc ra 0x0, 4) := by decide
theorem dec_at_216 : fetchRel edDecompressCode 0x216 = some (.jalr ra ra 0xFFFFFDBA, 4) := by decide
theorem dec_at_21a : fetchRel edDecompressCode 0x21A = some (.alu .add (9 : Fin 32) x0 a0, 2) := by decide
theorem dec_at_21c : fetchRel edDecompressCode 0x21C = some (.aluImm .add a0 sp 0x234, 2) := by decide
theorem dec_at_21e : fetchRel edDecompressCode 0x21E = some (.aluImm .add a2 sp 0x25C, 2) := by decide
theorem dec_at_220 : fetchRel edDecompressCode 0x220 = some (.alu .add a1 x0 (21 : Fin 32), 2) := by decide
theorem dec_at_222 : fetchRel edDecompressCode 0x222 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem dec_at_226 : fetchRel edDecompressCode 0x226 = some (.jalr ra ra 0x560, 4) := by decide
theorem dec_at_22a : fetchRel edDecompressCode 0x22A = some (.alu .or (9 : Fin 32) (9 : Fin 32) (8 : Fin 32), 2) := by decide
theorem dec_at_22c : fetchRel edDecompressCode 0x22C = some (.aluImm .and a0 (9 : Fin 32) 0xFF, 4) := by decide
theorem dec_at_230 : fetchRel edDecompressCode 0x230 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem dec_at_234 : fetchRel edDecompressCode 0x234 = some (.jalr ra ra 0x544, 4) := by decide
theorem dec_at_238 : fetchRel edDecompressCode 0x238 = some (.aluImm .and a2 a0 0xFF, 4) := by decide
theorem dec_at_23c : fetchRel edDecompressCode 0x23C = some (.aluImm .add a0 sp 0x25C, 2) := by decide
theorem dec_at_23e : fetchRel edDecompressCode 0x23E = some (.aluImm .add a1 sp 0x234, 2) := by decide
theorem dec_at_240 : fetchRel edDecompressCode 0x240 = some (.auipc ra 0x0, 4) := by decide
theorem dec_at_244 : fetchRel edDecompressCode 0x244 = some (.jalr ra ra 0xFFFFFB8E, 4) := by decide
theorem dec_at_248 : fetchRel edDecompressCode 0x248 = some (.aluImm .add a0 sp 0x25C, 2) := by decide
theorem dec_at_24a : fetchRel edDecompressCode 0x24A = some (.auipc ra 0x0, 4) := by decide
theorem dec_at_24e : fetchRel edDecompressCode 0x24E = some (.jalr ra ra 0xFFFFFB32, 4) := by decide
theorem dec_at_252 : fetchRel edDecompressCode 0x252 = some (.aluImm .and a1 a0 0xFF, 4) := by decide
theorem dec_at_256 : fetchRel edDecompressCode 0x256 = some (.aluImm .add a0 sp 0x25C, 2) := by decide
theorem dec_at_258 : fetchRel edDecompressCode 0x258 = some (.auipc ra 0x0, 4) := by decide
theorem dec_at_25c : fetchRel edDecompressCode 0x25C = some (.jalr ra ra 0xFFFFFB46, 4) := by decide
theorem dec_at_260 : fetchRel edDecompressCode 0x260 = some (.alu .or a0 (8 : Fin 32) (19 : Fin 32), 4) := by decide
theorem dec_at_264 : fetchRel edDecompressCode 0x264 = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem dec_at_268 : fetchRel edDecompressCode 0x268 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem dec_at_26c : fetchRel edDecompressCode 0x26C = some (.jalr ra ra 0x50C, 4) := by decide
theorem dec_at_270 : fetchRel edDecompressCode 0x270 = some (.aluImm .add (8 : Fin 32) sp 0x53, 4) := by decide
theorem dec_at_274 : fetchRel edDecompressCode 0x274 = some (.aluImm .and (9 : Fin 32) a0 0xFF, 4) := by decide
theorem dec_at_278 : fetchRel edDecompressCode 0x278 = some (.aluImm .add a1 sp 0x25C, 2) := by decide
theorem dec_at_27a : fetchRel edDecompressCode 0x27A = some (.aluImm .add a2 x0 0x28, 4) := by decide
theorem dec_at_27e : fetchRel edDecompressCode 0x27E = some (.alu .add a0 x0 (8 : Fin 32), 2) := by decide
theorem dec_at_280 : fetchRel edDecompressCode 0x280 = some (.auipc ra 0x4000, 4) := by decide
theorem dec_at_284 : fetchRel edDecompressCode 0x284 = some (.jalr ra ra 0x5FE, 4) := by decide
theorem dec_at_288 : fetchRel edDecompressCode 0x288 = some (.alu .add a0 x0 sp, 2) := by decide
theorem dec_at_28a : fetchRel edDecompressCode 0x28A = some (.aluImm .add a2 x0 0x28, 4) := by decide
theorem dec_at_28e : fetchRel edDecompressCode 0x28E = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem dec_at_290 : fetchRel edDecompressCode 0x290 = some (.auipc ra 0x4000, 4) := by decide
theorem dec_at_294 : fetchRel edDecompressCode 0x294 = some (.jalr ra ra 0x5EE, 4) := by decide
theorem dec_at_298 : fetchRel edDecompressCode 0x298 = some (.aluImm .add (8 : Fin 32) sp 0x28, 2) := by decide
theorem dec_at_29a : fetchRel edDecompressCode 0x29A = some (.aluImm .add a1 sp 0xF4, 2) := by decide
theorem dec_at_29c : fetchRel edDecompressCode 0x29C = some (.aluImm .add a2 x0 0x28, 4) := by decide
theorem dec_at_2a0 : fetchRel edDecompressCode 0x2A0 = some (.alu .add a0 x0 (8 : Fin 32), 2) := by decide
theorem dec_at_2a2 : fetchRel edDecompressCode 0x2A2 = some (.auipc ra 0x4000, 4) := by decide
theorem dec_at_2a6 : fetchRel edDecompressCode 0x2A6 = some (.jalr ra ra 0x5DC, 4) := by decide
theorem dec_at_2aa : fetchRel edDecompressCode 0x2AA = some (.aluImm .add a0 sp 0x25C, 2) := by decide
theorem dec_at_2ac : fetchRel edDecompressCode 0x2AC = some (.aluImm .add a2 x0 0x28, 4) := by decide
theorem dec_at_2b0 : fetchRel edDecompressCode 0x2B0 = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem dec_at_2b2 : fetchRel edDecompressCode 0x2B2 = some (.auipc ra 0x4000, 4) := by decide
theorem dec_at_2b6 : fetchRel edDecompressCode 0x2B6 = some (.jalr ra ra 0x5CC, 4) := by decide
theorem dec_at_2ba : fetchRel edDecompressCode 0x2BA = some (.branch .beq (9 : Fin 32) x0 0x78, 2) := by decide
theorem dec_at_2bc : fetchRel edDecompressCode 0x2BC = some (.load .lbu a0 (20 : Fin 32) 0x1F, 4) := by decide
theorem dec_at_2c0 : fetchRel edDecompressCode 0x2C0 = some (.aluImm .srl a0 a0 0x7, 2) := by decide
theorem dec_at_2c2 : fetchRel edDecompressCode 0x2C2 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem dec_at_2c6 : fetchRel edDecompressCode 0x2C6 = some (.jalr ra ra 0x4B2, 4) := by decide
theorem dec_at_2ca : fetchRel edDecompressCode 0x2CA = some (.aluImm .and a1 a0 0xFF, 4) := by decide
theorem dec_at_2ce : fetchRel edDecompressCode 0x2CE = some (.alu .add a0 x0 sp, 2) := by decide
theorem dec_at_2d0 : fetchRel edDecompressCode 0x2D0 = some (.auipc ra 0x0, 4) := by decide
theorem dec_at_2d4 : fetchRel edDecompressCode 0x2D4 = some (.jalr ra ra 0xFFFFFACE, 4) := by decide
theorem dec_at_2d8 : fetchRel edDecompressCode 0x2D8 = some (.aluImm .add a0 sp 0x50, 2) := by decide
theorem dec_at_2da : fetchRel edDecompressCode 0x2DA = some (.alu .add a1 x0 sp, 2) := by decide
theorem dec_at_2dc : fetchRel edDecompressCode 0x2DC = some (.aluImm .add a2 x0 0x28, 4) := by decide
theorem dec_at_2e0 : fetchRel edDecompressCode 0x2E0 = some (.auipc ra 0x4000, 4) := by decide
theorem dec_at_2e4 : fetchRel edDecompressCode 0x2E4 = some (.jalr ra ra 0x59E, 4) := by decide
theorem dec_at_2e8 : fetchRel edDecompressCode 0x2E8 = some (.aluImm .add a0 sp 0xC8, 2) := by decide
theorem dec_at_2ea : fetchRel edDecompressCode 0x2EA = some (.alu .add a1 x0 sp, 2) := by decide
theorem dec_at_2ec : fetchRel edDecompressCode 0x2EC = some (.aluImm .add a2 sp 0x25C, 2) := by decide
theorem dec_at_2ee : fetchRel edDecompressCode 0x2EE = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem dec_at_2f2 : fetchRel edDecompressCode 0x2F2 = some (.jalr ra ra 0x494, 4) := by decide
theorem dec_at_2f6 : fetchRel edDecompressCode 0x2F6 = some (.aluImm .add a0 sp 0x78, 2) := by decide
theorem dec_at_2f8 : fetchRel edDecompressCode 0x2F8 = some (.aluImm .add a1 sp 0x25C, 2) := by decide
theorem dec_at_2fa : fetchRel edDecompressCode 0x2FA = some (.aluImm .add a2 x0 0x28, 4) := by decide
theorem dec_at_2fe : fetchRel edDecompressCode 0x2FE = some (.auipc ra 0x4000, 4) := by decide
theorem dec_at_302 : fetchRel edDecompressCode 0x302 = some (.jalr ra ra 0x580, 4) := by decide
theorem dec_at_306 : fetchRel edDecompressCode 0x306 = some (.aluImm .add a0 sp 0xA0, 2) := by decide
theorem dec_at_308 : fetchRel edDecompressCode 0x308 = some (.lui a1 0x3FCC5000, 4) := by decide
theorem dec_at_30c : fetchRel edDecompressCode 0x30C = some (.aluImm .add a1 a1 0xFFFFF948, 4) := by decide
theorem dec_at_310 : fetchRel edDecompressCode 0x310 = some (.aluImm .add a2 x0 0x28, 4) := by decide
theorem dec_at_314 : fetchRel edDecompressCode 0x314 = some (.auipc ra 0x4000, 4) := by decide
theorem dec_at_318 : fetchRel edDecompressCode 0x318 = some (.jalr ra ra 0x56A, 4) := by decide
theorem dec_at_31c : fetchRel edDecompressCode 0x31C = some (.aluImm .add a0 (18 : Fin 32) 0x4, 4) := by decide
theorem dec_at_320 : fetchRel edDecompressCode 0x320 = some (.aluImm .add a1 sp 0x50, 2) := by decide
theorem dec_at_322 : fetchRel edDecompressCode 0x322 = some (.aluImm .add a2 x0 0xA0, 4) := by decide
theorem dec_at_326 : fetchRel edDecompressCode 0x326 = some (.auipc ra 0x4000, 4) := by decide
theorem dec_at_32a : fetchRel edDecompressCode 0x32A = some (.jalr ra ra 0x558, 4) := by decide
theorem dec_at_32e : fetchRel edDecompressCode 0x32E = some (.aluImm .add a0 x0 0x1, 2) := by decide
theorem dec_at_330 : fetchRel edDecompressCode 0x330 = some (.jal x0 0x4, 2) := by decide
theorem dec_at_332 : fetchRel edDecompressCode 0x332 = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem dec_at_334 : fetchRel edDecompressCode 0x334 = some (.store .sw (18 : Fin 32) a0 0x0, 4) := by decide
theorem dec_at_338 : fetchRel edDecompressCode 0x338 = some (.aluImm .add a0 sp 0x280, 2) := by decide
theorem dec_at_33a : fetchRel edDecompressCode 0x33A = some (.load .lw ra a0 0x1C, 4) := by decide
theorem dec_at_33e : fetchRel edDecompressCode 0x33E = some (.load .lw (8 : Fin 32) a0 0x18, 2) := by decide
theorem dec_at_340 : fetchRel edDecompressCode 0x340 = some (.load .lw (9 : Fin 32) a0 0x14, 2) := by decide
theorem dec_at_342 : fetchRel edDecompressCode 0x342 = some (.load .lw (18 : Fin 32) a0 0x10, 4) := by decide
theorem dec_at_346 : fetchRel edDecompressCode 0x346 = some (.load .lw (19 : Fin 32) a0 0xC, 4) := by decide
theorem dec_at_34a : fetchRel edDecompressCode 0x34A = some (.load .lw (20 : Fin 32) a0 0x8, 4) := by decide
theorem dec_at_34e : fetchRel edDecompressCode 0x34E = some (.load .lw (21 : Fin 32) a0 0x4, 4) := by decide
theorem dec_at_352 : fetchRel edDecompressCode 0x352 = some (.aluImm .add sp sp 0x2A0, 4) := by decide
theorem dec_at_356 : fetchRel edDecompressCode 0x356 = some (.jalr x0 ra 0x0, 2) := by decide
end

section Steps

variable {M0 Ms M : Word → BitVec 8} {R : Word} {r0 : Fin 32 → Word} {nm : Machine} {off : Nat}

theorem keep_sub : ∀ q : Fin 32, q.val ∈ [3, 4, 22, 23, 24, 25, 26, 27] →
    q.val ∈ [0, 2, 3, 4, 22, 23, 24, 25, 26, 27] := by decide

theorem DecSt.updR (D : DecSt M0 Ms R r0 M nm off) {nm1 : Machine} {off' : Nat} {rd : Fin 32} {v : Word}
    (u : St M DEC nm1 off' (upd (reg nm) rd v)) (hrd : rd.val ∉ [0, 2, 3, 4, 22, 23, 24, 25, 26, 27]) :
    DecSt M0 Ms R r0 M nm1 off' ∧ reg nm1 rd = v ∧ ∀ q, q ≠ rd → reg nm1 q = reg nm q := by
  have h0 : rd.val ≠ 0 := fun h => hrd (by rw [h]; decide)
  have hsp : sp ≠ rd := fun h => hrd (h ▸ (by decide : sp.val ∈ [0, 2, 3, 4, 22, 23, 24, 25, 26, 27]))
  refine ⟨⟨u.self, by rw [u.upd_ne D.zero sp hsp, D.hsp], fun q hq => ?_, D.agree, D.slots⟩, u.upd_eq h0,
    fun q hq => u.upd_ne D.zero q hq⟩
  have hq' : q ≠ rd := fun h => hrd (h ▸ keep_sub q hq)
  rw [u.upd_ne D.zero q hq', D.keep q hq]

set_option maxRecDepth 20000 in
theorem DecSt.aluImmS (C : DecCtx M0 R) (D : DecSt M0 Ms R r0 M nm off) {op : AluOp} {rd rs1 : Fin 32}
    {imm len : Word} {off' : Nat} (hf : fetchRel edDecompressCode off = some (.aluImm op rd rs1 imm, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') (hrd : rd.val ∉ [0, 2, 3, 4, 22, 23, 24, 25, 26, 27]) :
    ∃ nm1, Steps nm nm1 ∧ DecSt M0 Ms R r0 M nm1 off' ∧ reg nm1 rd = aluEval op (reg nm rs1) imm ∧
      ∀ q, q ≠ rd → reg nm1 q = reg nm q := by
  obtain ⟨n1, d1, u1⟩ := D.st.aluImm (C.code D.agree C.E.cod (by decide) (by decide)) hf hn
  obtain ⟨D1, v1, k1⟩ := D.updR u1 hrd
  exact ⟨n1, .single d1, D1, v1, k1⟩

set_option maxRecDepth 20000 in
theorem DecSt.aluS (C : DecCtx M0 R) (D : DecSt M0 Ms R r0 M nm off) {op : AluOp} {rd rs1 rs2 : Fin 32}
    {len : Word} {off' : Nat} (hf : fetchRel edDecompressCode off = some (.alu op rd rs1 rs2, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') (hrd : rd.val ∉ [0, 2, 3, 4, 22, 23, 24, 25, 26, 27]) :
    ∃ nm1, Steps nm nm1 ∧ DecSt M0 Ms R r0 M nm1 off' ∧ reg nm1 rd = aluEval op (reg nm rs1) (reg nm rs2) ∧
      ∀ q, q ≠ rd → reg nm1 q = reg nm q := by
  obtain ⟨n1, d1, u1⟩ := D.st.alu (C.code D.agree C.E.cod (by decide) (by decide)) hf hn
  obtain ⟨D1, v1, k1⟩ := D.updR u1 hrd
  exact ⟨n1, .single d1, D1, v1, k1⟩

set_option maxRecDepth 20000 in
theorem DecSt.luiS (C : DecCtx M0 R) (D : DecSt M0 Ms R r0 M nm off) {rd : Fin 32}
    {imm len : Word} {off' : Nat} (hf : fetchRel edDecompressCode off = some (.lui rd imm, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') (hrd : rd.val ∉ [0, 2, 3, 4, 22, 23, 24, 25, 26, 27]) :
    ∃ nm1, Steps nm nm1 ∧ DecSt M0 Ms R r0 M nm1 off' ∧ reg nm1 rd = imm ∧ ∀ q, q ≠ rd → reg nm1 q = reg nm q := by
  obtain ⟨n1, d1, u1⟩ := D.st.lui (C.code D.agree C.E.cod (by decide) (by decide)) hf hn
  obtain ⟨D1, v1, k1⟩ := D.updR u1 hrd
  exact ⟨n1, .single d1, D1, v1, k1⟩

set_option maxRecDepth 20000 in
theorem DecSt.lbuS (C : DecCtx M0 R) (D : DecSt M0 Ms R r0 M nm off) {rd rs1 : Fin 32}
    {o len : Word} {off' : Nat} (hf : fetchRel edDecompressCode off = some (.load .lbu rd rs1 o, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') (hrd : rd.val ∉ [0, 2, 3, 4, 22, 23, 24, 25, 26, 27]) :
    ∃ nm1, Steps nm nm1 ∧ DecSt M0 Ms R r0 M nm1 off' ∧ reg nm1 rd = (M (reg nm rs1 + o)).zeroExtend 32 ∧
      ∀ q, q ≠ rd → reg nm1 q = reg nm q := by
  obtain ⟨n1, d1, u1⟩ := D.st.lbu (C.code D.agree C.E.cod (by decide) (by decide)) hf hn
  obtain ⟨D1, v1, k1⟩ := D.updR u1 hrd
  exact ⟨n1, .single d1, D1, v1, k1⟩

theorem st32_frame {M : Word → BitVec 8} {a v x : Word} (h : Sep a 4 x 1) : memStore32 M a v x = M x :=
  memStore32_ne fun i hi e => h i hi 0 (by decide) (by rw [add_ofNat_zero]; exact e.symm)

set_option maxRecDepth 20000 in
/-- A store to the frame at `R + c`, below the saved registers. -/
theorem DecSt.swF (C : DecCtx M0 R) (D : DecSt M0 Ms R r0 M nm off) {rs1 rs2 : Fin 32} {o len : Word}
    {off' : Nat} (hf : fetchRel edDecompressCode off = some (.store .sw rs1 rs2 o, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') {c : Nat} (ha : reg nm rs1 + o = R + BitVec.ofNat 32 c)
    (hc4 : c % 4 = 0) (hc1 : 0x450 ≤ c) (hc2 : c + 4 ≤ 0x6D4) :
    ∃ nm1, Steps nm nm1 ∧ DecSt M0 Ms R r0 (memStore32 M (R + BitVec.ofNat 32 c) (reg nm rs2)) nm1 off' ∧
      ∀ q, reg nm1 q = reg nm q := by
  obtain ⟨n1, d1, u1⟩ := D.st.sw (C.code D.agree C.E.cod (by decide) (by decide)) hf hn
    (by rw [ha]; exact aligned_add C.hR hc4)
  rw [ha] at u1
  refine ⟨n1, .single d1, ⟨u1.self, by rw [u1.regs, D.hsp], fun q hq => by rw [u1.regs, D.keep q hq],
    fun x hx => by rw [st32_frame (C.inR (by omega) hx), D.agree x hx], fun c' h1 h2 => ?_⟩, u1.regs⟩
  rw [st32_frame (C.offs (Or.inl (by omega)) (by omega) (by omega)), D.slots c' h1 h2]

end Steps

end C3.RV32
