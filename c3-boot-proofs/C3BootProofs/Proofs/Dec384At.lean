import C3BootProofs.Proofs.P384Mont

/-! Fetch lemmas for P-384 point decompression (`p384DecompressCode`). -/

namespace C3.RV32.Dq

open C3.Image

/-- Where `decompress` is in the image. -/
abbrev DP : Word := BitVec.ofNat 32 p384DecompressAddress

set_option maxRecDepth 20000

theorem dp_at_0 : fetchRel p384DecompressCode 0x0 = some (.aluImm .add sp sp 0xFFFFF810, 4) := by decide
theorem dp_at_4 : fetchRel p384DecompressCode 0x4 = some (.aluImm .add a3 sp 0x780, 4) := by decide
theorem dp_at_8 : fetchRel p384DecompressCode 0x8 = some (.store .sw a3 ra 0x6C, 4) := by decide
theorem dp_at_c : fetchRel p384DecompressCode 0xC = some (.store .sw a3 (8 : Fin 32) 0x68, 2) := by decide
theorem dp_at_e : fetchRel p384DecompressCode 0xE = some (.store .sw a3 (9 : Fin 32) 0x64, 2) := by decide
theorem dp_at_10 : fetchRel p384DecompressCode 0x10 = some (.store .sw a3 (18 : Fin 32) 0x60, 4) := by decide
theorem dp_at_14 : fetchRel p384DecompressCode 0x14 = some (.store .sw a3 (19 : Fin 32) 0x5C, 4) := by decide
theorem dp_at_18 : fetchRel p384DecompressCode 0x18 = some (.store .sw a3 (20 : Fin 32) 0x58, 4) := by decide
theorem dp_at_1c : fetchRel p384DecompressCode 0x1C = some (.store .sw a3 (21 : Fin 32) 0x54, 4) := by decide
theorem dp_at_20 : fetchRel p384DecompressCode 0x20 = some (.store .sw a3 (22 : Fin 32) 0x50, 4) := by decide
theorem dp_at_24 : fetchRel p384DecompressCode 0x24 = some (.store .sw a3 (23 : Fin 32) 0x4C, 4) := by decide
theorem dp_at_28 : fetchRel p384DecompressCode 0x28 = some (.store .sw a3 (24 : Fin 32) 0x48, 4) := by decide
theorem dp_at_2c : fetchRel p384DecompressCode 0x2C = some (.store .sw a3 (25 : Fin 32) 0x44, 4) := by decide
theorem dp_at_30 : fetchRel p384DecompressCode 0x30 = some (.store .sw a3 (26 : Fin 32) 0x40, 4) := by decide
theorem dp_at_34 : fetchRel p384DecompressCode 0x34 = some (.store .sw a3 (27 : Fin 32) 0x3C, 4) := by decide
theorem dp_at_38 : fetchRel p384DecompressCode 0x38 = some (.aluImm .add sp sp 0xFFFFFDA0, 4) := by decide
theorem dp_at_3c : fetchRel p384DecompressCode 0x3C = some (.alu .add (21 : Fin 32) x0 a2, 2) := by decide
theorem dp_at_3e : fetchRel p384DecompressCode 0x3E = some (.alu .add (19 : Fin 32) x0 a0, 2) := by decide
theorem dp_at_40 : fetchRel p384DecompressCode 0x40 = some (.aluImm .add (25 : Fin 32) sp 0x7FF, 4) := by decide
theorem dp_at_44 : fetchRel p384DecompressCode 0x44 = some (.aluImm .add (25 : Fin 32) (25 : Fin 32) 0x18D, 4) := by decide
theorem dp_at_48 : fetchRel p384DecompressCode 0x48 = some (.aluImm .add a0 sp 0x40, 2) := by decide
theorem dp_at_4a : fetchRel p384DecompressCode 0x4A = some (.auipc ra 0x0, 4) := by decide
theorem dp_at_4e : fetchRel p384DecompressCode 0x4E = some (.jalr ra ra 0x6E6, 4) := by decide
theorem dp_at_52 : fetchRel p384DecompressCode 0x52 = some (.aluImm .add a0 sp 0x74, 2) := by decide
theorem dp_at_54 : fetchRel p384DecompressCode 0x54 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem dp_at_58 : fetchRel p384DecompressCode 0x58 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem dp_at_5a : fetchRel p384DecompressCode 0x5A = some (.auipc ra 0x11000, 4) := by decide
theorem dp_at_5e : fetchRel p384DecompressCode 0x5E = some (.jalr ra ra 0x33A, 4) := by decide
theorem dp_at_62 : fetchRel p384DecompressCode 0x62 = some (.load .lbu (20 : Fin 32) sp 0x70, 4) := by decide
theorem dp_at_66 : fetchRel p384DecompressCode 0x66 = some (.aluImm .add a0 sp 0xA4, 2) := by decide
theorem dp_at_68 : fetchRel p384DecompressCode 0x68 = some (.aluImm .add a1 sp 0x74, 2) := by decide
theorem dp_at_6a : fetchRel p384DecompressCode 0x6A = some (.aluImm .add a2 sp 0x40, 2) := by decide
theorem dp_at_6c : fetchRel p384DecompressCode 0x6C = some (.alu .add a3 x0 (20 : Fin 32), 2) := by decide
theorem dp_at_6e : fetchRel p384DecompressCode 0x6E = some (.auipc ra 0x10000, 4) := by decide
theorem dp_at_72 : fetchRel p384DecompressCode 0x72 = some (.jalr ra ra 0x374, 4) := by decide
theorem dp_at_76 : fetchRel p384DecompressCode 0x76 = some (.aluImm .add a0 sp 0x62C, 4) := by decide
theorem dp_at_7a : fetchRel p384DecompressCode 0x7A = some (.aluImm .add a1 sp 0xA4, 2) := by decide
theorem dp_at_7c : fetchRel p384DecompressCode 0x7C = some (.aluImm .add a2 sp 0xA4, 2) := by decide
theorem dp_at_7e : fetchRel p384DecompressCode 0x7E = some (.aluImm .add (8 : Fin 32) sp 0x62C, 4) := by decide
theorem dp_at_82 : fetchRel p384DecompressCode 0x82 = some (.auipc ra 0x10000, 4) := by decide
theorem dp_at_86 : fetchRel p384DecompressCode 0x86 = some (.jalr ra ra 0x3A8, 4) := by decide
theorem dp_at_8a : fetchRel p384DecompressCode 0x8A = some (.aluImm .add a0 sp 0x2FC, 2) := by decide
theorem dp_at_8c : fetchRel p384DecompressCode 0x8C = some (.aluImm .add a1 sp 0x62C, 4) := by decide
theorem dp_at_90 : fetchRel p384DecompressCode 0x90 = some (.aluImm .add a2 sp 0xA4, 2) := by decide
theorem dp_at_92 : fetchRel p384DecompressCode 0x92 = some (.auipc ra 0x10000, 4) := by decide
theorem dp_at_96 : fetchRel p384DecompressCode 0x96 = some (.jalr ra ra 0x398, 4) := by decide
theorem dp_at_9a : fetchRel p384DecompressCode 0x9A = some (.lui a1 0x3FCC4000, 4) := by decide
theorem dp_at_9e : fetchRel p384DecompressCode 0x9E = some (.aluImm .add a1 a1 0x74, 4) := by decide
theorem dp_at_a2 : fetchRel p384DecompressCode 0xA2 = some (.aluImm .add a0 sp 0x62C, 4) := by decide
theorem dp_at_a6 : fetchRel p384DecompressCode 0xA6 = some (.aluImm .add a2 sp 0xA4, 2) := by decide
theorem dp_at_a8 : fetchRel p384DecompressCode 0xA8 = some (.auipc ra 0x10000, 4) := by decide
theorem dp_at_ac : fetchRel p384DecompressCode 0xAC = some (.jalr ra ra 0x382, 4) := by decide
theorem dp_at_b0 : fetchRel p384DecompressCode 0xB0 = some (.aluImm .add a0 sp 0x29C, 2) := by decide
theorem dp_at_b2 : fetchRel p384DecompressCode 0xB2 = some (.aluImm .add a1 sp 0x2FC, 2) := by decide
theorem dp_at_b4 : fetchRel p384DecompressCode 0xB4 = some (.aluImm .add a2 sp 0x62C, 4) := by decide
theorem dp_at_b8 : fetchRel p384DecompressCode 0xB8 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem dp_at_bc : fetchRel p384DecompressCode 0xBC = some (.jalr ra ra 0xFFFFFE1A, 4) := by decide
theorem dp_at_c0 : fetchRel p384DecompressCode 0xC0 = some (.lui a2 0x3FCC4000, 4) := by decide
theorem dp_at_c4 : fetchRel p384DecompressCode 0xC4 = some (.aluImm .add a2 a2 0xA4, 4) := by decide
theorem dp_at_c8 : fetchRel p384DecompressCode 0xC8 = some (.aluImm .add a0 sp 0x104, 2) := by decide
theorem dp_at_ca : fetchRel p384DecompressCode 0xCA = some (.aluImm .add a1 sp 0x29C, 2) := by decide
theorem dp_at_cc : fetchRel p384DecompressCode 0xCC = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem dp_at_d0 : fetchRel p384DecompressCode 0xD0 = some (.jalr ra ra 0xFFFFFE06, 4) := by decide
theorem dp_at_d4 : fetchRel p384DecompressCode 0xD4 = some (.aluImm .add a0 sp 0x134, 2) := by decide
theorem dp_at_d6 : fetchRel p384DecompressCode 0xD6 = some (.lui (24 : Fin 32) 0x3FCC5000, 4) := by decide
theorem dp_at_da : fetchRel p384DecompressCode 0xDA = some (.aluImm .add (24 : Fin 32) (24 : Fin 32) 0xFFFFFCF4, 4) := by decide
theorem dp_at_de : fetchRel p384DecompressCode 0xDE = some (.aluImm .add a2 x0 0x9C, 4) := by decide
theorem dp_at_e2 : fetchRel p384DecompressCode 0xE2 = some (.alu .add a1 x0 (24 : Fin 32), 2) := by decide
theorem dp_at_e4 : fetchRel p384DecompressCode 0xE4 = some (.auipc ra 0x11000, 4) := by decide
theorem dp_at_e8 : fetchRel p384DecompressCode 0xE8 = some (.jalr ra ra 0x318, 4) := by decide
theorem dp_at_ec : fetchRel p384DecompressCode 0xEC = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem dp_at_ee : fetchRel p384DecompressCode 0xEE = some (.lui a1 0x40000000, 4) := by decide
theorem dp_at_f2 : fetchRel p384DecompressCode 0xF2 = some (.aluImm .add a2 x0 0x10, 2) := by decide
theorem dp_at_f4 : fetchRel p384DecompressCode 0xF4 = some (.aluImm .add a1 a1 0xFFFFFFFF, 2) := by decide
theorem dp_at_f6 : fetchRel p384DecompressCode 0xF6 = some (.branch .beq a2 x0 0x34, 2) := by decide
theorem dp_at_f8 : fetchRel p384DecompressCode 0xF8 = some (.alu .sub a3 x0 a2, 4) := by decide
theorem dp_at_fc : fetchRel p384DecompressCode 0xFC = some (.alu .srl a3 a1 a3, 4) := by decide
theorem dp_at_100 : fetchRel p384DecompressCode 0x100 = some (.store .sw sp a3 0x62C, 4) := by decide
theorem dp_at_104 : fetchRel p384DecompressCode 0x104 = some (.load .lw a3 sp 0x62C, 4) := by decide
theorem dp_at_108 : fetchRel p384DecompressCode 0x108 = some (.aluImm .sltu a3 a3 0x1, 4) := by decide
theorem dp_at_10c : fetchRel p384DecompressCode 0x10C = some (.store .sb sp a3 0x62C, 4) := by decide
theorem dp_at_110 : fetchRel p384DecompressCode 0x110 = some (.load .lbu a3 sp 0x62C, 4) := by decide
theorem dp_at_114 : fetchRel p384DecompressCode 0x114 = some (.alu .sll a4 a1 a2, 4) := by decide
theorem dp_at_118 : fetchRel p384DecompressCode 0x118 = some (.alu .xor a4 a4 a1, 2) := by decide
theorem dp_at_11a : fetchRel p384DecompressCode 0x11A = some (.alu .sub a3 x0 a3, 4) := by decide
theorem dp_at_11e : fetchRel p384DecompressCode 0x11E = some (.alu .and a4 a4 a3, 2) := by decide
theorem dp_at_120 : fetchRel p384DecompressCode 0x120 = some (.alu .and a3 a3 a2, 2) := by decide
theorem dp_at_122 : fetchRel p384DecompressCode 0x122 = some (.alu .xor a1 a1 a4, 2) := by decide
theorem dp_at_124 : fetchRel p384DecompressCode 0x124 = some (.alu .add a0 a0 a3, 2) := by decide
theorem dp_at_126 : fetchRel p384DecompressCode 0x126 = some (.aluImm .srl a2 a2 0x1, 2) := by decide
theorem dp_at_128 : fetchRel p384DecompressCode 0x128 = some (.branch .bne a2 x0 0xFFFFFFD0, 2) := by decide
theorem dp_at_12a : fetchRel p384DecompressCode 0x12A = some (.store .sw sp a1 0x62C, 4) := by decide
theorem dp_at_12e : fetchRel p384DecompressCode 0x12E = some (.aluImm .add a1 sp 0x62C, 4) := by decide
theorem dp_at_132 : fetchRel p384DecompressCode 0x132 = some (.load .lw a1 sp 0x62C, 4) := by decide
theorem dp_at_136 : fetchRel p384DecompressCode 0x136 = some (.aluImm .sltu a1 a1 0x1, 4) := by decide
theorem dp_at_13a : fetchRel p384DecompressCode 0x13A = some (.store .sb sp a1 0x62C, 4) := by decide
theorem dp_at_13e : fetchRel p384DecompressCode 0x13E = some (.aluImm .add a1 sp 0x62C, 4) := by decide
theorem dp_at_142 : fetchRel p384DecompressCode 0x142 = some (.load .lbu a1 sp 0x62C, 4) := by decide
theorem dp_at_146 : fetchRel p384DecompressCode 0x146 = some (.aluImm .and a1 a1 0x1, 2) := by decide
theorem dp_at_148 : fetchRel p384DecompressCode 0x148 = some (.alu .add (8 : Fin 32) a0 a1, 4) := by decide
theorem dp_at_14c : fetchRel p384DecompressCode 0x14C = some (.aluImm .add (9 : Fin 32) x0 0x180, 4) := by decide
theorem dp_at_150 : fetchRel p384DecompressCode 0x150 = some (.alu .sub (18 : Fin 32) (9 : Fin 32) (8 : Fin 32), 4) := by decide
theorem dp_at_154 : fetchRel p384DecompressCode 0x154 = some (.aluImm .add a0 sp 0x29C, 2) := by decide
theorem dp_at_156 : fetchRel p384DecompressCode 0x156 = some (.aluImm .add a1 sp 0x104, 2) := by decide
theorem dp_at_158 : fetchRel p384DecompressCode 0x158 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem dp_at_15c : fetchRel p384DecompressCode 0x15C = some (.auipc ra 0x11000, 4) := by decide
theorem dp_at_160 : fetchRel p384DecompressCode 0x160 = some (.jalr ra ra 0x2A0, 4) := by decide
theorem dp_at_164 : fetchRel p384DecompressCode 0x164 = some (.aluImm .add a0 sp 0x2CC, 2) := by decide
theorem dp_at_166 : fetchRel p384DecompressCode 0x166 = some (.lui (22 : Fin 32) 0x3FCC5000, 4) := by decide
theorem dp_at_16a : fetchRel p384DecompressCode 0x16A = some (.aluImm .add (22 : Fin 32) (22 : Fin 32) 0xFFFFFE94, 4) := by decide
theorem dp_at_16e : fetchRel p384DecompressCode 0x16E = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem dp_at_172 : fetchRel p384DecompressCode 0x172 = some (.alu .add a1 x0 (22 : Fin 32), 2) := by decide
theorem dp_at_174 : fetchRel p384DecompressCode 0x174 = some (.auipc ra 0x11000, 4) := by decide
theorem dp_at_178 : fetchRel p384DecompressCode 0x178 = some (.jalr ra ra 0x288, 4) := by decide
theorem dp_at_17c : fetchRel p384DecompressCode 0x17C = some (.branch .bltu (18 : Fin 32) (9 : Fin 32) 0x8, 4) := by decide
theorem dp_at_180 : fetchRel p384DecompressCode 0x180 = some (.aluImm .add (18 : Fin 32) x0 0x180, 4) := by decide
theorem dp_at_184 : fetchRel p384DecompressCode 0x184 = some (.aluImm .add a0 (8 : Fin 32) 0xFFFFFE80, 4) := by decide
theorem dp_at_188 : fetchRel p384DecompressCode 0x188 = some (.branch .bne a0 x0 0x16, 2) := by decide
theorem dp_at_18a : fetchRel p384DecompressCode 0x18A = some (.aluImm .add a1 (24 : Fin 32) 0x30, 4) := by decide
theorem dp_at_18e : fetchRel p384DecompressCode 0x18E = some (.aluImm .add a0 sp 0x1D0, 2) := by decide
theorem dp_at_190 : fetchRel p384DecompressCode 0x190 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem dp_at_194 : fetchRel p384DecompressCode 0x194 = some (.auipc ra 0x11000, 4) := by decide
theorem dp_at_198 : fetchRel p384DecompressCode 0x198 = some (.jalr ra ra 0x268, 4) := by decide
theorem dp_at_19c : fetchRel p384DecompressCode 0x19C = some (.jal x0 0x420, 2) := by decide
theorem dp_at_19e : fetchRel p384DecompressCode 0x19E = some (.aluImm .add (8 : Fin 32) sp 0x2FC, 2) := by decide
theorem dp_at_1a0 : fetchRel p384DecompressCode 0x1A0 = some (.aluImm .add (9 : Fin 32) x0 0x10, 2) := by decide
theorem dp_at_1a2 : fetchRel p384DecompressCode 0x1A2 = some (.branch .beq (9 : Fin 32) x0 0x1A, 2) := by decide
theorem dp_at_1a4 : fetchRel p384DecompressCode 0x1A4 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem dp_at_1a8 : fetchRel p384DecompressCode 0x1A8 = some (.alu .add a0 x0 (8 : Fin 32), 2) := by decide
theorem dp_at_1aa : fetchRel p384DecompressCode 0x1AA = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem dp_at_1ac : fetchRel p384DecompressCode 0x1AC = some (.auipc ra 0x11000, 4) := by decide
theorem dp_at_1b0 : fetchRel p384DecompressCode 0x1B0 = some (.jalr ra ra 0x1E8, 4) := by decide
theorem dp_at_1b4 : fetchRel p384DecompressCode 0x1B4 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x30, 4) := by decide
theorem dp_at_1b8 : fetchRel p384DecompressCode 0x1B8 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem dp_at_1ba : fetchRel p384DecompressCode 0x1BA = some (.branch .bne (9 : Fin 32) x0 0xFFFFFFEA, 2) := by decide
theorem dp_at_1bc : fetchRel p384DecompressCode 0x1BC = some (.store .sw sp (19 : Fin 32) 0x18, 2) := by decide
theorem dp_at_1be : fetchRel p384DecompressCode 0x1BE = some (.aluImm .add a0 sp 0x62C, 4) := by decide
theorem dp_at_1c2 : fetchRel p384DecompressCode 0x1C2 = some (.aluImm .add a1 sp 0x2FC, 2) := by decide
theorem dp_at_1c4 : fetchRel p384DecompressCode 0x1C4 = some (.aluImm .add a2 x0 0x300, 4) := by decide
theorem dp_at_1c8 : fetchRel p384DecompressCode 0x1C8 = some (.aluImm .add (9 : Fin 32) sp 0x62C, 4) := by decide
theorem dp_at_1cc : fetchRel p384DecompressCode 0x1CC = some (.auipc ra 0x11000, 4) := by decide
theorem dp_at_1d0 : fetchRel p384DecompressCode 0x1D0 = some (.jalr ra ra 0x230, 4) := by decide
theorem dp_at_1d4 : fetchRel p384DecompressCode 0x1D4 = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem dp_at_1d8 : fetchRel p384DecompressCode 0x1D8 = some (.aluImm .add a0 a0 0x12D, 4) := by decide
theorem dp_at_1dc : fetchRel p384DecompressCode 0x1DC = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem dp_at_1e0 : fetchRel p384DecompressCode 0x1E0 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem dp_at_1e2 : fetchRel p384DecompressCode 0x1E2 = some (.auipc ra 0x11000, 4) := by decide
theorem dp_at_1e6 : fetchRel p384DecompressCode 0x1E6 = some (.jalr ra ra 0x1B2, 4) := by decide
theorem dp_at_1ea : fetchRel p384DecompressCode 0x1EA = some (.aluImm .add a0 sp 0x2FC, 2) := by decide
theorem dp_at_1ec : fetchRel p384DecompressCode 0x1EC = some (.aluImm .add a1 sp 0x62C, 4) := by decide
theorem dp_at_1f0 : fetchRel p384DecompressCode 0x1F0 = some (.aluImm .add a2 x0 0x330, 4) := by decide
theorem dp_at_1f4 : fetchRel p384DecompressCode 0x1F4 = some (.auipc ra 0x11000, 4) := by decide
theorem dp_at_1f8 : fetchRel p384DecompressCode 0x1F8 = some (.jalr ra ra 0x208, 4) := by decide
theorem dp_at_1fc : fetchRel p384DecompressCode 0x1FC = some (.aluImm .add (19 : Fin 32) sp 0x65C, 4) := by decide
theorem dp_at_200 : fetchRel p384DecompressCode 0x200 = some (.aluImm .add (8 : Fin 32) x0 0x10, 2) := by decide
theorem dp_at_202 : fetchRel p384DecompressCode 0x202 = some (.aluImm .add (24 : Fin 32) (24 : Fin 32) 0x30, 4) := by decide
theorem dp_at_206 : fetchRel p384DecompressCode 0x206 = some (.branch .beq (8 : Fin 32) x0 0x1A, 2) := by decide
theorem dp_at_208 : fetchRel p384DecompressCode 0x208 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem dp_at_20c : fetchRel p384DecompressCode 0x20C = some (.alu .add a0 x0 (9 : Fin 32), 2) := by decide
theorem dp_at_20e : fetchRel p384DecompressCode 0x20E = some (.alu .add a1 x0 (24 : Fin 32), 2) := by decide
theorem dp_at_210 : fetchRel p384DecompressCode 0x210 = some (.auipc ra 0x11000, 4) := by decide
theorem dp_at_214 : fetchRel p384DecompressCode 0x214 = some (.jalr ra ra 0x1EC, 4) := by decide
theorem dp_at_218 : fetchRel p384DecompressCode 0x218 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x30, 4) := by decide
theorem dp_at_21c : fetchRel p384DecompressCode 0x21C = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem dp_at_21e : fetchRel p384DecompressCode 0x21E = some (.branch .bne (8 : Fin 32) x0 0xFFFFFFEA, 2) := by decide
theorem dp_at_220 : fetchRel p384DecompressCode 0x220 = some (.aluImm .add a1 sp 0x104, 2) := by decide
theorem dp_at_222 : fetchRel p384DecompressCode 0x222 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem dp_at_226 : fetchRel p384DecompressCode 0x226 = some (.alu .add a0 x0 (19 : Fin 32), 2) := by decide
theorem dp_at_228 : fetchRel p384DecompressCode 0x228 = some (.auipc ra 0x11000, 4) := by decide
theorem dp_at_22c : fetchRel p384DecompressCode 0x22C = some (.jalr ra ra 0x1D4, 4) := by decide
theorem dp_at_230 : fetchRel p384DecompressCode 0x230 = some (.aluImm .add (8 : Fin 32) x0 0xE, 2) := by decide
theorem dp_at_232 : fetchRel p384DecompressCode 0x232 = some (.branch .beq (8 : Fin 32) x0 0x3A, 2) := by decide
theorem dp_at_234 : fetchRel p384DecompressCode 0x234 = some (.aluImm .add (9 : Fin 32) (19 : Fin 32) 0x30, 4) := by decide
theorem dp_at_238 : fetchRel p384DecompressCode 0x238 = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem dp_at_23c : fetchRel p384DecompressCode 0x23C = some (.aluImm .add a0 a0 0x1ED, 4) := by decide
theorem dp_at_240 : fetchRel p384DecompressCode 0x240 = some (.aluImm .add a2 sp 0x29C, 2) := by decide
theorem dp_at_242 : fetchRel p384DecompressCode 0x242 = some (.aluImm .add a4 x0 0x1, 2) := by decide
theorem dp_at_244 : fetchRel p384DecompressCode 0x244 = some (.alu .add a1 x0 (19 : Fin 32), 2) := by decide
theorem dp_at_246 : fetchRel p384DecompressCode 0x246 = some (.aluImm .add a3 sp 0x134, 2) := by decide
theorem dp_at_248 : fetchRel p384DecompressCode 0x248 = some (.auipc ra 0xF000, 4) := by decide
theorem dp_at_24c : fetchRel p384DecompressCode 0x24C = some (.jalr ra ra 0x640, 4) := by decide
theorem dp_at_250 : fetchRel p384DecompressCode 0x250 = some (.aluImm .add a1 sp 0x7FF, 4) := by decide
theorem dp_at_254 : fetchRel p384DecompressCode 0x254 = some (.aluImm .add a1 a1 0x1ED, 4) := by decide
theorem dp_at_258 : fetchRel p384DecompressCode 0x258 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem dp_at_25c : fetchRel p384DecompressCode 0x25C = some (.alu .add a0 x0 (9 : Fin 32), 2) := by decide
theorem dp_at_25e : fetchRel p384DecompressCode 0x25E = some (.auipc ra 0x11000, 4) := by decide
theorem dp_at_262 : fetchRel p384DecompressCode 0x262 = some (.jalr ra ra 0x19E, 4) := by decide
theorem dp_at_266 : fetchRel p384DecompressCode 0x266 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem dp_at_268 : fetchRel p384DecompressCode 0x268 = some (.alu .add (19 : Fin 32) x0 (9 : Fin 32), 2) := by decide
theorem dp_at_26a : fetchRel p384DecompressCode 0x26A = some (.branch .bne (8 : Fin 32) x0 0xFFFFFFCA, 2) := by decide
theorem dp_at_26c : fetchRel p384DecompressCode 0x26C = some (.store .sw sp (21 : Fin 32) 0x10, 2) := by decide
theorem dp_at_26e : fetchRel p384DecompressCode 0x26E = some (.store .sw sp (20 : Fin 32) 0x14, 2) := by decide
theorem dp_at_270 : fetchRel p384DecompressCode 0x270 = some (.aluImm .add a0 sp 0x2FC, 2) := by decide
theorem dp_at_272 : fetchRel p384DecompressCode 0x272 = some (.aluImm .add a1 sp 0x62C, 4) := by decide
theorem dp_at_276 : fetchRel p384DecompressCode 0x276 = some (.aluImm .add a2 x0 0x300, 4) := by decide
theorem dp_at_27a : fetchRel p384DecompressCode 0x27A = some (.auipc ra 0x11000, 4) := by decide
theorem dp_at_27e : fetchRel p384DecompressCode 0x27E = some (.jalr ra ra 0x182, 4) := by decide
theorem dp_at_282 : fetchRel p384DecompressCode 0x282 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem dp_at_286 : fetchRel p384DecompressCode 0x286 = some (.aluImm .add a0 sp 0x5FC, 4) := by decide
theorem dp_at_28a : fetchRel p384DecompressCode 0x28A = some (.alu .add a1 x0 (22 : Fin 32), 2) := by decide
theorem dp_at_28c : fetchRel p384DecompressCode 0x28C = some (.auipc ra 0x11000, 4) := by decide
theorem dp_at_290 : fetchRel p384DecompressCode 0x290 = some (.jalr ra ra 0x170, 4) := by decide
theorem dp_at_294 : fetchRel p384DecompressCode 0x294 = some (.aluImm .add (18 : Fin 32) (18 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem dp_at_296 : fetchRel p384DecompressCode 0x296 = some (.aluImm .srl (9 : Fin 32) (18 : Fin 32) 0x5, 4) := by decide
theorem dp_at_29a : fetchRel p384DecompressCode 0x29A = some (.aluImm .and a0 (18 : Fin 32) 0x3, 4) := by decide
theorem dp_at_29e : fetchRel p384DecompressCode 0x29E = some (.aluImm .add a1 x0 0x2, 2) := by decide
theorem dp_at_2a0 : fetchRel p384DecompressCode 0x2A0 = some (.aluImm .sll (18 : Fin 32) (18 : Fin 32) 0x1B, 2) := by decide
theorem dp_at_2a2 : fetchRel p384DecompressCode 0x2A2 = some (.alu .sll a0 a1 a0, 4) := by decide
theorem dp_at_2a6 : fetchRel p384DecompressCode 0x2A6 = some (.aluImm .srl (8 : Fin 32) (18 : Fin 32) 0x1D, 4) := by decide
theorem dp_at_2aa : fetchRel p384DecompressCode 0x2AA = some (.aluImm .add (18 : Fin 32) a0 0xFFFFFFFF, 4) := by decide
theorem dp_at_2ae : fetchRel p384DecompressCode 0x2AE = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem dp_at_2b2 : fetchRel p384DecompressCode 0x2B2 = some (.aluImm .add a0 a0 0x15D, 4) := by decide
theorem dp_at_2b6 : fetchRel p384DecompressCode 0x2B6 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem dp_at_2ba : fetchRel p384DecompressCode 0x2BA = some (.alu .add a1 x0 (24 : Fin 32), 2) := by decide
theorem dp_at_2bc : fetchRel p384DecompressCode 0x2BC = some (.auipc ra 0x11000, 4) := by decide
theorem dp_at_2c0 : fetchRel p384DecompressCode 0x2C0 = some (.jalr ra ra 0x140, 4) := by decide
theorem dp_at_2c4 : fetchRel p384DecompressCode 0x2C4 = some (.store .sw sp (9 : Fin 32) 0x34, 2) := by decide
theorem dp_at_2c6 : fetchRel p384DecompressCode 0x2C6 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x1, 2) := by decide
theorem dp_at_2c8 : fetchRel p384DecompressCode 0x2C8 = some (.store .sw sp (8 : Fin 32) 0x30, 2) := by decide
theorem dp_at_2ca : fetchRel p384DecompressCode 0x2CA = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x1, 2) := by decide
theorem dp_at_2cc : fetchRel p384DecompressCode 0x2CC = some (.store .sw sp (8 : Fin 32) 0x1C, 2) := by decide
theorem dp_at_2ce : fetchRel p384DecompressCode 0x2CE = some (.aluImm .and a0 (18 : Fin 32) 0xF, 4) := by decide
theorem dp_at_2d2 : fetchRel p384DecompressCode 0x2D2 = some (.store .sw sp a0 0x24, 2) := by decide
theorem dp_at_2d4 : fetchRel p384DecompressCode 0x2D4 = some (.aluImm .add (18 : Fin 32) sp 0x7FF, 4) := by decide
theorem dp_at_2d8 : fetchRel p384DecompressCode 0x2D8 = some (.aluImm .add (18 : Fin 32) (18 : Fin 32) 0x1C1, 4) := by decide
theorem dp_at_2dc : fetchRel p384DecompressCode 0x2DC = some (.aluImm .add (26 : Fin 32) sp 0x7FF, 4) := by decide
theorem dp_at_2e0 : fetchRel p384DecompressCode 0x2E0 = some (.aluImm .add (26 : Fin 32) (26 : Fin 32) 0x191, 4) := by decide
theorem dp_at_2e4 : fetchRel p384DecompressCode 0x2E4 = some (.aluImm .add (21 : Fin 32) sp 0x138, 4) := by decide
theorem dp_at_2e8 : fetchRel p384DecompressCode 0x2E8 = some (.aluImm .add (19 : Fin 32) sp 0x7FF, 4) := by decide
theorem dp_at_2ec : fetchRel p384DecompressCode 0x2EC = some (.aluImm .add (19 : Fin 32) (19 : Fin 32) 0x1BD, 4) := by decide
theorem dp_at_2f0 : fetchRel p384DecompressCode 0x2F0 = some (.aluImm .add (22 : Fin 32) x0 0xC, 2) := by decide
theorem dp_at_2f2 : fetchRel p384DecompressCode 0x2F2 = some (.aluImm .add (23 : Fin 32) x0 0xFFFFFFFF, 2) := by decide
theorem dp_at_2f4 : fetchRel p384DecompressCode 0x2F4 = some (.branch .beq (9 : Fin 32) x0 0x2AC, 4) := by decide
theorem dp_at_2f8 : fetchRel p384DecompressCode 0x2F8 = some (.store .sw sp (9 : Fin 32) 0x2C, 2) := by decide
theorem dp_at_2fa : fetchRel p384DecompressCode 0x2FA = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem dp_at_2fc : fetchRel p384DecompressCode 0x2FC = some (.load .lw a3 sp 0x1C, 2) := by decide
theorem dp_at_2fe : fetchRel p384DecompressCode 0x2FE = some (.load .lw a0 sp 0x34, 2) := by decide
theorem dp_at_300 : fetchRel p384DecompressCode 0x300 = some (.store .sw sp (9 : Fin 32) 0x38, 2) := by decide
theorem dp_at_302 : fetchRel p384DecompressCode 0x302 = some (.branch .beq (9 : Fin 32) a0 0x6, 4) := by decide
theorem dp_at_306 : fetchRel p384DecompressCode 0x306 = some (.aluImm .add a3 x0 0x8, 2) := by decide
theorem dp_at_308 : fetchRel p384DecompressCode 0x308 = some (.load .lw a0 sp 0x38, 2) := by decide
theorem dp_at_30a : fetchRel p384DecompressCode 0x30A = some (.aluImm .sll a0 a0 0x2, 2) := by decide
theorem dp_at_30c : fetchRel p384DecompressCode 0x30C = some (.aluImm .add a1 sp 0x5FC, 4) := by decide
theorem dp_at_310 : fetchRel p384DecompressCode 0x310 = some (.alu .add a0 a0 a1, 2) := by decide
theorem dp_at_312 : fetchRel p384DecompressCode 0x312 = some (.store .sw sp a0 0x28, 2) := by decide
theorem dp_at_314 : fetchRel p384DecompressCode 0x314 = some (.branch .beq a3 x0 0x286, 4) := by decide
theorem dp_at_318 : fetchRel p384DecompressCode 0x318 = some (.aluImm .add a3 a3 0xFFFFFFFF, 2) := by decide
theorem dp_at_31a : fetchRel p384DecompressCode 0x31A = some (.load .lw a0 sp 0x34, 2) := by decide
theorem dp_at_31c : fetchRel p384DecompressCode 0x31C = some (.load .lw a1 sp 0x38, 2) := by decide
theorem dp_at_31e : fetchRel p384DecompressCode 0x31E = some (.branch .bne a1 a0 0xA, 4) := by decide
theorem dp_at_322 : fetchRel p384DecompressCode 0x322 = some (.load .lw a0 sp 0x30, 2) := by decide
theorem dp_at_324 : fetchRel p384DecompressCode 0x324 = some (.branch .beq a3 a0 0x208, 4) := by decide
theorem dp_at_328 : fetchRel p384DecompressCode 0x328 = some (.store .sw sp a3 0x20, 2) := by decide
theorem dp_at_32a : fetchRel p384DecompressCode 0x32A = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem dp_at_32e : fetchRel p384DecompressCode 0x32E = some (.aluImm .add a0 a0 0x18D, 4) := by decide
theorem dp_at_332 : fetchRel p384DecompressCode 0x332 = some (.aluImm .add a1 sp 0x7FF, 4) := by decide
theorem dp_at_336 : fetchRel p384DecompressCode 0x336 = some (.aluImm .add a1 a1 0x15D, 4) := by decide
theorem dp_at_33a : fetchRel p384DecompressCode 0x33A = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem dp_at_33e : fetchRel p384DecompressCode 0x33E = some (.auipc ra 0x11000, 4) := by decide
theorem dp_at_342 : fetchRel p384DecompressCode 0x342 = some (.jalr ra ra 0xBE, 4) := by decide
theorem dp_at_346 : fetchRel p384DecompressCode 0x346 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem dp_at_348 : fetchRel p384DecompressCode 0x348 = some (.aluImm .add a0 x0 0x4, 2) := by decide
theorem dp_at_34a : fetchRel p384DecompressCode 0x34A = some (.branch .beq a1 a0 0x1C4, 4) := by decide
theorem dp_at_34e : fetchRel p384DecompressCode 0x34E = some (.store .sw sp a1 0x3C, 2) := by decide
theorem dp_at_350 : fetchRel p384DecompressCode 0x350 = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem dp_at_354 : fetchRel p384DecompressCode 0x354 = some (.aluImm .add a0 a0 0x1BD, 4) := by decide
theorem dp_at_358 : fetchRel p384DecompressCode 0x358 = some (.aluImm .add a1 sp 0x7FF, 4) := by decide
theorem dp_at_35c : fetchRel p384DecompressCode 0x35C = some (.aluImm .add a1 a1 0x18D, 4) := by decide
theorem dp_at_360 : fetchRel p384DecompressCode 0x360 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem dp_at_364 : fetchRel p384DecompressCode 0x364 = some (.auipc ra 0x11000, 4) := by decide
theorem dp_at_368 : fetchRel p384DecompressCode 0x368 = some (.jalr ra ra 0x98, 4) := by decide
theorem dp_at_36c : fetchRel p384DecompressCode 0x36C = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem dp_at_370 : fetchRel p384DecompressCode 0x370 = some (.aluImm .add a0 a0 0x18D, 4) := by decide
theorem dp_at_374 : fetchRel p384DecompressCode 0x374 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem dp_at_378 : fetchRel p384DecompressCode 0x378 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem dp_at_37a : fetchRel p384DecompressCode 0x37A = some (.auipc ra 0x11000, 4) := by decide
theorem dp_at_37e : fetchRel p384DecompressCode 0x37E = some (.jalr ra ra 0x1A, 4) := by decide
theorem dp_at_382 : fetchRel p384DecompressCode 0x382 = some (.aluImm .add (27 : Fin 32) x0 0x0, 2) := by decide
theorem dp_at_384 : fetchRel p384DecompressCode 0x384 = some (.aluImm .add (17 : Fin 32) x0 0x0, 2) := by decide
theorem dp_at_386 : fetchRel p384DecompressCode 0x386 = some (.load .lw a6 (25 : Fin 32) 0x30, 4) := by decide
theorem dp_at_38a : fetchRel p384DecompressCode 0x38A = some (.aluImm .add (5 : Fin 32) x0 0x0, 2) := by decide
theorem dp_at_38c : fetchRel p384DecompressCode 0x38C = some (.branch .beq (22 : Fin 32) x0 0xB0, 4) := by decide
theorem dp_at_390 : fetchRel p384DecompressCode 0x390 = some (.aluImm .sll a0 (5 : Fin 32) 0x2, 4) := by decide
theorem dp_at_394 : fetchRel p384DecompressCode 0x394 = some (.alu .add a0 a0 (19 : Fin 32), 2) := by decide
theorem dp_at_396 : fetchRel p384DecompressCode 0x396 = some (.load .lw (6 : Fin 32) a0 0x0, 4) := by decide
theorem dp_at_39a : fetchRel p384DecompressCode 0x39A = some (.alu .mul a0 a6 (6 : Fin 32), 4) := by decide
theorem dp_at_39e : fetchRel p384DecompressCode 0x39E = some (.load .lw a4 (25 : Fin 32) 0x0, 4) := by decide
theorem dp_at_3a2 : fetchRel p384DecompressCode 0x3A2 = some (.alu .mulhu a1 a6 (6 : Fin 32), 4) := by decide
theorem dp_at_3a6 : fetchRel p384DecompressCode 0x3A6 = some (.alu .add (7 : Fin 32) a0 a4, 4) := by decide
theorem dp_at_3aa : fetchRel p384DecompressCode 0x3AA = some (.alu .mulhu a2 (7 : Fin 32) (23 : Fin 32), 4) := by decide
theorem dp_at_3ae : fetchRel p384DecompressCode 0x3AE = some (.alu .sltu a0 (7 : Fin 32) a0, 4) := by decide
theorem dp_at_3b2 : fetchRel p384DecompressCode 0x3B2 = some (.alu .add a0 a0 a1, 2) := by decide
theorem dp_at_3b4 : fetchRel p384DecompressCode 0x3B4 = some (.alu .sltu (9 : Fin 32) x0 (7 : Fin 32), 4) := by decide
theorem dp_at_3b8 : fetchRel p384DecompressCode 0x3B8 = some (.alu .add a0 a0 a2, 2) := by decide
theorem dp_at_3ba : fetchRel p384DecompressCode 0x3BA = some (.aluImm .add (29 : Fin 32) x0 0xB, 2) := by decide
theorem dp_at_3bc : fetchRel p384DecompressCode 0x3BC = some (.alu .add (9 : Fin 32) (9 : Fin 32) a0, 2) := by decide
theorem dp_at_3be : fetchRel p384DecompressCode 0x3BE = some (.alu .sltu a1 a0 a2, 4) := by decide
theorem dp_at_3c2 : fetchRel p384DecompressCode 0x3C2 = some (.alu .sltu a0 (9 : Fin 32) a0, 4) := by decide
theorem dp_at_3c6 : fetchRel p384DecompressCode 0x3C6 = some (.alu .add (30 : Fin 32) x0 (21 : Fin 32), 2) := by decide
theorem dp_at_3c8 : fetchRel p384DecompressCode 0x3C8 = some (.alu .add (28 : Fin 32) a1 a0, 4) := by decide
theorem dp_at_3cc : fetchRel p384DecompressCode 0x3CC = some (.alu .add a0 x0 (26 : Fin 32), 2) := by decide
theorem dp_at_3ce : fetchRel p384DecompressCode 0x3CE = some (.alu .add a2 x0 (18 : Fin 32), 2) := by decide
theorem dp_at_3d0 : fetchRel p384DecompressCode 0x3D0 = some (.branch .beq (29 : Fin 32) x0 0x52, 4) := by decide
theorem dp_at_3d4 : fetchRel p384DecompressCode 0x3D4 = some (.load .lw a3 (30 : Fin 32) 0x0, 4) := by decide
theorem dp_at_3d8 : fetchRel p384DecompressCode 0x3D8 = some (.load .lw a4 a2 0x0, 2) := by decide
theorem dp_at_3da : fetchRel p384DecompressCode 0x3DA = some (.alu .mulhu a1 (7 : Fin 32) a3, 4) := by decide
theorem dp_at_3de : fetchRel p384DecompressCode 0x3DE = some (.alu .mul a5 a4 (6 : Fin 32), 4) := by decide
theorem dp_at_3e2 : fetchRel p384DecompressCode 0x3E2 = some (.alu .mul a3 (7 : Fin 32) a3, 4) := by decide
theorem dp_at_3e6 : fetchRel p384DecompressCode 0x3E6 = some (.load .lw (8 : Fin 32) a0 0x0, 2) := by decide
theorem dp_at_3e8 : fetchRel p384DecompressCode 0x3E8 = some (.alu .mulhu a4 a4 (6 : Fin 32), 4) := by decide
theorem dp_at_3ec : fetchRel p384DecompressCode 0x3EC = some (.alu .add a1 a1 (28 : Fin 32), 2) := by decide
theorem dp_at_3ee : fetchRel p384DecompressCode 0x3EE = some (.aluImm .add a2 a2 0x4, 2) := by decide
theorem dp_at_3f0 : fetchRel p384DecompressCode 0x3F0 = some (.alu .add (8 : Fin 32) (8 : Fin 32) a5, 2) := by decide
theorem dp_at_3f2 : fetchRel p384DecompressCode 0x3F2 = some (.alu .add (9 : Fin 32) (9 : Fin 32) a3, 2) := by decide
theorem dp_at_3f4 : fetchRel p384DecompressCode 0x3F4 = some (.alu .sltu a5 (8 : Fin 32) a5, 4) := by decide
theorem dp_at_3f8 : fetchRel p384DecompressCode 0x3F8 = some (.alu .sltu a3 (9 : Fin 32) a3, 4) := by decide
theorem dp_at_3fc : fetchRel p384DecompressCode 0x3FC = some (.alu .add (8 : Fin 32) (8 : Fin 32) (9 : Fin 32), 2) := by decide
theorem dp_at_3fe : fetchRel p384DecompressCode 0x3FE = some (.alu .add a4 a4 a5, 2) := by decide
theorem dp_at_400 : fetchRel p384DecompressCode 0x400 = some (.alu .add a1 a1 a3, 2) := by decide
theorem dp_at_402 : fetchRel p384DecompressCode 0x402 = some (.alu .sltu (9 : Fin 32) (8 : Fin 32) (9 : Fin 32), 4) := by decide
theorem dp_at_406 : fetchRel p384DecompressCode 0x406 = some (.alu .add a4 a4 a1, 2) := by decide
theorem dp_at_408 : fetchRel p384DecompressCode 0x408 = some (.store .sw a0 (8 : Fin 32) 0xFFFFFFFC, 4) := by decide
theorem dp_at_40c : fetchRel p384DecompressCode 0x40C = some (.alu .add (9 : Fin 32) (9 : Fin 32) a4, 2) := by decide
theorem dp_at_40e : fetchRel p384DecompressCode 0x40E = some (.alu .sltu (28 : Fin 32) a4 a1, 4) := by decide
theorem dp_at_412 : fetchRel p384DecompressCode 0x412 = some (.alu .sltu a1 (9 : Fin 32) a4, 4) := by decide
theorem dp_at_416 : fetchRel p384DecompressCode 0x416 = some (.aluImm .add a0 a0 0x4, 2) := by decide
theorem dp_at_418 : fetchRel p384DecompressCode 0x418 = some (.alu .add (28 : Fin 32) (28 : Fin 32) a1, 2) := by decide
theorem dp_at_41a : fetchRel p384DecompressCode 0x41A = some (.aluImm .add (30 : Fin 32) (30 : Fin 32) 0x4, 2) := by decide
theorem dp_at_41c : fetchRel p384DecompressCode 0x41C = some (.aluImm .add (29 : Fin 32) (29 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem dp_at_41e : fetchRel p384DecompressCode 0x41E = some (.branch .bne (29 : Fin 32) x0 0xFFFFFFB6, 4) := by decide
theorem dp_at_422 : fetchRel p384DecompressCode 0x422 = some (.alu .add (27 : Fin 32) (27 : Fin 32) (9 : Fin 32), 2) := by decide
theorem dp_at_424 : fetchRel p384DecompressCode 0x424 = some (.alu .add a1 (28 : Fin 32) (17 : Fin 32), 4) := by decide
theorem dp_at_428 : fetchRel p384DecompressCode 0x428 = some (.alu .sltu a0 (27 : Fin 32) (9 : Fin 32), 4) := by decide
theorem dp_at_42c : fetchRel p384DecompressCode 0x42C = some (.store .sw (25 : Fin 32) (27 : Fin 32) 0x2C, 4) := by decide
theorem dp_at_430 : fetchRel p384DecompressCode 0x430 = some (.alu .add (27 : Fin 32) a1 a0, 4) := by decide
theorem dp_at_434 : fetchRel p384DecompressCode 0x434 = some (.aluImm .add (5 : Fin 32) (5 : Fin 32) 0x1, 2) := by decide
theorem dp_at_436 : fetchRel p384DecompressCode 0x436 = some (.aluImm .add (17 : Fin 32) x0 0x0, 2) := by decide
theorem dp_at_438 : fetchRel p384DecompressCode 0x438 = some (.branch .bne (5 : Fin 32) (22 : Fin 32) 0xFFFFFF58, 4) := by decide
theorem dp_at_43c : fetchRel p384DecompressCode 0x43C = some (.aluImm .add a0 sp 0x62C, 4) := by decide
theorem dp_at_440 : fetchRel p384DecompressCode 0x440 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem dp_at_444 : fetchRel p384DecompressCode 0x444 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem dp_at_446 : fetchRel p384DecompressCode 0x446 = some (.aluImm .add (24 : Fin 32) sp 0x62C, 4) := by decide
theorem dp_at_44a : fetchRel p384DecompressCode 0x44A = some (.auipc ra 0x11000, 4) := by decide
theorem dp_at_44e : fetchRel p384DecompressCode 0x44E = some (.jalr ra ra 0xFFFFFF4A, 4) := by decide
theorem dp_at_452 : fetchRel p384DecompressCode 0x452 = some (.aluImm .add (20 : Fin 32) x0 0x0, 2) := by decide
theorem dp_at_454 : fetchRel p384DecompressCode 0x454 = some (.aluImm .add (8 : Fin 32) sp 0x7FF, 4) := by decide
theorem dp_at_458 : fetchRel p384DecompressCode 0x458 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x18D, 4) := by decide
theorem dp_at_45c : fetchRel p384DecompressCode 0x45C = some (.aluImm .add (9 : Fin 32) x0 0xC, 2) := by decide
theorem dp_at_45e : fetchRel p384DecompressCode 0x45E = some (.aluImm .add (18 : Fin 32) sp 0x134, 4) := by decide
theorem dp_at_462 : fetchRel p384DecompressCode 0x462 = some (.branch .beq (9 : Fin 32) x0 0x22, 2) := by decide
theorem dp_at_464 : fetchRel p384DecompressCode 0x464 = some (.load .lw a0 (8 : Fin 32) 0x0, 2) := by decide
theorem dp_at_466 : fetchRel p384DecompressCode 0x466 = some (.load .lw a1 (18 : Fin 32) 0x0, 4) := by decide
theorem dp_at_46a : fetchRel p384DecompressCode 0x46A = some (.alu .add a2 x0 (20 : Fin 32), 2) := by decide
theorem dp_at_46c : fetchRel p384DecompressCode 0x46C = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem dp_at_470 : fetchRel p384DecompressCode 0x470 = some (.jalr ra ra 0xFFFFFC52, 4) := by decide
theorem dp_at_474 : fetchRel p384DecompressCode 0x474 = some (.alu .add (20 : Fin 32) x0 a1, 2) := by decide
theorem dp_at_476 : fetchRel p384DecompressCode 0x476 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, 2) := by decide
theorem dp_at_478 : fetchRel p384DecompressCode 0x478 = some (.store .sw (24 : Fin 32) a0 0x0, 4) := by decide
theorem dp_at_47c : fetchRel p384DecompressCode 0x47C = some (.aluImm .add (18 : Fin 32) (18 : Fin 32) 0x4, 2) := by decide
theorem dp_at_47e : fetchRel p384DecompressCode 0x47E = some (.aluImm .add (24 : Fin 32) (24 : Fin 32) 0x4, 2) := by decide
theorem dp_at_480 : fetchRel p384DecompressCode 0x480 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem dp_at_482 : fetchRel p384DecompressCode 0x482 = some (.branch .bne (9 : Fin 32) x0 0xFFFFFFE2, 2) := by decide
theorem dp_at_484 : fetchRel p384DecompressCode 0x484 = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem dp_at_488 : fetchRel p384DecompressCode 0x488 = some (.aluImm .add a0 a0 0x1ED, 4) := by decide
theorem dp_at_48c : fetchRel p384DecompressCode 0x48C = some (.aluImm .add a1 sp 0x62C, 4) := by decide
theorem dp_at_490 : fetchRel p384DecompressCode 0x490 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem dp_at_494 : fetchRel p384DecompressCode 0x494 = some (.auipc ra 0x11000, 4) := by decide
theorem dp_at_498 : fetchRel p384DecompressCode 0x498 = some (.jalr ra ra 0xFFFFFF68, 4) := by decide
theorem dp_at_49c : fetchRel p384DecompressCode 0x49C = some (.store .sw sp (27 : Fin 32) 0x62C, 4) := by decide
theorem dp_at_4a0 : fetchRel p384DecompressCode 0x4A0 = some (.aluImm .add a1 sp 0x62C, 4) := by decide
theorem dp_at_4a4 : fetchRel p384DecompressCode 0x4A4 = some (.load .lw a0 sp 0x62C, 4) := by decide
theorem dp_at_4a8 : fetchRel p384DecompressCode 0x4A8 = some (.aluImm .sltu a0 a0 0x1, 4) := by decide
theorem dp_at_4ac : fetchRel p384DecompressCode 0x4AC = some (.alu .and (24 : Fin 32) a0 (20 : Fin 32), 4) := by decide
theorem dp_at_4b0 : fetchRel p384DecompressCode 0x4B0 = some (.store .sb sp (24 : Fin 32) 0x62C, 4) := by decide
theorem dp_at_4b4 : fetchRel p384DecompressCode 0x4B4 = some (.load .lbu a0 sp 0x62C, 4) := by decide
theorem dp_at_4b8 : fetchRel p384DecompressCode 0x4B8 = some (.aluImm .add a0 a0 0xFFFFFFFF, 2) := by decide
theorem dp_at_4ba : fetchRel p384DecompressCode 0x4BA = some (.alu .and a2 (20 : Fin 32) a0, 4) := by decide
theorem dp_at_4be : fetchRel p384DecompressCode 0x4BE = some (.alu .add a0 x0 (27 : Fin 32), 2) := by decide
theorem dp_at_4c0 : fetchRel p384DecompressCode 0x4C0 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem dp_at_4c2 : fetchRel p384DecompressCode 0x4C2 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem dp_at_4c6 : fetchRel p384DecompressCode 0x4C6 = some (.jalr ra ra 0xFFFFFBFC, 4) := by decide
theorem dp_at_4ca : fetchRel p384DecompressCode 0x4CA = some (.aluImm .add a0 sp 0x62C, 4) := by decide
theorem dp_at_4ce : fetchRel p384DecompressCode 0x4CE = some (.aluImm .add a1 sp 0x7FF, 4) := by decide
theorem dp_at_4d2 : fetchRel p384DecompressCode 0x4D2 = some (.aluImm .add a1 a1 0x1ED, 4) := by decide
theorem dp_at_4d6 : fetchRel p384DecompressCode 0x4D6 = some (.aluImm .add a2 sp 0x7FF, 4) := by decide
theorem dp_at_4da : fetchRel p384DecompressCode 0x4DA = some (.aluImm .add a2 a2 0x18D, 4) := by decide
theorem dp_at_4de : fetchRel p384DecompressCode 0x4DE = some (.alu .add a3 x0 (24 : Fin 32), 2) := by decide
theorem dp_at_4e0 : fetchRel p384DecompressCode 0x4E0 = some (.auipc ra 0xF000, 4) := by decide
theorem dp_at_4e4 : fetchRel p384DecompressCode 0x4E4 = some (.jalr ra ra 0x536, 4) := by decide
theorem dp_at_4e8 : fetchRel p384DecompressCode 0x4E8 = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem dp_at_4ec : fetchRel p384DecompressCode 0x4EC = some (.aluImm .add a0 a0 0x18D, 4) := by decide
theorem dp_at_4f0 : fetchRel p384DecompressCode 0x4F0 = some (.aluImm .add a1 sp 0x62C, 4) := by decide
theorem dp_at_4f4 : fetchRel p384DecompressCode 0x4F4 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem dp_at_4f8 : fetchRel p384DecompressCode 0x4F8 = some (.auipc ra 0x11000, 4) := by decide
theorem dp_at_4fc : fetchRel p384DecompressCode 0x4FC = some (.jalr ra ra 0xFFFFFF04, 4) := by decide
theorem dp_at_500 : fetchRel p384DecompressCode 0x500 = some (.load .lw a1 sp 0x3C, 2) := by decide
theorem dp_at_502 : fetchRel p384DecompressCode 0x502 = some (.aluImm .add a1 a1 0x1, 2) := by decide
theorem dp_at_504 : fetchRel p384DecompressCode 0x504 = some (.aluImm .add (18 : Fin 32) sp 0x7FF, 4) := by decide
theorem dp_at_508 : fetchRel p384DecompressCode 0x508 = some (.aluImm .add (18 : Fin 32) (18 : Fin 32) 0x1C1, 4) := by decide
theorem dp_at_50c : fetchRel p384DecompressCode 0x50C = some (.jal x0 0xFFFFFE3C, 2) := by decide
theorem dp_at_50e : fetchRel p384DecompressCode 0x50E = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem dp_at_512 : fetchRel p384DecompressCode 0x512 = some (.aluImm .add a0 a0 0x15D, 4) := by decide
theorem dp_at_516 : fetchRel p384DecompressCode 0x516 = some (.aluImm .add a1 sp 0x7FF, 4) := by decide
theorem dp_at_51a : fetchRel p384DecompressCode 0x51A = some (.aluImm .add a1 a1 0x18D, 4) := by decide
theorem dp_at_51e : fetchRel p384DecompressCode 0x51E = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem dp_at_522 : fetchRel p384DecompressCode 0x522 = some (.auipc ra 0x11000, 4) := by decide
theorem dp_at_526 : fetchRel p384DecompressCode 0x526 = some (.jalr ra ra 0xFFFFFEDA, 4) := by decide
theorem dp_at_52a : fetchRel p384DecompressCode 0x52A = some (.load .lw a3 sp 0x20, 2) := by decide
theorem dp_at_52c : fetchRel p384DecompressCode 0x52C = some (.load .lw a0 sp 0x2C, 2) := by decide
theorem dp_at_52e : fetchRel p384DecompressCode 0x52E = some (.aluImm .add a1 x0 0xD, 2) := by decide
theorem dp_at_530 : fetchRel p384DecompressCode 0x530 = some (.branch .bgeu a0 a1 0x1F4, 4) := by decide
theorem dp_at_534 : fetchRel p384DecompressCode 0x534 = some (.load .lw a0 sp 0x34, 2) := by decide
theorem dp_at_536 : fetchRel p384DecompressCode 0x536 = some (.load .lw a1 sp 0x38, 2) := by decide
theorem dp_at_538 : fetchRel p384DecompressCode 0x538 = some (.alu .xor a0 a0 a1, 2) := by decide
theorem dp_at_53a : fetchRel p384DecompressCode 0x53A = some (.load .lw a1 sp 0x30, 2) := by decide
theorem dp_at_53c : fetchRel p384DecompressCode 0x53C = some (.alu .xor a1 a1 a3, 2) := by decide
theorem dp_at_53e : fetchRel p384DecompressCode 0x53E = some (.alu .or a1 a1 a0, 2) := by decide
theorem dp_at_540 : fetchRel p384DecompressCode 0x540 = some (.load .lw a0 sp 0x24, 2) := by decide
theorem dp_at_542 : fetchRel p384DecompressCode 0x542 = some (.branch .beq a1 x0 0x4, 2) := by decide
theorem dp_at_544 : fetchRel p384DecompressCode 0x544 = some (.aluImm .add a0 x0 0xF, 2) := by decide
theorem dp_at_546 : fetchRel p384DecompressCode 0x546 = some (.load .lw a1 sp 0x28, 2) := by decide
theorem dp_at_548 : fetchRel p384DecompressCode 0x548 = some (.load .lw a1 a1 0x0, 2) := by decide
theorem dp_at_54a : fetchRel p384DecompressCode 0x54A = some (.aluImm .sll a2 a3 0x2, 4) := by decide
theorem dp_at_54e : fetchRel p384DecompressCode 0x54E = some (.alu .srl a1 a1 a2, 4) := by decide
theorem dp_at_552 : fetchRel p384DecompressCode 0x552 = some (.alu .and a0 a0 a1, 2) := by decide
theorem dp_at_554 : fetchRel p384DecompressCode 0x554 = some (.branch .beq a0 x0 0xFFFFFDC0, 4) := by decide
theorem dp_at_558 : fetchRel p384DecompressCode 0x558 = some (.aluImm .add a1 x0 0x30, 4) := by decide
theorem dp_at_55c : fetchRel p384DecompressCode 0x55C = some (.alu .mul a2 a0 a1, 4) := by decide
theorem dp_at_560 : fetchRel p384DecompressCode 0x560 = some (.aluImm .add a0 sp 0x2FC, 2) := by decide
theorem dp_at_562 : fetchRel p384DecompressCode 0x562 = some (.alu .add a2 a2 a0, 2) := by decide
theorem dp_at_564 : fetchRel p384DecompressCode 0x564 = some (.aluImm .add a0 sp 0x62C, 4) := by decide
theorem dp_at_568 : fetchRel p384DecompressCode 0x568 = some (.aluImm .add a1 sp 0x7FF, 4) := by decide
theorem dp_at_56c : fetchRel p384DecompressCode 0x56C = some (.aluImm .add a1 a1 0x15D, 4) := by decide
theorem dp_at_570 : fetchRel p384DecompressCode 0x570 = some (.aluImm .add a4 x0 0x1, 2) := by decide
theorem dp_at_572 : fetchRel p384DecompressCode 0x572 = some (.alu .add (8 : Fin 32) x0 a3, 2) := by decide
theorem dp_at_574 : fetchRel p384DecompressCode 0x574 = some (.aluImm .add a3 sp 0x134, 2) := by decide
theorem dp_at_576 : fetchRel p384DecompressCode 0x576 = some (.auipc ra 0xF000, 4) := by decide
theorem dp_at_57a : fetchRel p384DecompressCode 0x57A = some (.jalr ra ra 0x312, 4) := by decide
theorem dp_at_57e : fetchRel p384DecompressCode 0x57E = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem dp_at_582 : fetchRel p384DecompressCode 0x582 = some (.aluImm .add a0 a0 0x15D, 4) := by decide
theorem dp_at_586 : fetchRel p384DecompressCode 0x586 = some (.aluImm .add a1 sp 0x62C, 4) := by decide
theorem dp_at_58a : fetchRel p384DecompressCode 0x58A = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem dp_at_58e : fetchRel p384DecompressCode 0x58E = some (.auipc ra 0x11000, 4) := by decide
theorem dp_at_592 : fetchRel p384DecompressCode 0x592 = some (.jalr ra ra 0xFFFFFE6E, 4) := by decide
theorem dp_at_596 : fetchRel p384DecompressCode 0x596 = some (.alu .add a3 x0 (8 : Fin 32), 2) := by decide
theorem dp_at_598 : fetchRel p384DecompressCode 0x598 = some (.jal x0 0xFFFFFD7C, 2) := by decide
theorem dp_at_59a : fetchRel p384DecompressCode 0x59A = some (.load .lw (9 : Fin 32) sp 0x38, 2) := by decide
theorem dp_at_59c : fetchRel p384DecompressCode 0x59C = some (.branch .bne (9 : Fin 32) x0 0xFFFFFD5C, 4) := by decide
theorem dp_at_5a0 : fetchRel p384DecompressCode 0x5A0 = some (.aluImm .add a0 sp 0x1D0, 2) := by decide
theorem dp_at_5a2 : fetchRel p384DecompressCode 0x5A2 = some (.aluImm .add a1 sp 0x7FF, 4) := by decide
theorem dp_at_5a6 : fetchRel p384DecompressCode 0x5A6 = some (.aluImm .add a1 a1 0x15D, 4) := by decide
theorem dp_at_5aa : fetchRel p384DecompressCode 0x5AA = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem dp_at_5ae : fetchRel p384DecompressCode 0x5AE = some (.auipc ra 0x11000, 4) := by decide
theorem dp_at_5b2 : fetchRel p384DecompressCode 0x5B2 = some (.jalr ra ra 0xFFFFFE4E, 4) := by decide
theorem dp_at_5b6 : fetchRel p384DecompressCode 0x5B6 = some (.load .lw (19 : Fin 32) sp 0x18, 2) := by decide
theorem dp_at_5b8 : fetchRel p384DecompressCode 0x5B8 = some (.load .lw (20 : Fin 32) sp 0x14, 2) := by decide
theorem dp_at_5ba : fetchRel p384DecompressCode 0x5BA = some (.load .lw (21 : Fin 32) sp 0x10, 2) := by decide
theorem dp_at_5bc : fetchRel p384DecompressCode 0x5BC = some (.aluImm .add (8 : Fin 32) sp 0x200, 2) := by decide
theorem dp_at_5be : fetchRel p384DecompressCode 0x5BE = some (.lui (9 : Fin 32) 0x3FCC5000, 4) := by decide
theorem dp_at_5c2 : fetchRel p384DecompressCode 0x5C2 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFCF4, 4) := by decide
theorem dp_at_5c6 : fetchRel p384DecompressCode 0x5C6 = some (.aluImm .add a2 x0 0x9C, 4) := by decide
theorem dp_at_5ca : fetchRel p384DecompressCode 0x5CA = some (.alu .add a0 x0 (8 : Fin 32), 2) := by decide
theorem dp_at_5cc : fetchRel p384DecompressCode 0x5CC = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem dp_at_5ce : fetchRel p384DecompressCode 0x5CE = some (.auipc ra 0x11000, 4) := by decide
theorem dp_at_5d2 : fetchRel p384DecompressCode 0x5D2 = some (.jalr ra ra 0xFFFFFE2E, 4) := by decide
theorem dp_at_5d6 : fetchRel p384DecompressCode 0x5D6 = some (.load .lw a0 sp 0x290, 4) := by decide
theorem dp_at_5da : fetchRel p384DecompressCode 0x5DA = some (.alu .sub a3 x0 a0, 4) := by decide
theorem dp_at_5de : fetchRel p384DecompressCode 0x5DE = some (.aluImm .add a0 sp 0x62C, 4) := by decide
theorem dp_at_5e2 : fetchRel p384DecompressCode 0x5E2 = some (.aluImm .add a1 sp 0x1D0, 2) := by decide
theorem dp_at_5e4 : fetchRel p384DecompressCode 0x5E4 = some (.alu .add a2 x0 (8 : Fin 32), 2) := by decide
theorem dp_at_5e6 : fetchRel p384DecompressCode 0x5E6 = some (.auipc ra 0x10000, 4) := by decide
theorem dp_at_5ea : fetchRel p384DecompressCode 0x5EA = some (.jalr ra ra 0xFFFFFF50, 4) := by decide
theorem dp_at_5ee : fetchRel p384DecompressCode 0x5EE = some (.aluImm .add a0 sp 0x65C, 4) := by decide
theorem dp_at_5f2 : fetchRel p384DecompressCode 0x5F2 = some (.aluImm .add a2 x0 0x9C, 4) := by decide
theorem dp_at_5f6 : fetchRel p384DecompressCode 0x5F6 = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem dp_at_5f8 : fetchRel p384DecompressCode 0x5F8 = some (.auipc ra 0x11000, 4) := by decide
theorem dp_at_5fc : fetchRel p384DecompressCode 0x5FC = some (.jalr ra ra 0xFFFFFE04, 4) := by decide
theorem dp_at_600 : fetchRel p384DecompressCode 0x600 = some (.aluImm .add a0 sp 0x62C, 4) := by decide
theorem dp_at_604 : fetchRel p384DecompressCode 0x604 = some (.aluImm .add a1 sp 0x104, 2) := by decide
theorem dp_at_606 : fetchRel p384DecompressCode 0x606 = some (.auipc ra 0x10000, 4) := by decide
theorem dp_at_60a : fetchRel p384DecompressCode 0x60A = some (.jalr ra ra 0xFFFFFF0A, 4) := by decide
theorem dp_at_60e : fetchRel p384DecompressCode 0x60E = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem dp_at_612 : fetchRel p384DecompressCode 0x612 = some (.auipc ra 0xA000, 4) := by decide
theorem dp_at_616 : fetchRel p384DecompressCode 0x616 = some (.jalr ra ra 0xFFFFFCE0, 4) := by decide
theorem dp_at_61a : fetchRel p384DecompressCode 0x61A = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem dp_at_61c : fetchRel p384DecompressCode 0x61C = some (.aluImm .add a0 sp 0x62C, 4) := by decide
theorem dp_at_620 : fetchRel p384DecompressCode 0x620 = some (.aluImm .add a1 sp 0x1D0, 2) := by decide
theorem dp_at_622 : fetchRel p384DecompressCode 0x622 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem dp_at_626 : fetchRel p384DecompressCode 0x626 = some (.auipc ra 0x11000, 4) := by decide
theorem dp_at_62a : fetchRel p384DecompressCode 0x62A = some (.jalr ra ra 0xFFFFFDD6, 4) := by decide
theorem dp_at_62e : fetchRel p384DecompressCode 0x62E = some (.store .sb sp (8 : Fin 32) 0x65C, 4) := by decide
theorem dp_at_632 : fetchRel p384DecompressCode 0x632 = some (.aluImm .add a0 sp 0x2FC, 2) := by decide
theorem dp_at_634 : fetchRel p384DecompressCode 0x634 = some (.aluImm .add a1 sp 0x62C, 4) := by decide
theorem dp_at_638 : fetchRel p384DecompressCode 0x638 = some (.auipc ra 0x10000, 4) := by decide
theorem dp_at_63c : fetchRel p384DecompressCode 0x63C = some (.jalr ra ra 0xFFFFFE96, 4) := by decide
theorem dp_at_640 : fetchRel p384DecompressCode 0x640 = some (.aluImm .add a0 sp 0x29C, 2) := by decide
theorem dp_at_642 : fetchRel p384DecompressCode 0x642 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem dp_at_646 : fetchRel p384DecompressCode 0x646 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem dp_at_648 : fetchRel p384DecompressCode 0x648 = some (.auipc ra 0x11000, 4) := by decide
theorem dp_at_64c : fetchRel p384DecompressCode 0x64C = some (.jalr ra ra 0xFFFFFD4C, 4) := by decide
theorem dp_at_650 : fetchRel p384DecompressCode 0x650 = some (.load .lbu (8 : Fin 32) sp 0x32C, 4) := by decide
theorem dp_at_654 : fetchRel p384DecompressCode 0x654 = some (.aluImm .add a0 sp 0xD4, 2) := by decide
theorem dp_at_656 : fetchRel p384DecompressCode 0x656 = some (.aluImm .add a1 sp 0x29C, 2) := by decide
theorem dp_at_658 : fetchRel p384DecompressCode 0x658 = some (.aluImm .add a2 sp 0x2FC, 2) := by decide
theorem dp_at_65a : fetchRel p384DecompressCode 0x65A = some (.alu .add a3 x0 (8 : Fin 32), 2) := by decide
theorem dp_at_65c : fetchRel p384DecompressCode 0x65C = some (.auipc ra 0x10000, 4) := by decide
theorem dp_at_660 : fetchRel p384DecompressCode 0x660 = some (.jalr ra ra 0xFFFFFD86, 4) := by decide
theorem dp_at_664 : fetchRel p384DecompressCode 0x664 = some (.aluImm .add a0 sp 0x104, 2) := by decide
theorem dp_at_666 : fetchRel p384DecompressCode 0x666 = some (.aluImm .add a1 sp 0xD4, 2) := by decide
theorem dp_at_668 : fetchRel p384DecompressCode 0x668 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem dp_at_66c : fetchRel p384DecompressCode 0x66C = some (.jalr ra ra 0xFFFFFFB0, 4) := by decide
theorem dp_at_670 : fetchRel p384DecompressCode 0x670 = some (.aluImm .add a0 sp 0x62C, 4) := by decide
theorem dp_at_674 : fetchRel p384DecompressCode 0x674 = some (.aluImm .add a1 sp 0xD4, 2) := by decide
theorem dp_at_676 : fetchRel p384DecompressCode 0x676 = some (.auipc ra 0x10000, 4) := by decide
theorem dp_at_67a : fetchRel p384DecompressCode 0x67A = some (.jalr ra ra 0x3CA, 4) := by decide
theorem dp_at_67e : fetchRel p384DecompressCode 0x67E = some (.load .lw a0 sp 0x62C, 4) := by decide
theorem dp_at_682 : fetchRel p384DecompressCode 0x682 = some (.aluImm .and a0 a0 0x1, 2) := by decide
theorem dp_at_684 : fetchRel p384DecompressCode 0x684 = some (.auipc ra 0xA000, 4) := by decide
theorem dp_at_688 : fetchRel p384DecompressCode 0x688 = some (.jalr ra ra 0xFFFFFC6E, 4) := by decide
theorem dp_at_68c : fetchRel p384DecompressCode 0x68C = some (.alu .add a1 x0 (21 : Fin 32), 2) := by decide
theorem dp_at_68e : fetchRel p384DecompressCode 0x68E = some (.auipc ra 0x0, 4) := by decide
theorem dp_at_692 : fetchRel p384DecompressCode 0x692 = some (.jalr ra ra 0x1E6, 4) := by decide
theorem dp_at_696 : fetchRel p384DecompressCode 0x696 = some (.aluImm .add a4 sp 0x65C, 4) := by decide
theorem dp_at_69a : fetchRel p384DecompressCode 0x69A = some (.aluImm .and a3 a0 0xFF, 4) := by decide
theorem dp_at_69e : fetchRel p384DecompressCode 0x69E = some (.aluImm .add a1 sp 0x104, 2) := by decide
theorem dp_at_6a0 : fetchRel p384DecompressCode 0x6A0 = some (.aluImm .add a2 sp 0xD4, 2) := by decide
theorem dp_at_6a2 : fetchRel p384DecompressCode 0x6A2 = some (.alu .add a0 x0 a4, 2) := by decide
theorem dp_at_6a4 : fetchRel p384DecompressCode 0x6A4 = some (.auipc ra 0x10000, 4) := by decide
theorem dp_at_6a8 : fetchRel p384DecompressCode 0x6A8 = some (.jalr ra ra 0xFFFFFD3E, 4) := by decide
theorem dp_at_6ac : fetchRel p384DecompressCode 0x6AC = some (.aluImm .add a0 sp 0x62C, 4) := by decide
theorem dp_at_6b0 : fetchRel p384DecompressCode 0x6B0 = some (.aluImm .add a1 sp 0xA4, 2) := by decide
theorem dp_at_6b2 : fetchRel p384DecompressCode 0x6B2 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem dp_at_6b6 : fetchRel p384DecompressCode 0x6B6 = some (.auipc ra 0x11000, 4) := by decide
theorem dp_at_6ba : fetchRel p384DecompressCode 0x6BA = some (.jalr ra ra 0xFFFFFD46, 4) := by decide
theorem dp_at_6be : fetchRel p384DecompressCode 0x6BE = some (.store .sb sp x0 0x68C, 4) := by decide
theorem dp_at_6c2 : fetchRel p384DecompressCode 0x6C2 = some (.alu .and a0 (8 : Fin 32) (20 : Fin 32), 4) := by decide
theorem dp_at_6c6 : fetchRel p384DecompressCode 0x6C6 = some (.auipc ra 0xA000, 4) := by decide
theorem dp_at_6ca : fetchRel p384DecompressCode 0x6CA = some (.jalr ra ra 0xFFFFFC2C, 4) := by decide
theorem dp_at_6ce : fetchRel p384DecompressCode 0x6CE = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem dp_at_6d0 : fetchRel p384DecompressCode 0x6D0 = some (.aluImm .add a1 sp 0x62C, 4) := by decide
theorem dp_at_6d4 : fetchRel p384DecompressCode 0x6D4 = some (.aluImm .add a2 x0 0x64, 4) := by decide
theorem dp_at_6d8 : fetchRel p384DecompressCode 0x6D8 = some (.alu .add a0 x0 (19 : Fin 32), 2) := by decide
theorem dp_at_6da : fetchRel p384DecompressCode 0x6DA = some (.auipc ra 0x11000, 4) := by decide
theorem dp_at_6de : fetchRel p384DecompressCode 0x6DE = some (.jalr ra ra 0xFFFFFD22, 4) := by decide
theorem dp_at_6e2 : fetchRel p384DecompressCode 0x6E2 = some (.store .sb (19 : Fin 32) (8 : Fin 32) 0x64, 4) := by decide
theorem dp_at_6e6 : fetchRel p384DecompressCode 0x6E6 = some (.aluImm .add sp sp 0x260, 4) := by decide
theorem dp_at_6ea : fetchRel p384DecompressCode 0x6EA = some (.aluImm .add a0 sp 0x780, 4) := by decide
theorem dp_at_6ee : fetchRel p384DecompressCode 0x6EE = some (.load .lw ra a0 0x6C, 4) := by decide
theorem dp_at_6f2 : fetchRel p384DecompressCode 0x6F2 = some (.load .lw (8 : Fin 32) a0 0x68, 2) := by decide
theorem dp_at_6f4 : fetchRel p384DecompressCode 0x6F4 = some (.load .lw (9 : Fin 32) a0 0x64, 2) := by decide
theorem dp_at_6f6 : fetchRel p384DecompressCode 0x6F6 = some (.load .lw (18 : Fin 32) a0 0x60, 4) := by decide
theorem dp_at_6fa : fetchRel p384DecompressCode 0x6FA = some (.load .lw (19 : Fin 32) a0 0x5C, 4) := by decide
theorem dp_at_6fe : fetchRel p384DecompressCode 0x6FE = some (.load .lw (20 : Fin 32) a0 0x58, 4) := by decide
theorem dp_at_702 : fetchRel p384DecompressCode 0x702 = some (.load .lw (21 : Fin 32) a0 0x54, 4) := by decide
theorem dp_at_706 : fetchRel p384DecompressCode 0x706 = some (.load .lw (22 : Fin 32) a0 0x50, 4) := by decide
theorem dp_at_70a : fetchRel p384DecompressCode 0x70A = some (.load .lw (23 : Fin 32) a0 0x4C, 4) := by decide
theorem dp_at_70e : fetchRel p384DecompressCode 0x70E = some (.load .lw (24 : Fin 32) a0 0x48, 4) := by decide
theorem dp_at_712 : fetchRel p384DecompressCode 0x712 = some (.load .lw (25 : Fin 32) a0 0x44, 4) := by decide
theorem dp_at_716 : fetchRel p384DecompressCode 0x716 = some (.load .lw (26 : Fin 32) a0 0x40, 4) := by decide
theorem dp_at_71a : fetchRel p384DecompressCode 0x71A = some (.load .lw (27 : Fin 32) a0 0x3C, 4) := by decide
theorem dp_at_71e : fetchRel p384DecompressCode 0x71E = some (.aluImm .add sp sp 0x7F0, 4) := by decide
theorem dp_at_722 : fetchRel p384DecompressCode 0x722 = some (.jalr x0 ra 0x0, 2) := by decide
theorem dp_at_724 : fetchRel p384DecompressCode 0x724 = some (.aluImm .add a1 x0 0xC, 2) := by decide
theorem dp_at_726 : fetchRel p384DecompressCode 0x726 = some (.load .lw a0 sp 0x38, 2) := by decide
theorem dp_at_728 : fetchRel p384DecompressCode 0x728 = some (.auipc ra 0x9000, 4) := by decide
theorem dp_at_72c : fetchRel p384DecompressCode 0x72C = some (.jalr ra ra 0x72E, 4) := by decide


end C3.RV32.Dq
