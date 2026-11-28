import C3BootProofs.Proofs.P384Mont

/-! Fetch lemmas for `AffinePoint<NistP256>::decompress` (`p256DecompressCode`). -/

namespace C3.RV32.Gd

open C3.Image

/-- Where the P-256 `decompress` is in the image. -/
abbrev GD : Word := BitVec.ofNat 32 p256DecompressAddress

set_option maxRecDepth 20000

theorem gd_at_0 : fetchRel p256DecompressCode 0x0 = some (.aluImm .add sp sp 0xFFFFF8F0, 4) := by decide
theorem gd_at_4 : fetchRel p256DecompressCode 0x4 = some (.aluImm .add a3 sp 0x700, 4) := by decide
theorem gd_at_8 : fetchRel p256DecompressCode 0x8 = some (.store .sw a3 ra 0xC, 4) := by decide
theorem gd_at_c : fetchRel p256DecompressCode 0xC = some (.store .sw a3 (8 : Fin 32) 0x8, 2) := by decide
theorem gd_at_e : fetchRel p256DecompressCode 0xE = some (.store .sw a3 (9 : Fin 32) 0x4, 2) := by decide
theorem gd_at_10 : fetchRel p256DecompressCode 0x10 = some (.store .sw a3 (18 : Fin 32) 0x0, 4) := by decide
theorem gd_at_14 : fetchRel p256DecompressCode 0x14 = some (.aluImm .add a3 sp 0x680, 4) := by decide
theorem gd_at_18 : fetchRel p256DecompressCode 0x18 = some (.store .sw a3 (19 : Fin 32) 0x7C, 4) := by decide
theorem gd_at_1c : fetchRel p256DecompressCode 0x1C = some (.store .sw a3 (20 : Fin 32) 0x78, 4) := by decide
theorem gd_at_20 : fetchRel p256DecompressCode 0x20 = some (.store .sw a3 (21 : Fin 32) 0x74, 4) := by decide
theorem gd_at_24 : fetchRel p256DecompressCode 0x24 = some (.store .sw a3 (22 : Fin 32) 0x70, 4) := by decide
theorem gd_at_28 : fetchRel p256DecompressCode 0x28 = some (.store .sw a3 (23 : Fin 32) 0x6C, 4) := by decide
theorem gd_at_2c : fetchRel p256DecompressCode 0x2C = some (.store .sw a3 (24 : Fin 32) 0x68, 4) := by decide
theorem gd_at_30 : fetchRel p256DecompressCode 0x30 = some (.store .sw a3 (25 : Fin 32) 0x64, 4) := by decide
theorem gd_at_34 : fetchRel p256DecompressCode 0x34 = some (.store .sw a3 (26 : Fin 32) 0x60, 4) := by decide
theorem gd_at_38 : fetchRel p256DecompressCode 0x38 = some (.store .sw a3 (27 : Fin 32) 0x5C, 4) := by decide
theorem gd_at_3c : fetchRel p256DecompressCode 0x3C = some (.alu .add (27 : Fin 32) x0 a2, 2) := by decide
theorem gd_at_3e : fetchRel p256DecompressCode 0x3E = some (.alu .add (25 : Fin 32) x0 a0, 2) := by decide
theorem gd_at_40 : fetchRel p256DecompressCode 0x40 = some (.aluImm .add a0 sp 0x40, 2) := by decide
theorem gd_at_42 : fetchRel p256DecompressCode 0x42 = some (.auipc ra 0x0, 4) := by decide
theorem gd_at_46 : fetchRel p256DecompressCode 0x46 = some (.jalr ra ra 0x7D0, 4) := by decide
theorem gd_at_4a : fetchRel p256DecompressCode 0x4A = some (.aluImm .add a0 sp 0x64, 2) := by decide
theorem gd_at_4c : fetchRel p256DecompressCode 0x4C = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem gd_at_50 : fetchRel p256DecompressCode 0x50 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem gd_at_52 : fetchRel p256DecompressCode 0x52 = some (.auipc ra 0x10000, 4) := by decide
theorem gd_at_56 : fetchRel p256DecompressCode 0x56 = some (.jalr ra ra 0x5C8, 4) := by decide
theorem gd_at_5a : fetchRel p256DecompressCode 0x5A = some (.load .lbu (26 : Fin 32) sp 0x60, 4) := by decide
theorem gd_at_5e : fetchRel p256DecompressCode 0x5E = some (.aluImm .add a0 sp 0x84, 2) := by decide
theorem gd_at_60 : fetchRel p256DecompressCode 0x60 = some (.aluImm .add a1 sp 0x64, 2) := by decide
theorem gd_at_62 : fetchRel p256DecompressCode 0x62 = some (.aluImm .add a2 sp 0x40, 2) := by decide
theorem gd_at_64 : fetchRel p256DecompressCode 0x64 = some (.alu .add a3 x0 (26 : Fin 32), 2) := by decide
theorem gd_at_66 : fetchRel p256DecompressCode 0x66 = some (.auipc ra 0xD000, 4) := by decide
theorem gd_at_6a : fetchRel p256DecompressCode 0x6A = some (.jalr ra ra 0x3DE, 4) := by decide
theorem gd_at_6e : fetchRel p256DecompressCode 0x6E = some (.aluImm .add a0 sp 0x43C, 4) := by decide
theorem gd_at_72 : fetchRel p256DecompressCode 0x72 = some (.aluImm .add a1 sp 0x84, 2) := by decide
theorem gd_at_74 : fetchRel p256DecompressCode 0x74 = some (.aluImm .add a2 sp 0x84, 2) := by decide
theorem gd_at_76 : fetchRel p256DecompressCode 0x76 = some (.aluImm .add (8 : Fin 32) sp 0x43C, 4) := by decide
theorem gd_at_7a : fetchRel p256DecompressCode 0x7A = some (.auipc ra 0xD000, 4) := by decide
theorem gd_at_7e : fetchRel p256DecompressCode 0x7E = some (.jalr ra ra 0x416, 4) := by decide
theorem gd_at_82 : fetchRel p256DecompressCode 0x82 = some (.aluImm .add a0 sp 0x21C, 2) := by decide
theorem gd_at_84 : fetchRel p256DecompressCode 0x84 = some (.aluImm .add a1 sp 0x43C, 4) := by decide
theorem gd_at_88 : fetchRel p256DecompressCode 0x88 = some (.aluImm .add a2 sp 0x84, 2) := by decide
theorem gd_at_8a : fetchRel p256DecompressCode 0x8A = some (.auipc ra 0xD000, 4) := by decide
theorem gd_at_8e : fetchRel p256DecompressCode 0x8E = some (.jalr ra ra 0x406, 4) := by decide
theorem gd_at_92 : fetchRel p256DecompressCode 0x92 = some (.lui a1 0x3FCC4000, 4) := by decide
theorem gd_at_96 : fetchRel p256DecompressCode 0x96 = some (.aluImm .add a1 a1 0x138, 4) := by decide
theorem gd_at_9a : fetchRel p256DecompressCode 0x9A = some (.aluImm .add a0 sp 0x43C, 4) := by decide
theorem gd_at_9e : fetchRel p256DecompressCode 0x9E = some (.aluImm .add a2 sp 0x84, 2) := by decide
theorem gd_at_a0 : fetchRel p256DecompressCode 0xA0 = some (.auipc ra 0xD000, 4) := by decide
theorem gd_at_a4 : fetchRel p256DecompressCode 0xA4 = some (.jalr ra ra 0x3F0, 4) := by decide
theorem gd_at_a8 : fetchRel p256DecompressCode 0xA8 = some (.aluImm .add a0 sp 0x1DC, 2) := by decide
theorem gd_at_aa : fetchRel p256DecompressCode 0xAA = some (.aluImm .add a1 sp 0x21C, 2) := by decide
theorem gd_at_ac : fetchRel p256DecompressCode 0xAC = some (.aluImm .add a2 sp 0x43C, 4) := by decide
theorem gd_at_b0 : fetchRel p256DecompressCode 0xB0 = some (.auipc ra 0xE000, 4) := by decide
theorem gd_at_b4 : fetchRel p256DecompressCode 0xB4 = some (.jalr ra ra 0xFFFFFBA6, 4) := by decide
theorem gd_at_b8 : fetchRel p256DecompressCode 0xB8 = some (.lui a2 0x3FCC4000, 4) := by decide
theorem gd_at_bc : fetchRel p256DecompressCode 0xBC = some (.aluImm .add a2 a2 0x1D8, 4) := by decide
theorem gd_at_c0 : fetchRel p256DecompressCode 0xC0 = some (.aluImm .add a0 sp 0xC4, 2) := by decide
theorem gd_at_c2 : fetchRel p256DecompressCode 0xC2 = some (.aluImm .add a1 sp 0x1DC, 2) := by decide
theorem gd_at_c4 : fetchRel p256DecompressCode 0xC4 = some (.auipc ra 0xE000, 4) := by decide
theorem gd_at_c8 : fetchRel p256DecompressCode 0xC8 = some (.jalr ra ra 0xFFFFFB92, 4) := by decide
theorem gd_at_cc : fetchRel p256DecompressCode 0xCC = some (.aluImm .add a0 sp 0xE4, 2) := by decide
theorem gd_at_ce : fetchRel p256DecompressCode 0xCE = some (.lui (24 : Fin 32) 0x3FCC5000, 4) := by decide
theorem gd_at_d2 : fetchRel p256DecompressCode 0xD2 = some (.aluImm .add (24 : Fin 32) (24 : Fin 32) 0xFFFFFBA0, 4) := by decide
theorem gd_at_d6 : fetchRel p256DecompressCode 0xD6 = some (.aluImm .add a2 x0 0x6C, 4) := by decide
theorem gd_at_da : fetchRel p256DecompressCode 0xDA = some (.alu .add a1 x0 (24 : Fin 32), 2) := by decide
theorem gd_at_dc : fetchRel p256DecompressCode 0xDC = some (.auipc ra 0x10000, 4) := by decide
theorem gd_at_e0 : fetchRel p256DecompressCode 0xE0 = some (.jalr ra ra 0x5A6, 4) := by decide
theorem gd_at_e4 : fetchRel p256DecompressCode 0xE4 = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem gd_at_e6 : fetchRel p256DecompressCode 0xE6 = some (.lui a1 0x40000000, 4) := by decide
theorem gd_at_ea : fetchRel p256DecompressCode 0xEA = some (.aluImm .add a2 x0 0x10, 2) := by decide
theorem gd_at_ec : fetchRel p256DecompressCode 0xEC = some (.aluImm .add a1 a1 0xFFFFFFFF, 2) := by decide
theorem gd_at_ee : fetchRel p256DecompressCode 0xEE = some (.branch .beq a2 x0 0x34, 2) := by decide
theorem gd_at_f0 : fetchRel p256DecompressCode 0xF0 = some (.alu .sub a3 x0 a2, 4) := by decide
theorem gd_at_f4 : fetchRel p256DecompressCode 0xF4 = some (.alu .srl a3 a1 a3, 4) := by decide
theorem gd_at_f8 : fetchRel p256DecompressCode 0xF8 = some (.store .sw sp a3 0x43C, 4) := by decide
theorem gd_at_fc : fetchRel p256DecompressCode 0xFC = some (.load .lw a3 sp 0x43C, 4) := by decide
theorem gd_at_100 : fetchRel p256DecompressCode 0x100 = some (.aluImm .sltu a3 a3 0x1, 4) := by decide
theorem gd_at_104 : fetchRel p256DecompressCode 0x104 = some (.store .sb sp a3 0x43C, 4) := by decide
theorem gd_at_108 : fetchRel p256DecompressCode 0x108 = some (.load .lbu a3 sp 0x43C, 4) := by decide
theorem gd_at_10c : fetchRel p256DecompressCode 0x10C = some (.alu .sll a4 a1 a2, 4) := by decide
theorem gd_at_110 : fetchRel p256DecompressCode 0x110 = some (.alu .xor a4 a4 a1, 2) := by decide
theorem gd_at_112 : fetchRel p256DecompressCode 0x112 = some (.alu .sub a3 x0 a3, 4) := by decide
theorem gd_at_116 : fetchRel p256DecompressCode 0x116 = some (.alu .and a4 a4 a3, 2) := by decide
theorem gd_at_118 : fetchRel p256DecompressCode 0x118 = some (.alu .and a3 a3 a2, 2) := by decide
theorem gd_at_11a : fetchRel p256DecompressCode 0x11A = some (.alu .xor a1 a1 a4, 2) := by decide
theorem gd_at_11c : fetchRel p256DecompressCode 0x11C = some (.alu .add a0 a0 a3, 2) := by decide
theorem gd_at_11e : fetchRel p256DecompressCode 0x11E = some (.aluImm .srl a2 a2 0x1, 2) := by decide
theorem gd_at_120 : fetchRel p256DecompressCode 0x120 = some (.branch .bne a2 x0 0xFFFFFFD0, 2) := by decide
theorem gd_at_122 : fetchRel p256DecompressCode 0x122 = some (.store .sw sp a1 0x43C, 4) := by decide
theorem gd_at_126 : fetchRel p256DecompressCode 0x126 = some (.aluImm .add a1 sp 0x43C, 4) := by decide
theorem gd_at_12a : fetchRel p256DecompressCode 0x12A = some (.load .lw a1 sp 0x43C, 4) := by decide
theorem gd_at_12e : fetchRel p256DecompressCode 0x12E = some (.aluImm .sltu a1 a1 0x1, 4) := by decide
theorem gd_at_132 : fetchRel p256DecompressCode 0x132 = some (.store .sb sp a1 0x43C, 4) := by decide
theorem gd_at_136 : fetchRel p256DecompressCode 0x136 = some (.aluImm .add a1 sp 0x43C, 4) := by decide
theorem gd_at_13a : fetchRel p256DecompressCode 0x13A = some (.load .lbu a1 sp 0x43C, 4) := by decide
theorem gd_at_13e : fetchRel p256DecompressCode 0x13E = some (.aluImm .and a1 a1 0x1, 2) := by decide
theorem gd_at_140 : fetchRel p256DecompressCode 0x140 = some (.alu .add (8 : Fin 32) a0 a1, 4) := by decide
theorem gd_at_144 : fetchRel p256DecompressCode 0x144 = some (.aluImm .add (9 : Fin 32) x0 0x100, 4) := by decide
theorem gd_at_148 : fetchRel p256DecompressCode 0x148 = some (.alu .sub (18 : Fin 32) (9 : Fin 32) (8 : Fin 32), 4) := by decide
theorem gd_at_14c : fetchRel p256DecompressCode 0x14C = some (.aluImm .add a0 sp 0x1DC, 2) := by decide
theorem gd_at_14e : fetchRel p256DecompressCode 0x14E = some (.aluImm .add a1 sp 0xC4, 2) := by decide
theorem gd_at_150 : fetchRel p256DecompressCode 0x150 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem gd_at_154 : fetchRel p256DecompressCode 0x154 = some (.auipc ra 0x10000, 4) := by decide
theorem gd_at_158 : fetchRel p256DecompressCode 0x158 = some (.jalr ra ra 0x52E, 4) := by decide
theorem gd_at_15c : fetchRel p256DecompressCode 0x15C = some (.aluImm .add a0 sp 0x1FC, 2) := by decide
theorem gd_at_15e : fetchRel p256DecompressCode 0x15E = some (.lui (22 : Fin 32) 0x3FCC5000, 4) := by decide
theorem gd_at_162 : fetchRel p256DecompressCode 0x162 = some (.aluImm .add (22 : Fin 32) (22 : Fin 32) 0xFFFFFC34, 4) := by decide
theorem gd_at_166 : fetchRel p256DecompressCode 0x166 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem gd_at_16a : fetchRel p256DecompressCode 0x16A = some (.alu .add a1 x0 (22 : Fin 32), 2) := by decide
theorem gd_at_16c : fetchRel p256DecompressCode 0x16C = some (.auipc ra 0x10000, 4) := by decide
theorem gd_at_170 : fetchRel p256DecompressCode 0x170 = some (.jalr ra ra 0x516, 4) := by decide
theorem gd_at_174 : fetchRel p256DecompressCode 0x174 = some (.branch .bltu (18 : Fin 32) (9 : Fin 32) 0x8, 4) := by decide
theorem gd_at_178 : fetchRel p256DecompressCode 0x178 = some (.aluImm .add (18 : Fin 32) x0 0x100, 4) := by decide
theorem gd_at_17c : fetchRel p256DecompressCode 0x17C = some (.aluImm .add a0 (8 : Fin 32) 0xFFFFFF00, 4) := by decide
theorem gd_at_180 : fetchRel p256DecompressCode 0x180 = some (.branch .bne a0 x0 0x16, 2) := by decide
theorem gd_at_182 : fetchRel p256DecompressCode 0x182 = some (.aluImm .add a1 (24 : Fin 32) 0x20, 4) := by decide
theorem gd_at_186 : fetchRel p256DecompressCode 0x186 = some (.aluImm .add a0 sp 0x150, 2) := by decide
theorem gd_at_188 : fetchRel p256DecompressCode 0x188 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem gd_at_18c : fetchRel p256DecompressCode 0x18C = some (.auipc ra 0x10000, 4) := by decide
theorem gd_at_190 : fetchRel p256DecompressCode 0x190 = some (.jalr ra ra 0x4F6, 4) := by decide
theorem gd_at_194 : fetchRel p256DecompressCode 0x194 = some (.jal x0 0x3BA, 2) := by decide
theorem gd_at_196 : fetchRel p256DecompressCode 0x196 = some (.aluImm .add (8 : Fin 32) sp 0x21C, 2) := by decide
theorem gd_at_198 : fetchRel p256DecompressCode 0x198 = some (.aluImm .add (9 : Fin 32) x0 0x10, 2) := by decide
theorem gd_at_19a : fetchRel p256DecompressCode 0x19A = some (.branch .beq (9 : Fin 32) x0 0x1A, 2) := by decide
theorem gd_at_19c : fetchRel p256DecompressCode 0x19C = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem gd_at_1a0 : fetchRel p256DecompressCode 0x1A0 = some (.alu .add a0 x0 (8 : Fin 32), 2) := by decide
theorem gd_at_1a2 : fetchRel p256DecompressCode 0x1A2 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem gd_at_1a4 : fetchRel p256DecompressCode 0x1A4 = some (.auipc ra 0x10000, 4) := by decide
theorem gd_at_1a8 : fetchRel p256DecompressCode 0x1A8 = some (.jalr ra ra 0x476, 4) := by decide
theorem gd_at_1ac : fetchRel p256DecompressCode 0x1AC = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x20, 4) := by decide
theorem gd_at_1b0 : fetchRel p256DecompressCode 0x1B0 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem gd_at_1b2 : fetchRel p256DecompressCode 0x1B2 = some (.branch .bne (9 : Fin 32) x0 0xFFFFFFEA, 2) := by decide
theorem gd_at_1b4 : fetchRel p256DecompressCode 0x1B4 = some (.aluImm .add a0 sp 0x43C, 4) := by decide
theorem gd_at_1b8 : fetchRel p256DecompressCode 0x1B8 = some (.aluImm .add a1 sp 0x21C, 2) := by decide
theorem gd_at_1ba : fetchRel p256DecompressCode 0x1BA = some (.aluImm .add a2 x0 0x200, 4) := by decide
theorem gd_at_1be : fetchRel p256DecompressCode 0x1BE = some (.aluImm .add (9 : Fin 32) sp 0x43C, 4) := by decide
theorem gd_at_1c2 : fetchRel p256DecompressCode 0x1C2 = some (.auipc ra 0x10000, 4) := by decide
theorem gd_at_1c6 : fetchRel p256DecompressCode 0x1C6 = some (.jalr ra ra 0x4C0, 4) := by decide
theorem gd_at_1ca : fetchRel p256DecompressCode 0x1CA = some (.aluImm .add a0 sp 0x63C, 4) := by decide
theorem gd_at_1ce : fetchRel p256DecompressCode 0x1CE = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem gd_at_1d2 : fetchRel p256DecompressCode 0x1D2 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem gd_at_1d4 : fetchRel p256DecompressCode 0x1D4 = some (.auipc ra 0x10000, 4) := by decide
theorem gd_at_1d8 : fetchRel p256DecompressCode 0x1D8 = some (.jalr ra ra 0x446, 4) := by decide
theorem gd_at_1dc : fetchRel p256DecompressCode 0x1DC = some (.aluImm .add a0 sp 0x21C, 2) := by decide
theorem gd_at_1de : fetchRel p256DecompressCode 0x1DE = some (.aluImm .add a1 sp 0x43C, 4) := by decide
theorem gd_at_1e2 : fetchRel p256DecompressCode 0x1E2 = some (.aluImm .add a2 x0 0x220, 4) := by decide
theorem gd_at_1e6 : fetchRel p256DecompressCode 0x1E6 = some (.auipc ra 0x10000, 4) := by decide
theorem gd_at_1ea : fetchRel p256DecompressCode 0x1EA = some (.jalr ra ra 0x49C, 4) := by decide
theorem gd_at_1ee : fetchRel p256DecompressCode 0x1EE = some (.aluImm .add (19 : Fin 32) sp 0x45C, 4) := by decide
theorem gd_at_1f2 : fetchRel p256DecompressCode 0x1F2 = some (.aluImm .add (8 : Fin 32) x0 0x10, 2) := by decide
theorem gd_at_1f4 : fetchRel p256DecompressCode 0x1F4 = some (.aluImm .add (24 : Fin 32) (24 : Fin 32) 0x20, 4) := by decide
theorem gd_at_1f8 : fetchRel p256DecompressCode 0x1F8 = some (.branch .beq (8 : Fin 32) x0 0x1A, 2) := by decide
theorem gd_at_1fa : fetchRel p256DecompressCode 0x1FA = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem gd_at_1fe : fetchRel p256DecompressCode 0x1FE = some (.alu .add a0 x0 (9 : Fin 32), 2) := by decide
theorem gd_at_200 : fetchRel p256DecompressCode 0x200 = some (.alu .add a1 x0 (24 : Fin 32), 2) := by decide
theorem gd_at_202 : fetchRel p256DecompressCode 0x202 = some (.auipc ra 0x10000, 4) := by decide
theorem gd_at_206 : fetchRel p256DecompressCode 0x206 = some (.jalr ra ra 0x480, 4) := by decide
theorem gd_at_20a : fetchRel p256DecompressCode 0x20A = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x20, 4) := by decide
theorem gd_at_20e : fetchRel p256DecompressCode 0x20E = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem gd_at_210 : fetchRel p256DecompressCode 0x210 = some (.branch .bne (8 : Fin 32) x0 0xFFFFFFEA, 2) := by decide
theorem gd_at_212 : fetchRel p256DecompressCode 0x212 = some (.aluImm .add a1 sp 0xC4, 2) := by decide
theorem gd_at_214 : fetchRel p256DecompressCode 0x214 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem gd_at_218 : fetchRel p256DecompressCode 0x218 = some (.alu .add a0 x0 (19 : Fin 32), 2) := by decide
theorem gd_at_21a : fetchRel p256DecompressCode 0x21A = some (.auipc ra 0x10000, 4) := by decide
theorem gd_at_21e : fetchRel p256DecompressCode 0x21E = some (.jalr ra ra 0x468, 4) := by decide
theorem gd_at_222 : fetchRel p256DecompressCode 0x222 = some (.aluImm .add (8 : Fin 32) x0 0xE, 2) := by decide
theorem gd_at_224 : fetchRel p256DecompressCode 0x224 = some (.branch .beq (8 : Fin 32) x0 0x32, 2) := by decide
theorem gd_at_226 : fetchRel p256DecompressCode 0x226 = some (.aluImm .add (9 : Fin 32) (19 : Fin 32) 0x20, 4) := by decide
theorem gd_at_22a : fetchRel p256DecompressCode 0x22A = some (.aluImm .add a0 sp 0x6BC, 4) := by decide
theorem gd_at_22e : fetchRel p256DecompressCode 0x22E = some (.aluImm .add a2 sp 0x1DC, 2) := by decide
theorem gd_at_230 : fetchRel p256DecompressCode 0x230 = some (.aluImm .add a4 x0 0x1, 2) := by decide
theorem gd_at_232 : fetchRel p256DecompressCode 0x232 = some (.alu .add a1 x0 (19 : Fin 32), 2) := by decide
theorem gd_at_234 : fetchRel p256DecompressCode 0x234 = some (.aluImm .add a3 sp 0xE4, 2) := by decide
theorem gd_at_236 : fetchRel p256DecompressCode 0x236 = some (.auipc ra 0xC000, 4) := by decide
theorem gd_at_23a : fetchRel p256DecompressCode 0x23A = some (.jalr ra ra 0x73C, 4) := by decide
theorem gd_at_23e : fetchRel p256DecompressCode 0x23E = some (.aluImm .add a1 sp 0x6BC, 4) := by decide
theorem gd_at_242 : fetchRel p256DecompressCode 0x242 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem gd_at_246 : fetchRel p256DecompressCode 0x246 = some (.alu .add a0 x0 (9 : Fin 32), 2) := by decide
theorem gd_at_248 : fetchRel p256DecompressCode 0x248 = some (.auipc ra 0x10000, 4) := by decide
theorem gd_at_24c : fetchRel p256DecompressCode 0x24C = some (.jalr ra ra 0x43A, 4) := by decide
theorem gd_at_250 : fetchRel p256DecompressCode 0x250 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem gd_at_252 : fetchRel p256DecompressCode 0x252 = some (.alu .add (19 : Fin 32) x0 (9 : Fin 32), 2) := by decide
theorem gd_at_254 : fetchRel p256DecompressCode 0x254 = some (.branch .bne (8 : Fin 32) x0 0xFFFFFFD2, 2) := by decide
theorem gd_at_256 : fetchRel p256DecompressCode 0x256 = some (.store .sw sp (27 : Fin 32) 0x10, 2) := by decide
theorem gd_at_258 : fetchRel p256DecompressCode 0x258 = some (.store .sw sp (26 : Fin 32) 0x14, 2) := by decide
theorem gd_at_25a : fetchRel p256DecompressCode 0x25A = some (.store .sw sp (25 : Fin 32) 0x18, 2) := by decide
theorem gd_at_25c : fetchRel p256DecompressCode 0x25C = some (.aluImm .add a0 sp 0x21C, 2) := by decide
theorem gd_at_25e : fetchRel p256DecompressCode 0x25E = some (.aluImm .add a1 sp 0x43C, 4) := by decide
theorem gd_at_262 : fetchRel p256DecompressCode 0x262 = some (.aluImm .add a2 x0 0x200, 4) := by decide
theorem gd_at_266 : fetchRel p256DecompressCode 0x266 = some (.auipc ra 0x10000, 4) := by decide
theorem gd_at_26a : fetchRel p256DecompressCode 0x26A = some (.jalr ra ra 0x41C, 4) := by decide
theorem gd_at_26e : fetchRel p256DecompressCode 0x26E = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem gd_at_272 : fetchRel p256DecompressCode 0x272 = some (.aluImm .add a0 sp 0x41C, 4) := by decide
theorem gd_at_276 : fetchRel p256DecompressCode 0x276 = some (.alu .add a1 x0 (22 : Fin 32), 2) := by decide
theorem gd_at_278 : fetchRel p256DecompressCode 0x278 = some (.auipc ra 0x10000, 4) := by decide
theorem gd_at_27c : fetchRel p256DecompressCode 0x27C = some (.jalr ra ra 0x40A, 4) := by decide
theorem gd_at_280 : fetchRel p256DecompressCode 0x280 = some (.aluImm .add (18 : Fin 32) (18 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem gd_at_282 : fetchRel p256DecompressCode 0x282 = some (.aluImm .srl (9 : Fin 32) (18 : Fin 32) 0x5, 4) := by decide
theorem gd_at_286 : fetchRel p256DecompressCode 0x286 = some (.aluImm .and a0 (18 : Fin 32) 0x3, 4) := by decide
theorem gd_at_28a : fetchRel p256DecompressCode 0x28A = some (.aluImm .add a1 x0 0x2, 2) := by decide
theorem gd_at_28c : fetchRel p256DecompressCode 0x28C = some (.aluImm .sll (18 : Fin 32) (18 : Fin 32) 0x1B, 2) := by decide
theorem gd_at_28e : fetchRel p256DecompressCode 0x28E = some (.alu .sll a0 a1 a0, 4) := by decide
theorem gd_at_292 : fetchRel p256DecompressCode 0x292 = some (.aluImm .srl (8 : Fin 32) (18 : Fin 32) 0x1D, 4) := by decide
theorem gd_at_296 : fetchRel p256DecompressCode 0x296 = some (.aluImm .add (18 : Fin 32) a0 0xFFFFFFFF, 4) := by decide
theorem gd_at_29a : fetchRel p256DecompressCode 0x29A = some (.aluImm .add a0 sp 0x65C, 4) := by decide
theorem gd_at_29e : fetchRel p256DecompressCode 0x29E = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem gd_at_2a2 : fetchRel p256DecompressCode 0x2A2 = some (.alu .add a1 x0 (24 : Fin 32), 2) := by decide
theorem gd_at_2a4 : fetchRel p256DecompressCode 0x2A4 = some (.auipc ra 0x10000, 4) := by decide
theorem gd_at_2a8 : fetchRel p256DecompressCode 0x2A8 = some (.jalr ra ra 0x3DE, 4) := by decide
theorem gd_at_2ac : fetchRel p256DecompressCode 0x2AC = some (.store .sw sp (9 : Fin 32) 0x34, 2) := by decide
theorem gd_at_2ae : fetchRel p256DecompressCode 0x2AE = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x1, 2) := by decide
theorem gd_at_2b0 : fetchRel p256DecompressCode 0x2B0 = some (.store .sw sp (8 : Fin 32) 0x30, 2) := by decide
theorem gd_at_2b2 : fetchRel p256DecompressCode 0x2B2 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x1, 2) := by decide
theorem gd_at_2b4 : fetchRel p256DecompressCode 0x2B4 = some (.store .sw sp (8 : Fin 32) 0x1C, 2) := by decide
theorem gd_at_2b6 : fetchRel p256DecompressCode 0x2B6 = some (.aluImm .and a0 (18 : Fin 32) 0xF, 4) := by decide
theorem gd_at_2ba : fetchRel p256DecompressCode 0x2BA = some (.store .sw sp a0 0x24, 2) := by decide
theorem gd_at_2bc : fetchRel p256DecompressCode 0x2BC = some (.aluImm .add (19 : Fin 32) sp 0x6A0, 4) := by decide
theorem gd_at_2c0 : fetchRel p256DecompressCode 0x2C0 = some (.aluImm .add (25 : Fin 32) sp 0x680, 4) := by decide
theorem gd_at_2c4 : fetchRel p256DecompressCode 0x2C4 = some (.aluImm .add (21 : Fin 32) sp 0xE8, 4) := by decide
theorem gd_at_2c8 : fetchRel p256DecompressCode 0x2C8 = some (.aluImm .add (18 : Fin 32) sp 0x69C, 4) := by decide
theorem gd_at_2cc : fetchRel p256DecompressCode 0x2CC = some (.aluImm .add (27 : Fin 32) x0 0x8, 2) := by decide
theorem gd_at_2ce : fetchRel p256DecompressCode 0x2CE = some (.aluImm .add (22 : Fin 32) x0 0xFFFFFFFF, 2) := by decide
theorem gd_at_2d0 : fetchRel p256DecompressCode 0x2D0 = some (.branch .beq (9 : Fin 32) x0 0x266, 4) := by decide
theorem gd_at_2d4 : fetchRel p256DecompressCode 0x2D4 = some (.store .sw sp (9 : Fin 32) 0x2C, 2) := by decide
theorem gd_at_2d6 : fetchRel p256DecompressCode 0x2D6 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem gd_at_2d8 : fetchRel p256DecompressCode 0x2D8 = some (.load .lw a3 sp 0x1C, 2) := by decide
theorem gd_at_2da : fetchRel p256DecompressCode 0x2DA = some (.load .lw a0 sp 0x34, 2) := by decide
theorem gd_at_2dc : fetchRel p256DecompressCode 0x2DC = some (.store .sw sp (9 : Fin 32) 0x38, 2) := by decide
theorem gd_at_2de : fetchRel p256DecompressCode 0x2DE = some (.branch .beq (9 : Fin 32) a0 0x6, 4) := by decide
theorem gd_at_2e2 : fetchRel p256DecompressCode 0x2E2 = some (.aluImm .add a3 x0 0x8, 2) := by decide
theorem gd_at_2e4 : fetchRel p256DecompressCode 0x2E4 = some (.load .lw a0 sp 0x38, 2) := by decide
theorem gd_at_2e6 : fetchRel p256DecompressCode 0x2E6 = some (.aluImm .sll a0 a0 0x2, 2) := by decide
theorem gd_at_2e8 : fetchRel p256DecompressCode 0x2E8 = some (.aluImm .add a1 sp 0x41C, 4) := by decide
theorem gd_at_2ec : fetchRel p256DecompressCode 0x2EC = some (.alu .add a0 a0 a1, 2) := by decide
theorem gd_at_2ee : fetchRel p256DecompressCode 0x2EE = some (.store .sw sp a0 0x28, 2) := by decide
theorem gd_at_2f0 : fetchRel p256DecompressCode 0x2F0 = some (.branch .beq a3 x0 0x240, 4) := by decide
theorem gd_at_2f4 : fetchRel p256DecompressCode 0x2F4 = some (.aluImm .add a3 a3 0xFFFFFFFF, 2) := by decide
theorem gd_at_2f6 : fetchRel p256DecompressCode 0x2F6 = some (.load .lw a0 sp 0x34, 2) := by decide
theorem gd_at_2f8 : fetchRel p256DecompressCode 0x2F8 = some (.load .lw a1 sp 0x38, 2) := by decide
theorem gd_at_2fa : fetchRel p256DecompressCode 0x2FA = some (.branch .bne a1 a0 0xA, 4) := by decide
theorem gd_at_2fe : fetchRel p256DecompressCode 0x2FE = some (.load .lw a0 sp 0x30, 2) := by decide
theorem gd_at_300 : fetchRel p256DecompressCode 0x300 = some (.branch .beq a3 a0 0x1D0, 4) := by decide
theorem gd_at_304 : fetchRel p256DecompressCode 0x304 = some (.store .sw sp a3 0x20, 2) := by decide
theorem gd_at_306 : fetchRel p256DecompressCode 0x306 = some (.aluImm .add a0 sp 0x67C, 4) := by decide
theorem gd_at_30a : fetchRel p256DecompressCode 0x30A = some (.aluImm .add a1 sp 0x65C, 4) := by decide
theorem gd_at_30e : fetchRel p256DecompressCode 0x30E = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem gd_at_312 : fetchRel p256DecompressCode 0x312 = some (.auipc ra 0x10000, 4) := by decide
theorem gd_at_316 : fetchRel p256DecompressCode 0x316 = some (.jalr ra ra 0x370, 4) := by decide
theorem gd_at_31a : fetchRel p256DecompressCode 0x31A = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem gd_at_31c : fetchRel p256DecompressCode 0x31C = some (.aluImm .add a0 x0 0x4, 2) := by decide
theorem gd_at_31e : fetchRel p256DecompressCode 0x31E = some (.branch .beq a1 a0 0x19C, 4) := by decide
theorem gd_at_322 : fetchRel p256DecompressCode 0x322 = some (.store .sw sp a1 0x3C, 2) := by decide
theorem gd_at_324 : fetchRel p256DecompressCode 0x324 = some (.aluImm .add a0 sp 0x69C, 4) := by decide
theorem gd_at_328 : fetchRel p256DecompressCode 0x328 = some (.aluImm .add a1 sp 0x67C, 4) := by decide
theorem gd_at_32c : fetchRel p256DecompressCode 0x32C = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem gd_at_330 : fetchRel p256DecompressCode 0x330 = some (.auipc ra 0x10000, 4) := by decide
theorem gd_at_334 : fetchRel p256DecompressCode 0x334 = some (.jalr ra ra 0x352, 4) := by decide
theorem gd_at_338 : fetchRel p256DecompressCode 0x338 = some (.aluImm .add a0 sp 0x67C, 4) := by decide
theorem gd_at_33c : fetchRel p256DecompressCode 0x33C = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem gd_at_340 : fetchRel p256DecompressCode 0x340 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem gd_at_342 : fetchRel p256DecompressCode 0x342 = some (.auipc ra 0x10000, 4) := by decide
theorem gd_at_346 : fetchRel p256DecompressCode 0x346 = some (.jalr ra ra 0x2D8, 4) := by decide
theorem gd_at_34a : fetchRel p256DecompressCode 0x34A = some (.aluImm .add (20 : Fin 32) x0 0x0, 2) := by decide
theorem gd_at_34c : fetchRel p256DecompressCode 0x34C = some (.aluImm .add (17 : Fin 32) x0 0x0, 2) := by decide
theorem gd_at_34e : fetchRel p256DecompressCode 0x34E = some (.load .lw a6 sp 0x69C, 4) := by decide
theorem gd_at_352 : fetchRel p256DecompressCode 0x352 = some (.aluImm .add (5 : Fin 32) x0 0x0, 2) := by decide
theorem gd_at_354 : fetchRel p256DecompressCode 0x354 = some (.branch .beq (27 : Fin 32) x0 0xB0, 4) := by decide
theorem gd_at_358 : fetchRel p256DecompressCode 0x358 = some (.aluImm .sll a0 (5 : Fin 32) 0x2, 4) := by decide
theorem gd_at_35c : fetchRel p256DecompressCode 0x35C = some (.alu .add a0 a0 (18 : Fin 32), 2) := by decide
theorem gd_at_35e : fetchRel p256DecompressCode 0x35E = some (.load .lw (6 : Fin 32) a0 0x0, 4) := by decide
theorem gd_at_362 : fetchRel p256DecompressCode 0x362 = some (.alu .mul a0 a6 (6 : Fin 32), 4) := by decide
theorem gd_at_366 : fetchRel p256DecompressCode 0x366 = some (.load .lw a4 sp 0x67C, 4) := by decide
theorem gd_at_36a : fetchRel p256DecompressCode 0x36A = some (.alu .mulhu a1 a6 (6 : Fin 32), 4) := by decide
theorem gd_at_36e : fetchRel p256DecompressCode 0x36E = some (.alu .add (7 : Fin 32) a0 a4, 4) := by decide
theorem gd_at_372 : fetchRel p256DecompressCode 0x372 = some (.alu .mulhu a2 (7 : Fin 32) (22 : Fin 32), 4) := by decide
theorem gd_at_376 : fetchRel p256DecompressCode 0x376 = some (.alu .sltu a0 (7 : Fin 32) a0, 4) := by decide
theorem gd_at_37a : fetchRel p256DecompressCode 0x37A = some (.alu .add a0 a0 a1, 2) := by decide
theorem gd_at_37c : fetchRel p256DecompressCode 0x37C = some (.alu .sltu (9 : Fin 32) x0 (7 : Fin 32), 4) := by decide
theorem gd_at_380 : fetchRel p256DecompressCode 0x380 = some (.alu .add a0 a0 a2, 2) := by decide
theorem gd_at_382 : fetchRel p256DecompressCode 0x382 = some (.aluImm .add (29 : Fin 32) x0 0x7, 2) := by decide
theorem gd_at_384 : fetchRel p256DecompressCode 0x384 = some (.alu .add (9 : Fin 32) (9 : Fin 32) a0, 2) := by decide
theorem gd_at_386 : fetchRel p256DecompressCode 0x386 = some (.alu .sltu a1 a0 a2, 4) := by decide
theorem gd_at_38a : fetchRel p256DecompressCode 0x38A = some (.alu .sltu a0 (9 : Fin 32) a0, 4) := by decide
theorem gd_at_38e : fetchRel p256DecompressCode 0x38E = some (.alu .add (30 : Fin 32) x0 (21 : Fin 32), 2) := by decide
theorem gd_at_390 : fetchRel p256DecompressCode 0x390 = some (.alu .add (28 : Fin 32) a1 a0, 4) := by decide
theorem gd_at_394 : fetchRel p256DecompressCode 0x394 = some (.alu .add a0 x0 (25 : Fin 32), 2) := by decide
theorem gd_at_396 : fetchRel p256DecompressCode 0x396 = some (.alu .add a2 x0 (19 : Fin 32), 2) := by decide
theorem gd_at_398 : fetchRel p256DecompressCode 0x398 = some (.branch .beq (29 : Fin 32) x0 0x52, 4) := by decide
theorem gd_at_39c : fetchRel p256DecompressCode 0x39C = some (.load .lw a3 (30 : Fin 32) 0x0, 4) := by decide
theorem gd_at_3a0 : fetchRel p256DecompressCode 0x3A0 = some (.load .lw a4 a2 0x0, 2) := by decide
theorem gd_at_3a2 : fetchRel p256DecompressCode 0x3A2 = some (.alu .mulhu a1 (7 : Fin 32) a3, 4) := by decide
theorem gd_at_3a6 : fetchRel p256DecompressCode 0x3A6 = some (.alu .mul a5 a4 (6 : Fin 32), 4) := by decide
theorem gd_at_3aa : fetchRel p256DecompressCode 0x3AA = some (.alu .mul a3 (7 : Fin 32) a3, 4) := by decide
theorem gd_at_3ae : fetchRel p256DecompressCode 0x3AE = some (.load .lw (8 : Fin 32) a0 0x0, 2) := by decide
theorem gd_at_3b0 : fetchRel p256DecompressCode 0x3B0 = some (.alu .mulhu a4 a4 (6 : Fin 32), 4) := by decide
theorem gd_at_3b4 : fetchRel p256DecompressCode 0x3B4 = some (.alu .add a1 a1 (28 : Fin 32), 2) := by decide
theorem gd_at_3b6 : fetchRel p256DecompressCode 0x3B6 = some (.aluImm .add a2 a2 0x4, 2) := by decide
theorem gd_at_3b8 : fetchRel p256DecompressCode 0x3B8 = some (.alu .add (8 : Fin 32) (8 : Fin 32) a5, 2) := by decide
theorem gd_at_3ba : fetchRel p256DecompressCode 0x3BA = some (.alu .add (9 : Fin 32) (9 : Fin 32) a3, 2) := by decide
theorem gd_at_3bc : fetchRel p256DecompressCode 0x3BC = some (.alu .sltu a5 (8 : Fin 32) a5, 4) := by decide
theorem gd_at_3c0 : fetchRel p256DecompressCode 0x3C0 = some (.alu .sltu a3 (9 : Fin 32) a3, 4) := by decide
theorem gd_at_3c4 : fetchRel p256DecompressCode 0x3C4 = some (.alu .add (8 : Fin 32) (8 : Fin 32) (9 : Fin 32), 2) := by decide
theorem gd_at_3c6 : fetchRel p256DecompressCode 0x3C6 = some (.alu .add a4 a4 a5, 2) := by decide
theorem gd_at_3c8 : fetchRel p256DecompressCode 0x3C8 = some (.alu .add a1 a1 a3, 2) := by decide
theorem gd_at_3ca : fetchRel p256DecompressCode 0x3CA = some (.alu .sltu (9 : Fin 32) (8 : Fin 32) (9 : Fin 32), 4) := by decide
theorem gd_at_3ce : fetchRel p256DecompressCode 0x3CE = some (.alu .add a4 a4 a1, 2) := by decide
theorem gd_at_3d0 : fetchRel p256DecompressCode 0x3D0 = some (.store .sw a0 (8 : Fin 32) 0xFFFFFFFC, 4) := by decide
theorem gd_at_3d4 : fetchRel p256DecompressCode 0x3D4 = some (.alu .add (9 : Fin 32) (9 : Fin 32) a4, 2) := by decide
theorem gd_at_3d6 : fetchRel p256DecompressCode 0x3D6 = some (.alu .sltu (28 : Fin 32) a4 a1, 4) := by decide
theorem gd_at_3da : fetchRel p256DecompressCode 0x3DA = some (.alu .sltu a1 (9 : Fin 32) a4, 4) := by decide
theorem gd_at_3de : fetchRel p256DecompressCode 0x3DE = some (.aluImm .add a0 a0 0x4, 2) := by decide
theorem gd_at_3e0 : fetchRel p256DecompressCode 0x3E0 = some (.alu .add (28 : Fin 32) (28 : Fin 32) a1, 2) := by decide
theorem gd_at_3e2 : fetchRel p256DecompressCode 0x3E2 = some (.aluImm .add (30 : Fin 32) (30 : Fin 32) 0x4, 2) := by decide
theorem gd_at_3e4 : fetchRel p256DecompressCode 0x3E4 = some (.aluImm .add (29 : Fin 32) (29 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem gd_at_3e6 : fetchRel p256DecompressCode 0x3E6 = some (.branch .bne (29 : Fin 32) x0 0xFFFFFFB6, 4) := by decide
theorem gd_at_3ea : fetchRel p256DecompressCode 0x3EA = some (.alu .add (20 : Fin 32) (20 : Fin 32) (9 : Fin 32), 2) := by decide
theorem gd_at_3ec : fetchRel p256DecompressCode 0x3EC = some (.alu .add a1 (28 : Fin 32) (17 : Fin 32), 4) := by decide
theorem gd_at_3f0 : fetchRel p256DecompressCode 0x3F0 = some (.alu .sltu a0 (20 : Fin 32) (9 : Fin 32), 4) := by decide
theorem gd_at_3f4 : fetchRel p256DecompressCode 0x3F4 = some (.store .sw sp (20 : Fin 32) 0x698, 4) := by decide
theorem gd_at_3f8 : fetchRel p256DecompressCode 0x3F8 = some (.alu .add (20 : Fin 32) a1 a0, 4) := by decide
theorem gd_at_3fc : fetchRel p256DecompressCode 0x3FC = some (.aluImm .add (5 : Fin 32) (5 : Fin 32) 0x1, 2) := by decide
theorem gd_at_3fe : fetchRel p256DecompressCode 0x3FE = some (.aluImm .add (17 : Fin 32) x0 0x0, 2) := by decide
theorem gd_at_400 : fetchRel p256DecompressCode 0x400 = some (.branch .bne (5 : Fin 32) (27 : Fin 32) 0xFFFFFF58, 4) := by decide
theorem gd_at_404 : fetchRel p256DecompressCode 0x404 = some (.aluImm .add a0 sp 0x43C, 4) := by decide
theorem gd_at_408 : fetchRel p256DecompressCode 0x408 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem gd_at_40c : fetchRel p256DecompressCode 0x40C = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem gd_at_40e : fetchRel p256DecompressCode 0x40E = some (.aluImm .add (24 : Fin 32) sp 0x43C, 4) := by decide
theorem gd_at_412 : fetchRel p256DecompressCode 0x412 = some (.auipc ra 0x10000, 4) := by decide
theorem gd_at_416 : fetchRel p256DecompressCode 0x416 = some (.jalr ra ra 0x208, 4) := by decide
theorem gd_at_41a : fetchRel p256DecompressCode 0x41A = some (.aluImm .add (26 : Fin 32) x0 0x0, 2) := by decide
theorem gd_at_41c : fetchRel p256DecompressCode 0x41C = some (.aluImm .add (8 : Fin 32) sp 0x67C, 4) := by decide
theorem gd_at_420 : fetchRel p256DecompressCode 0x420 = some (.aluImm .add (9 : Fin 32) x0 0x8, 2) := by decide
theorem gd_at_422 : fetchRel p256DecompressCode 0x422 = some (.aluImm .add (23 : Fin 32) sp 0xE4, 4) := by decide
theorem gd_at_426 : fetchRel p256DecompressCode 0x426 = some (.branch .beq (9 : Fin 32) x0 0x22, 2) := by decide
theorem gd_at_428 : fetchRel p256DecompressCode 0x428 = some (.load .lw a0 (8 : Fin 32) 0x0, 2) := by decide
theorem gd_at_42a : fetchRel p256DecompressCode 0x42A = some (.load .lw a1 (23 : Fin 32) 0x0, 4) := by decide
theorem gd_at_42e : fetchRel p256DecompressCode 0x42E = some (.alu .add a2 x0 (26 : Fin 32), 2) := by decide
theorem gd_at_430 : fetchRel p256DecompressCode 0x430 = some (.auipc ra 0xFFFFC000, 4) := by decide
theorem gd_at_434 : fetchRel p256DecompressCode 0x434 = some (.jalr ra ra 0xFFFFFF14, 4) := by decide
theorem gd_at_438 : fetchRel p256DecompressCode 0x438 = some (.alu .add (26 : Fin 32) x0 a1, 2) := by decide
theorem gd_at_43a : fetchRel p256DecompressCode 0x43A = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, 2) := by decide
theorem gd_at_43c : fetchRel p256DecompressCode 0x43C = some (.store .sw (24 : Fin 32) a0 0x0, 4) := by decide
theorem gd_at_440 : fetchRel p256DecompressCode 0x440 = some (.aluImm .add (23 : Fin 32) (23 : Fin 32) 0x4, 2) := by decide
theorem gd_at_442 : fetchRel p256DecompressCode 0x442 = some (.aluImm .add (24 : Fin 32) (24 : Fin 32) 0x4, 2) := by decide
theorem gd_at_444 : fetchRel p256DecompressCode 0x444 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem gd_at_446 : fetchRel p256DecompressCode 0x446 = some (.branch .bne (9 : Fin 32) x0 0xFFFFFFE2, 2) := by decide
theorem gd_at_448 : fetchRel p256DecompressCode 0x448 = some (.aluImm .add a0 sp 0x6BC, 4) := by decide
theorem gd_at_44c : fetchRel p256DecompressCode 0x44C = some (.aluImm .add a1 sp 0x43C, 4) := by decide
theorem gd_at_450 : fetchRel p256DecompressCode 0x450 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem gd_at_454 : fetchRel p256DecompressCode 0x454 = some (.auipc ra 0x10000, 4) := by decide
theorem gd_at_458 : fetchRel p256DecompressCode 0x458 = some (.jalr ra ra 0x22E, 4) := by decide
theorem gd_at_45c : fetchRel p256DecompressCode 0x45C = some (.store .sw sp (20 : Fin 32) 0x43C, 4) := by decide
theorem gd_at_460 : fetchRel p256DecompressCode 0x460 = some (.aluImm .add a1 sp 0x43C, 4) := by decide
theorem gd_at_464 : fetchRel p256DecompressCode 0x464 = some (.load .lw a0 sp 0x43C, 4) := by decide
theorem gd_at_468 : fetchRel p256DecompressCode 0x468 = some (.aluImm .sltu a0 a0 0x1, 4) := by decide
theorem gd_at_46c : fetchRel p256DecompressCode 0x46C = some (.alu .and (24 : Fin 32) a0 (26 : Fin 32), 4) := by decide
theorem gd_at_470 : fetchRel p256DecompressCode 0x470 = some (.store .sb sp (24 : Fin 32) 0x43C, 4) := by decide
theorem gd_at_474 : fetchRel p256DecompressCode 0x474 = some (.load .lbu a0 sp 0x43C, 4) := by decide
theorem gd_at_478 : fetchRel p256DecompressCode 0x478 = some (.aluImm .add a0 a0 0xFFFFFFFF, 2) := by decide
theorem gd_at_47a : fetchRel p256DecompressCode 0x47A = some (.alu .and a2 (26 : Fin 32) a0, 4) := by decide
theorem gd_at_47e : fetchRel p256DecompressCode 0x47E = some (.alu .add a0 x0 (20 : Fin 32), 2) := by decide
theorem gd_at_480 : fetchRel p256DecompressCode 0x480 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem gd_at_482 : fetchRel p256DecompressCode 0x482 = some (.auipc ra 0xFFFFC000, 4) := by decide
theorem gd_at_486 : fetchRel p256DecompressCode 0x486 = some (.jalr ra ra 0xFFFFFEC2, 4) := by decide
theorem gd_at_48a : fetchRel p256DecompressCode 0x48A = some (.aluImm .add a0 sp 0x43C, 4) := by decide
theorem gd_at_48e : fetchRel p256DecompressCode 0x48E = some (.aluImm .add a1 sp 0x6BC, 4) := by decide
theorem gd_at_492 : fetchRel p256DecompressCode 0x492 = some (.aluImm .add a2 sp 0x67C, 4) := by decide
theorem gd_at_496 : fetchRel p256DecompressCode 0x496 = some (.alu .add a3 x0 (24 : Fin 32), 2) := by decide
theorem gd_at_498 : fetchRel p256DecompressCode 0x498 = some (.auipc ra 0xC000, 4) := by decide
theorem gd_at_49c : fetchRel p256DecompressCode 0x49C = some (.jalr ra ra 0x668, 4) := by decide
theorem gd_at_4a0 : fetchRel p256DecompressCode 0x4A0 = some (.aluImm .add a0 sp 0x67C, 4) := by decide
theorem gd_at_4a4 : fetchRel p256DecompressCode 0x4A4 = some (.aluImm .add a1 sp 0x43C, 4) := by decide
theorem gd_at_4a8 : fetchRel p256DecompressCode 0x4A8 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem gd_at_4ac : fetchRel p256DecompressCode 0x4AC = some (.auipc ra 0x10000, 4) := by decide
theorem gd_at_4b0 : fetchRel p256DecompressCode 0x4B0 = some (.jalr ra ra 0x1D6, 4) := by decide
theorem gd_at_4b4 : fetchRel p256DecompressCode 0x4B4 = some (.load .lw a1 sp 0x3C, 2) := by decide
theorem gd_at_4b6 : fetchRel p256DecompressCode 0x4B6 = some (.aluImm .add a1 a1 0x1, 2) := by decide
theorem gd_at_4b8 : fetchRel p256DecompressCode 0x4B8 = some (.jal x0 0xFFFFFE64, 2) := by decide
theorem gd_at_4ba : fetchRel p256DecompressCode 0x4BA = some (.aluImm .add a0 sp 0x65C, 4) := by decide
theorem gd_at_4be : fetchRel p256DecompressCode 0x4BE = some (.aluImm .add a1 sp 0x67C, 4) := by decide
theorem gd_at_4c2 : fetchRel p256DecompressCode 0x4C2 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem gd_at_4c6 : fetchRel p256DecompressCode 0x4C6 = some (.auipc ra 0x10000, 4) := by decide
theorem gd_at_4ca : fetchRel p256DecompressCode 0x4CA = some (.jalr ra ra 0x1BC, 4) := by decide
theorem gd_at_4ce : fetchRel p256DecompressCode 0x4CE = some (.load .lw a3 sp 0x20, 2) := by decide
theorem gd_at_4d0 : fetchRel p256DecompressCode 0x4D0 = some (.load .lw a0 sp 0x2C, 2) := by decide
theorem gd_at_4d2 : fetchRel p256DecompressCode 0x4D2 = some (.aluImm .add a1 x0 0x9, 2) := by decide
theorem gd_at_4d4 : fetchRel p256DecompressCode 0x4D4 = some (.branch .bgeu a0 a1 0x332, 4) := by decide
theorem gd_at_4d8 : fetchRel p256DecompressCode 0x4D8 = some (.load .lw a0 sp 0x34, 2) := by decide
theorem gd_at_4da : fetchRel p256DecompressCode 0x4DA = some (.load .lw a1 sp 0x38, 2) := by decide
theorem gd_at_4dc : fetchRel p256DecompressCode 0x4DC = some (.alu .xor a0 a0 a1, 2) := by decide
theorem gd_at_4de : fetchRel p256DecompressCode 0x4DE = some (.load .lw a1 sp 0x30, 2) := by decide
theorem gd_at_4e0 : fetchRel p256DecompressCode 0x4E0 = some (.alu .xor a1 a1 a3, 2) := by decide
theorem gd_at_4e2 : fetchRel p256DecompressCode 0x4E2 = some (.alu .or a1 a1 a0, 2) := by decide
theorem gd_at_4e4 : fetchRel p256DecompressCode 0x4E4 = some (.load .lw a0 sp 0x24, 2) := by decide
theorem gd_at_4e6 : fetchRel p256DecompressCode 0x4E6 = some (.branch .beq a1 x0 0x4, 2) := by decide
theorem gd_at_4e8 : fetchRel p256DecompressCode 0x4E8 = some (.aluImm .add a0 x0 0xF, 2) := by decide
theorem gd_at_4ea : fetchRel p256DecompressCode 0x4EA = some (.load .lw a1 sp 0x28, 2) := by decide
theorem gd_at_4ec : fetchRel p256DecompressCode 0x4EC = some (.load .lw a1 a1 0x0, 2) := by decide
theorem gd_at_4ee : fetchRel p256DecompressCode 0x4EE = some (.aluImm .sll a2 a3 0x2, 4) := by decide
theorem gd_at_4f2 : fetchRel p256DecompressCode 0x4F2 = some (.alu .srl a1 a1 a2, 4) := by decide
theorem gd_at_4f6 : fetchRel p256DecompressCode 0x4F6 = some (.alu .and a0 a0 a1, 2) := by decide
theorem gd_at_4f8 : fetchRel p256DecompressCode 0x4F8 = some (.branch .beq a0 x0 0xFFFFFDF8, 4) := by decide
theorem gd_at_4fc : fetchRel p256DecompressCode 0x4FC = some (.aluImm .sll a0 a0 0x5, 2) := by decide
theorem gd_at_4fe : fetchRel p256DecompressCode 0x4FE = some (.aluImm .add a2 sp 0x21C, 2) := by decide
theorem gd_at_500 : fetchRel p256DecompressCode 0x500 = some (.alu .add a2 a2 a0, 2) := by decide
theorem gd_at_502 : fetchRel p256DecompressCode 0x502 = some (.aluImm .add a0 sp 0x43C, 4) := by decide
theorem gd_at_506 : fetchRel p256DecompressCode 0x506 = some (.aluImm .add a1 sp 0x65C, 4) := by decide
theorem gd_at_50a : fetchRel p256DecompressCode 0x50A = some (.aluImm .add a4 x0 0x1, 2) := by decide
theorem gd_at_50c : fetchRel p256DecompressCode 0x50C = some (.alu .add (8 : Fin 32) x0 a3, 2) := by decide
theorem gd_at_50e : fetchRel p256DecompressCode 0x50E = some (.aluImm .add a3 sp 0xE4, 2) := by decide
theorem gd_at_510 : fetchRel p256DecompressCode 0x510 = some (.auipc ra 0xC000, 4) := by decide
theorem gd_at_514 : fetchRel p256DecompressCode 0x514 = some (.jalr ra ra 0x462, 4) := by decide
theorem gd_at_518 : fetchRel p256DecompressCode 0x518 = some (.aluImm .add a0 sp 0x65C, 4) := by decide
theorem gd_at_51c : fetchRel p256DecompressCode 0x51C = some (.aluImm .add a1 sp 0x43C, 4) := by decide
theorem gd_at_520 : fetchRel p256DecompressCode 0x520 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem gd_at_524 : fetchRel p256DecompressCode 0x524 = some (.auipc ra 0x10000, 4) := by decide
theorem gd_at_528 : fetchRel p256DecompressCode 0x528 = some (.jalr ra ra 0x15E, 4) := by decide
theorem gd_at_52c : fetchRel p256DecompressCode 0x52C = some (.alu .add a3 x0 (8 : Fin 32), 2) := by decide
theorem gd_at_52e : fetchRel p256DecompressCode 0x52E = some (.jal x0 0xFFFFFDC2, 2) := by decide
theorem gd_at_530 : fetchRel p256DecompressCode 0x530 = some (.load .lw (9 : Fin 32) sp 0x38, 2) := by decide
theorem gd_at_532 : fetchRel p256DecompressCode 0x532 = some (.branch .bne (9 : Fin 32) x0 0xFFFFFDA2, 4) := by decide
theorem gd_at_536 : fetchRel p256DecompressCode 0x536 = some (.aluImm .add a0 sp 0x150, 2) := by decide
theorem gd_at_538 : fetchRel p256DecompressCode 0x538 = some (.aluImm .add a1 sp 0x65C, 4) := by decide
theorem gd_at_53c : fetchRel p256DecompressCode 0x53C = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem gd_at_540 : fetchRel p256DecompressCode 0x540 = some (.auipc ra 0x10000, 4) := by decide
theorem gd_at_544 : fetchRel p256DecompressCode 0x544 = some (.jalr ra ra 0x142, 4) := by decide
theorem gd_at_548 : fetchRel p256DecompressCode 0x548 = some (.load .lw (25 : Fin 32) sp 0x18, 2) := by decide
theorem gd_at_54a : fetchRel p256DecompressCode 0x54A = some (.load .lw (26 : Fin 32) sp 0x14, 2) := by decide
theorem gd_at_54c : fetchRel p256DecompressCode 0x54C = some (.load .lw (27 : Fin 32) sp 0x10, 2) := by decide
theorem gd_at_54e : fetchRel p256DecompressCode 0x54E = some (.aluImm .add (20 : Fin 32) sp 0x170, 4) := by decide
theorem gd_at_552 : fetchRel p256DecompressCode 0x552 = some (.lui a1 0x3FCC5000, 4) := by decide
theorem gd_at_556 : fetchRel p256DecompressCode 0x556 = some (.aluImm .add a1 a1 0xFFFFFBA0, 4) := by decide
theorem gd_at_55a : fetchRel p256DecompressCode 0x55A = some (.aluImm .add a2 x0 0x6C, 4) := by decide
theorem gd_at_55e : fetchRel p256DecompressCode 0x55E = some (.alu .add a0 x0 (20 : Fin 32), 2) := by decide
theorem gd_at_560 : fetchRel p256DecompressCode 0x560 = some (.auipc ra 0x10000, 4) := by decide
theorem gd_at_564 : fetchRel p256DecompressCode 0x564 = some (.jalr ra ra 0x122, 4) := by decide
theorem gd_at_568 : fetchRel p256DecompressCode 0x568 = some (.load .lw (18 : Fin 32) sp 0x1D0, 4) := by decide
theorem gd_at_56c : fetchRel p256DecompressCode 0x56C = some (.aluImm .add a0 sp 0x1DC, 2) := by decide
theorem gd_at_56e : fetchRel p256DecompressCode 0x56E = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem gd_at_572 : fetchRel p256DecompressCode 0x572 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem gd_at_574 : fetchRel p256DecompressCode 0x574 = some (.auipc ra 0x10000, 4) := by decide
theorem gd_at_578 : fetchRel p256DecompressCode 0x578 = some (.jalr ra ra 0xA6, 4) := by decide
theorem gd_at_57c : fetchRel p256DecompressCode 0x57C = some (.aluImm .add (19 : Fin 32) x0 0x0, 2) := by decide
theorem gd_at_57e : fetchRel p256DecompressCode 0x57E = some (.aluImm .add (29 : Fin 32) x0 0x0, 2) := by decide
theorem gd_at_580 : fetchRel p256DecompressCode 0x580 = some (.aluImm .add (30 : Fin 32) x0 0x0, 2) := by decide
theorem gd_at_582 : fetchRel p256DecompressCode 0x582 = some (.load .lw (7 : Fin 32) sp 0x150, 4) := by decide
theorem gd_at_586 : fetchRel p256DecompressCode 0x586 = some (.load .lw (28 : Fin 32) sp 0x170, 4) := by decide
theorem gd_at_58a : fetchRel p256DecompressCode 0x58A = some (.aluImm .add a6 sp 0x174, 4) := by decide
theorem gd_at_58e : fetchRel p256DecompressCode 0x58E = some (.aluImm .add (17 : Fin 32) sp 0x1E0, 4) := by decide
theorem gd_at_592 : fetchRel p256DecompressCode 0x592 = some (.aluImm .add (6 : Fin 32) x0 0x8, 2) := by decide
theorem gd_at_594 : fetchRel p256DecompressCode 0x594 = some (.aluImm .add (5 : Fin 32) sp 0x150, 4) := by decide
theorem gd_at_598 : fetchRel p256DecompressCode 0x598 = some (.branch .beq (6 : Fin 32) x0 0xB8, 4) := by decide
theorem gd_at_59c : fetchRel p256DecompressCode 0x59C = some (.aluImm .sll a1 (30 : Fin 32) 0x2, 4) := by decide
theorem gd_at_5a0 : fetchRel p256DecompressCode 0x5A0 = some (.alu .add a1 a1 (5 : Fin 32), 2) := by decide
theorem gd_at_5a2 : fetchRel p256DecompressCode 0x5A2 = some (.load .lw (31 : Fin 32) a1 0x0, 4) := by decide
theorem gd_at_5a6 : fetchRel p256DecompressCode 0x5A6 = some (.alu .mul a1 (7 : Fin 32) (31 : Fin 32), 4) := by decide
theorem gd_at_5aa : fetchRel p256DecompressCode 0x5AA = some (.load .lw a2 sp 0x1DC, 4) := by decide
theorem gd_at_5ae : fetchRel p256DecompressCode 0x5AE = some (.alu .add a2 a2 a1, 2) := by decide
theorem gd_at_5b0 : fetchRel p256DecompressCode 0x5B0 = some (.alu .mul a4 (18 : Fin 32) a2, 4) := by decide
theorem gd_at_5b4 : fetchRel p256DecompressCode 0x5B4 = some (.alu .sub (21 : Fin 32) x0 a4, 4) := by decide
theorem gd_at_5b8 : fetchRel p256DecompressCode 0x5B8 = some (.alu .mulhu a4 (7 : Fin 32) (31 : Fin 32), 4) := by decide
theorem gd_at_5bc : fetchRel p256DecompressCode 0x5BC = some (.alu .mul (9 : Fin 32) (21 : Fin 32) (28 : Fin 32), 4) := by decide
theorem gd_at_5c0 : fetchRel p256DecompressCode 0x5C0 = some (.alu .mulhu (8 : Fin 32) (21 : Fin 32) (28 : Fin 32), 4) := by decide
theorem gd_at_5c4 : fetchRel p256DecompressCode 0x5C4 = some (.alu .sltu a1 a2 a1, 4) := by decide
theorem gd_at_5c8 : fetchRel p256DecompressCode 0x5C8 = some (.alu .add a1 a1 a4, 2) := by decide
theorem gd_at_5ca : fetchRel p256DecompressCode 0x5CA = some (.alu .add a2 a2 (9 : Fin 32), 2) := by decide
theorem gd_at_5cc : fetchRel p256DecompressCode 0x5CC = some (.alu .add a1 a1 (8 : Fin 32), 2) := by decide
theorem gd_at_5ce : fetchRel p256DecompressCode 0x5CE = some (.alu .sltu a2 a2 (9 : Fin 32), 4) := by decide
theorem gd_at_5d2 : fetchRel p256DecompressCode 0x5D2 = some (.alu .add a2 a2 a1, 2) := by decide
theorem gd_at_5d4 : fetchRel p256DecompressCode 0x5D4 = some (.alu .sltu a4 a1 (8 : Fin 32), 4) := by decide
theorem gd_at_5d8 : fetchRel p256DecompressCode 0x5D8 = some (.alu .sltu a1 a2 a1, 4) := by decide
theorem gd_at_5dc : fetchRel p256DecompressCode 0x5DC = some (.aluImm .add (23 : Fin 32) x0 0x7, 2) := by decide
theorem gd_at_5de : fetchRel p256DecompressCode 0x5DE = some (.alu .add (22 : Fin 32) a4 a1, 4) := by decide
theorem gd_at_5e2 : fetchRel p256DecompressCode 0x5E2 = some (.alu .add a1 x0 (17 : Fin 32), 2) := by decide
theorem gd_at_5e4 : fetchRel p256DecompressCode 0x5E4 = some (.alu .add (8 : Fin 32) x0 a6, 2) := by decide
theorem gd_at_5e6 : fetchRel p256DecompressCode 0x5E6 = some (.branch .beq (23 : Fin 32) x0 0x50, 4) := by decide
theorem gd_at_5ea : fetchRel p256DecompressCode 0x5EA = some (.load .lw a0 (8 : Fin 32) 0xFFFFFFE0, 4) := by decide
theorem gd_at_5ee : fetchRel p256DecompressCode 0x5EE = some (.load .lw a3 (8 : Fin 32) 0x0, 2) := by decide
theorem gd_at_5f0 : fetchRel p256DecompressCode 0x5F0 = some (.alu .mul a5 a0 (31 : Fin 32), 4) := by decide
theorem gd_at_5f4 : fetchRel p256DecompressCode 0x5F4 = some (.alu .mulhu a4 a3 (21 : Fin 32), 4) := by decide
theorem gd_at_5f8 : fetchRel p256DecompressCode 0x5F8 = some (.alu .mul a3 a3 (21 : Fin 32), 4) := by decide
theorem gd_at_5fc : fetchRel p256DecompressCode 0x5FC = some (.load .lw (9 : Fin 32) a1 0x0, 2) := by decide
theorem gd_at_5fe : fetchRel p256DecompressCode 0x5FE = some (.alu .mulhu a0 a0 (31 : Fin 32), 4) := by decide
theorem gd_at_602 : fetchRel p256DecompressCode 0x602 = some (.alu .add a4 a4 (22 : Fin 32), 2) := by decide
theorem gd_at_604 : fetchRel p256DecompressCode 0x604 = some (.alu .add (9 : Fin 32) (9 : Fin 32) a5, 2) := by decide
theorem gd_at_606 : fetchRel p256DecompressCode 0x606 = some (.alu .add a2 a2 a3, 2) := by decide
theorem gd_at_608 : fetchRel p256DecompressCode 0x608 = some (.alu .sltu a5 (9 : Fin 32) a5, 4) := by decide
theorem gd_at_60c : fetchRel p256DecompressCode 0x60C = some (.alu .sltu a3 a2 a3, 4) := by decide
theorem gd_at_610 : fetchRel p256DecompressCode 0x610 = some (.alu .add (9 : Fin 32) (9 : Fin 32) a2, 2) := by decide
theorem gd_at_612 : fetchRel p256DecompressCode 0x612 = some (.alu .add a0 a0 a5, 2) := by decide
theorem gd_at_614 : fetchRel p256DecompressCode 0x614 = some (.alu .add a3 a3 a4, 2) := by decide
theorem gd_at_616 : fetchRel p256DecompressCode 0x616 = some (.alu .sltu a2 (9 : Fin 32) a2, 4) := by decide
theorem gd_at_61a : fetchRel p256DecompressCode 0x61A = some (.alu .add a0 a0 a3, 2) := by decide
theorem gd_at_61c : fetchRel p256DecompressCode 0x61C = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, 2) := by decide
theorem gd_at_61e : fetchRel p256DecompressCode 0x61E = some (.alu .add a2 a2 a0, 2) := by decide
theorem gd_at_620 : fetchRel p256DecompressCode 0x620 = some (.alu .sltu (22 : Fin 32) a0 a3, 4) := by decide
theorem gd_at_624 : fetchRel p256DecompressCode 0x624 = some (.alu .sltu a0 a2 a0, 4) := by decide
theorem gd_at_628 : fetchRel p256DecompressCode 0x628 = some (.store .sw a1 (9 : Fin 32) 0xFFFFFFFC, 4) := by decide
theorem gd_at_62c : fetchRel p256DecompressCode 0x62C = some (.alu .add (22 : Fin 32) (22 : Fin 32) a0, 2) := by decide
theorem gd_at_62e : fetchRel p256DecompressCode 0x62E = some (.aluImm .add a1 a1 0x4, 2) := by decide
theorem gd_at_630 : fetchRel p256DecompressCode 0x630 = some (.aluImm .add (23 : Fin 32) (23 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem gd_at_632 : fetchRel p256DecompressCode 0x632 = some (.branch .bne (23 : Fin 32) x0 0xFFFFFFB8, 4) := by decide
theorem gd_at_636 : fetchRel p256DecompressCode 0x636 = some (.alu .add (19 : Fin 32) (19 : Fin 32) a2, 2) := by decide
theorem gd_at_638 : fetchRel p256DecompressCode 0x638 = some (.alu .add a4 (22 : Fin 32) (29 : Fin 32), 4) := by decide
theorem gd_at_63c : fetchRel p256DecompressCode 0x63C = some (.alu .sltu a1 (19 : Fin 32) a2, 4) := by decide
theorem gd_at_640 : fetchRel p256DecompressCode 0x640 = some (.store .sw sp (19 : Fin 32) 0x1F8, 4) := by decide
theorem gd_at_644 : fetchRel p256DecompressCode 0x644 = some (.alu .add (19 : Fin 32) a4 a1, 4) := by decide
theorem gd_at_648 : fetchRel p256DecompressCode 0x648 = some (.aluImm .add (30 : Fin 32) (30 : Fin 32) 0x1, 2) := by decide
theorem gd_at_64a : fetchRel p256DecompressCode 0x64A = some (.aluImm .add (29 : Fin 32) x0 0x0, 2) := by decide
theorem gd_at_64c : fetchRel p256DecompressCode 0x64C = some (.branch .bne (30 : Fin 32) (6 : Fin 32) 0xFFFFFF50, 4) := by decide
theorem gd_at_650 : fetchRel p256DecompressCode 0x650 = some (.aluImm .add a0 sp 0x21C, 2) := by decide
theorem gd_at_652 : fetchRel p256DecompressCode 0x652 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem gd_at_656 : fetchRel p256DecompressCode 0x656 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem gd_at_658 : fetchRel p256DecompressCode 0x658 = some (.aluImm .add (18 : Fin 32) sp 0x21C, 4) := by decide
theorem gd_at_65c : fetchRel p256DecompressCode 0x65C = some (.auipc ra 0x10000, 4) := by decide
theorem gd_at_660 : fetchRel p256DecompressCode 0x660 = some (.jalr ra ra 0xFFFFFFBE, 4) := by decide
theorem gd_at_664 : fetchRel p256DecompressCode 0x664 = some (.aluImm .add a2 x0 0x0, 2) := by decide
theorem gd_at_666 : fetchRel p256DecompressCode 0x666 = some (.aluImm .add (9 : Fin 32) sp 0x1DC, 2) := by decide
theorem gd_at_668 : fetchRel p256DecompressCode 0x668 = some (.aluImm .add (8 : Fin 32) x0 0x8, 2) := by decide
theorem gd_at_66a : fetchRel p256DecompressCode 0x66A = some (.branch .beq (8 : Fin 32) x0 0x20, 2) := by decide
theorem gd_at_66c : fetchRel p256DecompressCode 0x66C = some (.load .lw a0 (9 : Fin 32) 0x0, 2) := by decide
theorem gd_at_66e : fetchRel p256DecompressCode 0x66E = some (.load .lw a1 (20 : Fin 32) 0x0, 4) := by decide
theorem gd_at_672 : fetchRel p256DecompressCode 0x672 = some (.auipc ra 0xFFFFC000, 4) := by decide
theorem gd_at_676 : fetchRel p256DecompressCode 0x676 = some (.jalr ra ra 0xFFFFFCD2, 4) := by decide
theorem gd_at_67a : fetchRel p256DecompressCode 0x67A = some (.alu .add a2 x0 a1, 2) := by decide
theorem gd_at_67c : fetchRel p256DecompressCode 0x67C = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x4, 2) := by decide
theorem gd_at_67e : fetchRel p256DecompressCode 0x67E = some (.store .sw (18 : Fin 32) a0 0x0, 4) := by decide
theorem gd_at_682 : fetchRel p256DecompressCode 0x682 = some (.aluImm .add (20 : Fin 32) (20 : Fin 32) 0x4, 2) := by decide
theorem gd_at_684 : fetchRel p256DecompressCode 0x684 = some (.aluImm .add (18 : Fin 32) (18 : Fin 32) 0x4, 2) := by decide
theorem gd_at_686 : fetchRel p256DecompressCode 0x686 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem gd_at_688 : fetchRel p256DecompressCode 0x688 = some (.branch .bne (8 : Fin 32) x0 0xFFFFFFE4, 2) := by decide
theorem gd_at_68a : fetchRel p256DecompressCode 0x68A = some (.store .sw sp (19 : Fin 32) 0x43C, 4) := by decide
theorem gd_at_68e : fetchRel p256DecompressCode 0x68E = some (.aluImm .add a0 sp 0x43C, 4) := by decide
theorem gd_at_692 : fetchRel p256DecompressCode 0x692 = some (.load .lw a0 sp 0x43C, 4) := by decide
theorem gd_at_696 : fetchRel p256DecompressCode 0x696 = some (.aluImm .sltu (8 : Fin 32) a0 0x1, 4) := by decide
theorem gd_at_69a : fetchRel p256DecompressCode 0x69A = some (.alu .and (8 : Fin 32) (8 : Fin 32) a2, 2) := by decide
theorem gd_at_69c : fetchRel p256DecompressCode 0x69C = some (.store .sb sp (8 : Fin 32) 0x43C, 4) := by decide
theorem gd_at_6a0 : fetchRel p256DecompressCode 0x6A0 = some (.aluImm .add a0 sp 0x43C, 4) := by decide
theorem gd_at_6a4 : fetchRel p256DecompressCode 0x6A4 = some (.load .lbu a0 sp 0x43C, 4) := by decide
theorem gd_at_6a8 : fetchRel p256DecompressCode 0x6A8 = some (.aluImm .add a0 a0 0xFFFFFFFF, 2) := by decide
theorem gd_at_6aa : fetchRel p256DecompressCode 0x6AA = some (.alu .and a2 a2 a0, 2) := by decide
theorem gd_at_6ac : fetchRel p256DecompressCode 0x6AC = some (.alu .add a0 x0 (19 : Fin 32), 2) := by decide
theorem gd_at_6ae : fetchRel p256DecompressCode 0x6AE = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem gd_at_6b0 : fetchRel p256DecompressCode 0x6B0 = some (.auipc ra 0xFFFFC000, 4) := by decide
theorem gd_at_6b4 : fetchRel p256DecompressCode 0x6B4 = some (.jalr ra ra 0xFFFFFC94, 4) := by decide
theorem gd_at_6b8 : fetchRel p256DecompressCode 0x6B8 = some (.aluImm .add a0 sp 0x43C, 4) := by decide
theorem gd_at_6bc : fetchRel p256DecompressCode 0x6BC = some (.aluImm .add a1 sp 0x21C, 2) := by decide
theorem gd_at_6be : fetchRel p256DecompressCode 0x6BE = some (.aluImm .add a2 sp 0x1DC, 2) := by decide
theorem gd_at_6c0 : fetchRel p256DecompressCode 0x6C0 = some (.alu .add a3 x0 (8 : Fin 32), 2) := by decide
theorem gd_at_6c2 : fetchRel p256DecompressCode 0x6C2 = some (.auipc ra 0xC000, 4) := by decide
theorem gd_at_6c6 : fetchRel p256DecompressCode 0x6C6 = some (.jalr ra ra 0x43E, 4) := by decide
theorem gd_at_6ca : fetchRel p256DecompressCode 0x6CA = some (.aluImm .add a0 sp 0x45C, 4) := by decide
theorem gd_at_6ce : fetchRel p256DecompressCode 0x6CE = some (.lui a1 0x3FCC5000, 4) := by decide
theorem gd_at_6d2 : fetchRel p256DecompressCode 0x6D2 = some (.aluImm .add a1 a1 0xFFFFFBA0, 4) := by decide
theorem gd_at_6d6 : fetchRel p256DecompressCode 0x6D6 = some (.aluImm .add a2 x0 0x6C, 4) := by decide
theorem gd_at_6da : fetchRel p256DecompressCode 0x6DA = some (.auipc ra 0x10000, 4) := by decide
theorem gd_at_6de : fetchRel p256DecompressCode 0x6DE = some (.jalr ra ra 0xFFFFFFA8, 4) := by decide
theorem gd_at_6e2 : fetchRel p256DecompressCode 0x6E2 = some (.aluImm .add a0 sp 0x43C, 4) := by decide
theorem gd_at_6e6 : fetchRel p256DecompressCode 0x6E6 = some (.aluImm .add a1 sp 0xC4, 2) := by decide
theorem gd_at_6e8 : fetchRel p256DecompressCode 0x6E8 = some (.auipc ra 0xD000, 4) := by decide
theorem gd_at_6ec : fetchRel p256DecompressCode 0x6EC = some (.jalr ra ra 0x184, 4) := by decide
theorem gd_at_6f0 : fetchRel p256DecompressCode 0x6F0 = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem gd_at_6f4 : fetchRel p256DecompressCode 0x6F4 = some (.auipc ra 0x9000, 4) := by decide
theorem gd_at_6f8 : fetchRel p256DecompressCode 0x6F8 = some (.jalr ra ra 0xFFFFFE84, 4) := by decide
theorem gd_at_6fc : fetchRel p256DecompressCode 0x6FC = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem gd_at_6fe : fetchRel p256DecompressCode 0x6FE = some (.aluImm .add a0 sp 0x43C, 4) := by decide
theorem gd_at_702 : fetchRel p256DecompressCode 0x702 = some (.aluImm .add a1 sp 0x150, 2) := by decide
theorem gd_at_704 : fetchRel p256DecompressCode 0x704 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem gd_at_708 : fetchRel p256DecompressCode 0x708 = some (.auipc ra 0x10000, 4) := by decide
theorem gd_at_70c : fetchRel p256DecompressCode 0x70C = some (.jalr ra ra 0xFFFFFF7A, 4) := by decide
theorem gd_at_710 : fetchRel p256DecompressCode 0x710 = some (.store .sb sp (8 : Fin 32) 0x45C, 4) := by decide
theorem gd_at_714 : fetchRel p256DecompressCode 0x714 = some (.aluImm .add a0 sp 0x21C, 2) := by decide
theorem gd_at_716 : fetchRel p256DecompressCode 0x716 = some (.aluImm .add a1 sp 0x43C, 4) := by decide
theorem gd_at_71a : fetchRel p256DecompressCode 0x71A = some (.auipc ra 0xD000, 4) := by decide
theorem gd_at_71e : fetchRel p256DecompressCode 0x71E = some (.jalr ra ra 0x110, 4) := by decide
theorem gd_at_722 : fetchRel p256DecompressCode 0x722 = some (.aluImm .add a0 sp 0x1DC, 2) := by decide
theorem gd_at_724 : fetchRel p256DecompressCode 0x724 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem gd_at_728 : fetchRel p256DecompressCode 0x728 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem gd_at_72a : fetchRel p256DecompressCode 0x72A = some (.auipc ra 0x10000, 4) := by decide
theorem gd_at_72e : fetchRel p256DecompressCode 0x72E = some (.jalr ra ra 0xFFFFFEF0, 4) := by decide
theorem gd_at_732 : fetchRel p256DecompressCode 0x732 = some (.load .lbu (8 : Fin 32) sp 0x23C, 4) := by decide
theorem gd_at_736 : fetchRel p256DecompressCode 0x736 = some (.aluImm .add a0 sp 0xA4, 2) := by decide
theorem gd_at_738 : fetchRel p256DecompressCode 0x738 = some (.aluImm .add a1 sp 0x1DC, 2) := by decide
theorem gd_at_73a : fetchRel p256DecompressCode 0x73A = some (.aluImm .add a2 sp 0x21C, 2) := by decide
theorem gd_at_73c : fetchRel p256DecompressCode 0x73C = some (.alu .add a3 x0 (8 : Fin 32), 2) := by decide
theorem gd_at_73e : fetchRel p256DecompressCode 0x73E = some (.auipc ra 0xD000, 4) := by decide
theorem gd_at_742 : fetchRel p256DecompressCode 0x742 = some (.jalr ra ra 0xFFFFFD06, 4) := by decide
theorem gd_at_746 : fetchRel p256DecompressCode 0x746 = some (.aluImm .add a0 sp 0xC4, 2) := by decide
theorem gd_at_748 : fetchRel p256DecompressCode 0x748 = some (.aluImm .add a1 sp 0xA4, 2) := by decide
theorem gd_at_74a : fetchRel p256DecompressCode 0x74A = some (.auipc ra 0xD000, 4) := by decide
theorem gd_at_74e : fetchRel p256DecompressCode 0x74E = some (.jalr ra ra 0x61C, 4) := by decide
theorem gd_at_752 : fetchRel p256DecompressCode 0x752 = some (.aluImm .add a0 sp 0x43C, 4) := by decide
theorem gd_at_756 : fetchRel p256DecompressCode 0x756 = some (.aluImm .add a1 sp 0xA4, 2) := by decide
theorem gd_at_758 : fetchRel p256DecompressCode 0x758 = some (.auipc ra 0xD000, 4) := by decide
theorem gd_at_75c : fetchRel p256DecompressCode 0x75C = some (.jalr ra ra 0x714, 4) := by decide
theorem gd_at_760 : fetchRel p256DecompressCode 0x760 = some (.load .lw a0 sp 0x43C, 4) := by decide
theorem gd_at_764 : fetchRel p256DecompressCode 0x764 = some (.aluImm .and a0 a0 0x1, 2) := by decide
theorem gd_at_766 : fetchRel p256DecompressCode 0x766 = some (.auipc ra 0x9000, 4) := by decide
theorem gd_at_76a : fetchRel p256DecompressCode 0x76A = some (.jalr ra ra 0xFFFFFE12, 4) := by decide
theorem gd_at_76e : fetchRel p256DecompressCode 0x76E = some (.alu .add a1 x0 (27 : Fin 32), 2) := by decide
theorem gd_at_770 : fetchRel p256DecompressCode 0x770 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem gd_at_774 : fetchRel p256DecompressCode 0x774 = some (.jalr ra ra 0x38A, 4) := by decide
theorem gd_at_778 : fetchRel p256DecompressCode 0x778 = some (.aluImm .add a4 sp 0x45C, 4) := by decide
theorem gd_at_77c : fetchRel p256DecompressCode 0x77C = some (.aluImm .and a3 a0 0xFF, 4) := by decide
theorem gd_at_780 : fetchRel p256DecompressCode 0x780 = some (.aluImm .add a1 sp 0xC4, 2) := by decide
theorem gd_at_782 : fetchRel p256DecompressCode 0x782 = some (.aluImm .add a2 sp 0xA4, 2) := by decide
theorem gd_at_784 : fetchRel p256DecompressCode 0x784 = some (.alu .add a0 x0 a4, 2) := by decide
theorem gd_at_786 : fetchRel p256DecompressCode 0x786 = some (.auipc ra 0xD000, 4) := by decide
theorem gd_at_78a : fetchRel p256DecompressCode 0x78A = some (.jalr ra ra 0xFFFFFCBE, 4) := by decide
theorem gd_at_78e : fetchRel p256DecompressCode 0x78E = some (.aluImm .add a0 sp 0x43C, 4) := by decide
theorem gd_at_792 : fetchRel p256DecompressCode 0x792 = some (.aluImm .add a1 sp 0x84, 2) := by decide
theorem gd_at_794 : fetchRel p256DecompressCode 0x794 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem gd_at_798 : fetchRel p256DecompressCode 0x798 = some (.auipc ra 0x10000, 4) := by decide
theorem gd_at_79c : fetchRel p256DecompressCode 0x79C = some (.jalr ra ra 0xFFFFFEEA, 4) := by decide
theorem gd_at_7a0 : fetchRel p256DecompressCode 0x7A0 = some (.store .sb sp x0 0x47C, 4) := by decide
theorem gd_at_7a4 : fetchRel p256DecompressCode 0x7A4 = some (.alu .and a0 (8 : Fin 32) (26 : Fin 32), 4) := by decide
theorem gd_at_7a8 : fetchRel p256DecompressCode 0x7A8 = some (.auipc ra 0x9000, 4) := by decide
theorem gd_at_7ac : fetchRel p256DecompressCode 0x7AC = some (.jalr ra ra 0xFFFFFDD0, 4) := by decide
theorem gd_at_7b0 : fetchRel p256DecompressCode 0x7B0 = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem gd_at_7b2 : fetchRel p256DecompressCode 0x7B2 = some (.aluImm .add a1 sp 0x43C, 4) := by decide
theorem gd_at_7b6 : fetchRel p256DecompressCode 0x7B6 = some (.aluImm .add a2 x0 0x44, 4) := by decide
theorem gd_at_7ba : fetchRel p256DecompressCode 0x7BA = some (.alu .add a0 x0 (25 : Fin 32), 2) := by decide
theorem gd_at_7bc : fetchRel p256DecompressCode 0x7BC = some (.auipc ra 0x10000, 4) := by decide
theorem gd_at_7c0 : fetchRel p256DecompressCode 0x7C0 = some (.jalr ra ra 0xFFFFFEC6, 4) := by decide
theorem gd_at_7c4 : fetchRel p256DecompressCode 0x7C4 = some (.store .sb (25 : Fin 32) (8 : Fin 32) 0x44, 4) := by decide
theorem gd_at_7c8 : fetchRel p256DecompressCode 0x7C8 = some (.aluImm .add a0 sp 0x700, 4) := by decide
theorem gd_at_7cc : fetchRel p256DecompressCode 0x7CC = some (.load .lw ra a0 0xC, 4) := by decide
theorem gd_at_7d0 : fetchRel p256DecompressCode 0x7D0 = some (.load .lw (8 : Fin 32) a0 0x8, 2) := by decide
theorem gd_at_7d2 : fetchRel p256DecompressCode 0x7D2 = some (.load .lw (9 : Fin 32) a0 0x4, 2) := by decide
theorem gd_at_7d4 : fetchRel p256DecompressCode 0x7D4 = some (.load .lw (18 : Fin 32) a0 0x0, 4) := by decide
theorem gd_at_7d8 : fetchRel p256DecompressCode 0x7D8 = some (.aluImm .add a0 sp 0x680, 4) := by decide
theorem gd_at_7dc : fetchRel p256DecompressCode 0x7DC = some (.load .lw (19 : Fin 32) a0 0x7C, 4) := by decide
theorem gd_at_7e0 : fetchRel p256DecompressCode 0x7E0 = some (.load .lw (20 : Fin 32) a0 0x78, 4) := by decide
theorem gd_at_7e4 : fetchRel p256DecompressCode 0x7E4 = some (.load .lw (21 : Fin 32) a0 0x74, 4) := by decide
theorem gd_at_7e8 : fetchRel p256DecompressCode 0x7E8 = some (.load .lw (22 : Fin 32) a0 0x70, 4) := by decide
theorem gd_at_7ec : fetchRel p256DecompressCode 0x7EC = some (.load .lw (23 : Fin 32) a0 0x6C, 4) := by decide
theorem gd_at_7f0 : fetchRel p256DecompressCode 0x7F0 = some (.load .lw (24 : Fin 32) a0 0x68, 4) := by decide
theorem gd_at_7f4 : fetchRel p256DecompressCode 0x7F4 = some (.load .lw (25 : Fin 32) a0 0x64, 4) := by decide
theorem gd_at_7f8 : fetchRel p256DecompressCode 0x7F8 = some (.load .lw (26 : Fin 32) a0 0x60, 4) := by decide
theorem gd_at_7fc : fetchRel p256DecompressCode 0x7FC = some (.load .lw (27 : Fin 32) a0 0x5C, 4) := by decide
theorem gd_at_800 : fetchRel p256DecompressCode 0x800 = some (.aluImm .add sp sp 0x710, 4) := by decide
theorem gd_at_804 : fetchRel p256DecompressCode 0x804 = some (.jalr x0 ra 0x0, 2) := by decide
theorem gd_at_806 : fetchRel p256DecompressCode 0x806 = some (.aluImm .add a1 x0 0x8, 2) := by decide
theorem gd_at_808 : fetchRel p256DecompressCode 0x808 = some (.load .lw a0 sp 0x38, 2) := by decide
theorem gd_at_80a : fetchRel p256DecompressCode 0x80A = some (.auipc ra 0x9000, 4) := by decide
theorem gd_at_80e : fetchRel p256DecompressCode 0x80E = some (.jalr ra ra 0xFFFFF8D2, 4) := by decide

end C3.RV32.Gd
