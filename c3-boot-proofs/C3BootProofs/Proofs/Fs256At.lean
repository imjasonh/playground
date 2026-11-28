import C3BootProofs.Proofs.P384Mont

/-! Fetch lemmas for `VerifyingKey<NistP256>::from_sec1_bytes` (`p256FromSec1Code`). -/

namespace C3.RV32.Gs

open C3.Image

/-- Where the P-256 `from_sec1_bytes` is in the image. -/
abbrev GP : Word := BitVec.ofNat 32 p256FromSec1Address

set_option maxRecDepth 20000

theorem gs_at_0 : fetchRel p256FromSec1Code 0x0 = some (.aluImm .add sp sp 0xFFFFFD30, 4) := by decide
theorem gs_at_4 : fetchRel p256FromSec1Code 0x4 = some (.aluImm .add a2 sp 0x280, 2) := by decide
theorem gs_at_6 : fetchRel p256FromSec1Code 0x6 = some (.store .sw a2 ra 0x4C, 4) := by decide
theorem gs_at_a : fetchRel p256FromSec1Code 0xA = some (.store .sw a2 (8 : Fin 32) 0x48, 2) := by decide
theorem gs_at_c : fetchRel p256FromSec1Code 0xC = some (.store .sw a2 (9 : Fin 32) 0x44, 2) := by decide
theorem gs_at_e : fetchRel p256FromSec1Code 0xE = some (.store .sw a2 (18 : Fin 32) 0x40, 4) := by decide
theorem gs_at_12 : fetchRel p256FromSec1Code 0x12 = some (.store .sw a2 (19 : Fin 32) 0x3C, 4) := by decide
theorem gs_at_16 : fetchRel p256FromSec1Code 0x16 = some (.store .sw a2 (20 : Fin 32) 0x38, 4) := by decide
theorem gs_at_1a : fetchRel p256FromSec1Code 0x1A = some (.store .sw a2 (21 : Fin 32) 0x34, 4) := by decide
theorem gs_at_1e : fetchRel p256FromSec1Code 0x1E = some (.store .sw a2 (22 : Fin 32) 0x30, 4) := by decide
theorem gs_at_22 : fetchRel p256FromSec1Code 0x22 = some (.store .sw a2 (23 : Fin 32) 0x2C, 4) := by decide
theorem gs_at_26 : fetchRel p256FromSec1Code 0x26 = some (.store .sw a2 (24 : Fin 32) 0x28, 4) := by decide
theorem gs_at_2a : fetchRel p256FromSec1Code 0x2A = some (.store .sw a2 (25 : Fin 32) 0x24, 4) := by decide
theorem gs_at_2e : fetchRel p256FromSec1Code 0x2E = some (.alu .add (9 : Fin 32) x0 a1, 2) := by decide
theorem gs_at_30 : fetchRel p256FromSec1Code 0x30 = some (.alu .add (24 : Fin 32) x0 a0, 2) := by decide
theorem gs_at_32 : fetchRel p256FromSec1Code 0x32 = some (.load .lbu a0 a1 0x0, 4) := by decide
theorem gs_at_36 : fetchRel p256FromSec1Code 0x36 = some (.aluImm .add (8 : Fin 32) x0 0xFFFFFFFF, 2) := by decide
theorem gs_at_38 : fetchRel p256FromSec1Code 0x38 = some (.store .sw sp (8 : Fin 32) 0xD4, 2) := by decide
theorem gs_at_3a : fetchRel p256FromSec1Code 0x3A = some (.store .sb sp a0 0xD8, 4) := by decide
theorem gs_at_3e : fetchRel p256FromSec1Code 0x3E = some (.aluImm .add a0 sp 0x8C, 2) := by decide
theorem gs_at_40 : fetchRel p256FromSec1Code 0x40 = some (.aluImm .add a1 sp 0xD4, 2) := by decide
theorem gs_at_42 : fetchRel p256FromSec1Code 0x42 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem gs_at_46 : fetchRel p256FromSec1Code 0x46 = some (.jalr ra ra 0x35E, 4) := by decide
theorem gs_at_4a : fetchRel p256FromSec1Code 0x4A = some (.load .lw a0 sp 0x8C, 2) := by decide
theorem gs_at_4c : fetchRel p256FromSec1Code 0x4C = some (.branch .beq a0 (8 : Fin 32) 0x18, 4) := by decide
theorem gs_at_50 : fetchRel p256FromSec1Code 0x50 = some (.aluImm .add a1 sp 0x91, 4) := by decide
theorem gs_at_54 : fetchRel p256FromSec1Code 0x54 = some (.aluImm .add a0 sp 0x160, 2) := by decide
theorem gs_at_56 : fetchRel p256FromSec1Code 0x56 = some (.aluImm .add a2 x0 0x2F, 4) := by decide
theorem gs_at_5a : fetchRel p256FromSec1Code 0x5A = some (.auipc ra 0x11000, 4) := by decide
theorem gs_at_5e : fetchRel p256FromSec1Code 0x5E = some (.jalr ra ra 0xFFFFFB0A, 4) := by decide
theorem gs_at_62 : fetchRel p256FromSec1Code 0x62 = some (.jal x0 0x41E, 2) := by decide
theorem gs_at_64 : fetchRel p256FromSec1Code 0x64 = some (.load .lbu a0 sp 0x90, 4) := by decide
theorem gs_at_68 : fetchRel p256FromSec1Code 0x68 = some (.aluImm .add a1 x0 0x20, 4) := by decide
theorem gs_at_6c : fetchRel p256FromSec1Code 0x6C = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem gs_at_70 : fetchRel p256FromSec1Code 0x70 = some (.jalr ra ra 0x354, 4) := by decide
theorem gs_at_74 : fetchRel p256FromSec1Code 0x74 = some (.aluImm .add a0 a0 0xFFFFFFBF, 4) := by decide
theorem gs_at_78 : fetchRel p256FromSec1Code 0x78 = some (.branch .bne a0 x0 0x408, 4) := by decide
theorem gs_at_7c : fetchRel p256FromSec1Code 0x7C = some (.aluImm .add (18 : Fin 32) sp 0x1C4, 4) := by decide
theorem gs_at_80 : fetchRel p256FromSec1Code 0x80 = some (.aluImm .add a0 x0 0x41, 4) := by decide
theorem gs_at_84 : fetchRel p256FromSec1Code 0x84 = some (.branch .beq a0 x0 0x6, 2) := by decide
theorem gs_at_86 : fetchRel p256FromSec1Code 0x86 = some (.aluImm .add a0 a0 0xFFFFFFFF, 2) := by decide
theorem gs_at_88 : fetchRel p256FromSec1Code 0x88 = some (.branch .bne a0 x0 0xFFFFFFFE, 2) := by decide
theorem gs_at_8a : fetchRel p256FromSec1Code 0x8A = some (.load .lbu a0 (9 : Fin 32) 0x0, 4) := by decide
theorem gs_at_8e : fetchRel p256FromSec1Code 0x8E = some (.load .lbu a1 (9 : Fin 32) 0x1, 4) := by decide
theorem gs_at_92 : fetchRel p256FromSec1Code 0x92 = some (.load .lbu a2 (9 : Fin 32) 0x2, 4) := by decide
theorem gs_at_96 : fetchRel p256FromSec1Code 0x96 = some (.load .lbu (23 : Fin 32) (9 : Fin 32) 0x3, 4) := by decide
theorem gs_at_9a : fetchRel p256FromSec1Code 0x9A = some (.load .lbu (19 : Fin 32) (9 : Fin 32) 0x4, 4) := by decide
theorem gs_at_9e : fetchRel p256FromSec1Code 0x9E = some (.load .lbu (20 : Fin 32) (9 : Fin 32) 0x5, 4) := by decide
theorem gs_at_a2 : fetchRel p256FromSec1Code 0xA2 = some (.load .lbu (21 : Fin 32) (9 : Fin 32) 0x6, 4) := by decide
theorem gs_at_a6 : fetchRel p256FromSec1Code 0xA6 = some (.load .lbu (22 : Fin 32) (9 : Fin 32) 0x7, 4) := by decide
theorem gs_at_aa : fetchRel p256FromSec1Code 0xAA = some (.aluImm .sll a1 a1 0x8, 2) := by decide
theorem gs_at_ac : fetchRel p256FromSec1Code 0xAC = some (.alu .or a0 a0 a1, 2) := by decide
theorem gs_at_ae : fetchRel p256FromSec1Code 0xAE = some (.aluImm .add a1 (9 : Fin 32) 0x8, 4) := by decide
theorem gs_at_b2 : fetchRel p256FromSec1Code 0xB2 = some (.store .sh sp a0 0x264, 4) := by decide
theorem gs_at_b6 : fetchRel p256FromSec1Code 0xB6 = some (.store .sb sp a2 0x266, 4) := by decide
theorem gs_at_ba : fetchRel p256FromSec1Code 0xBA = some (.aluImm .add a0 sp 0x160, 2) := by decide
theorem gs_at_bc : fetchRel p256FromSec1Code 0xBC = some (.aluImm .add a2 x0 0x2F, 4) := by decide
theorem gs_at_c0 : fetchRel p256FromSec1Code 0xC0 = some (.auipc ra 0x11000, 4) := by decide
theorem gs_at_c4 : fetchRel p256FromSec1Code 0xC4 = some (.jalr ra ra 0xFFFFFAA4, 4) := by decide
theorem gs_at_c8 : fetchRel p256FromSec1Code 0xC8 = some (.load .lbu a0 (9 : Fin 32) 0x40, 4) := by decide
theorem gs_at_cc : fetchRel p256FromSec1Code 0xCC = some (.load .lbu a1 (9 : Fin 32) 0x3F, 4) := by decide
theorem gs_at_d0 : fetchRel p256FromSec1Code 0xD0 = some (.load .lbu a2 (9 : Fin 32) 0x38, 4) := by decide
theorem gs_at_d4 : fetchRel p256FromSec1Code 0xD4 = some (.load .lbu a3 (9 : Fin 32) 0x37, 4) := by decide
theorem gs_at_d8 : fetchRel p256FromSec1Code 0xD8 = some (.load .lbu a4 (9 : Fin 32) 0x39, 4) := by decide
theorem gs_at_dc : fetchRel p256FromSec1Code 0xDC = some (.load .lbu a5 (9 : Fin 32) 0x3A, 4) := by decide
theorem gs_at_e0 : fetchRel p256FromSec1Code 0xE0 = some (.aluImm .sll a0 a0 0x8, 2) := by decide
theorem gs_at_e2 : fetchRel p256FromSec1Code 0xE2 = some (.aluImm .sll a2 a2 0x8, 2) := by decide
theorem gs_at_e4 : fetchRel p256FromSec1Code 0xE4 = some (.alu .or a6 a0 a1, 4) := by decide
theorem gs_at_e8 : fetchRel p256FromSec1Code 0xE8 = some (.load .lbu a1 (9 : Fin 32) 0x3B, 4) := by decide
theorem gs_at_ec : fetchRel p256FromSec1Code 0xEC = some (.load .lbu (8 : Fin 32) (9 : Fin 32) 0x3C, 4) := by decide
theorem gs_at_f0 : fetchRel p256FromSec1Code 0xF0 = some (.load .lbu a0 (9 : Fin 32) 0x3D, 4) := by decide
theorem gs_at_f4 : fetchRel p256FromSec1Code 0xF4 = some (.load .lbu (9 : Fin 32) (9 : Fin 32) 0x3E, 4) := by decide
theorem gs_at_f8 : fetchRel p256FromSec1Code 0xF8 = some (.aluImm .sll a4 a4 0x10, 2) := by decide
theorem gs_at_fa : fetchRel p256FromSec1Code 0xFA = some (.aluImm .sll a5 a5 0x18, 2) := by decide
theorem gs_at_fc : fetchRel p256FromSec1Code 0xFC = some (.alu .or a2 a2 a3, 2) := by decide
theorem gs_at_fe : fetchRel p256FromSec1Code 0xFE = some (.alu .or a4 a4 a5, 2) := by decide
theorem gs_at_100 : fetchRel p256FromSec1Code 0x100 = some (.alu .or a2 a2 a4, 2) := by decide
theorem gs_at_102 : fetchRel p256FromSec1Code 0x102 = some (.aluImm .sll (8 : Fin 32) (8 : Fin 32) 0x8, 2) := by decide
theorem gs_at_104 : fetchRel p256FromSec1Code 0x104 = some (.aluImm .sll a0 a0 0x10, 2) := by decide
theorem gs_at_106 : fetchRel p256FromSec1Code 0x106 = some (.aluImm .sll (9 : Fin 32) (9 : Fin 32) 0x18, 2) := by decide
theorem gs_at_108 : fetchRel p256FromSec1Code 0x108 = some (.load .lh a3 sp 0x264, 4) := by decide
theorem gs_at_10c : fetchRel p256FromSec1Code 0x10C = some (.load .lbu a4 sp 0x266, 4) := by decide
theorem gs_at_110 : fetchRel p256FromSec1Code 0x110 = some (.alu .or a1 a1 (8 : Fin 32), 2) := by decide
theorem gs_at_112 : fetchRel p256FromSec1Code 0x112 = some (.alu .or a0 a0 (9 : Fin 32), 2) := by decide
theorem gs_at_114 : fetchRel p256FromSec1Code 0x114 = some (.alu .or a0 a0 a1, 2) := by decide
theorem gs_at_116 : fetchRel p256FromSec1Code 0x116 = some (.store .sw sp a2 0x11C, 4) := by decide
theorem gs_at_11a : fetchRel p256FromSec1Code 0x11A = some (.store .sw sp a0 0x120, 4) := by decide
theorem gs_at_11e : fetchRel p256FromSec1Code 0x11E = some (.store .sh sp a6 0x124, 4) := by decide
theorem gs_at_122 : fetchRel p256FromSec1Code 0x122 = some (.store .sh sp a3 0x2, 4) := by decide
theorem gs_at_126 : fetchRel p256FromSec1Code 0x126 = some (.store .sb sp a4 0x4, 4) := by decide
theorem gs_at_12a : fetchRel p256FromSec1Code 0x12A = some (.store .sb sp (23 : Fin 32) 0x5, 4) := by decide
theorem gs_at_12e : fetchRel p256FromSec1Code 0x12E = some (.store .sb sp (19 : Fin 32) 0x6, 4) := by decide
theorem gs_at_132 : fetchRel p256FromSec1Code 0x132 = some (.store .sb sp (20 : Fin 32) 0x7, 4) := by decide
theorem gs_at_136 : fetchRel p256FromSec1Code 0x136 = some (.store .sb sp (21 : Fin 32) 0x8, 4) := by decide
theorem gs_at_13a : fetchRel p256FromSec1Code 0x13A = some (.store .sb sp (22 : Fin 32) 0x9, 4) := by decide
theorem gs_at_13e : fetchRel p256FromSec1Code 0x13E = some (.aluImm .add a0 sp 0xA, 4) := by decide
theorem gs_at_142 : fetchRel p256FromSec1Code 0x142 = some (.aluImm .add a1 sp 0x160, 2) := by decide
theorem gs_at_144 : fetchRel p256FromSec1Code 0x144 = some (.aluImm .add a2 x0 0x2F, 4) := by decide
theorem gs_at_148 : fetchRel p256FromSec1Code 0x148 = some (.auipc ra 0x11000, 4) := by decide
theorem gs_at_14c : fetchRel p256FromSec1Code 0x14C = some (.jalr ra ra 0xFFFFFA1C, 4) := by decide
theorem gs_at_150 : fetchRel p256FromSec1Code 0x150 = some (.aluImm .add a0 sp 0x39, 4) := by decide
theorem gs_at_154 : fetchRel p256FromSec1Code 0x154 = some (.aluImm .add a1 sp 0x11C, 2) := by decide
theorem gs_at_156 : fetchRel p256FromSec1Code 0x156 = some (.aluImm .add a2 x0 0xA, 2) := by decide
theorem gs_at_158 : fetchRel p256FromSec1Code 0x158 = some (.auipc ra 0x11000, 4) := by decide
theorem gs_at_15c : fetchRel p256FromSec1Code 0x15C = some (.jalr ra ra 0xFFFFFA0C, 4) := by decide
theorem gs_at_160 : fetchRel p256FromSec1Code 0x160 = some (.load .lbu (22 : Fin 32) sp 0x2, 4) := by decide
theorem gs_at_164 : fetchRel p256FromSec1Code 0x164 = some (.alu .add a0 x0 (22 : Fin 32), 2) := by decide
theorem gs_at_166 : fetchRel p256FromSec1Code 0x166 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem gs_at_16a : fetchRel p256FromSec1Code 0x16A = some (.jalr ra ra 0x57E, 4) := by decide
theorem gs_at_16e : fetchRel p256FromSec1Code 0x16E = some (.branch .beq a0 x0 0x20, 2) := by decide
theorem gs_at_170 : fetchRel p256FromSec1Code 0x170 = some (.lui a1 0x3FCC4000, 4) := by decide
theorem gs_at_174 : fetchRel p256FromSec1Code 0x174 = some (.aluImm .add a1 a1 0x29C, 4) := by decide
theorem gs_at_178 : fetchRel p256FromSec1Code 0x178 = some (.aluImm .add a0 sp 0x44, 2) := by decide
theorem gs_at_17a : fetchRel p256FromSec1Code 0x17A = some (.aluImm .add a2 x0 0x44, 4) := by decide
theorem gs_at_17e : fetchRel p256FromSec1Code 0x17E = some (.auipc ra 0x11000, 4) := by decide
theorem gs_at_182 : fetchRel p256FromSec1Code 0x182 = some (.jalr ra ra 0xFFFFF9E6, 4) := by decide
theorem gs_at_186 : fetchRel p256FromSec1Code 0x186 = some (.aluImm .add a0 x0 0x1, 2) := by decide
theorem gs_at_188 : fetchRel p256FromSec1Code 0x188 = some (.store .sb sp a0 0x88, 4) := by decide
theorem gs_at_18c : fetchRel p256FromSec1Code 0x18C = some (.jal x0 0x2BE, 2) := by decide
theorem gs_at_18e : fetchRel p256FromSec1Code 0x18E = some (.aluImm .add (19 : Fin 32) sp 0x3, 4) := by decide
theorem gs_at_192 : fetchRel p256FromSec1Code 0x192 = some (.alu .add a0 x0 (22 : Fin 32), 2) := by decide
theorem gs_at_194 : fetchRel p256FromSec1Code 0x194 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem gs_at_198 : fetchRel p256FromSec1Code 0x198 = some (.jalr ra ra 0x56A, 4) := by decide
theorem gs_at_19c : fetchRel p256FromSec1Code 0x19C = some (.aluImm .and (8 : Fin 32) a0 0xFE, 4) := by decide
theorem gs_at_1a0 : fetchRel p256FromSec1Code 0x1A0 = some (.alu .add a0 x0 (22 : Fin 32), 2) := by decide
theorem gs_at_1a2 : fetchRel p256FromSec1Code 0x1A2 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem gs_at_1a6 : fetchRel p256FromSec1Code 0x1A6 = some (.jalr ra ra 0x55C, 4) := by decide
theorem gs_at_1aa : fetchRel p256FromSec1Code 0x1AA = some (.aluImm .add a1 x0 0x2, 2) := by decide
theorem gs_at_1ac : fetchRel p256FromSec1Code 0x1AC = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem gs_at_1b0 : fetchRel p256FromSec1Code 0x1B0 = some (.branch .bne (8 : Fin 32) a1 0x20, 4) := by decide
theorem gs_at_1b4 : fetchRel p256FromSec1Code 0x1B4 = some (.aluImm .and a0 a0 0x1, 2) := by decide
theorem gs_at_1b6 : fetchRel p256FromSec1Code 0x1B6 = some (.auipc ra 0xA000, 4) := by decide
theorem gs_at_1ba : fetchRel p256FromSec1Code 0x1BA = some (.jalr ra ra 0xFFFFF8A4, 4) := by decide
theorem gs_at_1be : fetchRel p256FromSec1Code 0x1BE = some (.aluImm .and a2 a0 0xFF, 4) := by decide
theorem gs_at_1c2 : fetchRel p256FromSec1Code 0x1C2 = some (.aluImm .add a0 sp 0xD4, 2) := by decide
theorem gs_at_1c4 : fetchRel p256FromSec1Code 0x1C4 = some (.alu .add a1 x0 (19 : Fin 32), 2) := by decide
theorem gs_at_1c6 : fetchRel p256FromSec1Code 0x1C6 = some (.auipc ra 0x0, 4) := by decide
theorem gs_at_1ca : fetchRel p256FromSec1Code 0x1CA = some (.jalr ra ra 0x31C, 4) := by decide
theorem gs_at_1ce : fetchRel p256FromSec1Code 0x1CE = some (.jal x0 0x270, 2) := by decide
theorem gs_at_1d0 : fetchRel p256FromSec1Code 0x1D0 = some (.aluImm .add a1 x0 0x5, 2) := by decide
theorem gs_at_1d2 : fetchRel p256FromSec1Code 0x1D2 = some (.branch .bne a0 a1 0x140, 4) := by decide
theorem gs_at_1d6 : fetchRel p256FromSec1Code 0x1D6 = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem gs_at_1d8 : fetchRel p256FromSec1Code 0x1D8 = some (.auipc ra 0xA000, 4) := by decide
theorem gs_at_1dc : fetchRel p256FromSec1Code 0x1DC = some (.jalr ra ra 0xFFFFF882, 4) := by decide
theorem gs_at_1e0 : fetchRel p256FromSec1Code 0x1E0 = some (.aluImm .and a2 a0 0xFF, 4) := by decide
theorem gs_at_1e4 : fetchRel p256FromSec1Code 0x1E4 = some (.aluImm .add a0 sp 0xD4, 2) := by decide
theorem gs_at_1e6 : fetchRel p256FromSec1Code 0x1E6 = some (.alu .add a1 x0 (19 : Fin 32), 2) := by decide
theorem gs_at_1e8 : fetchRel p256FromSec1Code 0x1E8 = some (.auipc ra 0x0, 4) := by decide
theorem gs_at_1ec : fetchRel p256FromSec1Code 0x1EC = some (.jalr ra ra 0x2FA, 4) := by decide
theorem gs_at_1f0 : fetchRel p256FromSec1Code 0x1F0 = some (.load .lbu (19 : Fin 32) sp 0x118, 4) := by decide
theorem gs_at_1f4 : fetchRel p256FromSec1Code 0x1F4 = some (.lui (9 : Fin 32) 0x3FCC4000, 4) := by decide
theorem gs_at_1f8 : fetchRel p256FromSec1Code 0x1F8 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x29C, 4) := by decide
theorem gs_at_1fc : fetchRel p256FromSec1Code 0x1FC = some (.aluImm .add a0 sp 0x1A4, 2) := by decide
theorem gs_at_1fe : fetchRel p256FromSec1Code 0x1FE = some (.aluImm .add a2 sp 0xD4, 2) := by decide
theorem gs_at_200 : fetchRel p256FromSec1Code 0x200 = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem gs_at_202 : fetchRel p256FromSec1Code 0x202 = some (.alu .add a3 x0 (19 : Fin 32), 2) := by decide
theorem gs_at_204 : fetchRel p256FromSec1Code 0x204 = some (.auipc ra 0xD000, 4) := by decide
theorem gs_at_208 : fetchRel p256FromSec1Code 0x208 = some (.jalr ra ra 0x722, 4) := by decide
theorem gs_at_20c : fetchRel p256FromSec1Code 0x20C = some (.aluImm .add a2 sp 0xF4, 2) := by decide
theorem gs_at_20e : fetchRel p256FromSec1Code 0x20E = some (.aluImm .add a0 sp 0x1C4, 2) := by decide
theorem gs_at_210 : fetchRel p256FromSec1Code 0x210 = some (.aluImm .add a1 (9 : Fin 32) 0x20, 4) := by decide
theorem gs_at_214 : fetchRel p256FromSec1Code 0x214 = some (.alu .add a3 x0 (19 : Fin 32), 2) := by decide
theorem gs_at_216 : fetchRel p256FromSec1Code 0x216 = some (.auipc ra 0xD000, 4) := by decide
theorem gs_at_21a : fetchRel p256FromSec1Code 0x21A = some (.jalr ra ra 0x710, 4) := by decide
theorem gs_at_21e : fetchRel p256FromSec1Code 0x21E = some (.load .lbu a0 sp 0x114, 4) := by decide
theorem gs_at_222 : fetchRel p256FromSec1Code 0x222 = some (.alu .sub a1 x0 (19 : Fin 32), 4) := by decide
theorem gs_at_226 : fetchRel p256FromSec1Code 0x226 = some (.aluImm .xor a0 a0 0x1, 4) := by decide
theorem gs_at_22a : fetchRel p256FromSec1Code 0x22A = some (.alu .and a0 a0 a1, 2) := by decide
theorem gs_at_22c : fetchRel p256FromSec1Code 0x22C = some (.aluImm .xor (23 : Fin 32) a0 0x1, 4) := by decide
theorem gs_at_230 : fetchRel p256FromSec1Code 0x230 = some (.aluImm .add a0 sp 0x11C, 2) := by decide
theorem gs_at_232 : fetchRel p256FromSec1Code 0x232 = some (.aluImm .add a1 sp 0x1A4, 2) := by decide
theorem gs_at_234 : fetchRel p256FromSec1Code 0x234 = some (.aluImm .add a2 x0 0x40, 4) := by decide
theorem gs_at_238 : fetchRel p256FromSec1Code 0x238 = some (.auipc ra 0x11000, 4) := by decide
theorem gs_at_23c : fetchRel p256FromSec1Code 0x23C = some (.jalr ra ra 0xFFFFF92C, 4) := by decide
theorem gs_at_240 : fetchRel p256FromSec1Code 0x240 = some (.store .sb sp (23 : Fin 32) 0x15C, 4) := by decide
theorem gs_at_244 : fetchRel p256FromSec1Code 0x244 = some (.aluImm .add (20 : Fin 32) sp 0x13C, 4) := by decide
theorem gs_at_248 : fetchRel p256FromSec1Code 0x248 = some (.aluImm .add (21 : Fin 32) sp 0x180, 4) := by decide
theorem gs_at_24c : fetchRel p256FromSec1Code 0x24C = some (.alu .add a0 x0 (21 : Fin 32), 2) := by decide
theorem gs_at_24e : fetchRel p256FromSec1Code 0x24E = some (.alu .add a1 x0 (18 : Fin 32), 2) := by decide
theorem gs_at_250 : fetchRel p256FromSec1Code 0x250 = some (.auipc ra 0xE000, 4) := by decide
theorem gs_at_254 : fetchRel p256FromSec1Code 0x254 = some (.jalr ra ra 0xFFFFFFF8, 4) := by decide
theorem gs_at_258 : fetchRel p256FromSec1Code 0x258 = some (.aluImm .add a0 sp 0x160, 2) := by decide
theorem gs_at_25a : fetchRel p256FromSec1Code 0x25A = some (.aluImm .add a1 sp 0x1A4, 2) := by decide
theorem gs_at_25c : fetchRel p256FromSec1Code 0x25C = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem gs_at_260 : fetchRel p256FromSec1Code 0x260 = some (.auipc ra 0x11000, 4) := by decide
theorem gs_at_264 : fetchRel p256FromSec1Code 0x264 = some (.jalr ra ra 0xFFFFF904, 4) := by decide
theorem gs_at_268 : fetchRel p256FromSec1Code 0x268 = some (.store .sb sp (23 : Fin 32) 0x1A0, 4) := by decide
theorem gs_at_26c : fetchRel p256FromSec1Code 0x26C = some (.aluImm .add a0 sp 0x264, 2) := by decide
theorem gs_at_26e : fetchRel p256FromSec1Code 0x26E = some (.alu .add a1 x0 (20 : Fin 32), 2) := by decide
theorem gs_at_270 : fetchRel p256FromSec1Code 0x270 = some (.aluImm .add (25 : Fin 32) sp 0x264, 4) := by decide
theorem gs_at_274 : fetchRel p256FromSec1Code 0x274 = some (.auipc ra 0xE000, 4) := by decide
theorem gs_at_278 : fetchRel p256FromSec1Code 0x278 = some (.jalr ra ra 0xDA, 4) := by decide
theorem gs_at_27c : fetchRel p256FromSec1Code 0x27C = some (.aluImm .add a0 sp 0x8C, 2) := by decide
theorem gs_at_27e : fetchRel p256FromSec1Code 0x27E = some (.alu .add a1 x0 (21 : Fin 32), 2) := by decide
theorem gs_at_280 : fetchRel p256FromSec1Code 0x280 = some (.aluImm .add (9 : Fin 32) sp 0x8C, 2) := by decide
theorem gs_at_282 : fetchRel p256FromSec1Code 0x282 = some (.auipc ra 0xE000, 4) := by decide
theorem gs_at_286 : fetchRel p256FromSec1Code 0x286 = some (.jalr ra ra 0xCC, 4) := by decide
theorem gs_at_28a : fetchRel p256FromSec1Code 0x28A = some (.aluImm .add (18 : Fin 32) x0 0x0, 2) := by decide
theorem gs_at_28c : fetchRel p256FromSec1Code 0x28C = some (.aluImm .add (8 : Fin 32) x0 0x8, 2) := by decide
theorem gs_at_28e : fetchRel p256FromSec1Code 0x28E = some (.branch .beq (8 : Fin 32) x0 0x1C, 2) := by decide
theorem gs_at_290 : fetchRel p256FromSec1Code 0x290 = some (.load .lw a0 (9 : Fin 32) 0x0, 2) := by decide
theorem gs_at_292 : fetchRel p256FromSec1Code 0x292 = some (.load .lw a1 (25 : Fin 32) 0x0, 4) := by decide
theorem gs_at_296 : fetchRel p256FromSec1Code 0x296 = some (.alu .add a2 x0 (18 : Fin 32), 2) := by decide
theorem gs_at_298 : fetchRel p256FromSec1Code 0x298 = some (.auipc ra 0xFFFFC000, 4) := by decide
theorem gs_at_29c : fetchRel p256FromSec1Code 0x29C = some (.jalr ra ra 0x58E, 4) := by decide
theorem gs_at_2a0 : fetchRel p256FromSec1Code 0x2A0 = some (.alu .add (18 : Fin 32) x0 a1, 2) := by decide
theorem gs_at_2a2 : fetchRel p256FromSec1Code 0x2A2 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x4, 2) := by decide
theorem gs_at_2a4 : fetchRel p256FromSec1Code 0x2A4 = some (.aluImm .add (25 : Fin 32) (25 : Fin 32) 0x4, 2) := by decide
theorem gs_at_2a6 : fetchRel p256FromSec1Code 0x2A6 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem gs_at_2a8 : fetchRel p256FromSec1Code 0x2A8 = some (.branch .bne (8 : Fin 32) x0 0xFFFFFFE8, 2) := by decide
theorem gs_at_2aa : fetchRel p256FromSec1Code 0x2AA = some (.aluImm .add a0 sp 0x284, 2) := by decide
theorem gs_at_2ac : fetchRel p256FromSec1Code 0x2AC = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem gs_at_2ae : fetchRel p256FromSec1Code 0x2AE = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem gs_at_2b2 : fetchRel p256FromSec1Code 0x2B2 = some (.jalr ra ra 0xFFFFFEC4, 4) := by decide
theorem gs_at_2b6 : fetchRel p256FromSec1Code 0x2B6 = some (.aluImm .add a1 sp 0xAC, 2) := by decide
theorem gs_at_2b8 : fetchRel p256FromSec1Code 0x2B8 = some (.aluImm .and (8 : Fin 32) a0 0xFF, 4) := by decide
theorem gs_at_2bc : fetchRel p256FromSec1Code 0x2BC = some (.alu .add a0 x0 a1, 2) := by decide
theorem gs_at_2be : fetchRel p256FromSec1Code 0x2BE = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem gs_at_2c0 : fetchRel p256FromSec1Code 0x2C0 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem gs_at_2c4 : fetchRel p256FromSec1Code 0x2C4 = some (.jalr ra ra 0xFFFFFEB2, 4) := by decide
theorem gs_at_2c8 : fetchRel p256FromSec1Code 0x2C8 = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem gs_at_2cc : fetchRel p256FromSec1Code 0x2CC = some (.aluImm .xor a0 a0 0xFFFFFFFF, 4) := by decide
theorem gs_at_2d0 : fetchRel p256FromSec1Code 0x2D0 = some (.alu .and a0 (18 : Fin 32) a0, 4) := by decide
theorem gs_at_2d4 : fetchRel p256FromSec1Code 0x2D4 = some (.aluImm .and a0 a0 0x1, 2) := by decide
theorem gs_at_2d6 : fetchRel p256FromSec1Code 0x2D6 = some (.alu .or a0 a0 (8 : Fin 32), 2) := by decide
theorem gs_at_2d8 : fetchRel p256FromSec1Code 0x2D8 = some (.auipc ra 0x9000, 4) := by decide
theorem gs_at_2dc : fetchRel p256FromSec1Code 0x2DC = some (.jalr ra ra 0x782, 4) := by decide
theorem gs_at_2e0 : fetchRel p256FromSec1Code 0x2E0 = some (.aluImm .add a1 sp 0xAC, 2) := by decide
theorem gs_at_2e2 : fetchRel p256FromSec1Code 0x2E2 = some (.aluImm .and a3 a0 0xFF, 4) := by decide
theorem gs_at_2e6 : fetchRel p256FromSec1Code 0x2E6 = some (.alu .add a0 x0 a1, 2) := by decide
theorem gs_at_2e8 : fetchRel p256FromSec1Code 0x2E8 = some (.alu .add a1 x0 (20 : Fin 32), 2) := by decide
theorem gs_at_2ea : fetchRel p256FromSec1Code 0x2EA = some (.alu .add a2 x0 (21 : Fin 32), 2) := by decide
theorem gs_at_2ec : fetchRel p256FromSec1Code 0x2EC = some (.auipc ra 0xD000, 4) := by decide
theorem gs_at_2f0 : fetchRel p256FromSec1Code 0x2F0 = some (.jalr ra ra 0x63A, 4) := by decide
theorem gs_at_2f4 : fetchRel p256FromSec1Code 0x2F4 = some (.aluImm .add a0 sp 0x8C, 2) := by decide
theorem gs_at_2f6 : fetchRel p256FromSec1Code 0x2F6 = some (.aluImm .add a1 sp 0x1A4, 2) := by decide
theorem gs_at_2f8 : fetchRel p256FromSec1Code 0x2F8 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem gs_at_2fc : fetchRel p256FromSec1Code 0x2FC = some (.auipc ra 0x11000, 4) := by decide
theorem gs_at_300 : fetchRel p256FromSec1Code 0x300 = some (.jalr ra ra 0xFFFFF868, 4) := by decide
theorem gs_at_304 : fetchRel p256FromSec1Code 0x304 = some (.store .sb sp (23 : Fin 32) 0xCC, 4) := by decide
theorem gs_at_308 : fetchRel p256FromSec1Code 0x308 = some (.store .sb sp (19 : Fin 32) 0xD0, 4) := by decide
theorem gs_at_30c : fetchRel p256FromSec1Code 0x30C = some (.aluImm .add a0 sp 0x44, 2) := by decide
theorem gs_at_30e : fetchRel p256FromSec1Code 0x30E = some (.aluImm .add a1 sp 0x8C, 2) := by decide
theorem gs_at_310 : fetchRel p256FromSec1Code 0x310 = some (.jal x0 0x132, 2) := by decide
theorem gs_at_312 : fetchRel p256FromSec1Code 0x312 = some (.aluImm .add a1 sp 0x23, 4) := by decide
theorem gs_at_316 : fetchRel p256FromSec1Code 0x316 = some (.aluImm .add a0 sp 0x160, 2) := by decide
theorem gs_at_318 : fetchRel p256FromSec1Code 0x318 = some (.auipc ra 0x1000, 4) := by decide
theorem gs_at_31c : fetchRel p256FromSec1Code 0x31C = some (.jalr ra ra 0xFFFFF9DC, 4) := by decide
theorem gs_at_320 : fetchRel p256FromSec1Code 0x320 = some (.aluImm .add a0 sp 0x1E4, 2) := by decide
theorem gs_at_322 : fetchRel p256FromSec1Code 0x322 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem gs_at_326 : fetchRel p256FromSec1Code 0x326 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem gs_at_328 : fetchRel p256FromSec1Code 0x328 = some (.auipc ra 0x10000, 4) := by decide
theorem gs_at_32c : fetchRel p256FromSec1Code 0x32C = some (.jalr ra ra 0x7D4, 4) := by decide
theorem gs_at_330 : fetchRel p256FromSec1Code 0x330 = some (.load .lbu (18 : Fin 32) sp 0x180, 4) := by decide
theorem gs_at_334 : fetchRel p256FromSec1Code 0x334 = some (.aluImm .add a0 sp 0x244, 2) := by decide
theorem gs_at_336 : fetchRel p256FromSec1Code 0x336 = some (.aluImm .add a1 sp 0x1E4, 2) := by decide
theorem gs_at_338 : fetchRel p256FromSec1Code 0x338 = some (.aluImm .add a2 sp 0x160, 2) := by decide
theorem gs_at_33a : fetchRel p256FromSec1Code 0x33A = some (.alu .add a3 x0 (18 : Fin 32), 2) := by decide
theorem gs_at_33c : fetchRel p256FromSec1Code 0x33C = some (.auipc ra 0xD000, 4) := by decide
theorem gs_at_340 : fetchRel p256FromSec1Code 0x340 = some (.jalr ra ra 0x5EA, 4) := by decide
theorem gs_at_344 : fetchRel p256FromSec1Code 0x344 = some (.aluImm .add a0 sp 0xD4, 2) := by decide
theorem gs_at_346 : fetchRel p256FromSec1Code 0x346 = some (.alu .add a1 x0 (19 : Fin 32), 2) := by decide
theorem gs_at_348 : fetchRel p256FromSec1Code 0x348 = some (.auipc ra 0x1000, 4) := by decide
theorem gs_at_34c : fetchRel p256FromSec1Code 0x34C = some (.jalr ra ra 0xFFFFF9AC, 4) := by decide
theorem gs_at_350 : fetchRel p256FromSec1Code 0x350 = some (.aluImm .add a0 sp 0x204, 2) := by decide
theorem gs_at_352 : fetchRel p256FromSec1Code 0x352 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem gs_at_356 : fetchRel p256FromSec1Code 0x356 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem gs_at_358 : fetchRel p256FromSec1Code 0x358 = some (.auipc ra 0x10000, 4) := by decide
theorem gs_at_35c : fetchRel p256FromSec1Code 0x35C = some (.jalr ra ra 0x7A4, 4) := by decide
theorem gs_at_360 : fetchRel p256FromSec1Code 0x360 = some (.load .lbu (19 : Fin 32) sp 0xF4, 4) := by decide
theorem gs_at_364 : fetchRel p256FromSec1Code 0x364 = some (.aluImm .add a0 sp 0x284, 2) := by decide
theorem gs_at_366 : fetchRel p256FromSec1Code 0x366 = some (.aluImm .add a1 sp 0x204, 2) := by decide
theorem gs_at_368 : fetchRel p256FromSec1Code 0x368 = some (.aluImm .add a2 sp 0xD4, 2) := by decide
theorem gs_at_36a : fetchRel p256FromSec1Code 0x36A = some (.alu .add a3 x0 (19 : Fin 32), 2) := by decide
theorem gs_at_36c : fetchRel p256FromSec1Code 0x36C = some (.auipc ra 0xD000, 4) := by decide
theorem gs_at_370 : fetchRel p256FromSec1Code 0x370 = some (.jalr ra ra 0x5BA, 4) := by decide
theorem gs_at_374 : fetchRel p256FromSec1Code 0x374 = some (.aluImm .add a0 sp 0x224, 2) := by decide
theorem gs_at_376 : fetchRel p256FromSec1Code 0x376 = some (.aluImm .add a1 sp 0x244, 2) := by decide
theorem gs_at_378 : fetchRel p256FromSec1Code 0x378 = some (.aluImm .add a2 sp 0x244, 2) := by decide
theorem gs_at_37a : fetchRel p256FromSec1Code 0x37A = some (.auipc ra 0xD000, 4) := by decide
theorem gs_at_37e : fetchRel p256FromSec1Code 0x37E = some (.jalr ra ra 0x5F8, 4) := by decide
theorem gs_at_382 : fetchRel p256FromSec1Code 0x382 = some (.aluImm .add a0 sp 0x8C, 2) := by decide
theorem gs_at_384 : fetchRel p256FromSec1Code 0x384 = some (.aluImm .add a1 sp 0x284, 2) := by decide
theorem gs_at_386 : fetchRel p256FromSec1Code 0x386 = some (.aluImm .add a2 sp 0x284, 2) := by decide
theorem gs_at_388 : fetchRel p256FromSec1Code 0x388 = some (.auipc ra 0xD000, 4) := by decide
theorem gs_at_38c : fetchRel p256FromSec1Code 0x38C = some (.jalr ra ra 0x5EA, 4) := by decide
theorem gs_at_390 : fetchRel p256FromSec1Code 0x390 = some (.aluImm .add a0 sp 0x11C, 2) := by decide
theorem gs_at_392 : fetchRel p256FromSec1Code 0x392 = some (.aluImm .add a1 sp 0x8C, 2) := by decide
theorem gs_at_394 : fetchRel p256FromSec1Code 0x394 = some (.aluImm .add a2 sp 0x284, 2) := by decide
theorem gs_at_396 : fetchRel p256FromSec1Code 0x396 = some (.auipc ra 0xD000, 4) := by decide
theorem gs_at_39a : fetchRel p256FromSec1Code 0x39A = some (.jalr ra ra 0x5DC, 4) := by decide
theorem gs_at_39e : fetchRel p256FromSec1Code 0x39E = some (.lui a1 0x3FCC4000, 4) := by decide
theorem gs_at_3a2 : fetchRel p256FromSec1Code 0x3A2 = some (.aluImm .add a1 a1 0x138, 4) := by decide
theorem gs_at_3a6 : fetchRel p256FromSec1Code 0x3A6 = some (.aluImm .add a0 sp 0x8C, 2) := by decide
theorem gs_at_3a8 : fetchRel p256FromSec1Code 0x3A8 = some (.aluImm .add a2 sp 0x284, 2) := by decide
theorem gs_at_3aa : fetchRel p256FromSec1Code 0x3AA = some (.auipc ra 0xD000, 4) := by decide
theorem gs_at_3ae : fetchRel p256FromSec1Code 0x3AE = some (.jalr ra ra 0x5C8, 4) := by decide
theorem gs_at_3b2 : fetchRel p256FromSec1Code 0x3B2 = some (.aluImm .add a0 sp 0x264, 2) := by decide
theorem gs_at_3b4 : fetchRel p256FromSec1Code 0x3B4 = some (.aluImm .add a1 sp 0x11C, 2) := by decide
theorem gs_at_3b6 : fetchRel p256FromSec1Code 0x3B6 = some (.aluImm .add a2 sp 0x8C, 2) := by decide
theorem gs_at_3b8 : fetchRel p256FromSec1Code 0x3B8 = some (.auipc ra 0xE000, 4) := by decide
theorem gs_at_3bc : fetchRel p256FromSec1Code 0x3BC = some (.jalr ra ra 0xFFFFFD80, 4) := by decide
theorem gs_at_3c0 : fetchRel p256FromSec1Code 0x3C0 = some (.lui a2 0x3FCC4000, 4) := by decide
theorem gs_at_3c4 : fetchRel p256FromSec1Code 0x3C4 = some (.aluImm .add a2 a2 0x1D8, 4) := by decide
theorem gs_at_3c8 : fetchRel p256FromSec1Code 0x3C8 = some (.aluImm .add a0 sp 0x11C, 2) := by decide
theorem gs_at_3ca : fetchRel p256FromSec1Code 0x3CA = some (.aluImm .add a1 sp 0x264, 2) := by decide
theorem gs_at_3cc : fetchRel p256FromSec1Code 0x3CC = some (.auipc ra 0xE000, 4) := by decide
theorem gs_at_3d0 : fetchRel p256FromSec1Code 0x3D0 = some (.jalr ra ra 0xFFFFFD6C, 4) := by decide
theorem gs_at_3d4 : fetchRel p256FromSec1Code 0x3D4 = some (.aluImm .add a0 sp 0x8C, 2) := by decide
theorem gs_at_3d6 : fetchRel p256FromSec1Code 0x3D6 = some (.aluImm .add a1 sp 0x284, 2) := by decide
theorem gs_at_3d8 : fetchRel p256FromSec1Code 0x3D8 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem gs_at_3dc : fetchRel p256FromSec1Code 0x3DC = some (.auipc ra 0x10000, 4) := by decide
theorem gs_at_3e0 : fetchRel p256FromSec1Code 0x3E0 = some (.jalr ra ra 0x788, 4) := by decide
theorem gs_at_3e4 : fetchRel p256FromSec1Code 0x3E4 = some (.aluImm .add a0 sp 0xAC, 2) := by decide
theorem gs_at_3e6 : fetchRel p256FromSec1Code 0x3E6 = some (.aluImm .add a1 sp 0x244, 2) := by decide
theorem gs_at_3e8 : fetchRel p256FromSec1Code 0x3E8 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem gs_at_3ec : fetchRel p256FromSec1Code 0x3EC = some (.auipc ra 0x10000, 4) := by decide
theorem gs_at_3f0 : fetchRel p256FromSec1Code 0x3F0 = some (.jalr ra ra 0x778, 4) := by decide
theorem gs_at_3f4 : fetchRel p256FromSec1Code 0x3F4 = some (.aluImm .add a0 sp 0x224, 2) := by decide
theorem gs_at_3f6 : fetchRel p256FromSec1Code 0x3F6 = some (.aluImm .add a1 sp 0x11C, 2) := by decide
theorem gs_at_3f8 : fetchRel p256FromSec1Code 0x3F8 = some (.auipc ra 0xE000, 4) := by decide
theorem gs_at_3fc : fetchRel p256FromSec1Code 0x3FC = some (.jalr ra ra 0xFFFFF882, 4) := by decide
theorem gs_at_400 : fetchRel p256FromSec1Code 0x400 = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem gs_at_404 : fetchRel p256FromSec1Code 0x404 = some (.auipc ra 0x9000, 4) := by decide
theorem gs_at_408 : fetchRel p256FromSec1Code 0x408 = some (.jalr ra ra 0x656, 4) := by decide
theorem gs_at_40c : fetchRel p256FromSec1Code 0x40C = some (.alu .and a0 (19 : Fin 32) a0, 4) := by decide
theorem gs_at_410 : fetchRel p256FromSec1Code 0x410 = some (.auipc ra 0x9000, 4) := by decide
theorem gs_at_414 : fetchRel p256FromSec1Code 0x414 = some (.jalr ra ra 0x64A, 4) := by decide
theorem gs_at_418 : fetchRel p256FromSec1Code 0x418 = some (.alu .and a0 (18 : Fin 32) a0, 4) := by decide
theorem gs_at_41c : fetchRel p256FromSec1Code 0x41C = some (.auipc ra 0x9000, 4) := by decide
theorem gs_at_420 : fetchRel p256FromSec1Code 0x420 = some (.jalr ra ra 0x63E, 4) := by decide
theorem gs_at_424 : fetchRel p256FromSec1Code 0x424 = some (.alu .add (9 : Fin 32) x0 a0, 2) := by decide
theorem gs_at_426 : fetchRel p256FromSec1Code 0x426 = some (.aluImm .add a0 sp 0xD4, 2) := by decide
theorem gs_at_428 : fetchRel p256FromSec1Code 0x428 = some (.aluImm .add a1 sp 0x8C, 2) := by decide
theorem gs_at_42a : fetchRel p256FromSec1Code 0x42A = some (.aluImm .add a2 x0 0x40, 4) := by decide
theorem gs_at_42e : fetchRel p256FromSec1Code 0x42E = some (.auipc ra 0x10000, 4) := by decide
theorem gs_at_432 : fetchRel p256FromSec1Code 0x432 = some (.jalr ra ra 0x736, 4) := by decide
theorem gs_at_436 : fetchRel p256FromSec1Code 0x436 = some (.store .sb sp x0 0x114, 4) := by decide
theorem gs_at_43a : fetchRel p256FromSec1Code 0x43A = some (.store .sb sp (9 : Fin 32) 0x118, 4) := by decide
theorem gs_at_43e : fetchRel p256FromSec1Code 0x43E = some (.aluImm .add a0 sp 0x44, 2) := by decide
theorem gs_at_440 : fetchRel p256FromSec1Code 0x440 = some (.aluImm .add a1 sp 0xD4, 2) := by decide
theorem gs_at_442 : fetchRel p256FromSec1Code 0x442 = some (.auipc ra 0x0, 4) := by decide
theorem gs_at_446 : fetchRel p256FromSec1Code 0x446 = some (.jalr ra ra 0x74, 4) := by decide
theorem gs_at_44a : fetchRel p256FromSec1Code 0x44A = some (.alu .add a0 x0 (22 : Fin 32), 2) := by decide
theorem gs_at_44c : fetchRel p256FromSec1Code 0x44C = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem gs_at_450 : fetchRel p256FromSec1Code 0x450 = some (.jalr ra ra 0x298, 4) := by decide
theorem gs_at_454 : fetchRel p256FromSec1Code 0x454 = some (.load .lbu a1 sp 0x88, 4) := by decide
theorem gs_at_458 : fetchRel p256FromSec1Code 0x458 = some (.aluImm .add a0 a0 0xFFFFFFFF, 2) := by decide
theorem gs_at_45a : fetchRel p256FromSec1Code 0x45A = some (.alu .and a0 a0 a1, 2) := by decide
theorem gs_at_45c : fetchRel p256FromSec1Code 0x45C = some (.aluImm .and a0 a0 0x1, 2) := by decide
theorem gs_at_45e : fetchRel p256FromSec1Code 0x45E = some (.store .sb sp a0 0xD4, 4) := by decide
theorem gs_at_462 : fetchRel p256FromSec1Code 0x462 = some (.aluImm .add a0 sp 0xD4, 2) := by decide
theorem gs_at_464 : fetchRel p256FromSec1Code 0x464 = some (.load .lbu a0 sp 0xD4, 4) := by decide
theorem gs_at_468 : fetchRel p256FromSec1Code 0x468 = some (.branch .beq a0 x0 0x18, 2) := by decide
theorem gs_at_46a : fetchRel p256FromSec1Code 0x46A = some (.aluImm .add a0 (24 : Fin 32) 0x4, 4) := by decide
theorem gs_at_46e : fetchRel p256FromSec1Code 0x46E = some (.aluImm .add a1 sp 0x44, 2) := by decide
theorem gs_at_470 : fetchRel p256FromSec1Code 0x470 = some (.aluImm .add a2 x0 0x44, 4) := by decide
theorem gs_at_474 : fetchRel p256FromSec1Code 0x474 = some (.auipc ra 0x10000, 4) := by decide
theorem gs_at_478 : fetchRel p256FromSec1Code 0x478 = some (.jalr ra ra 0x6F0, 4) := by decide
theorem gs_at_47c : fetchRel p256FromSec1Code 0x47C = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem gs_at_47e : fetchRel p256FromSec1Code 0x47E = some (.jal x0 0x4, 2) := by decide
theorem gs_at_480 : fetchRel p256FromSec1Code 0x480 = some (.aluImm .add a0 x0 0x1, 2) := by decide
theorem gs_at_482 : fetchRel p256FromSec1Code 0x482 = some (.store .sw (24 : Fin 32) a0 0x0, 4) := by decide
theorem gs_at_486 : fetchRel p256FromSec1Code 0x486 = some (.aluImm .add a0 sp 0x280, 2) := by decide
theorem gs_at_488 : fetchRel p256FromSec1Code 0x488 = some (.load .lw ra a0 0x4C, 4) := by decide
theorem gs_at_48c : fetchRel p256FromSec1Code 0x48C = some (.load .lw (8 : Fin 32) a0 0x48, 2) := by decide
theorem gs_at_48e : fetchRel p256FromSec1Code 0x48E = some (.load .lw (9 : Fin 32) a0 0x44, 2) := by decide
theorem gs_at_490 : fetchRel p256FromSec1Code 0x490 = some (.load .lw (18 : Fin 32) a0 0x40, 4) := by decide
theorem gs_at_494 : fetchRel p256FromSec1Code 0x494 = some (.load .lw (19 : Fin 32) a0 0x3C, 4) := by decide
theorem gs_at_498 : fetchRel p256FromSec1Code 0x498 = some (.load .lw (20 : Fin 32) a0 0x38, 4) := by decide
theorem gs_at_49c : fetchRel p256FromSec1Code 0x49C = some (.load .lw (21 : Fin 32) a0 0x34, 4) := by decide
theorem gs_at_4a0 : fetchRel p256FromSec1Code 0x4A0 = some (.load .lw (22 : Fin 32) a0 0x30, 4) := by decide
theorem gs_at_4a4 : fetchRel p256FromSec1Code 0x4A4 = some (.load .lw (23 : Fin 32) a0 0x2C, 4) := by decide
theorem gs_at_4a8 : fetchRel p256FromSec1Code 0x4A8 = some (.load .lw (24 : Fin 32) a0 0x28, 4) := by decide
theorem gs_at_4ac : fetchRel p256FromSec1Code 0x4AC = some (.load .lw (25 : Fin 32) a0 0x24, 4) := by decide
theorem gs_at_4b0 : fetchRel p256FromSec1Code 0x4B0 = some (.aluImm .add sp sp 0x2D0, 4) := by decide
theorem gs_at_4b4 : fetchRel p256FromSec1Code 0x4B4 = some (.jalr x0 ra 0x0, 2) := by decide

end C3.RV32.Gs
