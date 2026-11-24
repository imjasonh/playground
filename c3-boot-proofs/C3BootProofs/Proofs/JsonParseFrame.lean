import C3BootProofs.Proofs.JsonParseModel
import C3BootProofs.Proofs.Arr32Eq

/-!
# `json::parse`: decoding, callees, and the frame

The decoded instructions of `parse`, the calls it makes that earlier files
don't wrap (`memcmp`, which `parse` reads the sign of, and `slice_ne`), and
the facts about its 240-byte frame that the loop proofs share.
-/

namespace C3.RV32

open C3.Image C3.Json

set_option maxRecDepth 20000

theorem pa_at_0 : fetchRel jsonParseCode 0x0 = some (.aluImm .add sp sp 0xFFFFFF10, 2) := by decide
theorem pa_at_2 : fetchRel jsonParseCode 0x2 = some (.store .sw sp ra 0xEC, 2) := by decide
theorem pa_at_4 : fetchRel jsonParseCode 0x4 = some (.store .sw sp (8 : Fin 32) 0xE8, 2) := by decide
theorem pa_at_6 : fetchRel jsonParseCode 0x6 = some (.store .sw sp (9 : Fin 32) 0xE4, 2) := by decide
theorem pa_at_8 : fetchRel jsonParseCode 0x8 = some (.store .sw sp (18 : Fin 32) 0xE0, 2) := by decide
theorem pa_at_a : fetchRel jsonParseCode 0xA = some (.store .sw sp (19 : Fin 32) 0xDC, 2) := by decide
theorem pa_at_c : fetchRel jsonParseCode 0xC = some (.store .sw sp (20 : Fin 32) 0xD8, 2) := by decide
theorem pa_at_e : fetchRel jsonParseCode 0xE = some (.store .sw sp (21 : Fin 32) 0xD4, 2) := by decide
theorem pa_at_10 : fetchRel jsonParseCode 0x10 = some (.store .sw sp (22 : Fin 32) 0xD0, 2) := by decide
theorem pa_at_12 : fetchRel jsonParseCode 0x12 = some (.store .sw sp (23 : Fin 32) 0xCC, 2) := by decide
theorem pa_at_14 : fetchRel jsonParseCode 0x14 = some (.store .sw sp (24 : Fin 32) 0xC8, 2) := by decide
theorem pa_at_16 : fetchRel jsonParseCode 0x16 = some (.store .sw sp (25 : Fin 32) 0xC4, 2) := by decide
theorem pa_at_18 : fetchRel jsonParseCode 0x18 = some (.store .sw sp (26 : Fin 32) 0xC0, 2) := by decide
theorem pa_at_1a : fetchRel jsonParseCode 0x1A = some (.store .sw sp (27 : Fin 32) 0xBC, 2) := by decide
theorem pa_at_1c : fetchRel jsonParseCode 0x1C = some (.alu .add (19 : Fin 32) x0 a3, 2) := by decide
theorem pa_at_1e : fetchRel jsonParseCode 0x1E = some (.alu .add (24 : Fin 32) x0 a2, 2) := by decide
theorem pa_at_20 : fetchRel jsonParseCode 0x20 = some (.alu .add (23 : Fin 32) x0 a1, 2) := by decide
theorem pa_at_22 : fetchRel jsonParseCode 0x22 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem pa_at_24 : fetchRel jsonParseCode 0x24 = some (.aluImm .add a0 x0 0x10, 2) := by decide
theorem pa_at_26 : fetchRel jsonParseCode 0x26 = some (.aluImm .add a1 sp 0x14, 2) := by decide
theorem pa_at_28 : fetchRel jsonParseCode 0x28 = some (.branch .beq a0 x0 0x10, 2) := by decide
theorem pa_at_2a : fetchRel jsonParseCode 0x2A = some (.store .sw a1 x0 0xFFFFFFFC, 4) := by decide
theorem pa_at_2e : fetchRel jsonParseCode 0x2E = some (.store .sb a1 x0 0x0, 4) := by decide
theorem pa_at_32 : fetchRel jsonParseCode 0x32 = some (.aluImm .add a1 a1 0x8, 2) := by decide
theorem pa_at_34 : fetchRel jsonParseCode 0x34 = some (.aluImm .add a0 a0 0xFFFFFFFF, 2) := by decide
theorem pa_at_36 : fetchRel jsonParseCode 0x36 = some (.branch .bne a0 x0 0xFFFFFFF4, 2) := by decide
theorem pa_at_38 : fetchRel jsonParseCode 0x38 = some (.branch .beq (19 : Fin 32) x0 0x8, 4) := by decide
theorem pa_at_3c : fetchRel jsonParseCode 0x3C = some (.aluImm .add (26 : Fin 32) x0 0x0, 2) := by decide
theorem pa_at_3e : fetchRel jsonParseCode 0x3E = some (.jal x0 0x12, 2) := by decide
theorem pa_at_40 : fetchRel jsonParseCode 0x40 = some (.alu .add a0 x0 (23 : Fin 32), 2) := by decide
theorem pa_at_42 : fetchRel jsonParseCode 0x42 = some (.alu .add a1 x0 (24 : Fin 32), 2) := by decide
theorem pa_at_44 : fetchRel jsonParseCode 0x44 = some (.aluImm .add a2 x0 0x0, 2) := by decide
theorem pa_at_46 : fetchRel jsonParseCode 0x46 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem pa_at_4a : fetchRel jsonParseCode 0x4A = some (.jalr ra ra 0xFFFFFBCA, 4) := by decide
theorem pa_at_4e : fetchRel jsonParseCode 0x4E = some (.alu .add (26 : Fin 32) x0 a0, 2) := by decide
theorem pa_at_50 : fetchRel jsonParseCode 0x50 = some (.aluImm .add (27 : Fin 32) x0 0x0, 2) := by decide
theorem pa_at_52 : fetchRel jsonParseCode 0x52 = some (.aluImm .add (8 : Fin 32) x0 0x0, 2) := by decide
theorem pa_at_54 : fetchRel jsonParseCode 0x54 = some (.aluImm .add (20 : Fin 32) (24 : Fin 32) 0x1, 4) := by decide
theorem pa_at_58 : fetchRel jsonParseCode 0x58 = some (.aluImm .add (21 : Fin 32) x0 0xF, 2) := by decide
theorem pa_at_5a : fetchRel jsonParseCode 0x5A = some (.alu .add (25 : Fin 32) x0 (26 : Fin 32), 2) := by decide
theorem pa_at_5c : fetchRel jsonParseCode 0x5C = some (.branch .beq (27 : Fin 32) (20 : Fin 32) 0x270, 4) := by decide
theorem pa_at_60 : fetchRel jsonParseCode 0x60 = some (.branch .bgeu (25 : Fin 32) (24 : Fin 32) 0x26C, 4) := by decide
theorem pa_at_64 : fetchRel jsonParseCode 0x64 = some (.alu .add a0 (23 : Fin 32) (25 : Fin 32), 4) := by decide
theorem pa_at_68 : fetchRel jsonParseCode 0x68 = some (.load .lbu a0 a0 0x0, 4) := by decide
theorem pa_at_6c : fetchRel jsonParseCode 0x6C = some (.aluImm .add a1 a0 0xFFFFFFDE, 4) := by decide
theorem pa_at_70 : fetchRel jsonParseCode 0x70 = some (.aluImm .add (27 : Fin 32) (27 : Fin 32) 0x1, 2) := by decide
theorem pa_at_72 : fetchRel jsonParseCode 0x72 = some (.branch .beq a1 x0 0x96, 2) := by decide
theorem pa_at_74 : fetchRel jsonParseCode 0x74 = some (.aluImm .add a1 a0 0xFFFFFFA5, 4) := by decide
theorem pa_at_78 : fetchRel jsonParseCode 0x78 = some (.aluImm .add (9 : Fin 32) a0 0xFFFFFF85, 4) := by decide
theorem pa_at_7c : fetchRel jsonParseCode 0x7C = some (.branch .beq a1 x0 0x16, 2) := by decide
theorem pa_at_7e : fetchRel jsonParseCode 0x7E = some (.aluImm .add a1 a0 0xFFFFFF9A, 4) := by decide
theorem pa_at_82 : fetchRel jsonParseCode 0x82 = some (.branch .beq a1 x0 0x58, 2) := by decide
theorem pa_at_84 : fetchRel jsonParseCode 0x84 = some (.aluImm .add a1 a0 0xFFFFFF92, 4) := by decide
theorem pa_at_88 : fetchRel jsonParseCode 0x88 = some (.branch .beq a1 x0 0x52, 2) := by decide
theorem pa_at_8a : fetchRel jsonParseCode 0x8A = some (.aluImm .add a1 a0 0xFFFFFF8C, 4) := by decide
theorem pa_at_8e : fetchRel jsonParseCode 0x8E = some (.branch .beq a1 x0 0x4C, 2) := by decide
theorem pa_at_90 : fetchRel jsonParseCode 0x90 = some (.branch .bne (9 : Fin 32) x0 0x5C, 2) := by decide
theorem pa_at_92 : fetchRel jsonParseCode 0x92 = some (.branch .bltu (21 : Fin 32) (8 : Fin 32) 0x23A, 4) := by decide
theorem pa_at_96 : fetchRel jsonParseCode 0x96 = some (.aluImm .sll a0 (8 : Fin 32) 0x3, 4) := by decide
theorem pa_at_9a : fetchRel jsonParseCode 0x9A = some (.aluImm .add a1 sp 0x10, 2) := by decide
theorem pa_at_9c : fetchRel jsonParseCode 0x9C = some (.alu .add a0 a0 a1, 2) := by decide
theorem pa_at_9e : fetchRel jsonParseCode 0x9E = some (.aluImm .sltu a1 (9 : Fin 32) 0x1, 4) := by decide
theorem pa_at_a2 : fetchRel jsonParseCode 0xA2 = some (.store .sw a0 (25 : Fin 32) 0x0, 4) := by decide
theorem pa_at_a6 : fetchRel jsonParseCode 0xA6 = some (.store .sb a0 a1 0x4, 4) := by decide
theorem pa_at_aa : fetchRel jsonParseCode 0xAA = some (.aluImm .add (25 : Fin 32) (25 : Fin 32) 0x1, 2) := by decide
theorem pa_at_ac : fetchRel jsonParseCode 0xAC = some (.branch .bne (19 : Fin 32) x0 0x14, 4) := by decide
theorem pa_at_b0 : fetchRel jsonParseCode 0xB0 = some (.alu .add a0 x0 (23 : Fin 32), 2) := by decide
theorem pa_at_b2 : fetchRel jsonParseCode 0xB2 = some (.alu .add a1 x0 (24 : Fin 32), 2) := by decide
theorem pa_at_b4 : fetchRel jsonParseCode 0xB4 = some (.alu .add a2 x0 (25 : Fin 32), 2) := by decide
theorem pa_at_b6 : fetchRel jsonParseCode 0xB6 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem pa_at_ba : fetchRel jsonParseCode 0xBA = some (.jalr ra ra 0xFFFFFB5A, 4) := by decide
theorem pa_at_be : fetchRel jsonParseCode 0xBE = some (.alu .add (25 : Fin 32) x0 a0, 2) := by decide
theorem pa_at_c0 : fetchRel jsonParseCode 0xC0 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x1, 2) := by decide
theorem pa_at_c2 : fetchRel jsonParseCode 0xC2 = some (.alu .add a0 (23 : Fin 32) (25 : Fin 32), 4) := by decide
theorem pa_at_c6 : fetchRel jsonParseCode 0xC6 = some (.branch .bne (9 : Fin 32) x0 0x192, 4) := by decide
theorem pa_at_ca : fetchRel jsonParseCode 0xCA = some (.branch .bgeu (25 : Fin 32) (24 : Fin 32) 0x1D6, 4) := by decide
theorem pa_at_ce : fetchRel jsonParseCode 0xCE = some (.load .lbu a0 a0 0x0, 4) := by decide
theorem pa_at_d2 : fetchRel jsonParseCode 0xD2 = some (.aluImm .add a0 a0 0xFFFFFF83, 4) := by decide
theorem pa_at_d6 : fetchRel jsonParseCode 0xD6 = some (.branch .beq a0 x0 0x4E, 2) := by decide
theorem pa_at_d8 : fetchRel jsonParseCode 0xD8 = some (.jal x0 0x1C8, 2) := by decide
theorem pa_at_da : fetchRel jsonParseCode 0xDA = some (.aluImm .add a0 sp 0xA8, 2) := by decide
theorem pa_at_dc : fetchRel jsonParseCode 0xDC = some (.alu .add a1 x0 (23 : Fin 32), 2) := by decide
theorem pa_at_de : fetchRel jsonParseCode 0xDE = some (.alu .add a2 x0 (24 : Fin 32), 2) := by decide
theorem pa_at_e0 : fetchRel jsonParseCode 0xE0 = some (.alu .add a3 x0 (25 : Fin 32), 2) := by decide
theorem pa_at_e2 : fetchRel jsonParseCode 0xE2 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem pa_at_e6 : fetchRel jsonParseCode 0xE6 = some (.jalr ra ra 0xFFFFFA24, 4) := by decide
theorem pa_at_ea : fetchRel jsonParseCode 0xEA = some (.jal x0 0x30, 2) := by decide
theorem pa_at_ec : fetchRel jsonParseCode 0xEC = some (.aluImm .add a0 a0 0xFFFFFFD0, 4) := by decide
theorem pa_at_f0 : fetchRel jsonParseCode 0xF0 = some (.aluImm .add a1 x0 0xA, 2) := by decide
theorem pa_at_f2 : fetchRel jsonParseCode 0xF2 = some (.branch .bgeu a0 a1 0x1DA, 4) := by decide
theorem pa_at_f6 : fetchRel jsonParseCode 0xF6 = some (.aluImm .add a0 sp 0xA8, 2) := by decide
theorem pa_at_f8 : fetchRel jsonParseCode 0xF8 = some (.alu .add a1 x0 (23 : Fin 32), 2) := by decide
theorem pa_at_fa : fetchRel jsonParseCode 0xFA = some (.alu .add a2 x0 (24 : Fin 32), 2) := by decide
theorem pa_at_fc : fetchRel jsonParseCode 0xFC = some (.alu .add a3 x0 (25 : Fin 32), 2) := by decide
theorem pa_at_fe : fetchRel jsonParseCode 0xFE = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem pa_at_102 : fetchRel jsonParseCode 0x102 = some (.jalr ra ra 0xFFFFFAA4, 4) := by decide
theorem pa_at_106 : fetchRel jsonParseCode 0x106 = some (.jal x0 0x14, 2) := by decide
theorem pa_at_108 : fetchRel jsonParseCode 0x108 = some (.aluImm .add a0 sp 0xA8, 2) := by decide
theorem pa_at_10a : fetchRel jsonParseCode 0x10A = some (.alu .add a1 x0 (23 : Fin 32), 2) := by decide
theorem pa_at_10c : fetchRel jsonParseCode 0x10C = some (.alu .add a2 x0 (24 : Fin 32), 2) := by decide
theorem pa_at_10e : fetchRel jsonParseCode 0x10E = some (.alu .add a3 x0 (25 : Fin 32), 2) := by decide
theorem pa_at_110 : fetchRel jsonParseCode 0x110 = some (.alu .add a4 x0 (19 : Fin 32), 2) := by decide
theorem pa_at_112 : fetchRel jsonParseCode 0x112 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem pa_at_116 : fetchRel jsonParseCode 0x116 = some (.jalr ra ra 0x782, 4) := by decide
theorem pa_at_11a : fetchRel jsonParseCode 0x11A = some (.load .lbu a0 sp 0xA8, 4) := by decide
theorem pa_at_11e : fetchRel jsonParseCode 0x11E = some (.branch .bne a0 x0 0x1E0, 4) := by decide
theorem pa_at_122 : fetchRel jsonParseCode 0x122 = some (.load .lw (25 : Fin 32) sp 0xAC, 2) := by decide
theorem pa_at_124 : fetchRel jsonParseCode 0x124 = some (.alu .add (22 : Fin 32) x0 (8 : Fin 32), 2) := by decide
theorem pa_at_126 : fetchRel jsonParseCode 0x126 = some (.store .sw sp (18 : Fin 32) 0xC, 2) := by decide
theorem pa_at_128 : fetchRel jsonParseCode 0x128 = some (.aluImm .add (21 : Fin 32) x0 0x0, 2) := by decide
theorem pa_at_12a : fetchRel jsonParseCode 0x12A = some (.alu .add (8 : Fin 32) x0 (22 : Fin 32), 2) := by decide
theorem pa_at_12c : fetchRel jsonParseCode 0x12C = some (.aluImm .add a0 x0 0x11, 2) := by decide
theorem pa_at_12e : fetchRel jsonParseCode 0x12E = some (.branch .beq (21 : Fin 32) a0 0x13E, 4) := by decide
theorem pa_at_132 : fetchRel jsonParseCode 0x132 = some (.alu .add a0 x0 (25 : Fin 32), 2) := by decide
theorem pa_at_134 : fetchRel jsonParseCode 0x134 = some (.branch .bne (19 : Fin 32) x0 0x12, 4) := by decide
theorem pa_at_138 : fetchRel jsonParseCode 0x138 = some (.alu .add a0 x0 (23 : Fin 32), 2) := by decide
theorem pa_at_13a : fetchRel jsonParseCode 0x13A = some (.alu .add a1 x0 (24 : Fin 32), 2) := by decide
theorem pa_at_13c : fetchRel jsonParseCode 0x13C = some (.alu .add a2 x0 (25 : Fin 32), 2) := by decide
theorem pa_at_13e : fetchRel jsonParseCode 0x13E = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem pa_at_142 : fetchRel jsonParseCode 0x142 = some (.jalr ra ra 0xFFFFFAD2, 4) := by decide
theorem pa_at_146 : fetchRel jsonParseCode 0x146 = some (.branch .beq (8 : Fin 32) x0 0x18C, 4) := by decide
theorem pa_at_14a : fetchRel jsonParseCode 0x14A = some (.aluImm .add a1 x0 0x10, 2) := by decide
theorem pa_at_14c : fetchRel jsonParseCode 0x14C = some (.branch .bltu a1 (22 : Fin 32) 0x1A2, 4) := by decide
theorem pa_at_150 : fetchRel jsonParseCode 0x150 = some (.branch .bgeu a0 (24 : Fin 32) 0x19E, 4) := by decide
theorem pa_at_154 : fetchRel jsonParseCode 0x154 = some (.aluImm .add (20 : Fin 32) (8 : Fin 32) 0xFFFFFFFF, 4) := by decide
theorem pa_at_158 : fetchRel jsonParseCode 0x158 = some (.alu .add a1 (23 : Fin 32) a0, 4) := by decide
theorem pa_at_15c : fetchRel jsonParseCode 0x15C = some (.aluImm .sll a3 (20 : Fin 32) 0x3, 4) := by decide
theorem pa_at_160 : fetchRel jsonParseCode 0x160 = some (.load .lbu a2 a1 0x0, 4) := by decide
theorem pa_at_164 : fetchRel jsonParseCode 0x164 = some (.aluImm .add a1 sp 0x10, 2) := by decide
theorem pa_at_166 : fetchRel jsonParseCode 0x166 = some (.alu .add a1 a1 a3, 2) := by decide
theorem pa_at_168 : fetchRel jsonParseCode 0x168 = some (.load .lbu (9 : Fin 32) a1 0x4, 4) := by decide
theorem pa_at_16c : fetchRel jsonParseCode 0x16C = some (.aluImm .add a3 a2 0xFFFFFFA3, 4) := by decide
theorem pa_at_170 : fetchRel jsonParseCode 0x170 = some (.aluImm .add (21 : Fin 32) (21 : Fin 32) 0x1, 2) := by decide
theorem pa_at_172 : fetchRel jsonParseCode 0x172 = some (.branch .beq a3 x0 0xCA, 2) := by decide
theorem pa_at_174 : fetchRel jsonParseCode 0x174 = some (.aluImm .add a3 a2 0xFFFFFF83, 4) := by decide
theorem pa_at_178 : fetchRel jsonParseCode 0x178 = some (.branch .bne a3 x0 0xFE, 2) := by decide
theorem pa_at_17a : fetchRel jsonParseCode 0x17A = some (.branch .beq (9 : Fin 32) x0 0x174, 4) := by decide
theorem pa_at_17e : fetchRel jsonParseCode 0x17E = some (.load .lw a1 a1 0x0, 2) := by decide
theorem pa_at_180 : fetchRel jsonParseCode 0x180 = some (.aluImm .add (25 : Fin 32) a0 0x1, 4) := by decide
theorem pa_at_184 : fetchRel jsonParseCode 0x184 = some (.branch .bltu (25 : Fin 32) a1 0x16A, 4) := by decide
theorem pa_at_188 : fetchRel jsonParseCode 0x188 = some (.alu .sub a2 (25 : Fin 32) a1, 4) := by decide
theorem pa_at_18c : fetchRel jsonParseCode 0x18C = some (.alu .add a1 a1 (23 : Fin 32), 2) := by decide
theorem pa_at_18e : fetchRel jsonParseCode 0x18E = some (.aluImm .add a0 sp 0xA8, 2) := by decide
theorem pa_at_190 : fetchRel jsonParseCode 0x190 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem pa_at_194 : fetchRel jsonParseCode 0x194 = some (.jalr ra ra 0x288, 4) := by decide
theorem pa_at_198 : fetchRel jsonParseCode 0x198 = some (.load .lw (9 : Fin 32) sp 0xA8, 2) := by decide
theorem pa_at_19a : fetchRel jsonParseCode 0x19A = some (.load .lbu (18 : Fin 32) sp 0xAC, 4) := by decide
theorem pa_at_19e : fetchRel jsonParseCode 0x19E = some (.branch .beq (9 : Fin 32) x0 0xA8, 2) := by decide
theorem pa_at_1a0 : fetchRel jsonParseCode 0x1A0 = some (.store .sw sp (26 : Fin 32) 0x8, 2) := by decide
theorem pa_at_1a2 : fetchRel jsonParseCode 0x1A2 = some (.aluImm .add a2 x0 0x7, 2) := by decide
theorem pa_at_1a4 : fetchRel jsonParseCode 0x1A4 = some (.aluImm .add a0 sp 0x95, 4) := by decide
theorem pa_at_1a8 : fetchRel jsonParseCode 0x1A8 = some (.aluImm .add a1 sp 0xAD, 4) := by decide
theorem pa_at_1ac : fetchRel jsonParseCode 0x1AC = some (.auipc ra 0xB000, 4) := by decide
theorem pa_at_1b0 : fetchRel jsonParseCode 0x1B0 = some (.jalr ra ra 0x1A0, 4) := by decide
theorem pa_at_1b4 : fetchRel jsonParseCode 0x1B4 = some (.aluImm .add (8 : Fin 32) x0 0x0, 2) := by decide
theorem pa_at_1b6 : fetchRel jsonParseCode 0x1B6 = some (.store .sw sp (9 : Fin 32) 0x90, 2) := by decide
theorem pa_at_1b8 : fetchRel jsonParseCode 0x1B8 = some (.store .sb sp (18 : Fin 32) 0x94, 4) := by decide
theorem pa_at_1bc : fetchRel jsonParseCode 0x1BC = some (.alu .add (9 : Fin 32) x0 (18 : Fin 32), 2) := by decide
theorem pa_at_1be : fetchRel jsonParseCode 0x1BE = some (.alu .add (26 : Fin 32) x0 (8 : Fin 32), 2) := by decide
theorem pa_at_1c0 : fetchRel jsonParseCode 0x1C0 = some (.aluImm .add a0 sp 0xA8, 2) := by decide
theorem pa_at_1c2 : fetchRel jsonParseCode 0x1C2 = some (.aluImm .add a1 sp 0x90, 2) := by decide
theorem pa_at_1c4 : fetchRel jsonParseCode 0x1C4 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem pa_at_1c8 : fetchRel jsonParseCode 0x1C8 = some (.jalr ra ra 0x5E6, 4) := by decide
theorem pa_at_1cc : fetchRel jsonParseCode 0x1CC = some (.load .lbu a0 sp 0xA8, 4) := by decide
theorem pa_at_1d0 : fetchRel jsonParseCode 0x1D0 = some (.branch .bne a0 x0 0xEC, 2) := by decide
theorem pa_at_1d2 : fetchRel jsonParseCode 0x1D2 = some (.load .lw (8 : Fin 32) sp 0xAC, 2) := by decide
theorem pa_at_1d4 : fetchRel jsonParseCode 0x1D4 = some (.branch .beq (8 : Fin 32) x0 0x7E, 2) := by decide
theorem pa_at_1d6 : fetchRel jsonParseCode 0x1D6 = some (.load .lw (18 : Fin 32) sp 0xB0, 2) := by decide
theorem pa_at_1d8 : fetchRel jsonParseCode 0x1D8 = some (.branch .beq (19 : Fin 32) x0 0x28, 4) := by decide
theorem pa_at_1dc : fetchRel jsonParseCode 0x1DC = some (.branch .beq (26 : Fin 32) x0 0xFFFFFFE0, 4) := by decide
theorem pa_at_1e0 : fetchRel jsonParseCode 0x1E0 = some (.alu .add a2 x0 (9 : Fin 32), 2) := by decide
theorem pa_at_1e2 : fetchRel jsonParseCode 0x1E2 = some (.branch .bltu (9 : Fin 32) (18 : Fin 32) 0x6, 4) := by decide
theorem pa_at_1e6 : fetchRel jsonParseCode 0x1E6 = some (.alu .add a2 x0 (18 : Fin 32), 2) := by decide
theorem pa_at_1e8 : fetchRel jsonParseCode 0x1E8 = some (.alu .add a0 x0 (26 : Fin 32), 2) := by decide
theorem pa_at_1ea : fetchRel jsonParseCode 0x1EA = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem pa_at_1ec : fetchRel jsonParseCode 0x1EC = some (.auipc ra 0xB000, 4) := by decide
theorem pa_at_1f0 : fetchRel jsonParseCode 0x1F0 = some (.jalr ra ra 0xD8, 4) := by decide
theorem pa_at_1f4 : fetchRel jsonParseCode 0x1F4 = some (.branch .bne a0 x0 0x6, 2) := by decide
theorem pa_at_1f6 : fetchRel jsonParseCode 0x1F6 = some (.alu .sub a0 (9 : Fin 32) (18 : Fin 32), 4) := by decide
theorem pa_at_1fa : fetchRel jsonParseCode 0x1FA = some (.branch .blt a0 x0 0xFFFFFFC2, 4) := by decide
theorem pa_at_1fe : fetchRel jsonParseCode 0x1FE = some (.jal x0 0x12A, 2) := by decide
theorem pa_at_200 : fetchRel jsonParseCode 0x200 = some (.load .lw a0 sp 0x90, 2) := by decide
theorem pa_at_202 : fetchRel jsonParseCode 0x202 = some (.load .lw a1 sp 0x94, 2) := by decide
theorem pa_at_204 : fetchRel jsonParseCode 0x204 = some (.load .lw a2 sp 0x98, 2) := by decide
theorem pa_at_206 : fetchRel jsonParseCode 0x206 = some (.store .sw sp a0 0x9C, 2) := by decide
theorem pa_at_208 : fetchRel jsonParseCode 0x208 = some (.store .sw sp a1 0xA0, 2) := by decide
theorem pa_at_20a : fetchRel jsonParseCode 0x20A = some (.store .sw sp a2 0xA4, 2) := by decide
theorem pa_at_20c : fetchRel jsonParseCode 0x20C = some (.aluImm .add (9 : Fin 32) x0 0x1, 2) := by decide
theorem pa_at_20e : fetchRel jsonParseCode 0x20E = some (.aluImm .add a0 sp 0xA8, 2) := by decide
theorem pa_at_210 : fetchRel jsonParseCode 0x210 = some (.aluImm .add a1 sp 0x9C, 2) := by decide
theorem pa_at_212 : fetchRel jsonParseCode 0x212 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem pa_at_216 : fetchRel jsonParseCode 0x216 = some (.jalr ra ra 0x598, 4) := by decide
theorem pa_at_21a : fetchRel jsonParseCode 0x21A = some (.load .lbu a0 sp 0xA8, 4) := by decide
theorem pa_at_21e : fetchRel jsonParseCode 0x21E = some (.branch .bne a0 x0 0x9E, 2) := by decide
theorem pa_at_220 : fetchRel jsonParseCode 0x220 = some (.load .lw a0 sp 0xAC, 2) := by decide
theorem pa_at_222 : fetchRel jsonParseCode 0x222 = some (.branch .beq a0 x0 0x14, 2) := by decide
theorem pa_at_224 : fetchRel jsonParseCode 0x224 = some (.load .lw a1 sp 0xB0, 2) := by decide
theorem pa_at_226 : fetchRel jsonParseCode 0x226 = some (.alu .add a2 x0 (8 : Fin 32), 2) := by decide
theorem pa_at_228 : fetchRel jsonParseCode 0x228 = some (.alu .add a3 x0 (18 : Fin 32), 2) := by decide
theorem pa_at_22a : fetchRel jsonParseCode 0x22A = some (.auipc ra 0x0, 4) := by decide
theorem pa_at_22e : fetchRel jsonParseCode 0x22E = some (.jalr ra ra 0xFFFFFDC0, 4) := by decide
theorem pa_at_232 : fetchRel jsonParseCode 0x232 = some (.alu .and (9 : Fin 32) (9 : Fin 32) a0, 2) := by decide
theorem pa_at_234 : fetchRel jsonParseCode 0x234 = some (.jal x0 0xFFFFFFDA, 2) := by decide
theorem pa_at_236 : fetchRel jsonParseCode 0x236 = some (.aluImm .and (9 : Fin 32) (9 : Fin 32) 0x1, 2) := by decide
theorem pa_at_238 : fetchRel jsonParseCode 0x238 = some (.branch .bne (9 : Fin 32) x0 0xFFFFFF84, 2) := by decide
theorem pa_at_23a : fetchRel jsonParseCode 0x23A = some (.jal x0 0xEE, 2) := by decide
theorem pa_at_23c : fetchRel jsonParseCode 0x23C = some (.branch .bne (9 : Fin 32) x0 0xB2, 2) := by decide
theorem pa_at_23e : fetchRel jsonParseCode 0x23E = some (.aluImm .add (25 : Fin 32) a0 0x1, 4) := by decide
theorem pa_at_242 : fetchRel jsonParseCode 0x242 = some (.alu .add (8 : Fin 32) x0 (20 : Fin 32), 2) := by decide
theorem pa_at_244 : fetchRel jsonParseCode 0x244 = some (.jal x0 0xFFFFFEE8, 2) := by decide
theorem pa_at_246 : fetchRel jsonParseCode 0x246 = some (.aluImm .add a0 (18 : Fin 32) 0xFFFFFF01, 4) := by decide
theorem pa_at_24a : fetchRel jsonParseCode 0x24A = some (.alu .add (8 : Fin 32) x0 (20 : Fin 32), 2) := by decide
theorem pa_at_24c : fetchRel jsonParseCode 0x24C = some (.branch .beq a0 x0 0xFFFFFEE0, 4) := by decide
theorem pa_at_250 : fetchRel jsonParseCode 0x250 = some (.jal x0 0x70, 2) := by decide
theorem pa_at_252 : fetchRel jsonParseCode 0x252 = some (.alu .add (8 : Fin 32) x0 (20 : Fin 32), 2) := by decide
theorem pa_at_254 : fetchRel jsonParseCode 0x254 = some (.load .lw (26 : Fin 32) sp 0x8, 2) := by decide
theorem pa_at_256 : fetchRel jsonParseCode 0x256 = some (.jal x0 0xFFFFFED6, 2) := by decide
theorem pa_at_258 : fetchRel jsonParseCode 0x258 = some (.branch .bgeu (25 : Fin 32) (24 : Fin 32) 0xFFFFFE04, 4) := by decide
theorem pa_at_25c : fetchRel jsonParseCode 0x25C = some (.load .lbu a0 a0 0x0, 4) := by decide
theorem pa_at_260 : fetchRel jsonParseCode 0x260 = some (.aluImm .add a0 a0 0xFFFFFFA3, 4) := by decide
theorem pa_at_264 : fetchRel jsonParseCode 0x264 = some (.alu .add (22 : Fin 32) x0 (8 : Fin 32), 2) := by decide
theorem pa_at_266 : fetchRel jsonParseCode 0x266 = some (.branch .bne a0 x0 0xFFFFFDF6, 4) := by decide
theorem pa_at_26a : fetchRel jsonParseCode 0x26A = some (.jal x0 0xFFFFFEBC, 2) := by decide
theorem pa_at_26c : fetchRel jsonParseCode 0x26C = some (.load .lw (18 : Fin 32) sp 0xC, 2) := by decide
theorem pa_at_26e : fetchRel jsonParseCode 0x26E = some (.aluImm .add (20 : Fin 32) (24 : Fin 32) 0x1, 4) := by decide
theorem pa_at_272 : fetchRel jsonParseCode 0x272 = some (.aluImm .add (21 : Fin 32) x0 0xF, 2) := by decide
theorem pa_at_274 : fetchRel jsonParseCode 0x274 = some (.jal x0 0xFFFFFDE8, 2) := by decide
theorem pa_at_276 : fetchRel jsonParseCode 0x276 = some (.aluImm .add a1 a2 0xFFFFFFD4, 4) := by decide
theorem pa_at_27a : fetchRel jsonParseCode 0x27A = some (.branch .bne a1 x0 0x74, 2) := by decide
theorem pa_at_27c : fetchRel jsonParseCode 0x27C = some (.aluImm .add (25 : Fin 32) a0 0x1, 4) := by decide
theorem pa_at_280 : fetchRel jsonParseCode 0x280 = some (.branch .bne (19 : Fin 32) x0 0x14, 4) := by decide
theorem pa_at_284 : fetchRel jsonParseCode 0x284 = some (.alu .add a0 x0 (23 : Fin 32), 2) := by decide
theorem pa_at_286 : fetchRel jsonParseCode 0x286 = some (.alu .add a1 x0 (24 : Fin 32), 2) := by decide
theorem pa_at_288 : fetchRel jsonParseCode 0x288 = some (.alu .add a2 x0 (25 : Fin 32), 2) := by decide
theorem pa_at_28a : fetchRel jsonParseCode 0x28A = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem pa_at_28e : fetchRel jsonParseCode 0x28E = some (.jalr ra ra 0xFFFFF986, 4) := by decide
theorem pa_at_292 : fetchRel jsonParseCode 0x292 = some (.alu .add (25 : Fin 32) x0 a0, 2) := by decide
theorem pa_at_294 : fetchRel jsonParseCode 0x294 = some (.aluImm .add (20 : Fin 32) (24 : Fin 32) 0x1, 4) := by decide
theorem pa_at_298 : fetchRel jsonParseCode 0x298 = some (.aluImm .add (21 : Fin 32) x0 0xF, 2) := by decide
theorem pa_at_29a : fetchRel jsonParseCode 0x29A = some (.load .lw (18 : Fin 32) sp 0xC, 2) := by decide
theorem pa_at_29c : fetchRel jsonParseCode 0x29C = some (.branch .beq (9 : Fin 32) x0 0xFFFFFDC0, 4) := by decide
theorem pa_at_2a0 : fetchRel jsonParseCode 0x2A0 = some (.aluImm .add a0 sp 0xA8, 2) := by decide
theorem pa_at_2a2 : fetchRel jsonParseCode 0x2A2 = some (.alu .add a1 x0 (23 : Fin 32), 2) := by decide
theorem pa_at_2a4 : fetchRel jsonParseCode 0x2A4 = some (.alu .add a2 x0 (24 : Fin 32), 2) := by decide
theorem pa_at_2a6 : fetchRel jsonParseCode 0x2A6 = some (.alu .add a3 x0 (25 : Fin 32), 2) := by decide
theorem pa_at_2a8 : fetchRel jsonParseCode 0x2A8 = some (.alu .add a4 x0 (19 : Fin 32), 2) := by decide
theorem pa_at_2aa : fetchRel jsonParseCode 0x2AA = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem pa_at_2ae : fetchRel jsonParseCode 0x2AE = some (.jalr ra ra 0x644, 4) := by decide
theorem pa_at_2b2 : fetchRel jsonParseCode 0x2B2 = some (.load .lbu a0 sp 0xA8, 4) := by decide
theorem pa_at_2b6 : fetchRel jsonParseCode 0x2B6 = some (.branch .bne a0 x0 0x48, 2) := by decide
theorem pa_at_2b8 : fetchRel jsonParseCode 0x2B8 = some (.load .lw (25 : Fin 32) sp 0xAC, 2) := by decide
theorem pa_at_2ba : fetchRel jsonParseCode 0x2BA = some (.jal x0 0xFFFFFDA2, 2) := by decide
theorem pa_at_2bc : fetchRel jsonParseCode 0x2BC = some (.load .lbu (18 : Fin 32) sp 0xA9, 4) := by decide
theorem pa_at_2c0 : fetchRel jsonParseCode 0x2C0 = some (.load .lw a0 sp 0xC, 2) := by decide
theorem pa_at_2c2 : fetchRel jsonParseCode 0x2C2 = some (.store .sw a0 x0 0x0, 4) := by decide
theorem pa_at_2c6 : fetchRel jsonParseCode 0x2C6 = some (.store .sb a0 (18 : Fin 32) 0x4, 4) := by decide
theorem pa_at_2ca : fetchRel jsonParseCode 0x2CA = some (.jal x0 0x40, 2) := by decide
theorem pa_at_2cc : fetchRel jsonParseCode 0x2CC = some (.aluImm .add a0 x0 0x20, 4) := by decide
theorem pa_at_2d0 : fetchRel jsonParseCode 0x2D0 = some (.jal x0 0x32, 2) := by decide
theorem pa_at_2d2 : fetchRel jsonParseCode 0x2D2 = some (.branch .bne a0 (24 : Fin 32) 0x1C, 4) := by decide
theorem pa_at_2d6 : fetchRel jsonParseCode 0x2D6 = some (.load .lw a1 sp 0xC, 2) := by decide
theorem pa_at_2d8 : fetchRel jsonParseCode 0x2D8 = some (.branch .bltu (25 : Fin 32) (26 : Fin 32) 0x56, 4) := by decide
theorem pa_at_2dc : fetchRel jsonParseCode 0x2DC = some (.branch .bltu (24 : Fin 32) (25 : Fin 32) 0x52, 4) := by decide
theorem pa_at_2e0 : fetchRel jsonParseCode 0x2E0 = some (.alu .add (23 : Fin 32) (23 : Fin 32) (26 : Fin 32), 2) := by decide
theorem pa_at_2e2 : fetchRel jsonParseCode 0x2E2 = some (.alu .sub a0 (25 : Fin 32) (26 : Fin 32), 4) := by decide
theorem pa_at_2e6 : fetchRel jsonParseCode 0x2E6 = some (.store .sw a1 (23 : Fin 32) 0x0, 4) := by decide
theorem pa_at_2ea : fetchRel jsonParseCode 0x2EA = some (.store .sw a1 a0 0x4, 2) := by decide
theorem pa_at_2ec : fetchRel jsonParseCode 0x2EC = some (.jal x0 0x1E, 2) := by decide
theorem pa_at_2ee : fetchRel jsonParseCode 0x2EE = some (.aluImm .add a0 x0 0x20, 4) := by decide
theorem pa_at_2f2 : fetchRel jsonParseCode 0x2F2 = some (.load .lw a1 sp 0xC, 2) := by decide
theorem pa_at_2f4 : fetchRel jsonParseCode 0x2F4 = some (.store .sw a1 x0 0x0, 4) := by decide
theorem pa_at_2f8 : fetchRel jsonParseCode 0x2F8 = some (.store .sb a1 a0 0x4, 4) := by decide
theorem pa_at_2fc : fetchRel jsonParseCode 0x2FC = some (.jal x0 0xE, 2) := by decide
theorem pa_at_2fe : fetchRel jsonParseCode 0x2FE = some (.load .lbu a0 sp 0xA9, 4) := by decide
theorem pa_at_302 : fetchRel jsonParseCode 0x302 = some (.store .sw (18 : Fin 32) x0 0x0, 4) := by decide
theorem pa_at_306 : fetchRel jsonParseCode 0x306 = some (.store .sb (18 : Fin 32) a0 0x4, 4) := by decide
theorem pa_at_30a : fetchRel jsonParseCode 0x30A = some (.load .lw ra sp 0xEC, 2) := by decide
theorem pa_at_30c : fetchRel jsonParseCode 0x30C = some (.load .lw (8 : Fin 32) sp 0xE8, 2) := by decide
theorem pa_at_30e : fetchRel jsonParseCode 0x30E = some (.load .lw (9 : Fin 32) sp 0xE4, 2) := by decide
theorem pa_at_310 : fetchRel jsonParseCode 0x310 = some (.load .lw (18 : Fin 32) sp 0xE0, 2) := by decide
theorem pa_at_312 : fetchRel jsonParseCode 0x312 = some (.load .lw (19 : Fin 32) sp 0xDC, 2) := by decide
theorem pa_at_314 : fetchRel jsonParseCode 0x314 = some (.load .lw (20 : Fin 32) sp 0xD8, 2) := by decide
theorem pa_at_316 : fetchRel jsonParseCode 0x316 = some (.load .lw (21 : Fin 32) sp 0xD4, 2) := by decide
theorem pa_at_318 : fetchRel jsonParseCode 0x318 = some (.load .lw (22 : Fin 32) sp 0xD0, 2) := by decide
theorem pa_at_31a : fetchRel jsonParseCode 0x31A = some (.load .lw (23 : Fin 32) sp 0xCC, 2) := by decide
theorem pa_at_31c : fetchRel jsonParseCode 0x31C = some (.load .lw (24 : Fin 32) sp 0xC8, 2) := by decide
theorem pa_at_31e : fetchRel jsonParseCode 0x31E = some (.load .lw (25 : Fin 32) sp 0xC4, 2) := by decide
theorem pa_at_320 : fetchRel jsonParseCode 0x320 = some (.load .lw (26 : Fin 32) sp 0xC0, 2) := by decide
theorem pa_at_322 : fetchRel jsonParseCode 0x322 = some (.load .lw (27 : Fin 32) sp 0xBC, 2) := by decide
theorem pa_at_324 : fetchRel jsonParseCode 0x324 = some (.aluImm .add sp sp 0xF0, 2) := by decide
theorem pa_at_326 : fetchRel jsonParseCode 0x326 = some (.jalr x0 ra 0x0, 2) := by decide
theorem pa_at_328 : fetchRel jsonParseCode 0x328 = some (.aluImm .add (18 : Fin 32) x0 0x20, 4) := by decide
theorem pa_at_32c : fetchRel jsonParseCode 0x32C = some (.jal x0 0xFFFFFF94, 2) := by decide
theorem pa_at_32e : fetchRel jsonParseCode 0x32E = some (.aluImm .add a0 x0 0x20, 4) := by decide
theorem pa_at_332 : fetchRel jsonParseCode 0x332 = some (.jal x0 0xFFFFFFC2, 2) := by decide

/-- `memcmp`'s result on the `n` bytes at `p` and `q`: 0 when they are
equal, or the difference of the first two bytes that differ. -/
def CmpRes (M : Word → BitVec 8) (p q : Word) (n : Nat) (v : Word) : Prop :=
  (v = 0 ∧ ∀ i, i < n → M (p + BitVec.ofNat 32 i) = M (q + BitVec.ofNat 32 i)) ∨
  ∃ i, i < n ∧ (∀ j, j < i → M (p + BitVec.ofNat 32 j) = M (q + BitVec.ofNat 32 j)) ∧
    M (p + BitVec.ofNat 32 i) ≠ M (q + BitVec.ofNat 32 i) ∧
    v = aluEval .sub ((M (p + BitVec.ofNat 32 i)).zeroExtend 32) ((M (q + BitVec.ofNat 32 i)).zeroExtend 32)

/-- **`memcmp`** returns `CmpRes` of its bytes. -/
theorem memcmp_cmp (m : Machine) {base retAddr p q : Word} {n : Nat} (hc : CodeIn m.mem base memcmpCode)
    (hpc : m.pc = base) (ha0 : reg m a0 = p) (ha1 : reg m a1 = q) (ha2 : reg m a2 = BitVec.ofNat 32 n)
    (hn : n < 2 ^ 32) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      CmpRes m.mem p q n (reg m' a0) ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → reg m' r = reg m r) ∧ m'.mem = m.mem := by
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  -- the loop, from byte `i` with `k` bytes left
  have loop : ∀ k i, i + k = n → 0 < k → ∀ {n1 : Machine}, St m.mem base n1 0x2 (reg n1) →
      reg n1 a0 = p + BitVec.ofNat 32 i → reg n1 a1 = q + BitVec.ofNat 32 i → reg n1 a2 = BitVec.ofNat 32 k →
      reg n1 ra = retAddr →
      (∀ j, j < i → m.mem (p + BitVec.ofNat 32 j) = m.mem (q + BitVec.ofNat 32 j)) →
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → reg n1 r = reg m r) →
      ∃ m', Steps n1 m' ∧ m'.pc = retAddr ∧
        CmpRes m.mem p q n (reg m' a0) ∧
        (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → reg m' r = reg m r) ∧ m'.mem = m.mem := by
    intro k
    induction k with
    | zero => intro i _ hk; exact absurd hk (Nat.lt_irrefl 0)
    | succ k ih =>
      intro i hik _ n1 s1 r0 r1 r2 rra heq hkeep
      obtain ⟨n2, d2, u2⟩ := s1.lbu hc mcx_at_2 (off' := 6) (by decide)
      obtain ⟨n3, d3, u3⟩ := u2.lbu hc mcx_at_6 (off' := 0xA) (by decide)
      have e3 : upd (upd (reg n1) a3 ((m.mem (reg n1 a0 + 0)).zeroExtend 32)) a4
          ((m.mem (upd (reg n1) a3 ((m.mem (reg n1 a0 + 0)).zeroExtend 32) a1 + 0)).zeroExtend 32) a3 =
          (m.mem (p + BitVec.ofNat 32 i)).zeroExtend 32 := by
        simp +decide only [upd_app, ↓reduceIte]; rw [r0, add_lit_zero]
      have e4 : upd (upd (reg n1) a3 ((m.mem (reg n1 a0 + 0)).zeroExtend 32)) a4
          ((m.mem (upd (reg n1) a3 ((m.mem (reg n1 a0 + 0)).zeroExtend 32) a1 + 0)).zeroExtend 32) a4 =
          (m.mem (q + BitVec.ofNat 32 i)).zeroExtend 32 := by
        simp +decide only [upd_app, ↓reduceIte]; rw [r1, add_lit_zero]
      have k3 : ∀ r, r ≠ a3 → r ≠ a4 → upd (upd (reg n1) a3 ((m.mem (reg n1 a0 + 0)).zeroExtend 32)) a4
          ((m.mem (upd (reg n1) a3 ((m.mem (reg n1 a0 + 0)).zeroExtend 32) a1 + 0)).zeroExtend 32) r = reg n1 r :=
        fun r h3 h4 => by
          by_cases h0 : r.val = 0
          · have : r = 0 := Fin.ext h0
            subst this; simp [upd]; exact s1.zero.symm
          simp only [upd_app, h0, h3, h4, ite_false]
      have hi : i < n := by omega
      by_cases hd : m.mem (p + BitVec.ofNat 32 i) = m.mem (q + BitVec.ofNat 32 i)
      · obtain ⟨n4, d4, u4⟩ := u3.notTaken hc 0xE mcx_at_a (by decide) (by
          rw [e3, e4, hd]; simp only [branchTaken, bne_self_eq_false])
        obtain ⟨n5, c5, u5⟩ := St.block mcStep u4 hc mcStep_end (by simp [BlockOk, BInstr.ok, mcStep])
        simp only [runBlock, BInstr.run, mcStep] at u5
        have g5 : ∀ r, reg n5 r = _ := u5.regs
        have r25 : reg n5 a2 = BitVec.ofNat 32 k := by
          rw [g5]; simp +decide only [upd_app, ↓reduceIte]
          rw [r2, ev_add, show k + 1 = (k + 1) - 0 by rfl, mc_cnt (by omega) (by omega),
            show k + 1 - (0 + 1) = k by omega]
        have keep5 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → reg n5 r = reg m r :=
          fun r h0' h1' h2' h3' h4' => by
            rw [g5]
            by_cases h0 : r.val = 0
            · have : r = 0 := Fin.ext h0
              subst this; simp [upd]; exact hz.symm
            simp only [upd_app, h0, h0', h1', h2', h3', h4', ite_false]
            exact hkeep r h0' h1' h2' h3' h4'
        have heq' : ∀ j, j < i + 1 → m.mem (p + BitVec.ofNat 32 j) = m.mem (q + BitVec.ofNat 32 j) :=
          fun j hj => by
            rcases (by omega : j < i ∨ j = i) with h | h
            · exact heq j h
            · subst h; exact hd
        by_cases hk : k = 0
        · subst hk
          obtain ⟨n6, d6, u6⟩ := u5.self.notTaken hc 0x16 mcx_at_14 (by decide) (by
            rw [r25, u5.self.zero]; decide)
          obtain ⟨n7, d7, u7⟩ := u6.aluImm hc mcx_at_16 (off' := 0x18) (by decide)
          obtain ⟨n8, d8, pc8, mem8, regs8⟩ := u7.jalr hc mcx_at_18
          refine ⟨n8, .cons d2 (.cons d3 (.cons d4 (c5.trans (.cons d6 (.cons d7 (.single d8)))))), ?_, ?_,
            fun r h0' h1' h2' h3' h4' => ?_, mem8⟩
          · rw [pc8]; simp +decide only [upd_app, ↓reduceIte]
            rw [keep5 ra (by decide) (by decide) (by decide) (by decide) (by decide), add_lit_zero, hra, hret]
          · rw [regs8]; simp +decide only [upd_app, ↓reduceIte]
            rw [show reg n5 x0 = 0 from u5.self.zero]
            exact Or.inl ⟨rfl, fun j hj => heq' j (by omega)⟩
          · rw [regs8]
            by_cases h0 : r.val = 0
            · have : r = 0 := Fin.ext h0
              subst this; simp [upd]; exact hz.symm
            simp only [upd_app, h0, h0', ite_false]; exact keep5 r h0' h1' h2' h3' h4'
        · obtain ⟨n6, d6, u6⟩ := u5.self.taken hc 0x2 mcx_at_14 (by decide) (by
            rw [r25, u5.self.zero]; simp only [branchTaken, bne_iff_ne, ne_eq]; intro h
            have := congrArg BitVec.toNat h; rw [ofNat_tn (by omega)] at this; exact hk this)
          obtain ⟨m', c', h1, h2, h3, h4⟩ := ih (i + 1) (by omega) (by omega) u6.self
            (by rw [u6.regs, g5]; simp +decide only [upd_app, ↓reduceIte]; rw [r0, ev_add,
              show (1 : Word) = BitVec.ofNat 32 1 from rfl, add_ofNat_assoc])
            (by rw [u6.regs, g5]; simp +decide only [upd_app, ↓reduceIte]; rw [r1, ev_add,
              show (1 : Word) = BitVec.ofNat 32 1 from rfl, add_ofNat_assoc])
            (by rw [u6.regs]; exact r25)
            (by rw [u6.regs, keep5 ra (by decide) (by decide) (by decide) (by decide) (by decide), hra])
            heq' (fun r h0' h1' h2' h3' h4' => by rw [u6.regs]; exact keep5 r h0' h1' h2' h3' h4')
          exact ⟨m', .cons d2 (.cons d3 (.cons d4 (c5.trans (.cons d6 c')))), h1, h2, h3, h4⟩
      · obtain ⟨n4, d4, u4⟩ := u3.taken hc 0x1A mcx_at_a (by decide) (by
          rw [e3, e4]; simp only [branchTaken, bne_iff_ne, ne_eq]; intro h
          apply hd; apply BitVec.eq_of_toNat_eq
          have := congrArg BitVec.toNat h
          simp only [BitVec.toNat_setWidth] at this
          rwa [Nat.mod_eq_of_lt (by have := (m.mem (p + BitVec.ofNat 32 i)).isLt; omega),
            Nat.mod_eq_of_lt (by have := (m.mem (q + BitVec.ofNat 32 i)).isLt; omega)] at this)
        obtain ⟨n5, d5, u5⟩ := u4.alu hc mcx_at_1a (off' := 0x1E) (by decide)
        obtain ⟨n6, d6, pc6, mem6, regs6⟩ := u5.jalr hc mcx_at_1e
        refine ⟨n6, .cons d2 (.cons d3 (.cons d4 (.cons d5 (.single d6)))), ?_, ?_,
          fun r h0' h1' h2' h3' h4' => ?_, mem6⟩
        · rw [pc6]; simp +decide only [upd_app, ↓reduceIte]
          rw [rra, add_lit_zero, hret]
        · rw [regs6]; simp +decide only [upd_app, ↓reduceIte]
          rw [r0, r1, add_lit_zero, add_lit_zero]
          exact Or.inr ⟨i, hi, heq, hd, rfl⟩
        · rw [regs6]
          by_cases h0 : r.val = 0
          · have : r = 0 := Fin.ext h0
            subst this; simp [upd]; exact hz.symm
          simp only [upd_app, h0, h0', h3', h4', ite_false]; exact hkeep r h0' h1' h2' h3' h4'
  by_cases hn0 : n = 0
  · subst hn0
    obtain ⟨n1, d1, u1⟩ := s0.taken hc 0x16 mcx_at_0 (by decide) (by rw [ha2, hz]; decide)
    obtain ⟨n2, d2, u2⟩ := u1.aluImm hc mcx_at_16 (off' := 0x18) (by decide)
    obtain ⟨n3, d3, pc3, mem3, regs3⟩ := u2.jalr hc mcx_at_18
    refine ⟨n3, .cons d1 (.cons d2 (.single d3)), ?_, ?_, fun r h0' _ _ _ _ => ?_, mem3⟩
    · rw [pc3]; simp +decide only [upd_app, ↓reduceIte]; rw [add_lit_zero, hra, hret]
    · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]; rw [hz]
      exact Or.inl ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    · rw [regs3]
      by_cases h0 : r.val = 0
      · have : r = 0 := Fin.ext h0
        subst this; simp [upd]; exact hz.symm
      simp only [upd_app, h0, h0', ite_false]
  · obtain ⟨n1, d1, u1⟩ := s0.notTaken hc 0x2 mcx_at_0 (by decide) (by
      rw [ha2, hz]; simp only [branchTaken, beq_eq_false_iff_ne, ne_eq]; intro h
      have := congrArg BitVec.toNat h; rw [ofNat_tn hn] at this; exact hn0 this)
    obtain ⟨m', c', h1, h2, h3, h4⟩ := loop n 0 (by omega) (by omega) u1.self
      (by rw [u1.regs, ha0, add_ofNat_zero]) (by rw [u1.regs, ha1, add_ofNat_zero]) (by rw [u1.regs, ha2])
      (by rw [u1.regs, hra]) (fun j hj => absurd hj (Nat.not_lt_zero j))
      (fun r _ _ _ _ _ => u1.regs r)
    exact ⟨m', .cons d1 c', h1, h2, h3, h4⟩

section
variable {code : List Nat} {base : Word} {Q : Post} {M : Word → BitVec 8} {off : Nat} {f : Fin 32 → Word}

/-- A call to `memcmp(p, q, l)` with the code at `tb`. -/
theorem WP.callMemcmp {hi lo tb p q : Word} {l : Nat}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = tb) (htb : tb.toNat % 2 = 0) (hev : (off + 8) % 2 = 0)
    (hct : CodeIn M tb memcmpCode) (h0 : f a0 = p) (ha1 : f a1 = q) (ha2 : f a2 = BitVec.ofNat 32 l)
    (hl : l < 2 ^ 32)
    (k : ∀ m2 : Machine, CmpRes M p q l (reg m2 a0) →
      WP code base Q M (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 eslClob)) :
    WP code base Q M off f := by
  refine WP.callGen (tb := tb) (cl := eslClob) (P := fun m2 => m2.mem = M ∧ CmpRes M p q l (reg m2 a0)) h1 h2
    (by rw [htgt]; exact even_clear _ htb) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc => by rw [hP.1]; exact hc) (fun m2 hP => by rw [hP.1]; exact k m2 hP.2)
  obtain ⟨m2, c2, pc2, hR, hfr, mem2⟩ := memcmp_cmp m1 (base := tb) (p := p) (q := q) (n := l)
    (by rw [hmem1]; exact hct) hpc1 (by rw [hreg1]; rsimp; exact h0) (by rw [hreg1]; rsimp; exact ha1)
    (by rw [hreg1]; rsimp; exact ha2) hl (retAddr := base + BitVec.ofNat 32 (off + 8)) (by rw [hreg1]; rsimp)
    (even_clear _ (even_at base hb _ hev))
  rw [hmem1] at mem2 hR
  refine ⟨m2, c2, pc2, ⟨mem2, hR⟩, fun x hx => ?_⟩
  simp only [eslClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
  obtain ⟨n0, n1, n2, n3, n4⟩ := hx
  exact hfr x n0 n1 n2 n3 n4

/-- A call to `slice_ne(p, pl, q, ql)` with the code at `tb`, which may
change the 20 bytes below `sp`. -/
theorem WP.callSliceNe {hi lo tb p q : Word} {pl ql : Nat}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = tb) (htb : tb.toNat % 2 = 0) (hev : (off + 8) % 2 = 0)
    (hc : CodeIn M tb sliceNeCode) (hs : CodeIn M (tb + 0xFFFFF372) sliceEqCode)
    (he : CodeIn M (tb + 0xFFFFDF1C) equalSameLengthCode) (hm : CodeIn M (tb + 0xB2DA) memcmpCode)
    (h0 : f a0 = p) (ha1 : f a1 = BitVec.ofNat 32 pl) (ha2 : f a2 = q) (ha3 : f a3 = BitVec.ofNat 32 ql)
    (hpl : pl < 2 ^ 32) (hql : ql < 2 ^ 32) (hal : (f sp).toNat % 4 = 0)
    (sSC : Sep (f sp + 0xFFFFFFEC) 0x14 tb sliceNeCode.length)
    (sSS : Sep (f sp + 0xFFFFFFEC) 0x14 (tb + 0xFFFFF372) sliceEqCode.length)
    (sSE : Sep (f sp + 0xFFFFFFEC) 0x14 (tb + 0xFFFFDF1C) equalSameLengthCode.length)
    (sSM : Sep (f sp + 0xFFFFFFEC) 0x14 (tb + 0xB2DA) memcmpCode.length)
    (sSP : Sep (f sp + 0xFFFFFFEC) 0x14 p pl) (sSQ : Sep (f sp + 0xFFFFFFEC) 0x14 q ql)
    (hSb : Sep (f sp + 0xFFFFFFEC) 0x14 base code.length)
    (k : ∀ m2 : Machine, reg m2 a0 = (if memBytes M p pl = memBytes M q ql then 0 else 1) →
      Out M m2.mem (f sp + 0xFFFFFFEC) 0x14 →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP code base Q M off f := by
  refine WP.callGen (tb := tb) (cl := jClob)
    (P := fun m2 => reg m2 a0 = (if memBytes M p pl = memBytes M q ql then 0 else 1) ∧
      Out M m2.mem (f sp + 0xFFFFFFEC) 0x14)
    h1 h2 (by rw [htgt]; exact even_clear _ htb) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc => hP.2.codeIn hc hSb) (fun m2 hP => k m2 hP.1 hP.2)
  have hsp1 : reg m1 sp = f sp := by rw [hreg1]; rsimp
  obtain ⟨m2, c2, pc2, ha0, hfr, hmem⟩ := sliceNe_correct m1 (base := tb) (p := p) (q := q) (pl := pl) (ql := ql)
    htb (by rw [hmem1]; exact hc) (by rw [hmem1]; exact hs) (by rw [hmem1]; exact he) (by rw [hmem1]; exact hm)
    hpc1 (by rw [hreg1]; rsimp; exact h0) (by rw [hreg1]; rsimp; exact ha1) (by rw [hreg1]; rsimp; exact ha2)
    (by rw [hreg1]; rsimp; exact ha3) hpl hql (retAddr := base + BitVec.ofNat 32 (off + 8)) (by rw [hreg1]; rsimp)
    (even_clear _ (even_at base hb _ hev)) (by rw [hsp1]; exact hal) (by rw [hsp1]; exact sSC)
    (by rw [hsp1]; exact sSS) (by rw [hsp1]; exact sSE) (by rw [hsp1]; exact sSM) (by rw [hsp1]; exact sSP)
    (by rw [hsp1]; exact sSQ)
  refine ⟨m2, c2, pc2, ⟨by rw [ha0, hmem1], fun x hx => ?_⟩, fun x hx => ?_⟩
  · rw [hmem x (by rw [hsp1]; exact hx.symm), hmem1]
  · exact hfr x (fun h => hx (by subst h; decide)) (fun h => hx (by subst h; decide))
      (fun h => hx (by subst h; decide)) (fun h => hx (by subst h; decide)) (fun h => hx (by subst h; decide))
      (fun h => hx (by subst h; decide))

end

theorem pa_sll3 : ∀ i : Nat, i < 17 → aluEval .sll (BitVec.ofNat 32 i) 3 = BitVec.ofNat 32 (8 * i) := by decide

/-- The code `parse` runs, at its offsets from `parse`'s address `b`: `get`
at `b + 0xFFFFF372` brings every callee but `slice_ne`. -/
structure ParseCode (M : Word → BitVec 8) (b : Word) : Prop where
  parse : CodeIn M b jsonParseCode
  get : GetCode M (b + 0xFFFFF372)
  ne : CodeIn M (b + 0xFFFFFFEA) sliceNeCode

/-- The `k` bytes at `s` are apart from `ParseCode M b`. -/
structure ParseSep (s : Word) (k : Nat) (b : Word) : Prop where
  parse : Sep s k b jsonParseCode.length
  get : GetSep s k (b + 0xFFFFF372)
  ne : Sep s k (b + 0xFFFFFFEA) sliceNeCode.length

theorem ParseSep.sub {s b : Word} {k : Nat} (h : ParseSep s k b) {c l : Nat} (hcl : c + l ≤ k) :
    ParseSep (s + BitVec.ofNat 32 c) l b :=
  ⟨h.parse.sub hcl, h.get.sub hcl, h.ne.sub hcl⟩

theorem ParseCode.out {M M' : Word → BitVec 8} {b s : Word} {k : Nat} (h : ParseCode M b) (hO : Out M M' s k)
    (hs : ParseSep s k b) : ParseCode M' b :=
  ⟨hO.codeIn h.parse hs.parse, h.get.out hO hs.get, hO.codeIn h.ne hs.ne⟩

/-- The registers `parse` changes before its epilogue restores the saved ones. -/
abbrev paE : List (Fin 32) := jClob ++ [ra, sp, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

abbrev paCs : List Nat := [0xBC, 0xC0, 0xC4, 0xC8, 0xCC, 0xD0, 0xD4, 0xD8, 0xDC, 0xE0, 0xE4, 0xE8, 0xEC]

/-- The saved registers in the frame at `F`. -/
def PaSaved (F : Word) (g0 : Fin 32 → Word) (M1 : Word → BitVec 8) : Prop :=
  memLoad32 M1 (F + BitVec.ofNat 32 0xEC) = g0 ra ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0xE8) = g0 8 ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0xE4) = g0 9 ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0xE0) = g0 18 ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0xDC) = g0 19 ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0xD8) = g0 20 ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0xD4) = g0 21 ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0xD0) = g0 22 ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0xCC) = g0 23 ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0xC8) = g0 24 ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0xC4) = g0 25 ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0xC0) = g0 26 ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0xBC) = g0 27

/-- Memory after the prologue. -/
def paM1 (M : Word → BitVec 8) (F : Word) (g0 : Fin 32 → Word) : Word → BitVec 8 :=
  memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M (F + 0xEC) (g0 ra))
    (F + 0xE8) (g0 8))
    (F + 0xE4) (g0 9))
    (F + 0xE0) (g0 18))
    (F + 0xDC) (g0 19))
    (F + 0xD8) (g0 20))
    (F + 0xD4) (g0 21))
    (F + 0xD0) (g0 22))
    (F + 0xCC) (g0 23))
    (F + 0xC8) (g0 24))
    (F + 0xC4) (g0 25))
    (F + 0xC0) (g0 26))
    (F + 0xBC) (g0 27)

theorem pa_ld {M : Word → BitVec 8} {F v : Word} (c : Nat) (hc : c + 4 ≤ 240) (ds : List Nat)
    (hd : ∀ d, d ∈ ds → c + 4 ≤ d ∨ d + 4 ≤ c) (hds : ∀ d, d ∈ ds → d + 4 ≤ 240)
    (h : memLoad32 M (F + BitVec.ofNat 32 c) = v) (ws : List Word) :
    memLoad32 ((ds.zip ws).foldl (fun M' x => memStore32 M' (F + BitVec.ofNat 32 x.1) x.2) M)
      (F + BitVec.ofNat 32 c) = v := by
  induction ds generalizing M ws with
  | nil => exact h
  | cons d ds ih =>
    cases ws with
    | nil => exact h
    | cons w ws =>
      exact ih (fun d hd' => hd d (List.mem_cons_of_mem _ hd')) (fun d hd' => hds d (List.mem_cons_of_mem _ hd'))
        (ld_skip c d (hd d (List.mem_cons_self ..)) (by omega) (by have := hds d (List.mem_cons_self ..); omega) h) ws

theorem pa_pro (M : Word → BitVec 8) (F : Word) (g0 : Fin 32 → Word) :
    Out M (paM1 M F g0) F 240 ∧ PaSaved F g0 (paM1 M F g0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((((((((((((((out_store32 _ _ _).widen (d := 0xEC) (by decide)).trans
      ((out_store32 _ _ _).widen (d := 0xE8) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0xE4) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0xE0) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0xDC) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0xD8) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0xD4) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0xD0) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0xCC) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0xC8) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0xC4) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0xC0) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0xBC) (by decide)))
  · exact pa_ld 0xEC (by decide) [0xE8, 0xE4, 0xE0, 0xDC, 0xD8, 0xD4, 0xD0, 0xCC, 0xC8, 0xC4, 0xC0, 0xBC] (by decide) (by decide)
      (memLoad32_store32_same _ _ _) [g0 8, g0 9, g0 18, g0 19, g0 20, g0 21, g0 22, g0 23, g0 24, g0 25, g0 26, g0 27]
  · exact pa_ld 0xE8 (by decide) [0xE4, 0xE0, 0xDC, 0xD8, 0xD4, 0xD0, 0xCC, 0xC8, 0xC4, 0xC0, 0xBC] (by decide) (by decide)
      (memLoad32_store32_same _ _ _) [g0 9, g0 18, g0 19, g0 20, g0 21, g0 22, g0 23, g0 24, g0 25, g0 26, g0 27]
  · exact pa_ld 0xE4 (by decide) [0xE0, 0xDC, 0xD8, 0xD4, 0xD0, 0xCC, 0xC8, 0xC4, 0xC0, 0xBC] (by decide) (by decide)
      (memLoad32_store32_same _ _ _) [g0 18, g0 19, g0 20, g0 21, g0 22, g0 23, g0 24, g0 25, g0 26, g0 27]
  · exact pa_ld 0xE0 (by decide) [0xDC, 0xD8, 0xD4, 0xD0, 0xCC, 0xC8, 0xC4, 0xC0, 0xBC] (by decide) (by decide)
      (memLoad32_store32_same _ _ _) [g0 19, g0 20, g0 21, g0 22, g0 23, g0 24, g0 25, g0 26, g0 27]
  · exact pa_ld 0xDC (by decide) [0xD8, 0xD4, 0xD0, 0xCC, 0xC8, 0xC4, 0xC0, 0xBC] (by decide) (by decide)
      (memLoad32_store32_same _ _ _) [g0 20, g0 21, g0 22, g0 23, g0 24, g0 25, g0 26, g0 27]
  · exact pa_ld 0xD8 (by decide) [0xD4, 0xD0, 0xCC, 0xC8, 0xC4, 0xC0, 0xBC] (by decide) (by decide)
      (memLoad32_store32_same _ _ _) [g0 21, g0 22, g0 23, g0 24, g0 25, g0 26, g0 27]
  · exact pa_ld 0xD4 (by decide) [0xD0, 0xCC, 0xC8, 0xC4, 0xC0, 0xBC] (by decide) (by decide)
      (memLoad32_store32_same _ _ _) [g0 22, g0 23, g0 24, g0 25, g0 26, g0 27]
  · exact pa_ld 0xD0 (by decide) [0xCC, 0xC8, 0xC4, 0xC0, 0xBC] (by decide) (by decide)
      (memLoad32_store32_same _ _ _) [g0 23, g0 24, g0 25, g0 26, g0 27]
  · exact pa_ld 0xCC (by decide) [0xC8, 0xC4, 0xC0, 0xBC] (by decide) (by decide)
      (memLoad32_store32_same _ _ _) [g0 24, g0 25, g0 26, g0 27]
  · exact pa_ld 0xC8 (by decide) [0xC4, 0xC0, 0xBC] (by decide) (by decide)
      (memLoad32_store32_same _ _ _) [g0 25, g0 26, g0 27]
  · exact pa_ld 0xC4 (by decide) [0xC0, 0xBC] (by decide) (by decide)
      (memLoad32_store32_same _ _ _) [g0 26, g0 27]
  · exact pa_ld 0xC0 (by decide) [0xBC] (by decide) (by decide)
      (memLoad32_store32_same _ _ _) [g0 27]
  · exact memLoad32_store32_same _ _ _

section
variable {M1 Mf : Word → BitVec 8} {base F : Word} {f g0 : Fin 32 → Word}

theorem pa_epi {R : (Word → BitVec 8) → Prop} (hsp : f sp = F)
    (hS : Slots paCs F M1 Mf) (hv : PaSaved F g0 M1) (hsp0 : g0 sp = F + BitVec.ofNat 32 0xF0)
    (hret : g0 ra &&& ~~~1 = g0 ra) (hal : F.toNat % 4 = 0) (hz0 : g0 0 = 0)
    (hfr : ∀ x, x ∉ paE → f x = g0 x) (hR : R Mf) :
    WP jsonParseCode base (RPost (g0 ra) R g0) Mf 0x30A f := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12⟩ := hv
  have e0 : memLoad32 Mf (F + 0xEC) = g0 ra := (hS 0xEC (by decide)).trans v0
  have e1 : memLoad32 Mf (F + 0xE8) = g0 8 := (hS 0xE8 (by decide)).trans v1
  have e2 : memLoad32 Mf (F + 0xE4) = g0 9 := (hS 0xE4 (by decide)).trans v2
  have e3 : memLoad32 Mf (F + 0xE0) = g0 18 := (hS 0xE0 (by decide)).trans v3
  have e4 : memLoad32 Mf (F + 0xDC) = g0 19 := (hS 0xDC (by decide)).trans v4
  have e5 : memLoad32 Mf (F + 0xD8) = g0 20 := (hS 0xD8 (by decide)).trans v5
  have e6 : memLoad32 Mf (F + 0xD4) = g0 21 := (hS 0xD4 (by decide)).trans v6
  have e7 : memLoad32 Mf (F + 0xD0) = g0 22 := (hS 0xD0 (by decide)).trans v7
  have e8 : memLoad32 Mf (F + 0xCC) = g0 23 := (hS 0xCC (by decide)).trans v8
  have e9 : memLoad32 Mf (F + 0xC8) = g0 24 := (hS 0xC8 (by decide)).trans v9
  have e10 : memLoad32 Mf (F + 0xC4) = g0 25 := (hS 0xC4 (by decide)).trans v10
  have e11 : memLoad32 Mf (F + 0xC0) = g0 26 := (hS 0xC0 (by decide)).trans v11
  have e12 : memLoad32 Mf (F + 0xBC) = g0 27 := (hS 0xBC (by decide)).trans v12
  refine WP.lw pa_at_30a (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0xEC) (by decide)) ?_; wn
  refine WP.lw pa_at_30c (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0xE8) (by decide)) ?_; wn
  refine WP.lw pa_at_30e (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0xE4) (by decide)) ?_; wn
  refine WP.lw pa_at_310 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0xE0) (by decide)) ?_; wn
  refine WP.lw pa_at_312 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0xDC) (by decide)) ?_; wn
  refine WP.lw pa_at_314 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0xD8) (by decide)) ?_; wn
  refine WP.lw pa_at_316 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0xD4) (by decide)) ?_; wn
  refine WP.lw pa_at_318 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0xD0) (by decide)) ?_; wn
  refine WP.lw pa_at_31a (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0xCC) (by decide)) ?_; wn
  refine WP.lw pa_at_31c (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0xC8) (by decide)) ?_; wn
  refine WP.lw pa_at_31e (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0xC4) (by decide)) ?_; wn
  refine WP.lw pa_at_320 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0xC0) (by decide)) ?_; wn
  refine WP.lw pa_at_322 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0xBC) (by decide)) ?_; wn
  refine WP.aluImm pa_at_324 ?_; wn
  refine WP.ret pa_at_326 ⟨?_, hR, ?_⟩
  · rsimp; rw [hsp, e0, add_lit_zero, hret]
  refine frame_of (L2 := [ra, sp, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]) (by keepz hz0) fun x hx => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rsimp
  · rw [hsp, e0]
  · rw [hsp, hsp0]; rfl
  · rw [hsp, e1]
  · rw [hsp, e2]
  · rw [hsp, e3]
  · rw [hsp, e4]
  · rw [hsp, e5]
  · rw [hsp, e6]
  · rw [hsp, e7]
  · rw [hsp, e8]
  · rw [hsp, e9]
  · rw [hsp, e10]
  · rw [hsp, e11]
  · rw [hsp, e12]

end

theorem pa_err_res (M : Word → BitVec 8) (out : Word) (b : BitVec 8) (e : Nat) (hv : b = BitVec.ofNat 8 e) :
    FieldRes M (memStore8 (memStore32 M out 0) (out + 4) b) out (.error e) := by
  have h4 : Sep (out + BitVec.ofNat 32 4) 1 out 4 := by
    have := sep_offsets out (c := 4) (n := 1) (d := 0) (k := 4) (Or.inr (by decide)) (by decide) (by decide)
    rwa [add_ofNat_zero] at this
  refine ⟨fun x hx => ?_, ?_, ?_⟩
  · have h0 : Sep x 1 out 4 := by
      have := hx.subR (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    exact (out_store8 _ _ _ x (hx.subR (c := 4) (l := 1) (by decide))).trans (out_store32 _ _ _ x h0)
  · exact (memLoad32_store8_sep h4).trans (memLoad32_store32_same _ _ _)
  · rw [memStore8_same, hv]

theorem pa_ok_res (M : Word → BitVec 8) (out q : Word) (l : Nat) :
    FieldRes M (memStore32 (memStore32 M out q) (out + 4) (BitVec.ofNat 32 l)) out (.ok (q, l)) := by
  have h4 : Sep (out + BitVec.ofNat 32 4) 4 (out + BitVec.ofNat 32 0) 4 :=
    sep_offsets out (Or.inr (by decide)) (by decide) (by decide)
  rw [add_ofNat_zero] at h4
  refine ⟨fun x hx => ?_, ?_, memLoad32_store32_same _ _ _⟩
  · have h0 : Sep x 1 out 4 := by
      have := hx.subR (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    exact (out_store32 _ _ _ x (hx.subR (c := 4) (l := 4) (by decide))).trans (out_store32 _ _ _ x h0)
  · exact (memLoad32_store32_sep h4).trans (memLoad32_store32_same _ _ _)

/-- What `parse` gets from its caller: the code, the stack region `[s, s + 404)`
with the frame at `F = s + 164`, the document `p`, `n`, and `out`. `Mp` is the
memory after the prologue saved the callee-saved registers. -/
structure PaEnv (M0 : Word → BitVec 8) (base s p out : Word) (n : Nat) (g0 : Fin 32 → Word)
    (Mp : Word → BitVec 8) (F : Word) : Prop where
  hF : s + BitVec.ofNat 32 164 = F
  hb : base.toNat % 2 = 0
  hal : s.toNat % 4 = 0
  halo : out.toNat % 4 = 0
  hn : n < 2 ^ 31
  hp0 : p.toNat ≠ 0
  hpn : p.toNat + n < 2 ^ 32
  hsw : s.toNat + 404 < 2 ^ 32
  code : ParseCode M0 base
  sep : ParseSep s 404 base
  sP : Sep s 404 p n
  so : Sep out 8 s 404
  sc : Sep out 8 base jsonParseCode.length
  saved : PaSaved F g0 Mp
  sp0 : g0 sp = F + BitVec.ofNat 32 0xF0
  ret : g0 ra &&& ~~~1 = g0 ra
  z0 : g0 0 = 0

/-- `parse` returned to its caller with `r`'s word-level form at `out`. -/
def PPost (M0 : Word → BitVec 8) (s p out : Word) (g0 : Fin 32 → Word) (r : Except Nat (Nat × Nat)) : Post :=
  RPost (g0 ra) (fun M' => FieldResF M0 M' out s 404 (fieldRes p r)) g0

section
variable {M0 Mp Mf : Word → BitVec 8} {base s p out F : Word} {n : Nat} {f g0 : Fin 32 → Word}

theorem PaEnv.halF (E : PaEnv M0 base s p out n g0 Mp F) : F.toNat % 4 = 0 := by
  rw [← E.hF]; exact aligned_add E.hal (k := 164) (by decide)

theorem PaEnv.soF (E : PaEnv M0 base s p out n g0 Mp F) : Sep out 8 F 240 := by
  rw [← E.hF]; exact E.so.subR (by decide)

theorem PaEnv.sc4 (E : PaEnv M0 base s p out n g0 Mp F) : Sep out 4 base jsonParseCode.length := by
  have := E.sc.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this

theorem PaEnv.slots_out (E : PaEnv M0 base s p out n g0 Mp F) {c l : Nat} (hcl : c + l ≤ 8) :
    ∀ x, x ∈ paCs → Sep (out + BitVec.ofNat 32 c) l (F + BitVec.ofNat 32 x) 4 :=
  slots_sep_out (E.soF.sub hcl) (by decide)

theorem PaEnv.slots_out0 (E : PaEnv M0 base s p out n g0 Mp F) :
    ∀ x, x ∈ paCs → Sep out 4 (F + BitVec.ofNat 32 x) 4 := by
  have := E.slots_out (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this

/-- The error exit at `0x302`, with `out` in `s2` and the error byte in `a0`. -/
theorem pa_302 {e : Nat} (E : PaEnv M0 base s p out n g0 Mp F) (hsp : f sp = F) (h18 : f 18 = out)
    (ha0 : (f a0).extractLsb' 0 8 = BitVec.ofNat 8 e) (hO : Out M0 Mf s 404) (hS : Slots paCs F Mp Mf)
    (hfr : ∀ x, x ∉ paE → f x = g0 x) :
    WP jsonParseCode base (PPost M0 s p out g0 (.error e)) Mf 0x302 f := by
  refine WP.zero fun hz => ?_
  refine WP.sw pa_at_302 (by (try rsimp); rw [h18, add_lit_zero]; exact E.halo)
    (by (try rsimp); rw [h18, add_lit_zero]; exact E.sc4) ?_; wn
  refine WP.sb pa_at_306 (by (try rsimp); rw [h18]; exact E.sc.sub (c := 4) (l := 1) (by decide)) ?_; wn
  rw [h18, add_lit_zero, hz]
  exact pa_epi hsp ((hS.out (out_store32 _ _ _) E.slots_out0).out (out_store8 _ _ _)
    (E.slots_out (c := 4) (l := 1) (by decide))) E.saved E.sp0 E.ret E.halF E.z0 hfr
    ⟨Mf, hO, pa_err_res Mf out _ e ha0⟩

/-- The error exit at `0x2F4`, with `out` in `a1` and the error byte in `a0`. -/
theorem pa_2f4 {e : Nat} (E : PaEnv M0 base s p out n g0 Mp F) (hsp : f sp = F) (ha1 : f a1 = out)
    (ha0 : (f a0).extractLsb' 0 8 = BitVec.ofNat 8 e) (hO : Out M0 Mf s 404) (hS : Slots paCs F Mp Mf)
    (hfr : ∀ x, x ∉ paE → f x = g0 x) :
    WP jsonParseCode base (PPost M0 s p out g0 (.error e)) Mf 0x2F4 f := by
  refine WP.zero fun hz => ?_
  refine WP.sw pa_at_2f4 (by (try rsimp); rw [ha1, add_lit_zero]; exact E.halo)
    (by (try rsimp); rw [ha1, add_lit_zero]; exact E.sc4) ?_; wn
  refine WP.sb pa_at_2f8 (by (try rsimp); rw [ha1]; exact E.sc.sub (c := 4) (l := 1) (by decide)) ?_; wn
  refine WP.jal pa_at_2fc (by decide) ?_; wn
  rw [ha1, add_lit_zero, hz]
  exact pa_epi hsp ((hS.out (out_store32 _ _ _) E.slots_out0).out (out_store8 _ _ _)
    (E.slots_out (c := 4) (l := 1) (by decide))) E.saved E.sp0 E.ret E.halF E.z0 hfr
    ⟨Mf, hO, pa_err_res Mf out _ e ha0⟩

/-- The error exit at `0x2C0`, with `out` at `F + 0xC` and the error byte in
`s2`. -/
theorem pa_2c0 {e : Nat} (E : PaEnv M0 base s p out n g0 Mp F) (hsp : f sp = F)
    (hC : memLoad32 Mf (F + 0xC) = out) (h18 : (f 18).extractLsb' 0 8 = BitVec.ofNat 8 e)
    (hO : Out M0 Mf s 404) (hS : Slots paCs F Mp Mf) (hfr : ∀ x, x ∉ paE → f x = g0 x) :
    WP jsonParseCode base (PPost M0 s p out g0 (.error e)) Mf 0x2C0 f := by
  refine WP.zero fun hz => ?_
  refine WP.lw pa_at_2c0 (by (try rsimp); rw [hsp]; exact aligned_add E.halF (k := 0xC) (by decide)) ?_; wn
  rw [hsp, hC]
  refine WP.sw pa_at_2c2 (by (try rsimp); rw [add_lit_zero]; exact E.halo)
    (by (try rsimp); rw [add_lit_zero]; exact E.sc4) ?_; wn
  refine WP.sb pa_at_2c6 (by (try rsimp); exact E.sc.sub (c := 4) (l := 1) (by decide)) ?_; wn
  refine WP.jal pa_at_2ca (by decide) ?_; wn
  try rw [add_lit_zero]
  exact pa_epi (by (try rsimp); exact hsp) ((hS.out (out_store32 _ _ _) E.slots_out0).out (out_store8 _ _ _)
    (E.slots_out (c := 4) (l := 1) (by decide))) E.saved E.sp0 E.ret E.halF E.z0 (by keepz E.z0)
    ⟨Mf, hO, pa_err_res Mf out _ e (by (try rsimp); exact h18)⟩

end

end C3.RV32
