import C3BootProofs.Proofs.Sha512Bits

/-!
# `compress512`'s decoded instructions

One `fetchRel` lemma for each instruction of the compiled
`sha2::sha512::compress512`, from `scripts/decode-lemmas.py`; `decide`
checks each one against the extracted bytes.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem s5_at_0 : fetchRel sha512CompressCode 0x0 = some (.aluImm .add sp sp 0xFFFFFC70, 4) := by decide
theorem s5_at_4 : fetchRel sha512CompressCode 0x4 = some (.aluImm .add a3 sp 0x380, 2) := by decide
theorem s5_at_6 : fetchRel sha512CompressCode 0x6 = some (.store .sw a3 ra 0xC, 4) := by decide
theorem s5_at_a : fetchRel sha512CompressCode 0xA = some (.store .sw a3 (8 : Fin 32) 0x8, 2) := by decide
theorem s5_at_c : fetchRel sha512CompressCode 0xC = some (.store .sw a3 (9 : Fin 32) 0x4, 2) := by decide
theorem s5_at_e : fetchRel sha512CompressCode 0xE = some (.store .sw a3 (18 : Fin 32) 0x0, 4) := by decide
theorem s5_at_12 : fetchRel sha512CompressCode 0x12 = some (.aluImm .add a3 sp 0x300, 2) := by decide
theorem s5_at_14 : fetchRel sha512CompressCode 0x14 = some (.store .sw a3 (19 : Fin 32) 0x7C, 4) := by decide
theorem s5_at_18 : fetchRel sha512CompressCode 0x18 = some (.store .sw a3 (20 : Fin 32) 0x78, 4) := by decide
theorem s5_at_1c : fetchRel sha512CompressCode 0x1C = some (.store .sw a3 (21 : Fin 32) 0x74, 4) := by decide
theorem s5_at_20 : fetchRel sha512CompressCode 0x20 = some (.store .sw a3 (22 : Fin 32) 0x70, 4) := by decide
theorem s5_at_24 : fetchRel sha512CompressCode 0x24 = some (.store .sw a3 (23 : Fin 32) 0x6C, 4) := by decide
theorem s5_at_28 : fetchRel sha512CompressCode 0x28 = some (.store .sw a3 (24 : Fin 32) 0x68, 4) := by decide
theorem s5_at_2c : fetchRel sha512CompressCode 0x2C = some (.store .sw a3 (25 : Fin 32) 0x64, 4) := by decide
theorem s5_at_30 : fetchRel sha512CompressCode 0x30 = some (.store .sw a3 (26 : Fin 32) 0x60, 4) := by decide
theorem s5_at_34 : fetchRel sha512CompressCode 0x34 = some (.store .sw a3 (27 : Fin 32) 0x5C, 4) := by decide
theorem s5_at_38 : fetchRel sha512CompressCode 0x38 = some (.alu .add (21 : Fin 32) x0 a1, 2) := by decide
theorem s5_at_3a : fetchRel sha512CompressCode 0x3A = some (.aluImm .sll a2 a2 0x7, 2) := by decide
theorem s5_at_3c : fetchRel sha512CompressCode 0x3C = some (.load .lw (23 : Fin 32) a0 0x0, 4) := by decide
theorem s5_at_40 : fetchRel sha512CompressCode 0x40 = some (.load .lw (19 : Fin 32) a0 0x4, 4) := by decide
theorem s5_at_44 : fetchRel sha512CompressCode 0x44 = some (.load .lw (22 : Fin 32) a0 0x8, 4) := by decide
theorem s5_at_48 : fetchRel sha512CompressCode 0x48 = some (.load .lw (27 : Fin 32) a0 0xC, 4) := by decide
theorem s5_at_4c : fetchRel sha512CompressCode 0x4C = some (.load .lw (24 : Fin 32) a0 0x10, 4) := by decide
theorem s5_at_50 : fetchRel sha512CompressCode 0x50 = some (.load .lw (26 : Fin 32) a0 0x14, 4) := by decide
theorem s5_at_54 : fetchRel sha512CompressCode 0x54 = some (.load .lw (18 : Fin 32) a0 0x18, 4) := by decide
theorem s5_at_58 : fetchRel sha512CompressCode 0x58 = some (.load .lw a1 a0 0x1C, 2) := by decide
theorem s5_at_5a : fetchRel sha512CompressCode 0x5A = some (.store .sw sp a1 0x54, 2) := by decide
theorem s5_at_5c : fetchRel sha512CompressCode 0x5C = some (.load .lw (20 : Fin 32) a0 0x20, 4) := by decide
theorem s5_at_60 : fetchRel sha512CompressCode 0x60 = some (.load .lw a1 a0 0x24, 2) := by decide
theorem s5_at_62 : fetchRel sha512CompressCode 0x62 = some (.store .sw sp a1 0x4C, 2) := by decide
theorem s5_at_64 : fetchRel sha512CompressCode 0x64 = some (.load .lw a1 a0 0x28, 2) := by decide
theorem s5_at_66 : fetchRel sha512CompressCode 0x66 = some (.store .sw sp a1 0x50, 2) := by decide
theorem s5_at_68 : fetchRel sha512CompressCode 0x68 = some (.load .lw a1 a0 0x2C, 2) := by decide
theorem s5_at_6a : fetchRel sha512CompressCode 0x6A = some (.store .sw sp a1 0x44, 2) := by decide
theorem s5_at_6c : fetchRel sha512CompressCode 0x6C = some (.load .lw a1 a0 0x30, 2) := by decide
theorem s5_at_6e : fetchRel sha512CompressCode 0x6E = some (.store .sw sp a1 0x48, 2) := by decide
theorem s5_at_70 : fetchRel sha512CompressCode 0x70 = some (.load .lw a1 a0 0x34, 2) := by decide
theorem s5_at_72 : fetchRel sha512CompressCode 0x72 = some (.store .sw sp a1 0x3C, 2) := by decide
theorem s5_at_74 : fetchRel sha512CompressCode 0x74 = some (.load .lw a1 a0 0x38, 2) := by decide
theorem s5_at_76 : fetchRel sha512CompressCode 0x76 = some (.store .sw sp a1 0x40, 2) := by decide
theorem s5_at_78 : fetchRel sha512CompressCode 0x78 = some (.store .sw sp a0 0xC, 2) := by decide
theorem s5_at_7a : fetchRel sha512CompressCode 0x7A = some (.load .lw a0 a0 0x3C, 2) := by decide
theorem s5_at_7c : fetchRel sha512CompressCode 0x7C = some (.store .sw sp a0 0x38, 2) := by decide
theorem s5_at_7e : fetchRel sha512CompressCode 0x7E = some (.alu .add a2 a2 (21 : Fin 32), 2) := by decide
theorem s5_at_80 : fetchRel sha512CompressCode 0x80 = some (.store .sw sp a2 0x10, 2) := by decide
theorem s5_at_82 : fetchRel sha512CompressCode 0x82 = some (.aluImm .add (25 : Fin 32) sp 0x58, 4) := by decide
theorem s5_at_86 : fetchRel sha512CompressCode 0x86 = some (.load .lw a0 sp 0x10, 2) := by decide
theorem s5_at_88 : fetchRel sha512CompressCode 0x88 = some (.branch .beq (21 : Fin 32) a0 0x3B6, 4) := by decide
theorem s5_at_8c : fetchRel sha512CompressCode 0x8C = some (.aluImm .add (8 : Fin 32) x0 0x0, 2) := by decide
theorem s5_at_8e : fetchRel sha512CompressCode 0x8E = some (.aluImm .add a0 (21 : Fin 32) 0x80, 4) := by decide
theorem s5_at_92 : fetchRel sha512CompressCode 0x92 = some (.store .sw sp a0 0x34, 2) := by decide
theorem s5_at_94 : fetchRel sha512CompressCode 0x94 = some (.aluImm .add a0 (8 : Fin 32) 0xFFFFFF80, 4) := by decide
theorem s5_at_98 : fetchRel sha512CompressCode 0x98 = some (.branch .beq a0 x0 0x60, 2) := by decide
theorem s5_at_9a : fetchRel sha512CompressCode 0x9A = some (.aluImm .add a2 x0 0x80, 4) := by decide
theorem s5_at_9e : fetchRel sha512CompressCode 0x9E = some (.alu .add a0 x0 (8 : Fin 32), 2) := by decide
theorem s5_at_a0 : fetchRel sha512CompressCode 0xA0 = some (.alu .add a1 x0 (21 : Fin 32), 2) := by decide
theorem s5_at_a2 : fetchRel sha512CompressCode 0xA2 = some (.auipc ra 0x0, 4) := by decide
theorem s5_at_a6 : fetchRel sha512CompressCode 0xA6 = some (.jalr ra ra 0xFFFFFF48, 4) := by decide
theorem s5_at_aa : fetchRel sha512CompressCode 0xAA = some (.alu .add a2 x0 a1, 2) := by decide
theorem s5_at_ac : fetchRel sha512CompressCode 0xAC = some (.aluImm .add a1 x0 0x7, 2) := by decide
theorem s5_at_ae : fetchRel sha512CompressCode 0xAE = some (.branch .bgeu a1 a2 0x3CA, 4) := by decide
theorem s5_at_b2 : fetchRel sha512CompressCode 0xB2 = some (.load .lbu a1 a0 0x5, 4) := by decide
theorem s5_at_b6 : fetchRel sha512CompressCode 0xB6 = some (.load .lbu a2 a0 0x6, 4) := by decide
theorem s5_at_ba : fetchRel sha512CompressCode 0xBA = some (.load .lbu a3 a0 0x4, 4) := by decide
theorem s5_at_be : fetchRel sha512CompressCode 0xBE = some (.load .lbu a4 a0 0x7, 4) := by decide
theorem s5_at_c2 : fetchRel sha512CompressCode 0xC2 = some (.load .lbu a6 a0 0x0, 4) := by decide
theorem s5_at_c6 : fetchRel sha512CompressCode 0xC6 = some (.load .lbu (9 : Fin 32) a0 0x2, 4) := by decide
theorem s5_at_ca : fetchRel sha512CompressCode 0xCA = some (.load .lbu a5 a0 0x1, 4) := by decide
theorem s5_at_ce : fetchRel sha512CompressCode 0xCE = some (.load .lbu a0 a0 0x3, 4) := by decide
theorem s5_at_d2 : fetchRel sha512CompressCode 0xD2 = some (.aluImm .sll a2 a2 0x8, 2) := by decide
theorem s5_at_d4 : fetchRel sha512CompressCode 0xD4 = some (.aluImm .sll a1 a1 0x10, 2) := by decide
theorem s5_at_d6 : fetchRel sha512CompressCode 0xD6 = some (.aluImm .sll a3 a3 0x18, 2) := by decide
theorem s5_at_d8 : fetchRel sha512CompressCode 0xD8 = some (.alu .or a2 a2 a4, 2) := by decide
theorem s5_at_da : fetchRel sha512CompressCode 0xDA = some (.alu .or a1 a1 a3, 2) := by decide
theorem s5_at_dc : fetchRel sha512CompressCode 0xDC = some (.aluImm .sll (9 : Fin 32) (9 : Fin 32) 0x8, 2) := by decide
theorem s5_at_de : fetchRel sha512CompressCode 0xDE = some (.alu .or a1 a1 a2, 2) := by decide
theorem s5_at_e0 : fetchRel sha512CompressCode 0xE0 = some (.alu .or a0 a0 (9 : Fin 32), 2) := by decide
theorem s5_at_e2 : fetchRel sha512CompressCode 0xE2 = some (.aluImm .sll a5 a5 0x10, 2) := by decide
theorem s5_at_e4 : fetchRel sha512CompressCode 0xE4 = some (.aluImm .sll a6 a6 0x18, 2) := by decide
theorem s5_at_e6 : fetchRel sha512CompressCode 0xE6 = some (.alu .or a2 a6 a5, 4) := by decide
theorem s5_at_ea : fetchRel sha512CompressCode 0xEA = some (.alu .add a3 (25 : Fin 32) (8 : Fin 32), 4) := by decide
theorem s5_at_ee : fetchRel sha512CompressCode 0xEE = some (.alu .or a0 a0 a2, 2) := by decide
theorem s5_at_f0 : fetchRel sha512CompressCode 0xF0 = some (.store .sw a3 a1 0x0, 2) := by decide
theorem s5_at_f2 : fetchRel sha512CompressCode 0xF2 = some (.store .sw a3 a0 0x4, 2) := by decide
theorem s5_at_f4 : fetchRel sha512CompressCode 0xF4 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x8, 2) := by decide
theorem s5_at_f6 : fetchRel sha512CompressCode 0xF6 = some (.jal x0 0xFFFFFF9E, 2) := by decide
theorem s5_at_f8 : fetchRel sha512CompressCode 0xF8 = some (.aluImm .add a0 sp 0xD8, 2) := by decide
theorem s5_at_fa : fetchRel sha512CompressCode 0xFA = some (.aluImm .add a1 sp 0x58, 2) := by decide
theorem s5_at_fc : fetchRel sha512CompressCode 0xFC = some (.aluImm .add a2 x0 0x80, 4) := by decide
theorem s5_at_100 : fetchRel sha512CompressCode 0x100 = some (.auipc ra 0x0, 4) := by decide
theorem s5_at_104 : fetchRel sha512CompressCode 0x104 = some (.jalr ra ra 0x4AC, 4) := by decide
theorem s5_at_108 : fetchRel sha512CompressCode 0x108 = some (.aluImm .add a2 x0 0x200, 4) := by decide
theorem s5_at_10c : fetchRel sha512CompressCode 0x10C = some (.aluImm .add (8 : Fin 32) sp 0x158, 2) := by decide
theorem s5_at_10e : fetchRel sha512CompressCode 0x10E = some (.alu .add a0 x0 (8 : Fin 32), 2) := by decide
theorem s5_at_110 : fetchRel sha512CompressCode 0x110 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem s5_at_112 : fetchRel sha512CompressCode 0x112 = some (.auipc ra 0x0, 4) := by decide
theorem s5_at_116 : fetchRel sha512CompressCode 0x116 = some (.jalr ra ra 0x432, 4) := by decide
theorem s5_at_11a : fetchRel sha512CompressCode 0x11A = some (.aluImm .add a6 x0 0x40, 4) := by decide
theorem s5_at_11e : fetchRel sha512CompressCode 0x11E = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem s5_at_120 : fetchRel sha512CompressCode 0x120 = some (.branch .beq a6 x0 0xD0, 4) := by decide
theorem s5_at_124 : fetchRel sha512CompressCode 0x124 = some (.load .lw (29 : Fin 32) a1 0xFFFFFFF0, 4) := by decide
theorem s5_at_128 : fetchRel sha512CompressCode 0x128 = some (.load .lw a2 a1 0xFFFFFFF4, 4) := by decide
theorem s5_at_12c : fetchRel sha512CompressCode 0x12C = some (.load .lw (5 : Fin 32) a1 0xFFFFFFC8, 4) := by decide
theorem s5_at_130 : fetchRel sha512CompressCode 0x130 = some (.load .lw (17 : Fin 32) a1 0xFFFFFFCC, 4) := by decide
theorem s5_at_134 : fetchRel sha512CompressCode 0x134 = some (.aluImm .srl a5 (29 : Fin 32) 0x13, 4) := by decide
theorem s5_at_138 : fetchRel sha512CompressCode 0x138 = some (.aluImm .sll (8 : Fin 32) a2 0xD, 4) := by decide
theorem s5_at_13c : fetchRel sha512CompressCode 0x13C = some (.aluImm .srl a0 a2 0x13, 4) := by decide
theorem s5_at_140 : fetchRel sha512CompressCode 0x140 = some (.aluImm .sll a3 (29 : Fin 32) 0xD, 4) := by decide
theorem s5_at_144 : fetchRel sha512CompressCode 0x144 = some (.aluImm .srl (6 : Fin 32) a2 0x1D, 4) := by decide
theorem s5_at_148 : fetchRel sha512CompressCode 0x148 = some (.aluImm .srl (9 : Fin 32) (29 : Fin 32) 0x1D, 4) := by decide
theorem s5_at_14c : fetchRel sha512CompressCode 0x14C = some (.alu .or a4 (8 : Fin 32) a5, 4) := by decide
theorem s5_at_150 : fetchRel sha512CompressCode 0x150 = some (.alu .or a0 a0 a3, 2) := by decide
theorem s5_at_152 : fetchRel sha512CompressCode 0x152 = some (.aluImm .sll a3 a2 0x3, 4) := by decide
theorem s5_at_156 : fetchRel sha512CompressCode 0x156 = some (.aluImm .sll a5 (29 : Fin 32) 0x3, 4) := by decide
theorem s5_at_15a : fetchRel sha512CompressCode 0x15A = some (.alu .or a3 a3 (9 : Fin 32), 2) := by decide
theorem s5_at_15c : fetchRel sha512CompressCode 0x15C = some (.alu .or a5 a5 (6 : Fin 32), 4) := by decide
theorem s5_at_160 : fetchRel sha512CompressCode 0x160 = some (.alu .xor (28 : Fin 32) a0 a3, 4) := by decide
theorem s5_at_164 : fetchRel sha512CompressCode 0x164 = some (.load .lw (6 : Fin 32) a1 0xFFFFFF80, 4) := by decide
theorem s5_at_168 : fetchRel sha512CompressCode 0x168 = some (.load .lw (7 : Fin 32) a1 0xFFFFFF84, 4) := by decide
theorem s5_at_16c : fetchRel sha512CompressCode 0x16C = some (.load .lw a3 a1 0xFFFFFF88, 4) := by decide
theorem s5_at_170 : fetchRel sha512CompressCode 0x170 = some (.load .lw (8 : Fin 32) a1 0xFFFFFF8C, 4) := by decide
theorem s5_at_174 : fetchRel sha512CompressCode 0x174 = some (.aluImm .sll (9 : Fin 32) a2 0x1A, 4) := by decide
theorem s5_at_178 : fetchRel sha512CompressCode 0x178 = some (.aluImm .srl a0 (29 : Fin 32) 0x6, 4) := by decide
theorem s5_at_17c : fetchRel sha512CompressCode 0x17C = some (.alu .xor a5 a5 a4, 2) := by decide
theorem s5_at_17e : fetchRel sha512CompressCode 0x17E = some (.alu .or a0 a0 (9 : Fin 32), 2) := by decide
theorem s5_at_180 : fetchRel sha512CompressCode 0x180 = some (.aluImm .srl a2 a2 0x6, 2) := by decide
theorem s5_at_182 : fetchRel sha512CompressCode 0x182 = some (.alu .xor (29 : Fin 32) a5 a0, 4) := by decide
theorem s5_at_186 : fetchRel sha512CompressCode 0x186 = some (.aluImm .srl (9 : Fin 32) (8 : Fin 32) 0x1, 4) := by decide
theorem s5_at_18a : fetchRel sha512CompressCode 0x18A = some (.aluImm .sll a5 a3 0x1F, 4) := by decide
theorem s5_at_18e : fetchRel sha512CompressCode 0x18E = some (.alu .xor (28 : Fin 32) (28 : Fin 32) a2, 4) := by decide
theorem s5_at_192 : fetchRel sha512CompressCode 0x192 = some (.alu .or a2 a5 (9 : Fin 32), 4) := by decide
theorem s5_at_196 : fetchRel sha512CompressCode 0x196 = some (.aluImm .srl a5 a3 0x1, 4) := by decide
theorem s5_at_19a : fetchRel sha512CompressCode 0x19A = some (.aluImm .sll (9 : Fin 32) (8 : Fin 32) 0x1F, 4) := by decide
theorem s5_at_19e : fetchRel sha512CompressCode 0x19E = some (.alu .or a5 a5 (9 : Fin 32), 2) := by decide
theorem s5_at_1a0 : fetchRel sha512CompressCode 0x1A0 = some (.aluImm .srl (9 : Fin 32) (8 : Fin 32) 0x8, 4) := by decide
theorem s5_at_1a4 : fetchRel sha512CompressCode 0x1A4 = some (.aluImm .srl a0 a3 0x8, 4) := by decide
theorem s5_at_1a8 : fetchRel sha512CompressCode 0x1A8 = some (.aluImm .sll a4 (8 : Fin 32) 0x18, 4) := by decide
theorem s5_at_1ac : fetchRel sha512CompressCode 0x1AC = some (.alu .or a0 a0 a4, 2) := by decide
theorem s5_at_1ae : fetchRel sha512CompressCode 0x1AE = some (.aluImm .sll a4 a3 0x18, 4) := by decide
theorem s5_at_1b2 : fetchRel sha512CompressCode 0x1B2 = some (.alu .or a4 a4 (9 : Fin 32), 2) := by decide
theorem s5_at_1b4 : fetchRel sha512CompressCode 0x1B4 = some (.alu .xor a0 a0 a5, 2) := by decide
theorem s5_at_1b6 : fetchRel sha512CompressCode 0x1B6 = some (.alu .xor a2 a2 a4, 2) := by decide
theorem s5_at_1b8 : fetchRel sha512CompressCode 0x1B8 = some (.aluImm .sll a4 (8 : Fin 32) 0x19, 4) := by decide
theorem s5_at_1bc : fetchRel sha512CompressCode 0x1BC = some (.aluImm .srl a3 a3 0x7, 2) := by decide
theorem s5_at_1be : fetchRel sha512CompressCode 0x1BE = some (.aluImm .srl (8 : Fin 32) (8 : Fin 32) 0x7, 2) := by decide
theorem s5_at_1c0 : fetchRel sha512CompressCode 0x1C0 = some (.alu .or a3 a3 a4, 2) := by decide
theorem s5_at_1c2 : fetchRel sha512CompressCode 0x1C2 = some (.alu .xor a2 a2 (8 : Fin 32), 2) := by decide
theorem s5_at_1c4 : fetchRel sha512CompressCode 0x1C4 = some (.alu .xor a0 a0 a3, 2) := by decide
theorem s5_at_1c6 : fetchRel sha512CompressCode 0x1C6 = some (.alu .add (6 : Fin 32) (6 : Fin 32) (5 : Fin 32), 2) := by decide
theorem s5_at_1c8 : fetchRel sha512CompressCode 0x1C8 = some (.alu .add (17 : Fin 32) (17 : Fin 32) (7 : Fin 32), 2) := by decide
theorem s5_at_1ca : fetchRel sha512CompressCode 0x1CA = some (.alu .sltu a3 (6 : Fin 32) (5 : Fin 32), 4) := by decide
theorem s5_at_1ce : fetchRel sha512CompressCode 0x1CE = some (.alu .add a3 a3 (17 : Fin 32), 2) := by decide
theorem s5_at_1d0 : fetchRel sha512CompressCode 0x1D0 = some (.alu .add (29 : Fin 32) (29 : Fin 32) (6 : Fin 32), 2) := by decide
theorem s5_at_1d2 : fetchRel sha512CompressCode 0x1D2 = some (.alu .add a3 a3 (28 : Fin 32), 2) := by decide
theorem s5_at_1d4 : fetchRel sha512CompressCode 0x1D4 = some (.alu .sltu a4 (29 : Fin 32) (6 : Fin 32), 4) := by decide
theorem s5_at_1d8 : fetchRel sha512CompressCode 0x1D8 = some (.alu .add a0 a0 (29 : Fin 32), 2) := by decide
theorem s5_at_1da : fetchRel sha512CompressCode 0x1DA = some (.alu .add a2 a2 a3, 2) := by decide
theorem s5_at_1dc : fetchRel sha512CompressCode 0x1DC = some (.alu .sltu a3 a0 (29 : Fin 32), 4) := by decide
theorem s5_at_1e0 : fetchRel sha512CompressCode 0x1E0 = some (.alu .add a2 a2 a4, 2) := by decide
theorem s5_at_1e2 : fetchRel sha512CompressCode 0x1E2 = some (.alu .add a2 a2 a3, 2) := by decide
theorem s5_at_1e4 : fetchRel sha512CompressCode 0x1E4 = some (.store .sw a1 a0 0x0, 2) := by decide
theorem s5_at_1e6 : fetchRel sha512CompressCode 0x1E6 = some (.store .sw a1 a2 0x4, 2) := by decide
theorem s5_at_1e8 : fetchRel sha512CompressCode 0x1E8 = some (.aluImm .add a6 a6 0xFFFFFFFF, 2) := by decide
theorem s5_at_1ea : fetchRel sha512CompressCode 0x1EA = some (.aluImm .add a1 a1 0x8, 2) := by decide
theorem s5_at_1ec : fetchRel sha512CompressCode 0x1EC = some (.branch .bne a6 x0 0xFFFFFF38, 4) := by decide
theorem s5_at_1f0 : fetchRel sha512CompressCode 0x1F0 = some (.aluImm .add (30 : Fin 32) sp 0xD8, 4) := by decide
theorem s5_at_1f4 : fetchRel sha512CompressCode 0x1F4 = some (.aluImm .add (29 : Fin 32) x0 0x50, 4) := by decide
theorem s5_at_1f8 : fetchRel sha512CompressCode 0x1F8 = some (.lui (25 : Fin 32) 0x3FCC5000, 4) := by decide
theorem s5_at_1fc : fetchRel sha512CompressCode 0x1FC = some (.aluImm .add (25 : Fin 32) (25 : Fin 32) 0xFFFFFFC0, 4) := by decide
theorem s5_at_200 : fetchRel sha512CompressCode 0x200 = some (.store .sw sp (20 : Fin 32) 0x14, 2) := by decide
theorem s5_at_202 : fetchRel sha512CompressCode 0x202 = some (.alu .add a2 x0 (20 : Fin 32), 2) := by decide
theorem s5_at_204 : fetchRel sha512CompressCode 0x204 = some (.load .lw a3 sp 0x4C, 2) := by decide
theorem s5_at_206 : fetchRel sha512CompressCode 0x206 = some (.store .sw sp (23 : Fin 32) 0x30, 2) := by decide
theorem s5_at_208 : fetchRel sha512CompressCode 0x208 = some (.store .sw sp (19 : Fin 32) 0x1C, 2) := by decide
theorem s5_at_20a : fetchRel sha512CompressCode 0x20A = some (.alu .add a0 x0 (19 : Fin 32), 2) := by decide
theorem s5_at_20c : fetchRel sha512CompressCode 0x20C = some (.load .lw ra sp 0x40, 2) := by decide
theorem s5_at_20e : fetchRel sha512CompressCode 0x20E = some (.load .lw a6 sp 0x38, 2) := by decide
theorem s5_at_210 : fetchRel sha512CompressCode 0x210 = some (.load .lw (17 : Fin 32) sp 0x48, 2) := by decide
theorem s5_at_212 : fetchRel sha512CompressCode 0x212 = some (.load .lw (21 : Fin 32) sp 0x3C, 2) := by decide
theorem s5_at_214 : fetchRel sha512CompressCode 0x214 = some (.load .lw (6 : Fin 32) sp 0x50, 2) := by decide
theorem s5_at_216 : fetchRel sha512CompressCode 0x216 = some (.load .lw (5 : Fin 32) sp 0x44, 2) := by decide
theorem s5_at_218 : fetchRel sha512CompressCode 0x218 = some (.store .sw sp (18 : Fin 32) 0x24, 2) := by decide
theorem s5_at_21a : fetchRel sha512CompressCode 0x21A = some (.alu .add (19 : Fin 32) x0 (18 : Fin 32), 2) := by decide
theorem s5_at_21c : fetchRel sha512CompressCode 0x21C = some (.load .lw (20 : Fin 32) sp 0x54, 2) := by decide
theorem s5_at_21e : fetchRel sha512CompressCode 0x21E = some (.store .sw sp (24 : Fin 32) 0x28, 2) := by decide
theorem s5_at_220 : fetchRel sha512CompressCode 0x220 = some (.alu .add (18 : Fin 32) x0 (24 : Fin 32), 2) := by decide
theorem s5_at_222 : fetchRel sha512CompressCode 0x222 = some (.store .sw sp (26 : Fin 32) 0x20, 2) := by decide
theorem s5_at_224 : fetchRel sha512CompressCode 0x224 = some (.store .sw sp (22 : Fin 32) 0x2C, 2) := by decide
theorem s5_at_226 : fetchRel sha512CompressCode 0x226 = some (.alu .add (28 : Fin 32) x0 (22 : Fin 32), 2) := by decide
theorem s5_at_228 : fetchRel sha512CompressCode 0x228 = some (.store .sw sp (27 : Fin 32) 0x18, 2) := by decide
theorem s5_at_22a : fetchRel sha512CompressCode 0x22A = some (.alu .add (7 : Fin 32) x0 (27 : Fin 32), 2) := by decide
theorem s5_at_22c : fetchRel sha512CompressCode 0x22C = some (.alu .add (24 : Fin 32) x0 a0, 2) := by decide
theorem s5_at_22e : fetchRel sha512CompressCode 0x22E = some (.alu .add (31 : Fin 32) x0 (23 : Fin 32), 2) := by decide
theorem s5_at_230 : fetchRel sha512CompressCode 0x230 = some (.alu .add (22 : Fin 32) x0 a3, 2) := by decide
theorem s5_at_232 : fetchRel sha512CompressCode 0x232 = some (.alu .add (27 : Fin 32) x0 a2, 2) := by decide
theorem s5_at_234 : fetchRel sha512CompressCode 0x234 = some (.branch .beq (29 : Fin 32) x0 0x142, 4) := by decide
theorem s5_at_238 : fetchRel sha512CompressCode 0x238 = some (.aluImm .sll a2 (27 : Fin 32) 0x12, 4) := by decide
theorem s5_at_23c : fetchRel sha512CompressCode 0x23C = some (.aluImm .srl a3 (22 : Fin 32) 0xE, 4) := by decide
theorem s5_at_240 : fetchRel sha512CompressCode 0x240 = some (.aluImm .srl (9 : Fin 32) (27 : Fin 32) 0xE, 4) := by decide
theorem s5_at_244 : fetchRel sha512CompressCode 0x244 = some (.alu .or a2 a2 a3, 2) := by decide
theorem s5_at_246 : fetchRel sha512CompressCode 0x246 = some (.aluImm .sll a3 (22 : Fin 32) 0x12, 4) := by decide
theorem s5_at_24a : fetchRel sha512CompressCode 0x24A = some (.alu .or a3 a3 (9 : Fin 32), 2) := by decide
theorem s5_at_24c : fetchRel sha512CompressCode 0x24C = some (.aluImm .sll (9 : Fin 32) (27 : Fin 32) 0xE, 4) := by decide
theorem s5_at_250 : fetchRel sha512CompressCode 0x250 = some (.aluImm .srl a1 (27 : Fin 32) 0x12, 4) := by decide
theorem s5_at_254 : fetchRel sha512CompressCode 0x254 = some (.aluImm .sll a0 (22 : Fin 32) 0xE, 4) := by decide
theorem s5_at_258 : fetchRel sha512CompressCode 0x258 = some (.aluImm .srl (8 : Fin 32) (22 : Fin 32) 0x12, 4) := by decide
theorem s5_at_25c : fetchRel sha512CompressCode 0x25C = some (.alu .or a0 a0 a1, 2) := by decide
theorem s5_at_25e : fetchRel sha512CompressCode 0x25E = some (.alu .or (8 : Fin 32) (8 : Fin 32) (9 : Fin 32), 2) := by decide
theorem s5_at_260 : fetchRel sha512CompressCode 0x260 = some (.alu .xor a0 a0 a3, 2) := by decide
theorem s5_at_262 : fetchRel sha512CompressCode 0x262 = some (.alu .xor a2 a2 (8 : Fin 32), 2) := by decide
theorem s5_at_264 : fetchRel sha512CompressCode 0x264 = some (.aluImm .sll a1 (27 : Fin 32) 0x17, 4) := by decide
theorem s5_at_268 : fetchRel sha512CompressCode 0x268 = some (.aluImm .srl a3 (27 : Fin 32) 0x9, 4) := by decide
theorem s5_at_26c : fetchRel sha512CompressCode 0x26C = some (.aluImm .sll (8 : Fin 32) (22 : Fin 32) 0x17, 4) := by decide
theorem s5_at_270 : fetchRel sha512CompressCode 0x270 = some (.aluImm .srl (9 : Fin 32) (22 : Fin 32) 0x9, 4) := by decide
theorem s5_at_274 : fetchRel sha512CompressCode 0x274 = some (.alu .or a3 a3 (8 : Fin 32), 2) := by decide
theorem s5_at_276 : fetchRel sha512CompressCode 0x276 = some (.alu .or a1 a1 (9 : Fin 32), 2) := by decide
theorem s5_at_278 : fetchRel sha512CompressCode 0x278 = some (.alu .xor a2 a2 a3, 2) := by decide
theorem s5_at_27a : fetchRel sha512CompressCode 0x27A = some (.alu .xor a0 a0 a1, 2) := by decide
theorem s5_at_27c : fetchRel sha512CompressCode 0x27C = some (.alu .and (23 : Fin 32) (6 : Fin 32) (27 : Fin 32), 4) := by decide
theorem s5_at_280 : fetchRel sha512CompressCode 0x280 = some (.alu .and a4 (5 : Fin 32) (22 : Fin 32), 4) := by decide
theorem s5_at_284 : fetchRel sha512CompressCode 0x284 = some (.aluImm .xor (8 : Fin 32) (22 : Fin 32) 0xFFFFFFFF, 4) := by decide
theorem s5_at_288 : fetchRel sha512CompressCode 0x288 = some (.aluImm .xor (9 : Fin 32) (27 : Fin 32) 0xFFFFFFFF, 4) := by decide
theorem s5_at_28c : fetchRel sha512CompressCode 0x28C = some (.alu .and (8 : Fin 32) (21 : Fin 32) (8 : Fin 32), 4) := by decide
theorem s5_at_290 : fetchRel sha512CompressCode 0x290 = some (.alu .and (9 : Fin 32) (17 : Fin 32) (9 : Fin 32), 4) := by decide
theorem s5_at_294 : fetchRel sha512CompressCode 0x294 = some (.alu .add a2 a2 a6, 2) := by decide
theorem s5_at_296 : fetchRel sha512CompressCode 0x296 = some (.alu .add a2 a2 (8 : Fin 32), 2) := by decide
theorem s5_at_298 : fetchRel sha512CompressCode 0x298 = some (.alu .add a3 x0 (25 : Fin 32), 2) := by decide
theorem s5_at_29a : fetchRel sha512CompressCode 0x29A = some (.load .lw (8 : Fin 32) a3 0x0, 2) := by decide
theorem s5_at_29c : fetchRel sha512CompressCode 0x29C = some (.load .lw a1 a3 0x4, 2) := by decide
theorem s5_at_29e : fetchRel sha512CompressCode 0x29E = some (.alu .add ra ra a0, 2) := by decide
theorem s5_at_2a0 : fetchRel sha512CompressCode 0x2A0 = some (.alu .sltu a0 ra a0, 4) := by decide
theorem s5_at_2a4 : fetchRel sha512CompressCode 0x2A4 = some (.alu .add (9 : Fin 32) (9 : Fin 32) ra, 2) := by decide
theorem s5_at_2a6 : fetchRel sha512CompressCode 0x2A6 = some (.alu .sltu a3 (9 : Fin 32) ra, 4) := by decide
theorem s5_at_2aa : fetchRel sha512CompressCode 0x2AA = some (.alu .add a0 a0 a2, 2) := by decide
theorem s5_at_2ac : fetchRel sha512CompressCode 0x2AC = some (.alu .add a0 a0 a3, 2) := by decide
theorem s5_at_2ae : fetchRel sha512CompressCode 0x2AE = some (.alu .add a5 x0 (30 : Fin 32), 2) := by decide
theorem s5_at_2b0 : fetchRel sha512CompressCode 0x2B0 = some (.load .lw a2 a5 0x0, 2) := by decide
theorem s5_at_2b2 : fetchRel sha512CompressCode 0x2B2 = some (.load .lw a3 a5 0x4, 2) := by decide
theorem s5_at_2b4 : fetchRel sha512CompressCode 0x2B4 = some (.alu .add (23 : Fin 32) (23 : Fin 32) (9 : Fin 32), 2) := by decide
theorem s5_at_2b6 : fetchRel sha512CompressCode 0x2B6 = some (.alu .add a0 a0 a4, 2) := by decide
theorem s5_at_2b8 : fetchRel sha512CompressCode 0x2B8 = some (.alu .sltu (9 : Fin 32) (23 : Fin 32) (9 : Fin 32), 4) := by decide
theorem s5_at_2bc : fetchRel sha512CompressCode 0x2BC = some (.alu .add a1 a1 (9 : Fin 32), 2) := by decide
theorem s5_at_2be : fetchRel sha512CompressCode 0x2BE = some (.alu .add (8 : Fin 32) (8 : Fin 32) (23 : Fin 32), 2) := by decide
theorem s5_at_2c0 : fetchRel sha512CompressCode 0x2C0 = some (.alu .add a0 a0 a1, 2) := by decide
theorem s5_at_2c2 : fetchRel sha512CompressCode 0x2C2 = some (.alu .sltu a1 (8 : Fin 32) (23 : Fin 32), 4) := by decide
theorem s5_at_2c6 : fetchRel sha512CompressCode 0x2C6 = some (.alu .add a1 a1 a3, 2) := by decide
theorem s5_at_2c8 : fetchRel sha512CompressCode 0x2C8 = some (.alu .add (23 : Fin 32) (8 : Fin 32) a2, 4) := by decide
theorem s5_at_2cc : fetchRel sha512CompressCode 0x2CC = some (.alu .add a0 a0 a1, 2) := by decide
theorem s5_at_2ce : fetchRel sha512CompressCode 0x2CE = some (.alu .sltu a1 (23 : Fin 32) (8 : Fin 32), 4) := by decide
theorem s5_at_2d2 : fetchRel sha512CompressCode 0x2D2 = some (.aluImm .srl a2 (31 : Fin 32) 0x1C, 4) := by decide
theorem s5_at_2d6 : fetchRel sha512CompressCode 0x2D6 = some (.aluImm .sll a3 (24 : Fin 32) 0x4, 4) := by decide
theorem s5_at_2da : fetchRel sha512CompressCode 0x2DA = some (.alu .add a0 a0 a1, 2) := by decide
theorem s5_at_2dc : fetchRel sha512CompressCode 0x2DC = some (.alu .or a2 a2 a3, 2) := by decide
theorem s5_at_2de : fetchRel sha512CompressCode 0x2DE = some (.aluImm .sll a1 (31 : Fin 32) 0x4, 4) := by decide
theorem s5_at_2e2 : fetchRel sha512CompressCode 0x2E2 = some (.aluImm .srl a3 (24 : Fin 32) 0x1C, 4) := by decide
theorem s5_at_2e6 : fetchRel sha512CompressCode 0x2E6 = some (.alu .or a1 a1 a3, 2) := by decide
theorem s5_at_2e8 : fetchRel sha512CompressCode 0x2E8 = some (.aluImm .sll a3 (31 : Fin 32) 0x1E, 4) := by decide
theorem s5_at_2ec : fetchRel sha512CompressCode 0x2EC = some (.aluImm .srl a4 (31 : Fin 32) 0x2, 4) := by decide
theorem s5_at_2f0 : fetchRel sha512CompressCode 0x2F0 = some (.aluImm .sll a5 (24 : Fin 32) 0x1E, 4) := by decide
theorem s5_at_2f4 : fetchRel sha512CompressCode 0x2F4 = some (.alu .or a4 a4 a5, 2) := by decide
theorem s5_at_2f6 : fetchRel sha512CompressCode 0x2F6 = some (.aluImm .srl a5 (24 : Fin 32) 0x2, 4) := by decide
theorem s5_at_2fa : fetchRel sha512CompressCode 0x2FA = some (.alu .or a3 a3 a5, 2) := by decide
theorem s5_at_2fc : fetchRel sha512CompressCode 0x2FC = some (.alu .xor a1 a1 a4, 2) := by decide
theorem s5_at_2fe : fetchRel sha512CompressCode 0x2FE = some (.alu .xor a2 a2 a3, 2) := by decide
theorem s5_at_300 : fetchRel sha512CompressCode 0x300 = some (.aluImm .srl a3 (31 : Fin 32) 0x7, 4) := by decide
theorem s5_at_304 : fetchRel sha512CompressCode 0x304 = some (.aluImm .sll a4 (31 : Fin 32) 0x19, 4) := by decide
theorem s5_at_308 : fetchRel sha512CompressCode 0x308 = some (.aluImm .srl a5 (24 : Fin 32) 0x7, 4) := by decide
theorem s5_at_30c : fetchRel sha512CompressCode 0x30C = some (.alu .or a4 a4 a5, 2) := by decide
theorem s5_at_30e : fetchRel sha512CompressCode 0x30E = some (.aluImm .sll a5 (24 : Fin 32) 0x19, 4) := by decide
theorem s5_at_312 : fetchRel sha512CompressCode 0x312 = some (.alu .or a3 a3 a5, 2) := by decide
theorem s5_at_314 : fetchRel sha512CompressCode 0x314 = some (.alu .xor a2 a2 a4, 2) := by decide
theorem s5_at_316 : fetchRel sha512CompressCode 0x316 = some (.alu .xor a1 a1 a3, 2) := by decide
theorem s5_at_318 : fetchRel sha512CompressCode 0x318 = some (.alu .xor a3 (7 : Fin 32) (26 : Fin 32), 4) := by decide
theorem s5_at_31c : fetchRel sha512CompressCode 0x31C = some (.alu .xor a4 (28 : Fin 32) (18 : Fin 32), 4) := by decide
theorem s5_at_320 : fetchRel sha512CompressCode 0x320 = some (.alu .and a3 a3 (24 : Fin 32), 4) := by decide
theorem s5_at_324 : fetchRel sha512CompressCode 0x324 = some (.alu .and a4 a4 (31 : Fin 32), 4) := by decide
theorem s5_at_328 : fetchRel sha512CompressCode 0x328 = some (.alu .and a5 (28 : Fin 32) (18 : Fin 32), 4) := by decide
theorem s5_at_32c : fetchRel sha512CompressCode 0x32C = some (.alu .xor a4 a4 a5, 2) := by decide
theorem s5_at_32e : fetchRel sha512CompressCode 0x32E = some (.alu .and a5 (7 : Fin 32) (26 : Fin 32), 4) := by decide
theorem s5_at_332 : fetchRel sha512CompressCode 0x332 = some (.alu .xor a3 a3 a5, 2) := by decide
theorem s5_at_334 : fetchRel sha512CompressCode 0x334 = some (.alu .add a5 a4 a2, 4) := by decide
theorem s5_at_338 : fetchRel sha512CompressCode 0x338 = some (.alu .add a1 a1 a3, 2) := by decide
theorem s5_at_33a : fetchRel sha512CompressCode 0x33A = some (.alu .sltu a2 a5 a4, 4) := by decide
theorem s5_at_33e : fetchRel sha512CompressCode 0x33E = some (.alu .add a1 a1 a2, 2) := by decide
theorem s5_at_340 : fetchRel sha512CompressCode 0x340 = some (.alu .add a2 (23 : Fin 32) (19 : Fin 32), 4) := by decide
theorem s5_at_344 : fetchRel sha512CompressCode 0x344 = some (.alu .sltu a3 a2 (23 : Fin 32), 4) := by decide
theorem s5_at_348 : fetchRel sha512CompressCode 0x348 = some (.alu .add (23 : Fin 32) (23 : Fin 32) a5, 2) := by decide
theorem s5_at_34a : fetchRel sha512CompressCode 0x34A = some (.alu .add a3 a3 (20 : Fin 32), 2) := by decide
theorem s5_at_34c : fetchRel sha512CompressCode 0x34C = some (.alu .sltu a4 (23 : Fin 32) a5, 4) := by decide
theorem s5_at_350 : fetchRel sha512CompressCode 0x350 = some (.alu .add a1 a1 a4, 2) := by decide
theorem s5_at_352 : fetchRel sha512CompressCode 0x352 = some (.alu .add a3 a3 a0, 2) := by decide
theorem s5_at_354 : fetchRel sha512CompressCode 0x354 = some (.alu .add a0 a0 a1, 2) := by decide
theorem s5_at_356 : fetchRel sha512CompressCode 0x356 = some (.aluImm .add (25 : Fin 32) (25 : Fin 32) 0x8, 2) := by decide
theorem s5_at_358 : fetchRel sha512CompressCode 0x358 = some (.aluImm .add (30 : Fin 32) (30 : Fin 32) 0x8, 2) := by decide
theorem s5_at_35a : fetchRel sha512CompressCode 0x35A = some (.aluImm .add (29 : Fin 32) (29 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem s5_at_35c : fetchRel sha512CompressCode 0x35C = some (.alu .add ra x0 (17 : Fin 32), 2) := by decide
theorem s5_at_35e : fetchRel sha512CompressCode 0x35E = some (.alu .add a6 x0 (21 : Fin 32), 2) := by decide
theorem s5_at_360 : fetchRel sha512CompressCode 0x360 = some (.alu .add (17 : Fin 32) x0 (6 : Fin 32), 2) := by decide
theorem s5_at_362 : fetchRel sha512CompressCode 0x362 = some (.alu .add (21 : Fin 32) x0 (5 : Fin 32), 2) := by decide
theorem s5_at_364 : fetchRel sha512CompressCode 0x364 = some (.alu .add (6 : Fin 32) x0 (27 : Fin 32), 2) := by decide
theorem s5_at_366 : fetchRel sha512CompressCode 0x366 = some (.alu .add (5 : Fin 32) x0 (22 : Fin 32), 2) := by decide
theorem s5_at_368 : fetchRel sha512CompressCode 0x368 = some (.alu .add (19 : Fin 32) x0 (18 : Fin 32), 2) := by decide
theorem s5_at_36a : fetchRel sha512CompressCode 0x36A = some (.alu .add (20 : Fin 32) x0 (26 : Fin 32), 2) := by decide
theorem s5_at_36c : fetchRel sha512CompressCode 0x36C = some (.alu .add (18 : Fin 32) x0 (28 : Fin 32), 2) := by decide
theorem s5_at_36e : fetchRel sha512CompressCode 0x36E = some (.alu .add (26 : Fin 32) x0 (7 : Fin 32), 2) := by decide
theorem s5_at_370 : fetchRel sha512CompressCode 0x370 = some (.alu .add (28 : Fin 32) x0 (31 : Fin 32), 2) := by decide
theorem s5_at_372 : fetchRel sha512CompressCode 0x372 = some (.alu .add (7 : Fin 32) x0 (24 : Fin 32), 2) := by decide
theorem s5_at_374 : fetchRel sha512CompressCode 0x374 = some (.jal x0 0xFFFFFEB8, 2) := by decide
theorem s5_at_376 : fetchRel sha512CompressCode 0x376 = some (.load .lw a0 sp 0x1C, 2) := by decide
theorem s5_at_378 : fetchRel sha512CompressCode 0x378 = some (.alu .add (24 : Fin 32) (24 : Fin 32) a0, 2) := by decide
theorem s5_at_37a : fetchRel sha512CompressCode 0x37A = some (.load .lw a0 sp 0x18, 2) := by decide
theorem s5_at_37c : fetchRel sha512CompressCode 0x37C = some (.alu .add (7 : Fin 32) (7 : Fin 32) a0, 2) := by decide
theorem s5_at_37e : fetchRel sha512CompressCode 0x37E = some (.load .lw (23 : Fin 32) sp 0x30, 2) := by decide
theorem s5_at_380 : fetchRel sha512CompressCode 0x380 = some (.alu .add (23 : Fin 32) (23 : Fin 32) (31 : Fin 32), 2) := by decide
theorem s5_at_382 : fetchRel sha512CompressCode 0x382 = some (.alu .sltu a0 (23 : Fin 32) (31 : Fin 32), 4) := by decide
theorem s5_at_386 : fetchRel sha512CompressCode 0x386 = some (.load .lw a1 sp 0x2C, 2) := by decide
theorem s5_at_388 : fetchRel sha512CompressCode 0x388 = some (.alu .add a1 a1 (28 : Fin 32), 2) := by decide
theorem s5_at_38a : fetchRel sha512CompressCode 0x38A = some (.alu .add a2 (24 : Fin 32) a0, 4) := by decide
theorem s5_at_38e : fetchRel sha512CompressCode 0x38E = some (.alu .sltu a0 a1 (28 : Fin 32), 4) := by decide
theorem s5_at_392 : fetchRel sha512CompressCode 0x392 = some (.alu .add (7 : Fin 32) (7 : Fin 32) a0, 2) := by decide
theorem s5_at_394 : fetchRel sha512CompressCode 0x394 = some (.load .lw (24 : Fin 32) sp 0x28, 2) := by decide
theorem s5_at_396 : fetchRel sha512CompressCode 0x396 = some (.alu .add (24 : Fin 32) (24 : Fin 32) (18 : Fin 32), 2) := by decide
theorem s5_at_398 : fetchRel sha512CompressCode 0x398 = some (.load .lw a0 sp 0x20, 2) := by decide
theorem s5_at_39a : fetchRel sha512CompressCode 0x39A = some (.alu .add (26 : Fin 32) (26 : Fin 32) a0, 2) := by decide
theorem s5_at_39c : fetchRel sha512CompressCode 0x39C = some (.alu .sltu a0 (24 : Fin 32) (18 : Fin 32), 4) := by decide
theorem s5_at_3a0 : fetchRel sha512CompressCode 0x3A0 = some (.alu .add (26 : Fin 32) (26 : Fin 32) a0, 2) := by decide
theorem s5_at_3a2 : fetchRel sha512CompressCode 0x3A2 = some (.load .lw (18 : Fin 32) sp 0x24, 2) := by decide
theorem s5_at_3a4 : fetchRel sha512CompressCode 0x3A4 = some (.alu .add (18 : Fin 32) (18 : Fin 32) (19 : Fin 32), 2) := by decide
theorem s5_at_3a6 : fetchRel sha512CompressCode 0x3A6 = some (.load .lw a0 sp 0x54, 2) := by decide
theorem s5_at_3a8 : fetchRel sha512CompressCode 0x3A8 = some (.alu .add (20 : Fin 32) (20 : Fin 32) a0, 2) := by decide
theorem s5_at_3aa : fetchRel sha512CompressCode 0x3AA = some (.alu .sltu a0 (18 : Fin 32) (19 : Fin 32), 4) := by decide
theorem s5_at_3ae : fetchRel sha512CompressCode 0x3AE = some (.alu .add (19 : Fin 32) x0 a2, 2) := by decide
theorem s5_at_3b0 : fetchRel sha512CompressCode 0x3B0 = some (.alu .add a2 (20 : Fin 32) a0, 4) := by decide
theorem s5_at_3b4 : fetchRel sha512CompressCode 0x3B4 = some (.load .lw (20 : Fin 32) sp 0x14, 2) := by decide
theorem s5_at_3b6 : fetchRel sha512CompressCode 0x3B6 = some (.alu .add (20 : Fin 32) (20 : Fin 32) (27 : Fin 32), 2) := by decide
theorem s5_at_3b8 : fetchRel sha512CompressCode 0x3B8 = some (.load .lw a0 sp 0x4C, 2) := by decide
theorem s5_at_3ba : fetchRel sha512CompressCode 0x3BA = some (.alu .add (22 : Fin 32) (22 : Fin 32) a0, 2) := by decide
theorem s5_at_3bc : fetchRel sha512CompressCode 0x3BC = some (.alu .sltu a0 (20 : Fin 32) (27 : Fin 32), 4) := by decide
theorem s5_at_3c0 : fetchRel sha512CompressCode 0x3C0 = some (.alu .add (27 : Fin 32) x0 (7 : Fin 32), 2) := by decide
theorem s5_at_3c2 : fetchRel sha512CompressCode 0x3C2 = some (.alu .add a3 (22 : Fin 32) a0, 4) := by decide
theorem s5_at_3c6 : fetchRel sha512CompressCode 0x3C6 = some (.alu .add (22 : Fin 32) x0 a1, 2) := by decide
theorem s5_at_3c8 : fetchRel sha512CompressCode 0x3C8 = some (.load .lw a1 sp 0x50, 2) := by decide
theorem s5_at_3ca : fetchRel sha512CompressCode 0x3CA = some (.alu .add a1 a1 (6 : Fin 32), 2) := by decide
theorem s5_at_3cc : fetchRel sha512CompressCode 0x3CC = some (.load .lw a0 sp 0x44, 2) := by decide
theorem s5_at_3ce : fetchRel sha512CompressCode 0x3CE = some (.alu .add (5 : Fin 32) (5 : Fin 32) a0, 2) := by decide
theorem s5_at_3d0 : fetchRel sha512CompressCode 0x3D0 = some (.alu .sltu a0 a1 (6 : Fin 32), 4) := by decide
theorem s5_at_3d4 : fetchRel sha512CompressCode 0x3D4 = some (.alu .add (5 : Fin 32) (5 : Fin 32) a0, 2) := by decide
theorem s5_at_3d6 : fetchRel sha512CompressCode 0x3D6 = some (.load .lw a4 sp 0x48, 2) := by decide
theorem s5_at_3d8 : fetchRel sha512CompressCode 0x3D8 = some (.alu .add a4 a4 (17 : Fin 32), 2) := by decide
theorem s5_at_3da : fetchRel sha512CompressCode 0x3DA = some (.load .lw a0 sp 0x3C, 2) := by decide
theorem s5_at_3dc : fetchRel sha512CompressCode 0x3DC = some (.alu .add (21 : Fin 32) (21 : Fin 32) a0, 2) := by decide
theorem s5_at_3de : fetchRel sha512CompressCode 0x3DE = some (.alu .sltu a0 a4 (17 : Fin 32), 4) := by decide
theorem s5_at_3e2 : fetchRel sha512CompressCode 0x3E2 = some (.alu .add (21 : Fin 32) (21 : Fin 32) a0, 2) := by decide
theorem s5_at_3e4 : fetchRel sha512CompressCode 0x3E4 = some (.load .lw a5 sp 0x40, 2) := by decide
theorem s5_at_3e6 : fetchRel sha512CompressCode 0x3E6 = some (.alu .add a5 a5 ra, 2) := by decide
theorem s5_at_3e8 : fetchRel sha512CompressCode 0x3E8 = some (.load .lw a0 sp 0x38, 2) := by decide
theorem s5_at_3ea : fetchRel sha512CompressCode 0x3EA = some (.alu .add a6 a6 a0, 2) := by decide
theorem s5_at_3ec : fetchRel sha512CompressCode 0x3EC = some (.alu .sltu a0 a5 ra, 4) := by decide
theorem s5_at_3f0 : fetchRel sha512CompressCode 0x3F0 = some (.alu .add a6 a6 a0, 2) := by decide
theorem s5_at_3f2 : fetchRel sha512CompressCode 0x3F2 = some (.load .lw a0 sp 0xC, 2) := by decide
theorem s5_at_3f4 : fetchRel sha512CompressCode 0x3F4 = some (.store .sw a0 (23 : Fin 32) 0x0, 4) := by decide
theorem s5_at_3f8 : fetchRel sha512CompressCode 0x3F8 = some (.store .sw a0 (19 : Fin 32) 0x4, 4) := by decide
theorem s5_at_3fc : fetchRel sha512CompressCode 0x3FC = some (.store .sw a0 (22 : Fin 32) 0x8, 4) := by decide
theorem s5_at_400 : fetchRel sha512CompressCode 0x400 = some (.store .sw a0 (7 : Fin 32) 0xC, 4) := by decide
theorem s5_at_404 : fetchRel sha512CompressCode 0x404 = some (.store .sw a0 (24 : Fin 32) 0x10, 4) := by decide
theorem s5_at_408 : fetchRel sha512CompressCode 0x408 = some (.store .sw a0 (26 : Fin 32) 0x14, 4) := by decide
theorem s5_at_40c : fetchRel sha512CompressCode 0x40C = some (.store .sw a0 (18 : Fin 32) 0x18, 4) := by decide
theorem s5_at_410 : fetchRel sha512CompressCode 0x410 = some (.store .sw sp a2 0x54, 2) := by decide
theorem s5_at_412 : fetchRel sha512CompressCode 0x412 = some (.store .sw a0 a2 0x1C, 2) := by decide
theorem s5_at_414 : fetchRel sha512CompressCode 0x414 = some (.store .sw a0 (20 : Fin 32) 0x20, 4) := by decide
theorem s5_at_418 : fetchRel sha512CompressCode 0x418 = some (.store .sw sp a3 0x4C, 2) := by decide
theorem s5_at_41a : fetchRel sha512CompressCode 0x41A = some (.store .sw a0 a3 0x24, 2) := by decide
theorem s5_at_41c : fetchRel sha512CompressCode 0x41C = some (.store .sw sp a1 0x50, 2) := by decide
theorem s5_at_41e : fetchRel sha512CompressCode 0x41E = some (.store .sw a0 a1 0x28, 2) := by decide
theorem s5_at_420 : fetchRel sha512CompressCode 0x420 = some (.store .sw sp (5 : Fin 32) 0x44, 2) := by decide
theorem s5_at_422 : fetchRel sha512CompressCode 0x422 = some (.store .sw a0 (5 : Fin 32) 0x2C, 4) := by decide
theorem s5_at_426 : fetchRel sha512CompressCode 0x426 = some (.store .sw sp a4 0x48, 2) := by decide
theorem s5_at_428 : fetchRel sha512CompressCode 0x428 = some (.store .sw a0 a4 0x30, 2) := by decide
theorem s5_at_42a : fetchRel sha512CompressCode 0x42A = some (.store .sw sp (21 : Fin 32) 0x3C, 2) := by decide
theorem s5_at_42c : fetchRel sha512CompressCode 0x42C = some (.store .sw a0 (21 : Fin 32) 0x34, 4) := by decide
theorem s5_at_430 : fetchRel sha512CompressCode 0x430 = some (.store .sw sp a5 0x40, 2) := by decide
theorem s5_at_432 : fetchRel sha512CompressCode 0x432 = some (.store .sw a0 a5 0x38, 2) := by decide
theorem s5_at_434 : fetchRel sha512CompressCode 0x434 = some (.store .sw sp a6 0x38, 2) := by decide
theorem s5_at_436 : fetchRel sha512CompressCode 0x436 = some (.store .sw a0 a6 0x3C, 4) := by decide
theorem s5_at_43a : fetchRel sha512CompressCode 0x43A = some (.load .lw (21 : Fin 32) sp 0x34, 2) := by decide
theorem s5_at_43c : fetchRel sha512CompressCode 0x43C = some (.jal x0 0xFFFFFC46, 2) := by decide
theorem s5_at_43e : fetchRel sha512CompressCode 0x43E = some (.aluImm .add a0 sp 0x380, 2) := by decide
theorem s5_at_440 : fetchRel sha512CompressCode 0x440 = some (.load .lw ra a0 0xC, 4) := by decide
theorem s5_at_444 : fetchRel sha512CompressCode 0x444 = some (.load .lw (8 : Fin 32) a0 0x8, 2) := by decide
theorem s5_at_446 : fetchRel sha512CompressCode 0x446 = some (.load .lw (9 : Fin 32) a0 0x4, 2) := by decide
theorem s5_at_448 : fetchRel sha512CompressCode 0x448 = some (.load .lw (18 : Fin 32) a0 0x0, 4) := by decide
theorem s5_at_44c : fetchRel sha512CompressCode 0x44C = some (.aluImm .add a0 sp 0x300, 2) := by decide
theorem s5_at_44e : fetchRel sha512CompressCode 0x44E = some (.load .lw (19 : Fin 32) a0 0x7C, 4) := by decide
theorem s5_at_452 : fetchRel sha512CompressCode 0x452 = some (.load .lw (20 : Fin 32) a0 0x78, 4) := by decide
theorem s5_at_456 : fetchRel sha512CompressCode 0x456 = some (.load .lw (21 : Fin 32) a0 0x74, 4) := by decide
theorem s5_at_45a : fetchRel sha512CompressCode 0x45A = some (.load .lw (22 : Fin 32) a0 0x70, 4) := by decide
theorem s5_at_45e : fetchRel sha512CompressCode 0x45E = some (.load .lw (23 : Fin 32) a0 0x6C, 4) := by decide
theorem s5_at_462 : fetchRel sha512CompressCode 0x462 = some (.load .lw (24 : Fin 32) a0 0x68, 4) := by decide
theorem s5_at_466 : fetchRel sha512CompressCode 0x466 = some (.load .lw (25 : Fin 32) a0 0x64, 4) := by decide
theorem s5_at_46a : fetchRel sha512CompressCode 0x46A = some (.load .lw (26 : Fin 32) a0 0x60, 4) := by decide
theorem s5_at_46e : fetchRel sha512CompressCode 0x46E = some (.load .lw (27 : Fin 32) a0 0x5C, 4) := by decide
theorem s5_at_472 : fetchRel sha512CompressCode 0x472 = some (.aluImm .add sp sp 0x390, 4) := by decide
theorem s5_at_476 : fetchRel sha512CompressCode 0x476 = some (.jalr x0 ra 0x0, 2) := by decide
theorem s5_at_478 : fetchRel sha512CompressCode 0x478 = some (.aluImm .add a1 x0 0x8, 2) := by decide
theorem s5_at_47a : fetchRel sha512CompressCode 0x47A = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem s5_at_47c : fetchRel sha512CompressCode 0x47C = some (.auipc ra 0xFFFF9000, 4) := by decide
theorem s5_at_480 : fetchRel sha512CompressCode 0x480 = some (.jalr ra ra 0xFFFFFB6A, 4) := by decide
end

end C3.RV32
