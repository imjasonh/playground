import C3BootProofs.Proofs.Block

/-! # `image::parse`'s instructions, decoded from the image's bytes -/

namespace C3.RV32

open C3.Image

set_option maxRecDepth 20000

theorem ip_at_0 : fetchRel imageParseCode 0x0 = some (.aluImm .add sp sp 0xFFFFFEA0, 2) := by decide
theorem ip_at_2 : fetchRel imageParseCode 0x2 = some (.aluImm .add a4 sp 0x100, 2) := by decide
theorem ip_at_4 : fetchRel imageParseCode 0x4 = some (.store .sw a4 ra 0x5C, 4) := by decide
theorem ip_at_8 : fetchRel imageParseCode 0x8 = some (.store .sw a4 s0 0x58, 2) := by decide
theorem ip_at_a : fetchRel imageParseCode 0xA = some (.store .sw a4 s1 0x54, 2) := by decide
theorem ip_at_c : fetchRel imageParseCode 0xC = some (.store .sw a4 s2 0x50, 4) := by decide
theorem ip_at_10 : fetchRel imageParseCode 0x10 = some (.store .sw a4 s3 0x4C, 4) := by decide
theorem ip_at_14 : fetchRel imageParseCode 0x14 = some (.store .sw a4 s4 0x48, 4) := by decide
theorem ip_at_18 : fetchRel imageParseCode 0x18 = some (.store .sw a4 s5 0x44, 4) := by decide
theorem ip_at_1c : fetchRel imageParseCode 0x1C = some (.store .sw a4 s6 0x40, 4) := by decide
theorem ip_at_20 : fetchRel imageParseCode 0x20 = some (.store .sw a4 (23 : Fin 32) 0x3C, 4) := by decide
theorem ip_at_24 : fetchRel imageParseCode 0x24 = some (.store .sw a4 (24 : Fin 32) 0x38, 4) := by decide
theorem ip_at_28 : fetchRel imageParseCode 0x28 = some (.store .sw a4 (25 : Fin 32) 0x34, 4) := by decide
theorem ip_at_2c : fetchRel imageParseCode 0x2C = some (.store .sw a4 (26 : Fin 32) 0x30, 4) := by decide
theorem ip_at_30 : fetchRel imageParseCode 0x30 = some (.store .sw a4 (27 : Fin 32) 0x2C, 4) := by decide
theorem ip_at_34 : fetchRel imageParseCode 0x34 = some (.alu .add s1 x0 a3, 2) := by decide
theorem ip_at_36 : fetchRel imageParseCode 0x36 = some (.alu .add s0 x0 a0, 2) := by decide
theorem ip_at_38 : fetchRel imageParseCode 0x38 = some (.store .sw sp a1 0x18, 2) := by decide
theorem ip_at_3a : fetchRel imageParseCode 0x3A = some (.store .sw sp a2 0x1C, 2) := by decide
theorem ip_at_3c : fetchRel imageParseCode 0x3C = some (.store .sw sp x0 0x20, 2) := by decide
theorem ip_at_3e : fetchRel imageParseCode 0x3E = some (.lui a1 0x4D493000, 4) := by decide
theorem ip_at_42 : fetchRel imageParseCode 0x42 = some (.aluImm .add a1 a1 0x343, 4) := by decide
theorem ip_at_46 : fetchRel imageParseCode 0x46 = some (.aluImm .add a0 sp 0x18, 2) := by decide
theorem ip_at_48 : fetchRel imageParseCode 0x48 = some (.auipc ra 0x0, 4) := by decide
theorem ip_at_4c : fetchRel imageParseCode 0x4C = some (.jalr ra ra 0xFFFFFD0A, 4) := by decide
theorem ip_at_50 : fetchRel imageParseCode 0x50 = some (.aluImm .and a1 a0 0xFF, 4) := by decide
theorem ip_at_54 : fetchRel imageParseCode 0x54 = some (.aluImm .add a1 a1 0xFFFFFF01, 4) := by decide
theorem ip_at_58 : fetchRel imageParseCode 0x58 = some (.branch .bne a1 x0 0x5E, 2) := by decide
theorem ip_at_5a : fetchRel imageParseCode 0x5A = some (.aluImm .add a0 sp 0x18, 2) := by decide
theorem ip_at_5c : fetchRel imageParseCode 0x5C = some (.auipc ra 0x0, 4) := by decide
theorem ip_at_60 : fetchRel imageParseCode 0x60 = some (.jalr ra ra 0xFFFFFD38, 4) := by decide
theorem ip_at_64 : fetchRel imageParseCode 0x64 = some (.aluImm .and a1 a0 0xFF, 4) := by decide
theorem ip_at_68 : fetchRel imageParseCode 0x68 = some (.aluImm .add a1 a1 0xFFFFFF01, 4) := by decide
theorem ip_at_6c : fetchRel imageParseCode 0x6C = some (.branch .bne a1 x0 0x4A, 2) := by decide
theorem ip_at_6e : fetchRel imageParseCode 0x6E = some (.aluImm .add a0 sp 0x18, 2) := by decide
theorem ip_at_70 : fetchRel imageParseCode 0x70 = some (.auipc ra 0x0, 4) := by decide
theorem ip_at_74 : fetchRel imageParseCode 0x74 = some (.jalr ra ra 0xFFFFFE4A, 4) := by decide
theorem ip_at_78 : fetchRel imageParseCode 0x78 = some (.aluImm .and a1 a0 0x1, 4) := by decide
theorem ip_at_7c : fetchRel imageParseCode 0x7C = some (.branch .beq a1 x0 0x6, 2) := by decide
theorem ip_at_7e : fetchRel imageParseCode 0x7E = some (.aluImm .srl a0 a0 0x8, 2) := by decide
theorem ip_at_80 : fetchRel imageParseCode 0x80 = some (.jal x0 0x36, 2) := by decide
theorem ip_at_82 : fetchRel imageParseCode 0x82 = some (.aluImm .srl a0 a0 0x10, 2) := by decide
theorem ip_at_84 : fetchRel imageParseCode 0x84 = some (.aluImm .add a1 x0 0x5, 2) := by decide
theorem ip_at_86 : fetchRel imageParseCode 0x86 = some (.branch .bne a0 a1 0x20, 4) := by decide
theorem ip_at_8a : fetchRel imageParseCode 0x8A = some (.aluImm .add a0 sp 0x18, 2) := by decide
theorem ip_at_8c : fetchRel imageParseCode 0x8C = some (.auipc ra 0x0, 4) := by decide
theorem ip_at_90 : fetchRel imageParseCode 0x90 = some (.jalr ra ra 0xFFFFFD32, 4) := by decide
theorem ip_at_94 : fetchRel imageParseCode 0x94 = some (.aluImm .and a0 a0 0x1, 2) := by decide
theorem ip_at_96 : fetchRel imageParseCode 0x96 = some (.alu .add s2 x0 a1, 2) := by decide
theorem ip_at_98 : fetchRel imageParseCode 0x98 = some (.branch .beq a0 x0 0x12, 2) := by decide
theorem ip_at_9a : fetchRel imageParseCode 0x9A = some (.aluImm .add a0 x0 0xFFFFFFFF, 2) := by decide
theorem ip_at_9c : fetchRel imageParseCode 0x9C = some (.store .sb s0 s2 0x0, 4) := by decide
theorem ip_at_a0 : fetchRel imageParseCode 0xA0 = some (.store .sb s0 a0 0xC, 4) := by decide
theorem ip_at_a4 : fetchRel imageParseCode 0xA4 = some (.jal x0 0x1C, 2) := by decide
theorem ip_at_a6 : fetchRel imageParseCode 0xA6 = some (.aluImm .add a0 x0 0x8, 2) := by decide
theorem ip_at_a8 : fetchRel imageParseCode 0xA8 = some (.jal x0 0xE, 2) := by decide
theorem ip_at_aa : fetchRel imageParseCode 0xAA = some (.aluImm .and a0 s2 0xFF, 4) := by decide
theorem ip_at_ae : fetchRel imageParseCode 0xAE = some (.aluImm .add a1 x0 0x10, 2) := by decide
theorem ip_at_b0 : fetchRel imageParseCode 0xB0 = some (.branch .bgeu a1 a0 0x32, 4) := by decide
theorem ip_at_b4 : fetchRel imageParseCode 0xB4 = some (.aluImm .add a0 x0 0x5, 2) := by decide
theorem ip_at_b6 : fetchRel imageParseCode 0xB6 = some (.aluImm .add a1 x0 0xFFFFFFFF, 2) := by decide
theorem ip_at_b8 : fetchRel imageParseCode 0xB8 = some (.store .sb s0 a0 0x0, 4) := by decide
theorem ip_at_bc : fetchRel imageParseCode 0xBC = some (.store .sb s0 a1 0xC, 4) := by decide
theorem ip_at_ca : fetchRel imageParseCode 0xCA = some (.load .lw (23 : Fin 32) a0 0x3C, 4) := by decide
theorem ip_at_ce : fetchRel imageParseCode 0xCE = some (.load .lw (24 : Fin 32) a0 0x38, 4) := by decide
theorem ip_at_d2 : fetchRel imageParseCode 0xD2 = some (.load .lw (25 : Fin 32) a0 0x34, 4) := by decide
theorem ip_at_d6 : fetchRel imageParseCode 0xD6 = some (.load .lw (26 : Fin 32) a0 0x30, 4) := by decide
theorem ip_at_da : fetchRel imageParseCode 0xDA = some (.load .lw (27 : Fin 32) a0 0x2C, 4) := by decide
theorem ip_at_de : fetchRel imageParseCode 0xDE = some (.aluImm .add sp sp 0x160, 2) := by decide
theorem ip_at_e2 : fetchRel imageParseCode 0xE2 = some (.aluImm .add a0 sp 0x18, 2) := by decide
theorem ip_at_e4 : fetchRel imageParseCode 0xE4 = some (.auipc ra 0x0, 4) := by decide
theorem ip_at_e8 : fetchRel imageParseCode 0xE8 = some (.jalr ra ra 0xFFFFFCDA, 4) := by decide
theorem ip_at_ec : fetchRel imageParseCode 0xEC = some (.aluImm .and a0 a0 0x1, 2) := by decide
theorem ip_at_ee : fetchRel imageParseCode 0xEE = some (.alu .add s3 x0 a1, 2) := by decide
theorem ip_at_f0 : fetchRel imageParseCode 0xF0 = some (.branch .beq a0 x0 0xA, 2) := by decide
theorem ip_at_f2 : fetchRel imageParseCode 0xF2 = some (.aluImm .add a0 x0 0xFFFFFFFF, 2) := by decide
theorem ip_at_f4 : fetchRel imageParseCode 0xF4 = some (.store .sb s0 s3 0x0, 4) := by decide
theorem ip_at_f8 : fetchRel imageParseCode 0xF8 = some (.jal x0 0xFFFFFFA8, 2) := by decide
theorem ip_at_fa : fetchRel imageParseCode 0xFA = some (.aluImm .add a0 s3 0xFFFFFFEF, 4) := by decide
theorem ip_at_fe : fetchRel imageParseCode 0xFE = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem ip_at_102 : fetchRel imageParseCode 0x102 = some (.aluImm .add a1 x0 0xEF, 4) := by decide
theorem ip_at_106 : fetchRel imageParseCode 0x106 = some (.branch .bgeu a1 a0 0xFFFFFFAE, 4) := by decide
theorem ip_at_10a : fetchRel imageParseCode 0x10A = some (.aluImm .add a0 sp 0x18, 2) := by decide
theorem ip_at_10c : fetchRel imageParseCode 0x10C = some (.aluImm .add a1 x0 0x2, 2) := by decide
theorem ip_at_10e : fetchRel imageParseCode 0x10E = some (.auipc ra 0x0, 4) := by decide
theorem ip_at_112 : fetchRel imageParseCode 0x112 = some (.jalr ra ra 0xFFFFFCEA, 4) := by decide
theorem ip_at_116 : fetchRel imageParseCode 0x116 = some (.aluImm .and a1 a0 0xFF, 4) := by decide
theorem ip_at_11a : fetchRel imageParseCode 0x11A = some (.aluImm .add a1 a1 0xFFFFFF01, 4) := by decide
theorem ip_at_11e : fetchRel imageParseCode 0x11E = some (.branch .bne a1 x0 0xFFFFFF98, 2) := by decide
theorem ip_at_120 : fetchRel imageParseCode 0x120 = some (.aluImm .add a0 sp 0x24, 2) := by decide
theorem ip_at_122 : fetchRel imageParseCode 0x122 = some (.aluImm .add a1 sp 0x18, 2) := by decide
theorem ip_at_124 : fetchRel imageParseCode 0x124 = some (.auipc ra 0x0, 4) := by decide
theorem ip_at_128 : fetchRel imageParseCode 0x128 = some (.jalr ra ra 0x2FC, 4) := by decide
theorem ip_at_12c : fetchRel imageParseCode 0x12C = some (.load .lbu a0 sp 0x24, 4) := by decide
theorem ip_at_130 : fetchRel imageParseCode 0x130 = some (.branch .bne a0 x0 0x16, 2) := by decide
theorem ip_at_132 : fetchRel imageParseCode 0x132 = some (.load .lw s4 sp 0x28, 2) := by decide
theorem ip_at_134 : fetchRel imageParseCode 0x134 = some (.aluImm .add a0 sp 0x24, 2) := by decide
theorem ip_at_136 : fetchRel imageParseCode 0x136 = some (.aluImm .add a1 sp 0x18, 2) := by decide
theorem ip_at_138 : fetchRel imageParseCode 0x138 = some (.auipc ra 0x0, 4) := by decide
theorem ip_at_13c : fetchRel imageParseCode 0x13C = some (.jalr ra ra 0x2E8, 4) := by decide
theorem ip_at_140 : fetchRel imageParseCode 0x140 = some (.load .lbu a0 sp 0x24, 4) := by decide
theorem ip_at_144 : fetchRel imageParseCode 0x144 = some (.branch .beq a0 x0 0x8, 2) := by decide
theorem ip_at_146 : fetchRel imageParseCode 0x146 = some (.load .lbu a0 sp 0x25, 4) := by decide
theorem ip_at_14a : fetchRel imageParseCode 0x14A = some (.jal x0 0xFFFFFF6C, 2) := by decide
theorem ip_at_14c : fetchRel imageParseCode 0x14C = some (.load .lw a0 sp 0x28, 2) := by decide
theorem ip_at_14e : fetchRel imageParseCode 0x14E = some (.branch .bne a0 s1 0x196, 4) := by decide
theorem ip_at_152 : fetchRel imageParseCode 0x152 = some (.store .sw sp s4 0x8, 2) := by decide
theorem ip_at_154 : fetchRel imageParseCode 0x154 = some (.aluImm .and a0 s3 0xFF, 4) := by decide
theorem ip_at_158 : fetchRel imageParseCode 0x158 = some (.store .sw sp a0 0xC, 2) := by decide
theorem ip_at_15a : fetchRel imageParseCode 0x15A = some (.aluImm .add a0 sp 0x24, 2) := by decide
theorem ip_at_15c : fetchRel imageParseCode 0x15C = some (.aluImm .add a1 x0 0x10, 2) := by decide
theorem ip_at_15e : fetchRel imageParseCode 0x15E = some (.branch .beq a1 x0 0x12, 2) := by decide
theorem ip_at_160 : fetchRel imageParseCode 0x160 = some (.aluImm .add a2 x0 0x0, 2) := by decide
theorem ip_at_162 : fetchRel imageParseCode 0x162 = some (.store .sw a0 a2 0x0, 2) := by decide
theorem ip_at_164 : fetchRel imageParseCode 0x164 = some (.store .sw a0 a2 0x4, 2) := by decide
theorem ip_at_166 : fetchRel imageParseCode 0x166 = some (.store .sw a0 a2 0x8, 2) := by decide
theorem ip_at_168 : fetchRel imageParseCode 0x168 = some (.store .sw a0 a2 0xC, 2) := by decide
theorem ip_at_16a : fetchRel imageParseCode 0x16A = some (.aluImm .add a0 a0 0x10, 2) := by decide
theorem ip_at_16c : fetchRel imageParseCode 0x16C = some (.aluImm .add a1 a1 0xFFFFFFFF, 2) := by decide
theorem ip_at_16e : fetchRel imageParseCode 0x16E = some (.branch .bne a1 x0 0xFFFFFFF2, 2) := by decide
theorem ip_at_170 : fetchRel imageParseCode 0x170 = some (.store .sw sp x0 0x10, 2) := by decide
theorem ip_at_172 : fetchRel imageParseCode 0x172 = some (.lui a0 0x10000, 2) := by decide
theorem ip_at_174 : fetchRel imageParseCode 0x174 = some (.load .lw (27 : Fin 32) sp 0xC, 2) := by decide
theorem ip_at_176 : fetchRel imageParseCode 0x176 = some (.aluImm .sll (27 : Fin 32) (27 : Fin 32) 0x4, 2) := by decide
theorem ip_at_178 : fetchRel imageParseCode 0x178 = some (.aluImm .add a0 a0 0xFFFFFFFF, 2) := by decide
theorem ip_at_17a : fetchRel imageParseCode 0x17A = some (.store .sw sp a0 0x14, 2) := by decide
theorem ip_at_17c : fetchRel imageParseCode 0x17C = some (.aluImm .add s5 (27 : Fin 32) 0x14, 4) := by decide
theorem ip_at_180 : fetchRel imageParseCode 0x180 = some (.aluImm .add (24 : Fin 32) x0 0x100, 4) := by decide
theorem ip_at_184 : fetchRel imageParseCode 0x184 = some (.aluImm .add (25 : Fin 32) sp 0x2C, 4) := by decide
theorem ip_at_188 : fetchRel imageParseCode 0x188 = some (.alu .add a0 (27 : Fin 32) (24 : Fin 32), 4) := by decide
theorem ip_at_18c : fetchRel imageParseCode 0x18C = some (.aluImm .add a0 a0 0xFFFFFF00, 4) := by decide
theorem ip_at_190 : fetchRel imageParseCode 0x190 = some (.branch .beq a0 x0 0x158, 4) := by decide
theorem ip_at_194 : fetchRel imageParseCode 0x194 = some (.branch .beq (24 : Fin 32) x0 0x154, 4) := by decide
theorem ip_at_198 : fetchRel imageParseCode 0x198 = some (.aluImm .add a0 sp 0x18, 2) := by decide
theorem ip_at_19a : fetchRel imageParseCode 0x19A = some (.auipc ra 0x0, 4) := by decide
theorem ip_at_19e : fetchRel imageParseCode 0x19E = some (.jalr ra ra 0xFFFFFC24, 4) := by decide
theorem ip_at_1a2 : fetchRel imageParseCode 0x1A2 = some (.aluImm .and a0 a0 0x1, 2) := by decide
theorem ip_at_1a4 : fetchRel imageParseCode 0x1A4 = some (.branch .bne a0 x0 0x6E, 2) := by decide
theorem ip_at_1a6 : fetchRel imageParseCode 0x1A6 = some (.aluImm .add a1 a1 0xFFFFFFFF, 2) := by decide
theorem ip_at_1a8 : fetchRel imageParseCode 0x1A8 = some (.aluImm .and s6 a1 0xFF, 4) := by decide
theorem ip_at_1ac : fetchRel imageParseCode 0x1AC = some (.aluImm .add a0 x0 0x3, 2) := by decide
theorem ip_at_1ae : fetchRel imageParseCode 0x1AE = some (.branch .bgeu a0 s6 0x8, 4) := by decide
theorem ip_at_1b2 : fetchRel imageParseCode 0x1B2 = some (.aluImm .add a1 x0 0x9, 2) := by decide
theorem ip_at_1b4 : fetchRel imageParseCode 0x1B4 = some (.jal x0 0x5E, 2) := by decide
theorem ip_at_1b6 : fetchRel imageParseCode 0x1B6 = some (.aluImm .add a0 sp 0x18, 2) := by decide
theorem ip_at_1b8 : fetchRel imageParseCode 0x1B8 = some (.aluImm .add a1 x0 0x3, 2) := by decide
theorem ip_at_1ba : fetchRel imageParseCode 0x1BA = some (.auipc ra 0x0, 4) := by decide
theorem ip_at_1be : fetchRel imageParseCode 0x1BE = some (.jalr ra ra 0xFFFFFC3E, 4) := by decide
theorem ip_at_1c2 : fetchRel imageParseCode 0x1C2 = some (.alu .add a1 x0 a0, 2) := by decide
theorem ip_at_1c4 : fetchRel imageParseCode 0x1C4 = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem ip_at_1c8 : fetchRel imageParseCode 0x1C8 = some (.aluImm .add a0 a0 0xFFFFFF01, 4) := by decide
theorem ip_at_1cc : fetchRel imageParseCode 0x1CC = some (.branch .bne a0 x0 0x46, 2) := by decide
theorem ip_at_1ce : fetchRel imageParseCode 0x1CE = some (.aluImm .add a0 sp 0x124, 2) := by decide
theorem ip_at_1d0 : fetchRel imageParseCode 0x1D0 = some (.aluImm .add a1 sp 0x18, 2) := by decide
theorem ip_at_1d2 : fetchRel imageParseCode 0x1D2 = some (.auipc ra 0x0, 4) := by decide
theorem ip_at_1d6 : fetchRel imageParseCode 0x1D6 = some (.jalr ra ra 0x24E, 4) := by decide
theorem ip_at_1da : fetchRel imageParseCode 0x1DA = some (.load .lbu a0 sp 0x124, 4) := by decide
theorem ip_at_1de : fetchRel imageParseCode 0x1DE = some (.branch .bne a0 x0 0x30, 2) := by decide
theorem ip_at_1e0 : fetchRel imageParseCode 0x1E0 = some (.load .lw (23 : Fin 32) sp 0x128, 4) := by decide
theorem ip_at_1e4 : fetchRel imageParseCode 0x1E4 = some (.aluImm .add a0 sp 0x124, 2) := by decide
theorem ip_at_1e6 : fetchRel imageParseCode 0x1E6 = some (.aluImm .add a1 sp 0x18, 2) := by decide
theorem ip_at_1e8 : fetchRel imageParseCode 0x1E8 = some (.auipc ra 0x0, 4) := by decide
theorem ip_at_1ec : fetchRel imageParseCode 0x1EC = some (.jalr ra ra 0x238, 4) := by decide
theorem ip_at_1f0 : fetchRel imageParseCode 0x1F0 = some (.load .lbu a0 sp 0x124, 4) := by decide
theorem ip_at_1f4 : fetchRel imageParseCode 0x1F4 = some (.branch .bne a0 x0 0x1A, 2) := by decide
theorem ip_at_1f6 : fetchRel imageParseCode 0x1F6 = some (.load .lw a0 sp 0x128, 4) := by decide
theorem ip_at_1fa : fetchRel imageParseCode 0x1FA = some (.store .sw sp a0 0x4, 2) := by decide
theorem ip_at_1fc : fetchRel imageParseCode 0x1FC = some (.aluImm .add a0 sp 0x124, 2) := by decide
theorem ip_at_1fe : fetchRel imageParseCode 0x1FE = some (.aluImm .add a1 sp 0x18, 2) := by decide
theorem ip_at_200 : fetchRel imageParseCode 0x200 = some (.auipc ra 0x0, 4) := by decide
theorem ip_at_204 : fetchRel imageParseCode 0x204 = some (.jalr ra ra 0x220, 4) := by decide
theorem ip_at_208 : fetchRel imageParseCode 0x208 = some (.load .lbu a0 sp 0x124, 4) := by decide
theorem ip_at_20c : fetchRel imageParseCode 0x20C = some (.branch .beq a0 x0 0xBE, 2) := by decide
theorem ip_at_20e : fetchRel imageParseCode 0x20E = some (.load .lbu a1 sp 0x125, 4) := by decide
theorem ip_at_212 : fetchRel imageParseCode 0x212 = some (.aluImm .and (23 : Fin 32) a1 0xFF, 4) := by decide
theorem ip_at_216 : fetchRel imageParseCode 0x216 = some (.aluImm .or (26 : Fin 32) (26 : Fin 32) 0xFF, 4) := by decide
theorem ip_at_21a : fetchRel imageParseCode 0x21A = some (.aluImm .and a2 (26 : Fin 32) 0xFF, 4) := by decide
theorem ip_at_21e : fetchRel imageParseCode 0x21E = some (.aluImm .add a0 a2 0xFFFFFF01, 4) := by decide
theorem ip_at_222 : fetchRel imageParseCode 0x222 = some (.branch .beq a0 x0 0xDA, 2) := by decide
theorem ip_at_224 : fetchRel imageParseCode 0x224 = some (.aluImm .add (16 : Fin 32) x0 0x9, 2) := by decide
theorem ip_at_226 : fetchRel imageParseCode 0x226 = some (.branch .beq s3 x0 0x1F2, 4) := by decide
theorem ip_at_22a : fetchRel imageParseCode 0x22A = some (.alu .add a1 s4 s3, 4) := by decide
theorem ip_at_22e : fetchRel imageParseCode 0x22E = some (.branch .bltu a1 s4 0xD2, 4) := by decide
theorem ip_at_232 : fetchRel imageParseCode 0x232 = some (.branch .bltu s1 a1 0x1E6, 4) := by decide
theorem ip_at_236 : fetchRel imageParseCode 0x236 = some (.aluImm .sll a4 (26 : Fin 32) 0x18, 4) := by decide
theorem ip_at_23a : fetchRel imageParseCode 0x23A = some (.aluImm .srl a4 a4 0x16, 2) := by decide
theorem ip_at_23c : fetchRel imageParseCode 0x23C = some (.lui a3 0x3FCC5000, 4) := by decide
theorem ip_at_240 : fetchRel imageParseCode 0x240 = some (.aluImm .add a3 a3 0x240, 4) := by decide
theorem ip_at_244 : fetchRel imageParseCode 0x244 = some (.alu .add a3 a3 a4, 2) := by decide
theorem ip_at_246 : fetchRel imageParseCode 0x246 = some (.load .lw a0 a3 0x0, 2) := by decide
theorem ip_at_248 : fetchRel imageParseCode 0x248 = some (.load .lw a3 sp 0x10, 2) := by decide
theorem ip_at_24a : fetchRel imageParseCode 0x24A = some (.aluImm .sll a3 a3 0x8, 2) := by decide
theorem ip_at_24c : fetchRel imageParseCode 0x24C = some (.aluImm .and a5 (23 : Fin 32) 0xFF, 4) := by decide
theorem ip_at_250 : fetchRel imageParseCode 0x250 = some (.alu .or a3 a3 a5, 2) := by decide
theorem ip_at_252 : fetchRel imageParseCode 0x252 = some (.alu .add a5 a3 s3, 4) := by decide
theorem ip_at_256 : fetchRel imageParseCode 0x256 = some (.branch .bltu a0 a5 0x1C2, 4) := by decide
theorem ip_at_25a : fetchRel imageParseCode 0x25A = some (.branch .bltu a5 a3 0x1BE, 4) := by decide
theorem ip_at_25e : fetchRel imageParseCode 0x25E = some (.lui a0 0x3FCC5000, 4) := by decide
theorem ip_at_262 : fetchRel imageParseCode 0x262 = some (.aluImm .add a0 a0 0x250, 4) := by decide
theorem ip_at_266 : fetchRel imageParseCode 0x266 = some (.alu .add a4 a4 a0, 2) := by decide
theorem ip_at_268 : fetchRel imageParseCode 0x268 = some (.load .lw a0 a4 0x0, 2) := by decide
theorem ip_at_26a : fetchRel imageParseCode 0x26A = some (.branch .bltu a3 a0 0x1AE, 4) := by decide
theorem ip_at_26e : fetchRel imageParseCode 0x26E = some (.alu .or a4 a3 s4, 4) := by decide
theorem ip_at_272 : fetchRel imageParseCode 0x272 = some (.load .lw a0 sp 0x14, 2) := by decide
theorem ip_at_274 : fetchRel imageParseCode 0x274 = some (.alu .and a0 a0 a4, 2) := by decide
theorem ip_at_276 : fetchRel imageParseCode 0x276 = some (.branch .beq a0 x0 0xA, 2) := by decide
theorem ip_at_278 : fetchRel imageParseCode 0x278 = some (.aluImm .add a0 x0 0x2, 2) := by decide
theorem ip_at_27a : fetchRel imageParseCode 0x27A = some (.branch .bltu a2 a0 0x19E, 4) := by decide
theorem ip_at_27e : fetchRel imageParseCode 0x27E = some (.jal x0 0x12, 2) := by decide
theorem ip_at_280 : fetchRel imageParseCode 0x280 = some (.aluImm .add a0 x0 0x1, 2) := by decide
theorem ip_at_282 : fetchRel imageParseCode 0x282 = some (.branch .bltu a0 a2 0xE, 4) := by decide
theorem ip_at_286 : fetchRel imageParseCode 0x286 = some (.load .lw a0 sp 0x14, 2) := by decide
theorem ip_at_288 : fetchRel imageParseCode 0x288 = some (.alu .and a0 s3 a0, 4) := by decide
theorem ip_at_28c : fetchRel imageParseCode 0x28C = some (.branch .bne a0 x0 0x18C, 4) := by decide
theorem ip_at_290 : fetchRel imageParseCode 0x290 = some (.aluImm .and a4 a4 0x3, 2) := by decide
theorem ip_at_292 : fetchRel imageParseCode 0x292 = some (.branch .beq a4 x0 0xA, 2) := by decide
theorem ip_at_294 : fetchRel imageParseCode 0x294 = some (.aluImm .add a0 x0 0x1, 2) := by decide
theorem ip_at_296 : fetchRel imageParseCode 0x296 = some (.branch .bltu a0 a2 0x182, 4) := by decide
theorem ip_at_29a : fetchRel imageParseCode 0x29A = some (.jal x0 0x14, 2) := by decide
theorem ip_at_29c : fetchRel imageParseCode 0x29C = some (.aluImm .and a0 s3 0x3, 4) := by decide
theorem ip_at_2a0 : fetchRel imageParseCode 0x2A0 = some (.aluImm .sltu a0 a0 0x1, 4) := by decide
theorem ip_at_2a4 : fetchRel imageParseCode 0x2A4 = some (.aluImm .sltu a2 a2 0x2, 4) := by decide
theorem ip_at_2a8 : fetchRel imageParseCode 0x2A8 = some (.alu .or a0 a0 a2, 2) := by decide
theorem ip_at_2aa : fetchRel imageParseCode 0x2AA = some (.branch .beq a0 x0 0x16E, 4) := by decide
theorem ip_at_2ae : fetchRel imageParseCode 0x2AE = some (.branch .bltu s4 s5 0x16A, 4) := by decide
theorem ip_at_2b2 : fetchRel imageParseCode 0x2B2 = some (.store .sw (25 : Fin 32) a3 0xFFFFFFF8, 4) := by decide
theorem ip_at_2b6 : fetchRel imageParseCode 0x2B6 = some (.store .sw (25 : Fin 32) s4 0xFFFFFFFC, 4) := by decide
theorem ip_at_2ba : fetchRel imageParseCode 0x2BA = some (.store .sw (25 : Fin 32) s3 0x0, 4) := by decide
theorem ip_at_2be : fetchRel imageParseCode 0x2BE = some (.store .sw (25 : Fin 32) (26 : Fin 32) 0x4, 4) := by decide
theorem ip_at_2c2 : fetchRel imageParseCode 0x2C2 = some (.aluImm .add (24 : Fin 32) (24 : Fin 32) 0xFFFFFFF0, 2) := by decide
theorem ip_at_2c4 : fetchRel imageParseCode 0x2C4 = some (.aluImm .add (25 : Fin 32) (25 : Fin 32) 0x10, 2) := by decide
theorem ip_at_2c6 : fetchRel imageParseCode 0x2C6 = some (.alu .add s5 x0 a1, 2) := by decide
theorem ip_at_2c8 : fetchRel imageParseCode 0x2C8 = some (.jal x0 0xFFFFFEC0, 2) := by decide
theorem ip_at_2ca : fetchRel imageParseCode 0x2CA = some (.load .lw s3 sp 0x128, 4) := by decide
theorem ip_at_2ce : fetchRel imageParseCode 0x2CE = some (.load .lw a0 sp 0x0, 2) := by decide
theorem ip_at_2d0 : fetchRel imageParseCode 0x2D0 = some (.aluImm .and a0 a0 0xFFFFFF00, 4) := by decide
theorem ip_at_2d4 : fetchRel imageParseCode 0x2D4 = some (.alu .or (26 : Fin 32) a0 s6, 4) := by decide
theorem ip_at_2d8 : fetchRel imageParseCode 0x2D8 = some (.aluImm .srl a0 (23 : Fin 32) 0x8, 4) := by decide
theorem ip_at_2dc : fetchRel imageParseCode 0x2DC = some (.store .sw sp a0 0x10, 2) := by decide
theorem ip_at_2de : fetchRel imageParseCode 0x2DE = some (.store .sw sp (26 : Fin 32) 0x0, 2) := by decide
theorem ip_at_2e0 : fetchRel imageParseCode 0x2E0 = some (.load .lw s4 sp 0x4, 2) := by decide
theorem ip_at_2e2 : fetchRel imageParseCode 0x2E2 = some (.jal x0 0xFFFFFF38, 2) := by decide
theorem ip_at_2e4 : fetchRel imageParseCode 0x2E4 = some (.aluImm .add a0 x0 0x7, 2) := by decide
theorem ip_at_2e6 : fetchRel imageParseCode 0x2E6 = some (.jal x0 0xFFFFFDD0, 2) := by decide
theorem ip_at_2e8 : fetchRel imageParseCode 0x2E8 = some (.branch .bne s5 s1 0x10, 4) := by decide
theorem ip_at_2ec : fetchRel imageParseCode 0x2EC = some (.aluImm .add a0 x0 0x10, 2) := by decide
theorem ip_at_2ee : fetchRel imageParseCode 0x2EE = some (.load .lw a1 sp 0xC, 2) := by decide
theorem ip_at_2f0 : fetchRel imageParseCode 0x2F0 = some (.branch .bgeu a0 a1 0x14, 4) := by decide
theorem ip_at_2f4 : fetchRel imageParseCode 0x2F4 = some (.aluImm .add (16 : Fin 32) x0 0x5, 2) := by decide
theorem ip_at_2f6 : fetchRel imageParseCode 0x2F6 = some (.jal x0 0x122, 2) := by decide
theorem ip_at_2f8 : fetchRel imageParseCode 0x2F8 = some (.aluImm .add (16 : Fin 32) x0 0x9, 2) := by decide
theorem ip_at_2fa : fetchRel imageParseCode 0x2FA = some (.jal x0 0x11E, 2) := by decide
theorem ip_at_2fc : fetchRel imageParseCode 0x2FC = some (.alu .add (16 : Fin 32) x0 (23 : Fin 32), 2) := by decide
theorem ip_at_2fe : fetchRel imageParseCode 0x2FE = some (.jal x0 0x11A, 2) := by decide
theorem ip_at_300 : fetchRel imageParseCode 0x300 = some (.aluImm .add (16 : Fin 32) x0 0x6, 2) := by decide
theorem ip_at_302 : fetchRel imageParseCode 0x302 = some (.jal x0 0x116, 2) := by decide
theorem ip_at_304 : fetchRel imageParseCode 0x304 = some (.aluImm .add s4 x0 0x0, 2) := by decide
theorem ip_at_306 : fetchRel imageParseCode 0x306 = some (.load .lw a0 sp 0xC, 2) := by decide
theorem ip_at_308 : fetchRel imageParseCode 0x308 = some (.aluImm .sltu a0 a0 0x11, 4) := by decide
theorem ip_at_30c : fetchRel imageParseCode 0x30C = some (.aluImm .add s5 sp 0x24, 4) := by decide
theorem ip_at_310 : fetchRel imageParseCode 0x310 = some (.alu .sub a0 x0 a0, 4) := by decide
theorem ip_at_314 : fetchRel imageParseCode 0x314 = some (.alu .and a0 a0 s5, 4) := by decide
theorem ip_at_318 : fetchRel imageParseCode 0x318 = some (.store .sw sp a0 0x14, 2) := by decide
theorem ip_at_31a : fetchRel imageParseCode 0x31A = some (.alu .add (27 : Fin 32) (27 : Fin 32) s5, 2) := by decide
theorem ip_at_31c : fetchRel imageParseCode 0x31C = some (.aluImm .add s6 x0 0x2, 2) := by decide
theorem ip_at_31e : fetchRel imageParseCode 0x31E = some (.branch .beq s5 (27 : Fin 32) 0xA2, 4) := by decide
theorem ip_at_322 : fetchRel imageParseCode 0x322 = some (.load .lw a1 s5 0x0, 4) := by decide
theorem ip_at_326 : fetchRel imageParseCode 0x326 = some (.load .lbu a2 s5 0xC, 4) := by decide
theorem ip_at_32a : fetchRel imageParseCode 0x32A = some (.aluImm .add a0 sp 0x124, 2) := by decide
theorem ip_at_32c : fetchRel imageParseCode 0x32C = some (.auipc ra 0x0, 4) := by decide
theorem ip_at_330 : fetchRel imageParseCode 0x330 = some (.jalr ra ra 0x144, 4) := by decide
theorem ip_at_334 : fetchRel imageParseCode 0x334 = some (.load .lbu (23 : Fin 32) sp 0x124, 4) := by decide
theorem ip_at_338 : fetchRel imageParseCode 0x338 = some (.branch .beq (23 : Fin 32) s6 0xDC, 4) := by decide
theorem ip_at_33c : fetchRel imageParseCode 0x33C = some (.load .lw (25 : Fin 32) sp 0x128, 4) := by decide
theorem ip_at_340 : fetchRel imageParseCode 0x340 = some (.aluImm .add (24 : Fin 32) s5 0x10, 4) := by decide
theorem ip_at_344 : fetchRel imageParseCode 0x344 = some (.aluImm .add s4 s4 0x1, 2) := by decide
theorem ip_at_346 : fetchRel imageParseCode 0x346 = some (.load .lw s3 sp 0x14, 2) := by decide
theorem ip_at_348 : fetchRel imageParseCode 0x348 = some (.alu .add a1 x0 s4, 2) := by decide
theorem ip_at_34a : fetchRel imageParseCode 0x34A = some (.branch .bne a1 x0 0x60, 2) := by decide
theorem ip_at_34c : fetchRel imageParseCode 0x34C = some (.alu .add (26 : Fin 32) x0 s3, 2) := by decide
theorem ip_at_34e : fetchRel imageParseCode 0x34E = some (.branch .beq s3 (27 : Fin 32) 0x6C, 4) := by decide
theorem ip_at_352 : fetchRel imageParseCode 0x352 = some (.aluImm .add s3 (26 : Fin 32) 0x10, 4) := by decide
theorem ip_at_356 : fetchRel imageParseCode 0x356 = some (.branch .beq (26 : Fin 32) x0 0x64, 4) := by decide
theorem ip_at_35a : fetchRel imageParseCode 0x35A = some (.load .lw a1 (26 : Fin 32) 0x0, 4) := by decide
theorem ip_at_35e : fetchRel imageParseCode 0x35E = some (.load .lbu a2 (26 : Fin 32) 0xC, 4) := by decide
theorem ip_at_362 : fetchRel imageParseCode 0x362 = some (.aluImm .add a0 sp 0x124, 2) := by decide
theorem ip_at_364 : fetchRel imageParseCode 0x364 = some (.auipc ra 0x0, 4) := by decide
theorem ip_at_368 : fetchRel imageParseCode 0x368 = some (.jalr ra ra 0x10C, 4) := by decide
theorem ip_at_36c : fetchRel imageParseCode 0x36C = some (.load .lbu a0 sp 0x124, 4) := by decide
theorem ip_at_370 : fetchRel imageParseCode 0x370 = some (.branch .beq a0 s6 0xA4, 4) := by decide
theorem ip_at_374 : fetchRel imageParseCode 0x374 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem ip_at_376 : fetchRel imageParseCode 0x376 = some (.branch .bne (23 : Fin 32) a0 0xFFFFFFD4, 4) := by decide
theorem ip_at_37a : fetchRel imageParseCode 0x37A = some (.load .lw a2 s5 0x8, 4) := by decide
theorem ip_at_37e : fetchRel imageParseCode 0x37E = some (.alu .add a1 a2 (25 : Fin 32), 4) := by decide
theorem ip_at_382 : fetchRel imageParseCode 0x382 = some (.aluImm .add (16 : Fin 32) x0 0xA, 2) := by decide
theorem ip_at_384 : fetchRel imageParseCode 0x384 = some (.branch .bltu a1 a2 0x94, 4) := by decide
theorem ip_at_388 : fetchRel imageParseCode 0x388 = some (.load .lw a2 sp 0x128, 4) := by decide
theorem ip_at_38c : fetchRel imageParseCode 0x38C = some (.load .lw a4 (26 : Fin 32) 0x8, 4) := by decide
theorem ip_at_390 : fetchRel imageParseCode 0x390 = some (.alu .add a3 a4 a2, 4) := by decide
theorem ip_at_394 : fetchRel imageParseCode 0x394 = some (.alu .sltu a4 a3 a4, 4) := by decide
theorem ip_at_398 : fetchRel imageParseCode 0x398 = some (.branch .bne a4 x0 0x80, 2) := by decide
theorem ip_at_39a : fetchRel imageParseCode 0x39A = some (.alu .sltu a3 (25 : Fin 32) a3, 4) := by decide
theorem ip_at_39e : fetchRel imageParseCode 0x39E = some (.alu .sltu a1 a2 a1, 4) := by decide
theorem ip_at_3a2 : fetchRel imageParseCode 0x3A2 = some (.alu .and a3 a3 a1, 2) := by decide
theorem ip_at_3a4 : fetchRel imageParseCode 0x3A4 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem ip_at_3a6 : fetchRel imageParseCode 0x3A6 = some (.branch .bne a3 x0 0x72, 2) := by decide
theorem ip_at_3a8 : fetchRel imageParseCode 0x3A8 = some (.jal x0 0xFFFFFFA2, 2) := by decide
theorem ip_at_3aa : fetchRel imageParseCode 0x3AA = some (.alu .sub a0 (27 : Fin 32) s3, 4) := by decide
theorem ip_at_3ae : fetchRel imageParseCode 0x3AE = some (.aluImm .srl a0 a0 0x4, 2) := by decide
theorem ip_at_3b0 : fetchRel imageParseCode 0x3B0 = some (.aluImm .sll (26 : Fin 32) a1 0x4, 4) := by decide
theorem ip_at_3b4 : fetchRel imageParseCode 0x3B4 = some (.alu .add (26 : Fin 32) (26 : Fin 32) s3, 2) := by decide
theorem ip_at_3b6 : fetchRel imageParseCode 0x3B6 = some (.branch .bltu a1 a0 0xFFFFFF9C, 4) := by decide
theorem ip_at_3ba : fetchRel imageParseCode 0x3BA = some (.alu .add s5 x0 (24 : Fin 32), 2) := by decide
theorem ip_at_3bc : fetchRel imageParseCode 0x3BC = some (.branch .bne (24 : Fin 32) (27 : Fin 32) 0xFFFFFF66, 4) := by decide
theorem ip_at_3c0 : fetchRel imageParseCode 0x3C0 = some (.load .lw a1 sp 0x8, 2) := by decide
theorem ip_at_3c2 : fetchRel imageParseCode 0x3C2 = some (.aluImm .and a1 a1 0x1, 2) := by decide
theorem ip_at_3c4 : fetchRel imageParseCode 0x3C4 = some (.aluImm .add (16 : Fin 32) x0 0xB, 2) := by decide
theorem ip_at_3c6 : fetchRel imageParseCode 0x3C6 = some (.branch .bne a1 x0 0x52, 2) := by decide
theorem ip_at_3c8 : fetchRel imageParseCode 0x3C8 = some (.load .lw a1 sp 0x14, 2) := by decide
theorem ip_at_3ca : fetchRel imageParseCode 0x3CA = some (.branch .beq a1 (27 : Fin 32) 0x4E, 4) := by decide
theorem ip_at_3ce : fetchRel imageParseCode 0x3CE = some (.load .lbu a2 a1 0xC, 4) := by decide
theorem ip_at_3d2 : fetchRel imageParseCode 0x3D2 = some (.aluImm .and a2 a2 0x1, 2) := by decide
theorem ip_at_3d4 : fetchRel imageParseCode 0x3D4 = some (.aluImm .add a0 a1 0x10, 4) := by decide
theorem ip_at_3d8 : fetchRel imageParseCode 0x3D8 = some (.store .sw sp a0 0x14, 2) := by decide
theorem ip_at_3da : fetchRel imageParseCode 0x3DA = some (.branch .bne a2 x0 0xFFFFFFEE, 2) := by decide
theorem ip_at_3dc : fetchRel imageParseCode 0x3DC = some (.load .lw a2 a1 0x0, 2) := by decide
theorem ip_at_3de : fetchRel imageParseCode 0x3DE = some (.load .lw a0 sp 0x8, 2) := by decide
theorem ip_at_3e0 : fetchRel imageParseCode 0x3E0 = some (.branch .bltu a0 a2 0xFFFFFFE8, 4) := by decide
theorem ip_at_3e4 : fetchRel imageParseCode 0x3E4 = some (.load .lw a1 a1 0x8, 2) := by decide
theorem ip_at_3e6 : fetchRel imageParseCode 0x3E6 = some (.load .lw a0 sp 0x8, 2) := by decide
theorem ip_at_3e8 : fetchRel imageParseCode 0x3E8 = some (.alu .sub a2 a0 a2, 4) := by decide
theorem ip_at_3ec : fetchRel imageParseCode 0x3EC = some (.branch .bgeu a2 a1 0xFFFFFFDC, 4) := by decide
theorem ip_at_3f0 : fetchRel imageParseCode 0x3F0 = some (.aluImm .add a1 sp 0x24, 2) := by decide
theorem ip_at_3f2 : fetchRel imageParseCode 0x3F2 = some (.aluImm .add a2 x0 0x100, 4) := by decide
theorem ip_at_3f6 : fetchRel imageParseCode 0x3F6 = some (.alu .add a0 x0 s0, 2) := by decide
theorem ip_at_3f8 : fetchRel imageParseCode 0x3F8 = some (.auipc ra 0x16000, 4) := by decide
theorem ip_at_3fc : fetchRel imageParseCode 0x3FC = some (.jalr ra ra 0x4D0, 4) := by decide
theorem ip_at_400 : fetchRel imageParseCode 0x400 = some (.load .lw a0 sp 0x8, 2) := by decide
theorem ip_at_402 : fetchRel imageParseCode 0x402 = some (.aluImm .add a1 s0 0x100, 4) := by decide
theorem ip_at_406 : fetchRel imageParseCode 0x406 = some (.store .sw a1 a0 0x0, 2) := by decide
theorem ip_at_408 : fetchRel imageParseCode 0x408 = some (.store .sw a1 s1 0x4, 2) := by decide
theorem ip_at_40a : fetchRel imageParseCode 0x40A = some (.load .lw a0 sp 0xC, 2) := by decide
theorem ip_at_40c : fetchRel imageParseCode 0x40C = some (.store .sw a1 a0 0x8, 2) := by decide
theorem ip_at_40e : fetchRel imageParseCode 0x40E = some (.store .sb s0 s2 0x10C, 4) := by decide
theorem ip_at_412 : fetchRel imageParseCode 0x412 = some (.jal x0 0xFFFFFCAE, 2) := by decide
theorem ip_at_414 : fetchRel imageParseCode 0x414 = some (.load .lbu (16 : Fin 32) sp 0x125, 4) := by decide
theorem ip_at_418 : fetchRel imageParseCode 0x418 = some (.aluImm .add a1 x0 0xFFFFFFFF, 2) := by decide
theorem ip_at_41a : fetchRel imageParseCode 0x41A = some (.store .sb s0 (16 : Fin 32) 0x0, 4) := by decide
theorem ip_at_41e : fetchRel imageParseCode 0x41E = some (.jal x0 0xFFFFFC9E, 2) := by decide

end C3.RV32
